//! The different conditions that can be checked by an interior node in a constraint set BDD
#![expect(dead_code)]

use std::fmt::Display;

use itertools::Either;
use salsa::plumbing::AsId;

use crate::types::constraints::{
    ALWAYS_FALSE, ALWAYS_TRUE, ConstraintSetBuilder, ConstraintSetStorage, Node, NodeId,
    SourceOrderId, max_constructor_and_typevar_depth,
};
use crate::types::typevar::TypeVarSet;
use crate::types::{ApplyTypeMappingVisitor, BoundTypeVarInstance, Type, TypeContext, TypeMapping};
use crate::{Db, ProgramEnvironment};

/// The _provenance_ of a BDD constraint.
///
/// Most bounds come from specific relationships found at the call site — for instance, the
/// relationship between the argument type and parameter annotation when invoking a generic
/// function. These bounds express actual user intent, and are called _evidence_ bounds.
///
/// Other bounds are background limitations on which specializations are valid — for instance, a
/// typevar's declared `bound_or_constraints`. These are called _validity_ bounds. Importantly, we
/// don't want to choose a validity bound as a solution unless we have no other choice. There is
/// often an evidence bound that is a better choice.
///
/// A bound derived only from validity remains validity. Any derivation that also depends on
/// evidence is itself evidence.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(crate) enum ConstraintProvenance {
    Validity,
    Evidence,
}

impl ConstraintProvenance {
    /// Returns the provenance of a constraint derived from two existing constraints.
    ///
    /// Derived constraints must retain any call-site evidence that contributed to them. Otherwise,
    /// a derivation could downgrade evidence to a background validity restriction, causing the
    /// solver to ignore a specialization justified by the call site.
    pub(super) const fn derived(left: Self, right: Self) -> Self {
        match (left, right) {
            (Self::Validity, Self::Validity) => Self::Validity,
            _ => Self::Evidence,
        }
    }

    /// Returns the provenance of a bound produced by simplifying two existing bounds.
    ///
    /// Simplifying bounds can make one input redundant, and a redundant input must not affect
    /// provenance. In particular, allowing redundant evidence to promote a surviving validity
    /// bound to evidence could make the solver choose a specialization that the call site does not
    /// actually support. When neither input alone
    /// determines the combined bound, its provenance must reflect both inputs.
    pub(super) fn simplified<'db>(
        left_provenance: Self,
        left_bound: Type<'db>,
        right_provenance: Self,
        right_bound: Type<'db>,
        combined: Type<'db>,
    ) -> Self {
        match (combined == left_bound, combined == right_bound) {
            (true, false) => left_provenance,
            (false, true) => right_provenance,
            _ => ConstraintProvenance::derived(left_provenance, right_provenance),
        }
    }
}

pub(super) struct UnsatisfiableBound;

/// One condition that can be checked by an interior node in a constraint set BDD
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(crate) enum Constraint<'db> {
    ConcreteLower(ConcreteLowerBound<'db>),
    ConcreteUpper(ConcreteUpperBound<'db>),
    ConcreteEquivalence(ConcreteEquivalenceBound<'db>),
    TypeVarRange(TypeVarRangeBound<'db>),
    TypeVarEquivalence(TypeVarEquivalenceBound<'db>),
}

impl<'db> Constraint<'db> {
    pub(super) fn new_node(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let constraint_id = storage.intern_constraint(db, env, self);
        Node::new_constraint(storage, constraint_id)
    }

    pub(super) fn new_nodes(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        storage: &mut ConstraintSetStorage<'db>,
        constraints: impl IntoIterator<Item = Result<Self, UnsatisfiableBound>>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let (mut node, mut source_order) = (ALWAYS_TRUE, None);
        for constraint in constraints {
            let Ok(constraint) = constraint else {
                return (ALWAYS_FALSE, None);
            };
            let (constraint_node, constraint_source_order) = constraint.new_node(db, env, storage);
            node = node.and(storage, constraint_node);
            source_order = storage.ordered_source_order(source_order, constraint_source_order);
        }
        (node, source_order)
    }

    /// Returns the constraints that model the requirement that `bound` must be assignable to
    /// `typevar`. Union lower bounds are broken apart into separate constraints. Returns no
    /// constraints when the relationship always holds (e.g. when comparing a typevar with itself).
    pub(super) fn new_lower_bound(
        db: &'db dyn Db,
        provenance: ConstraintProvenance,
        typevar: BoundTypeVarInstance<'db>,
        bound: Type<'db>,
    ) -> impl Iterator<Item = Result<Self, UnsatisfiableBound>> {
        let choose_lower_bound = move |bound: Type<'db>| match bound {
            // Two identical typevars must always solve to the same type, so it is not useful to
            // have a lower bound that is the typevar being constrained.
            Type::TypeVar(lower) if typevar.is_same_typevar_as(db, lower) => None,

            // The same applies for a lower bound that's an intersection containing the typevar
            // being constrained.
            Type::Intersection(intersection)
                if intersection.positive(db).iter().any(|element| {
                    element.as_typevar().is_some_and(|element_bound_typevar| {
                        typevar.is_same_typevar_as(db, element_bound_typevar)
                    })
                }) =>
            {
                None
            }

            // And if we find the _negation_ of the typevar being constrained, the overall result
            // is unsatisfiable.
            Type::Intersection(intersection)
                if intersection.negative(db).iter().any(|element| {
                    element.as_typevar().is_some_and(|element_bound_typevar| {
                        typevar.is_same_typevar_as(db, element_bound_typevar)
                    })
                }) =>
            {
                Some(Err(UnsatisfiableBound))
            }

            // Otherwise we construct a concrete or typevar constraint, as appropriate.
            Type::TypeVar(lower) => Some(Ok(Constraint::TypeVarRange(TypeVarRangeBound {
                provenance,
                left: lower,
                right: typevar,
            }))),
            _ => Some(Ok(Constraint::ConcreteLower(ConcreteLowerBound {
                provenance,
                typevar,
                bound,
            }))),
        };

        // It's not useful for a lower bound to be a union type. Because the following equivalence
        // holds, we can break these bounds apart and create an equivalent BDD with more nodes but
        // simpler constraints. (Fewer, simpler constraints mean that our sequent maps won't grow
        // pathologically large.)
        //
        //   (α | β) ≤ T   ⇔ (α ≤ T) ∧ (β ≤ T)
        match bound {
            Type::Union(bound) => Either::Left(
                bound
                    .elements(db)
                    .iter()
                    .copied()
                    .filter_map(choose_lower_bound),
            ),
            _ => Either::Right(choose_lower_bound(bound).into_iter()),
        }
    }

    /// Returns the constraints that model the requirement that `typevar` must be assignable to
    /// `bound`. Intersection upper bounds are broken apart into separate constraints. We also
    /// return whether each constraint should hold (for positive intersection elements) or not hold
    /// (for negative). Returns no constraints when the relationship always holds (e.g. when
    /// comparing a typevar with itself).
    pub(super) fn new_upper_bound(
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
        provenance: ConstraintProvenance,
        typevar: BoundTypeVarInstance<'db>,
        bound: Type<'db>,
    ) -> impl Iterator<Item = Result<Self, UnsatisfiableBound>> {
        let choose_upper_bound = move |bound: Type<'db>| match bound {
            // Two identical typevars must always solve to the same type, so it is not useful to
            // have an upper bound that is the typevar being constrained.
            Type::TypeVar(upper) if typevar.is_same_typevar_as(db, upper) => None,

            // The same applies for an upper bound that's a union containing the typevar
            // being constrained.
            Type::Union(union)
                if union.elements(db).iter().any(|element| {
                    element.as_typevar().is_some_and(|element_bound_typevar| {
                        typevar.is_same_typevar_as(db, element_bound_typevar)
                    })
                }) =>
            {
                None
            }

            // Otherwise we construct a concrete or typevar constraint, as appropriate.
            Type::TypeVar(upper) => Some(Ok(Constraint::TypeVarRange(TypeVarRangeBound {
                provenance,
                left: typevar,
                right: upper,
            }))),
            _ => Some(Ok(Constraint::ConcreteUpper(ConcreteUpperBound {
                provenance,
                typevar,
                bound,
            }))),
        };

        // It's not useful for an upper bound to be an intersection type. Because the following
        // equivalences hold, we can break these bounds apart and create an equivalent BDD with
        // more nodes but simpler constraints. (Fewer, simpler constraints mean that our sequent
        // maps won't grow pathologically large.)
        //
        //   T ≤ (α & β)   ⇔ (T ≤ α) ∧ (T ≤ β)
        //   T ≤ (¬α & ¬β) ⇔ (T ≤ ¬α) ∧ (T ≤ ¬β)
        match bound {
            Type::Intersection(bound) => {
                let positive = bound.iter_positive(db);
                let negative = bound.iter_negative(db).map(|ty| ty.negate(db, env));
                Either::Left(std::iter::chain(positive, negative).filter_map(choose_upper_bound))
            }
            _ => Either::Right(choose_upper_bound(bound).into_iter()),
        }
    }

    /// Returns the constraints that model the requirement that `typevar` must be equivalent to
    /// `bound`. Unlike [`new_lower_bound`][Self::new_lower_bound] and
    /// [`new_upper_bound`][Self::new_upper_bound], we do not break apart unions or intersections
    /// to create separate constraints. Returns `None` when the relationship always holds (e.g.
    /// when comparing a typevar with itself).
    pub(super) fn new_equivalence_bound(
        db: &'db dyn Db,
        provenance: ConstraintProvenance,
        typevar: BoundTypeVarInstance<'db>,
        bound: Type<'db>,
    ) -> Option<Result<Self, UnsatisfiableBound>> {
        match bound {
            // Two identical typevars must always solve to the same type, so it is not useful to
            // have an equivalence bound that is the typevar being constrained.
            Type::TypeVar(bound) if typevar.is_same_typevar_as(db, bound) => None,

            // The same applies for an equivalence bound that's an intersection containing the
            // typevar being constrained.
            Type::Intersection(intersection)
                if intersection.positive(db).iter().any(|element| {
                    element.as_typevar().is_some_and(|element_bound_typevar| {
                        typevar.is_same_typevar_as(db, element_bound_typevar)
                    })
                }) =>
            {
                None
            }

            // And if we find the _negation_ of the typevar being constrained, the overall result
            // is unsatisfiable.
            Type::Intersection(intersection)
                if intersection.negative(db).iter().any(|element| {
                    element.as_typevar().is_some_and(|element_bound_typevar| {
                        typevar.is_same_typevar_as(db, element_bound_typevar)
                    })
                }) =>
            {
                Some(Err(UnsatisfiableBound))
            }

            // The same applies for an equivalence bound that's a union containing the typevar
            // being constrained.
            Type::Union(union)
                if union.elements(db).iter().any(|element| {
                    element.as_typevar().is_some_and(|element_bound_typevar| {
                        typevar.is_same_typevar_as(db, element_bound_typevar)
                    })
                }) =>
            {
                None
            }

            // Otherwise we construct a concrete or typevar constraint, as appropriate.
            Type::TypeVar(bound) => Some(Ok(Constraint::TypeVarEquivalence(
                TypeVarEquivalenceBound::new(provenance, typevar, bound),
            ))),
            _ => Some(Ok(Constraint::ConcreteEquivalence(
                ConcreteEquivalenceBound {
                    provenance,
                    typevar,
                    bound,
                },
            ))),
        }
    }

    pub(super) fn is_reflexive_typevar_relation(self, db: &'db dyn Db) -> bool {
        match self {
            Constraint::TypeVarRange(this) => this.left.is_same_typevar_as(db, this.right),
            Constraint::TypeVarEquivalence(this) => this.left.is_same_typevar_as(db, this.right),
            Constraint::ConcreteLower(_)
            | Constraint::ConcreteUpper(_)
            | Constraint::ConcreteEquivalence(_) => false,
        }
    }

    pub(super) fn provides_lower(self) -> bool {
        matches!(
            self,
            Constraint::ConcreteLower(_)
                | Constraint::ConcreteEquivalence(_)
                | Constraint::TypeVarRange(_)
                | Constraint::TypeVarEquivalence(_)
        )
    }

    pub(super) fn provides_upper(self) -> bool {
        matches!(
            self,
            Constraint::ConcreteUpper(_)
                | Constraint::ConcreteEquivalence(_)
                | Constraint::TypeVarRange(_)
                | Constraint::TypeVarEquivalence(_)
        )
    }

    pub(super) fn as_concrete(
        self,
        db: &'db dyn Db,
        env: &ProgramEnvironment<'db>,
    ) -> Option<BoundTypeVarInstance<'db>> {
        let bound_is_concrete = |bound: Type<'db>| {
            !bound.has_typevar(db, env)
                && !bound.has_unspecialized_type_var(db, env)
                && bound.bottom_materialization(db, env) == bound.top_materialization(db, env)
        };
        match self {
            Constraint::ConcreteLower(this) => {
                bound_is_concrete(this.bound).then_some(this.typevar)
            }
            Constraint::ConcreteUpper(this) => {
                bound_is_concrete(this.bound).then_some(this.typevar)
            }
            Constraint::ConcreteEquivalence(this) => {
                bound_is_concrete(this.bound).then_some(this.typevar)
            }
            Constraint::TypeVarRange(_) | Constraint::TypeVarEquivalence(_) => None,
        }
    }

    pub(crate) fn bound_depth(self, db: &'db dyn Db, env: &ProgramEnvironment<'db>) -> (u16, u16) {
        match self {
            Constraint::ConcreteLower(this) => {
                max_constructor_and_typevar_depth(db, env, this.bound)
            }
            Constraint::ConcreteUpper(this) => {
                max_constructor_and_typevar_depth(db, env, this.bound)
            }
            Constraint::ConcreteEquivalence(this) => {
                max_constructor_and_typevar_depth(db, env, this.bound)
            }
            Constraint::TypeVarRange(_) | Constraint::TypeVarEquivalence(_) => (0, 0),
        }
    }

    pub(super) fn directly_constrains_inferable_typevar(
        self,
        db: &'db dyn Db,
        inferable: TypeVarSet<'db>,
    ) -> bool {
        match self {
            Constraint::ConcreteLower(this) => this.typevar.is_inferable(db, inferable),
            Constraint::ConcreteUpper(this) => this.typevar.is_inferable(db, inferable),
            Constraint::ConcreteEquivalence(this) => this.typevar.is_inferable(db, inferable),
            Constraint::TypeVarRange(this) => {
                this.left.is_inferable(db, inferable) || this.right.is_inferable(db, inferable)
            }
            Constraint::TypeVarEquivalence(this) => {
                this.left.is_inferable(db, inferable) || this.right.is_inferable(db, inferable)
            }
        }
    }

    pub(super) fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        builder: &ConstraintSetBuilder<'db>,
        type_mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        match self {
            Constraint::ConcreteLower(this) => {
                this.apply_type_mapping_impl(db, builder, type_mapping, tcx, visitor)
            }
            Constraint::ConcreteUpper(this) => {
                this.apply_type_mapping_impl(db, builder, type_mapping, tcx, visitor)
            }
            Constraint::ConcreteEquivalence(this) => {
                this.apply_type_mapping_impl(db, builder, type_mapping, tcx, visitor)
            }
            Constraint::TypeVarRange(this) => {
                this.apply_type_mapping_impl(db, builder, type_mapping, tcx, visitor)
            }
            Constraint::TypeVarEquivalence(this) => {
                this.apply_type_mapping_impl(db, builder, type_mapping, tcx, visitor)
            }
        }
    }

    pub(super) fn types(self) -> impl Iterator<Item = Type<'db>> {
        let types = match self {
            Constraint::ConcreteLower(this) => [Type::TypeVar(this.typevar), this.bound],
            Constraint::ConcreteUpper(this) => [Type::TypeVar(this.typevar), this.bound],
            Constraint::ConcreteEquivalence(this) => [Type::TypeVar(this.typevar), this.bound],
            Constraint::TypeVarRange(this) => [Type::TypeVar(this.left), Type::TypeVar(this.right)],
            Constraint::TypeVarEquivalence(this) => {
                [Type::TypeVar(this.left), Type::TypeVar(this.right)]
            }
        };
        types.into_iter()
    }

    pub(super) fn display<'a>(
        self,
        db: &'db dyn Db,
        env: &'a ProgramEnvironment<'db>,
        holds: Option<bool>,
    ) -> impl Display + 'a {
        std::fmt::from_fn(move |f| match self {
            Constraint::ConcreteLower(this) => this.display(db, env, holds).fmt(f),
            Constraint::ConcreteUpper(this) => this.display(db, env, holds).fmt(f),
            Constraint::ConcreteEquivalence(this) => this.display(db, env, holds).fmt(f),
            Constraint::TypeVarRange(this) => this.display(db, holds).fmt(f),
            Constraint::TypeVarEquivalence(this) => this.display(db, holds).fmt(f),
        })
    }
}

pub(super) trait ProvidesConcreteBound<'db>: Copy {
    fn provenance(self) -> ConstraintProvenance;
    fn typevar(self) -> BoundTypeVarInstance<'db>;
    fn bound(self) -> Type<'db>;
    fn constraint(self) -> Constraint<'db>;
    fn map(self, provenance: ConstraintProvenance, bound: Type<'db>) -> Self;
}

pub(super) trait ProvidesConcreteLowerBound<'db>: ProvidesConcreteBound<'db> {
    fn into_lower_bound(self) -> ConcreteLowerBound<'db>;
}

pub(super) trait ProvidesConcreteUpperBound<'db>: ProvidesConcreteBound<'db> {
    fn into_upper_bound(self) -> ConcreteUpperBound<'db>;
}

pub(super) trait ProvidesTypeVarBound<'db>: Copy {
    fn provenance(self) -> ConstraintProvenance;
    fn left(self) -> BoundTypeVarInstance<'db>;
    fn right(self) -> BoundTypeVarInstance<'db>;
    fn constraint(self) -> Constraint<'db>;
}

pub(super) trait ProvidesTypeVarRangeBound<'db>: ProvidesTypeVarBound<'db> {}
pub(super) trait ProvidesTypeVarEquivalenceBound<'db>:
    ProvidesTypeVarRangeBound<'db>
{
}

/// Restricts a single typevar so that a concrete lower bound is assignable to it. (A concrete type
/// is not a bare typevar. [`TypeVarRangeBound`] is used to model an assignability relationship
/// between two typevars.)
///
/// The bound will never be a union type, since union lower bounds can be broken apart into
/// separate constraints for each union element.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct ConcreteLowerBound<'db> {
    pub(super) provenance: ConstraintProvenance,
    pub(super) typevar: BoundTypeVarInstance<'db>,
    pub(super) bound: Type<'db>,
}

impl<'db> ConcreteLowerBound<'db> {
    fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        builder: &ConstraintSetBuilder<'db>,
        type_mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let env = visitor.env;
        let subject =
            Type::TypeVar(self.typevar).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let bound = self
            .bound
            .apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let mut storage = builder.storage.borrow_mut();
        match subject {
            Type::TypeVar(typevar) => {
                let applied = Constraint::new_lower_bound(db, self.provenance, typevar, bound);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            _ => storage.load(
                db,
                env,
                &bound.when_constraint_set_assignable_to_owned(db, env, subject),
            ),
        }
    }

    fn display<'a>(
        self,
        db: &'db dyn Db,
        env: &'a ProgramEnvironment<'db>,
        holds: Option<bool>,
    ) -> impl Display + 'a {
        let range_prefix = match holds {
            Some(true) => "",
            Some(false) => "¬",
            None => "?",
        };
        std::fmt::from_fn(move |f| {
            write!(
                f,
                "{range_prefix}({} ≤ {})",
                self.bound.display(db, env),
                self.typevar.identity(db).display(db),
            )
        })
    }
}

impl<'db> ProvidesConcreteBound<'db> for ConcreteLowerBound<'db> {
    fn provenance(self) -> ConstraintProvenance {
        self.provenance
    }

    fn typevar(self) -> BoundTypeVarInstance<'db> {
        self.typevar
    }

    fn bound(self) -> Type<'db> {
        self.bound
    }

    fn constraint(self) -> Constraint<'db> {
        Constraint::ConcreteLower(self)
    }

    fn map(self, provenance: ConstraintProvenance, bound: Type<'db>) -> Self {
        Self {
            provenance,
            typevar: self.typevar,
            bound,
        }
    }
}

impl<'db> ProvidesConcreteLowerBound<'db> for ConcreteLowerBound<'db> {
    fn into_lower_bound(self) -> ConcreteLowerBound<'db> {
        self
    }
}

/// Restricts a single typevar so that it is assignable to a concrete upper bound. (A concrete type
/// is not a bare typevar. [`TypeVarRangeBound`] is used to model an assignability relationship
/// between two typevars.)
///
/// The bound will never be an intersection type, since intersection upper bounds can be broken
/// apart into separate constraints for each intersection element.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct ConcreteUpperBound<'db> {
    pub(super) provenance: ConstraintProvenance,
    pub(super) typevar: BoundTypeVarInstance<'db>,
    pub(super) bound: Type<'db>,
}

impl<'db> ConcreteUpperBound<'db> {
    fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        builder: &ConstraintSetBuilder<'db>,
        type_mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let env = visitor.env;
        let subject =
            Type::TypeVar(self.typevar).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let bound = self
            .bound
            .apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let mut storage = builder.storage.borrow_mut();
        match subject {
            Type::TypeVar(typevar) => {
                let applied = Constraint::new_upper_bound(db, env, self.provenance, typevar, bound);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            _ => storage.load(
                db,
                env,
                &subject.when_constraint_set_assignable_to_owned(db, env, bound),
            ),
        }
    }

    fn display<'a>(
        self,
        db: &'db dyn Db,
        env: &'a ProgramEnvironment<'db>,
        holds: Option<bool>,
    ) -> impl Display + 'a {
        let range_prefix = match holds {
            Some(true) => "",
            Some(false) => "¬",
            None => "?",
        };
        std::fmt::from_fn(move |f| {
            write!(
                f,
                "{range_prefix}({} ≤ {})",
                self.typevar.identity(db).display(db),
                self.bound.display(db, env),
            )
        })
    }
}

impl<'db> ProvidesConcreteBound<'db> for ConcreteUpperBound<'db> {
    fn provenance(self) -> ConstraintProvenance {
        self.provenance
    }

    fn typevar(self) -> BoundTypeVarInstance<'db> {
        self.typevar
    }

    fn bound(self) -> Type<'db> {
        self.bound
    }

    fn constraint(self) -> Constraint<'db> {
        Constraint::ConcreteUpper(self)
    }

    fn map(self, provenance: ConstraintProvenance, bound: Type<'db>) -> Self {
        Self {
            provenance,
            typevar: self.typevar,
            bound,
        }
    }
}

impl<'db> ProvidesConcreteUpperBound<'db> for ConcreteUpperBound<'db> {
    fn into_upper_bound(self) -> ConcreteUpperBound<'db> {
        self
    }
}

/// Restricts a single typevar so that it is equivalent to some concrete type. (A concrete type is
/// not a bare typevar. [`TypeVarEquivalenceBound`] is used to model an equivalence relationship
/// between two typevars.)
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct ConcreteEquivalenceBound<'db> {
    pub(super) provenance: ConstraintProvenance,
    pub(super) typevar: BoundTypeVarInstance<'db>,
    pub(super) bound: Type<'db>,
}

impl<'db> ConcreteEquivalenceBound<'db> {
    fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        builder: &ConstraintSetBuilder<'db>,
        type_mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let env = visitor.env;
        let subject =
            Type::TypeVar(self.typevar).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let bound = self
            .bound
            .apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let mut storage = builder.storage.borrow_mut();
        match subject {
            Type::TypeVar(typevar) => {
                let applied =
                    Constraint::new_equivalence_bound(db, self.provenance, typevar, bound);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            _ => storage.load(
                db,
                env,
                &subject.when_constraint_set_equivalent_to_owned(db, env, bound),
            ),
        }
    }

    fn display<'a>(
        self,
        db: &'db dyn Db,
        env: &'a ProgramEnvironment<'db>,
        holds: Option<bool>,
    ) -> impl Display + 'a {
        let equality_sign = match holds {
            Some(true) => "=",
            Some(false) => "≠",
            None => "=?",
        };
        std::fmt::from_fn(move |f| {
            write!(
                f,
                "({} {equality_sign} {})",
                self.typevar.identity(db).display(db),
                self.bound.display(db, env),
            )
        })
    }
}

impl<'db> ProvidesConcreteBound<'db> for ConcreteEquivalenceBound<'db> {
    fn provenance(self) -> ConstraintProvenance {
        self.provenance
    }

    fn typevar(self) -> BoundTypeVarInstance<'db> {
        self.typevar
    }

    fn bound(self) -> Type<'db> {
        self.bound
    }

    fn constraint(self) -> Constraint<'db> {
        Constraint::ConcreteEquivalence(self)
    }

    fn map(self, provenance: ConstraintProvenance, bound: Type<'db>) -> Self {
        Self {
            provenance,
            typevar: self.typevar,
            bound,
        }
    }
}

impl<'db> ProvidesConcreteLowerBound<'db> for ConcreteEquivalenceBound<'db> {
    fn into_lower_bound(self) -> ConcreteLowerBound<'db> {
        ConcreteLowerBound {
            provenance: self.provenance,
            typevar: self.typevar,
            bound: self.bound,
        }
    }
}

impl<'db> ProvidesConcreteUpperBound<'db> for ConcreteEquivalenceBound<'db> {
    fn into_upper_bound(self) -> ConcreteUpperBound<'db> {
        ConcreteUpperBound {
            provenance: self.provenance,
            typevar: self.typevar,
            bound: self.bound,
        }
    }
}

/// Restricts two typevars so that `left` must be assignable to `right`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct TypeVarRangeBound<'db> {
    pub(super) provenance: ConstraintProvenance,
    pub(super) left: BoundTypeVarInstance<'db>,
    pub(super) right: BoundTypeVarInstance<'db>,
}

impl<'db> TypeVarRangeBound<'db> {
    fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        builder: &ConstraintSetBuilder<'db>,
        type_mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let env = visitor.env;
        let left = Type::TypeVar(self.left).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let right =
            Type::TypeVar(self.right).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let mut storage = builder.storage.borrow_mut();
        match (left, right) {
            (Type::TypeVar(left_typevar), _) => {
                let applied =
                    Constraint::new_upper_bound(db, env, self.provenance, left_typevar, right);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            (_, Type::TypeVar(right_typevar)) => {
                let applied = Constraint::new_lower_bound(db, self.provenance, right_typevar, left);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            _ => storage.load(
                db,
                env,
                &left.when_constraint_set_assignable_to_owned(db, env, right),
            ),
        }
    }

    fn display(self, db: &'db dyn Db, holds: Option<bool>) -> impl Display {
        let range_prefix = match holds {
            Some(true) => "",
            Some(false) => "¬",
            None => "?",
        };
        std::fmt::from_fn(move |f| {
            write!(
                f,
                "{range_prefix}({} ≤ {})",
                self.left.identity(db).display(db),
                self.right.identity(db).display(db),
            )
        })
    }
}

impl<'db> ProvidesTypeVarBound<'db> for TypeVarRangeBound<'db> {
    fn provenance(self) -> ConstraintProvenance {
        self.provenance
    }

    fn left(self) -> BoundTypeVarInstance<'db> {
        self.left
    }

    fn right(self) -> BoundTypeVarInstance<'db> {
        self.right
    }

    fn constraint(self) -> Constraint<'db> {
        Constraint::TypeVarRange(self)
    }
}

impl<'db> ProvidesTypeVarRangeBound<'db> for TypeVarRangeBound<'db> {}

/// Restricts two typevars so that `left` must be equivalent to `right`.
///
/// (As an invariant, these are always created so that the typevar with the smaller salsa ID is
/// `left`. This does _not_ affect the BDD variable ordering assigned to this constraint in a
/// particular builder.)
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, get_size2::GetSize, salsa::SalsaValue)]
pub(super) struct TypeVarEquivalenceBound<'db> {
    pub(super) provenance: ConstraintProvenance,
    pub(super) left: BoundTypeVarInstance<'db>,
    pub(super) right: BoundTypeVarInstance<'db>,
}

impl<'db> TypeVarEquivalenceBound<'db> {
    pub(super) fn new(
        provenance: ConstraintProvenance,
        left: BoundTypeVarInstance<'db>,
        right: BoundTypeVarInstance<'db>,
    ) -> Self {
        let (left, right) = if left.as_id() > right.as_id() {
            (right, left)
        } else {
            (left, right)
        };
        Self {
            provenance,
            left,
            right,
        }
    }

    pub(super) fn forwards(self) -> impl ProvidesTypeVarEquivalenceBound<'db> {
        #[derive(Clone, Copy)]
        struct Forwards<'db>(TypeVarEquivalenceBound<'db>);

        impl<'db> ProvidesTypeVarBound<'db> for Forwards<'db> {
            fn provenance(self) -> ConstraintProvenance {
                self.0.provenance
            }

            fn left(self) -> BoundTypeVarInstance<'db> {
                self.0.left
            }

            fn right(self) -> BoundTypeVarInstance<'db> {
                self.0.right
            }

            fn constraint(self) -> Constraint<'db> {
                Constraint::TypeVarEquivalence(self.0)
            }
        }

        impl<'db> ProvidesTypeVarRangeBound<'db> for Forwards<'db> {}
        impl<'db> ProvidesTypeVarEquivalenceBound<'db> for Forwards<'db> {}

        Forwards(self)
    }

    pub(super) fn backwards(self) -> impl ProvidesTypeVarEquivalenceBound<'db> {
        #[derive(Clone, Copy)]
        struct Backwards<'db>(TypeVarEquivalenceBound<'db>);

        impl<'db> ProvidesTypeVarBound<'db> for Backwards<'db> {
            fn provenance(self) -> ConstraintProvenance {
                self.0.provenance
            }

            #[expect(clippy::misnamed_getters)]
            fn left(self) -> BoundTypeVarInstance<'db> {
                // Reversed!
                self.0.right
            }

            #[expect(clippy::misnamed_getters)]
            fn right(self) -> BoundTypeVarInstance<'db> {
                // Reversed!
                self.0.left
            }

            fn constraint(self) -> Constraint<'db> {
                Constraint::TypeVarEquivalence(self.0)
            }
        }

        impl<'db> ProvidesTypeVarRangeBound<'db> for Backwards<'db> {}
        impl<'db> ProvidesTypeVarEquivalenceBound<'db> for Backwards<'db> {}

        Backwards(self)
    }

    fn apply_type_mapping_impl(
        self,
        db: &'db dyn Db,
        builder: &ConstraintSetBuilder<'db>,
        type_mapping: &TypeMapping<'_, 'db>,
        tcx: TypeContext<'db>,
        visitor: &ApplyTypeMappingVisitor<'_, 'db>,
    ) -> (NodeId, Option<SourceOrderId>) {
        let env = visitor.env;
        let left = Type::TypeVar(self.left).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let right =
            Type::TypeVar(self.right).apply_type_mapping_impl(db, type_mapping, tcx, visitor);
        let mut storage = builder.storage.borrow_mut();
        match (left, right) {
            (Type::TypeVar(left_typevar), _) => {
                let applied =
                    Constraint::new_equivalence_bound(db, self.provenance, left_typevar, right);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            (_, Type::TypeVar(right_typevar)) => {
                let applied =
                    Constraint::new_equivalence_bound(db, self.provenance, right_typevar, left);
                Constraint::new_nodes(db, env, &mut storage, applied)
            }
            _ => storage.load(
                db,
                env,
                &left.when_constraint_set_equivalent_to_owned(db, env, right),
            ),
        }
    }

    fn display(self, db: &'db dyn Db, holds: Option<bool>) -> impl Display {
        let equality_sign = match holds {
            Some(true) => "=",
            Some(false) => "≠",
            None => "=?",
        };
        std::fmt::from_fn(move |f| {
            write!(
                f,
                "({} {equality_sign} {})",
                self.left.identity(db).display(db),
                self.right.identity(db).display(db),
            )
        })
    }
}
