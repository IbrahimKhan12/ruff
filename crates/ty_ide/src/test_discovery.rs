//! Presents collected pytest tests as editor items.

use ruff_db::parsed::parsed_module;
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::FxHashMap;
use ty_python_core::definition::DefinitionKind;
use ty_python_core::{ProgramFile, semantic_index};
use ty_python_semantic::pytest_tests_in_file;

use crate::Db;

/// Returns collected test functions and their containing classes in source order.
///
/// Collection follows pytest's default conventions, including `unittest.TestCase` methods.
/// Class items are included only when they contain a collected test, directly or in a nested
/// class. Identifiers and parent identifiers are relative to `file`.
fn discover_tests<'db>(db: &'db dyn Db, file: ProgramFile<'db>) -> Vec<DiscoveredTest> {
    let tests = pytest_tests_in_file(db, file);
    if tests.is_empty() {
        return Vec::new();
    }

    let module = parsed_module(db, file.python_file(db)).load(db);
    let index = semantic_index(db, file);
    let mut items = Vec::<DiscoveredTest>::new();
    let mut class_items = FxHashMap::default();

    for test in tests {
        let binding = test.binding();
        let Some(symbol) = binding.place(db).as_symbol() else {
            continue;
        };
        let name = index
            .place_table(binding.file_scope(db))
            .symbol(symbol)
            .name();
        let range = match binding.kind(db) {
            DefinitionKind::ImportFrom(import) => {
                let alias = import.alias(&module);
                alias.asname.as_ref().unwrap_or(&alias.name).range()
            }
            _ => binding.focus_range(db, &module).range(),
        };

        // Collection has already established that these enclosing classes are eligible.
        // Walk from the outermost class so every item's parent is present before the item.
        let classes = index
            .ancestor_scopes(binding.file_scope(db))
            .filter_map(|(scope_id, scope)| {
                Some((scope_id, scope.node().as_class()?.node(&module)))
            })
            .collect::<Vec<_>>();
        let mut parent: Option<usize> = None;
        for (scope_id, class) in classes.into_iter().rev() {
            parent = Some(*class_items.entry(scope_id).or_insert_with(|| {
                let item = DiscoveredTest::new(
                    &class.name,
                    class.name.range(),
                    DiscoveredTestKind::Class,
                    parent.map(|index| &items[index]),
                );
                let index = items.len();
                items.push(item);
                index
            }));
        }

        items.push(DiscoveredTest::new(
            name.as_str(),
            range,
            DiscoveredTestKind::Function,
            parent.map(|index| &items[index]),
        ));
    }

    items
}

/// A collected test function or a class containing collected tests.
#[derive(Debug, PartialEq, Eq)]
struct DiscoveredTest {
    /// File-relative pytest target, such as `TestUsers::test_lookup`.
    ///
    /// This identifier is unchanged by edits that only move the item's source location.
    id: String,
    /// Whether this item is a class or a function/method.
    kind: DiscoveredTestKind,
    /// The source range of the test binding or class name.
    range: TextRange,
    /// The collected test name or class name shown in the editor.
    label: String,
    /// The containing class's identifier, or `None` for a module-level item.
    parent: Option<String>,
}

impl DiscoveredTest {
    fn new(name: &str, range: TextRange, kind: DiscoveredTestKind, parent: Option<&Self>) -> Self {
        Self {
            id: parent.map_or_else(
                || name.to_string(),
                |parent| format!("{}::{name}", parent.id),
            ),
            kind,
            range,
            label: name.to_string(),
            parent: parent.map(|parent| parent.id.clone()),
        }
    }
}

/// Whether an editor item represents a test class or a test function/method.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DiscoveredTestKind {
    /// A class containing collected tests.
    Class,
    /// A collected function or method, including `unittest.TestCase` methods.
    Function,
}

#[cfg(test)]
mod tests {
    use ruff_db::source::source_text;
    use ruff_text_size::TextSize;

    use super::{DiscoveredTest, DiscoveredTestKind, discover_tests};
    use crate::tests::CursorTest;

    #[test]
    fn discovers_functions_and_test_classes() {
        let test = discovery_test(
            r#"
import unittest

def test_module(): ...

class TestUsers:
    def test_lookup(self): ...
    def test_update(self): ...

class UserCase(unittest.TestCase):
    def test_unit(self): ...
"#,
        );

        assert_eq!(
            item_details(&discovered_tests(&test)),
            [
                ("test_module", DiscoveredTestKind::Function, None),
                ("TestUsers", DiscoveredTestKind::Class, None),
                (
                    "TestUsers::test_lookup",
                    DiscoveredTestKind::Function,
                    Some("TestUsers")
                ),
                (
                    "TestUsers::test_update",
                    DiscoveredTestKind::Function,
                    Some("TestUsers")
                ),
                ("UserCase", DiscoveredTestKind::Class, None),
                (
                    "UserCase::test_unit",
                    DiscoveredTestKind::Function,
                    Some("UserCase")
                ),
            ]
        );
    }

    #[test]
    fn uses_binding_names_and_locations() {
        let mut test = discovery_test(
            r#"
from helpers import check as test_imported
from helpers import test_exported

def helper(): ...
test_alias = helper
test_second_alias = helper

class TestUsers:
    test_method = test_imported
"#,
        );
        test.write_file(
            "helpers.py",
            r#"
def check(): ...
def test_exported(): ...
"#,
        )
        .expect("writing imported test functions should succeed");

        assert_eq!(
            item_details(&discovered_tests(&test)),
            [
                ("test_imported", DiscoveredTestKind::Function, None),
                ("test_exported", DiscoveredTestKind::Function, None),
                ("test_alias", DiscoveredTestKind::Function, None),
                ("test_second_alias", DiscoveredTestKind::Function, None),
                ("TestUsers", DiscoveredTestKind::Class, None),
                (
                    "TestUsers::test_method",
                    DiscoveredTestKind::Function,
                    Some("TestUsers")
                ),
            ]
        );
    }

    #[test]
    fn preserves_nested_class_paths() {
        let test = discovery_test(
            r#"
class TestUsers[T]:
    class TestPermissions:
        def test_read[U](self): ...
        def test_write(self): ...

class TestGroups:
    class TestPermissions:
        def test_read(self): ...
"#,
        );

        assert_eq!(
            item_details(&discovered_tests(&test)),
            [
                ("TestUsers", DiscoveredTestKind::Class, None),
                (
                    "TestUsers::TestPermissions",
                    DiscoveredTestKind::Class,
                    Some("TestUsers")
                ),
                (
                    "TestUsers::TestPermissions::test_read",
                    DiscoveredTestKind::Function,
                    Some("TestUsers::TestPermissions")
                ),
                (
                    "TestUsers::TestPermissions::test_write",
                    DiscoveredTestKind::Function,
                    Some("TestUsers::TestPermissions")
                ),
                ("TestGroups", DiscoveredTestKind::Class, None),
                (
                    "TestGroups::TestPermissions",
                    DiscoveredTestKind::Class,
                    Some("TestGroups")
                ),
                (
                    "TestGroups::TestPermissions::test_read",
                    DiscoveredTestKind::Function,
                    Some("TestGroups::TestPermissions")
                ),
            ]
        );
    }

    #[test]
    fn omits_classes_without_collected_tests() {
        let test = discovery_test(
            r#"
class TestEmpty: ...
"#,
        );

        assert!(discovered_tests(&test).is_empty());
    }

    #[test]
    fn updates_locations_and_identifiers() {
        let mut test = discovery_test(
            r#"
class TestUsers:
    def test_lookup(self): ...
"#,
        );
        let before = discovered_tests(&test);
        let source = test.cursor.source.as_str();
        let shifted = format!(
            r#"
{source}"#
        );
        test.write_file("test_users.py", &shifted)
            .expect("moving the test should succeed");
        let after = discovered_tests(&test);

        assert_eq!(item_details(&after), item_details(&before));
        for (before, after) in before.iter().zip(&after) {
            assert_eq!(after.range, before.range + TextSize::new(1));
        }

        test.write_file(
            "test_users.py",
            &shifted.replace("test_lookup", "test_search"),
        )
        .expect("renaming the test should succeed");
        assert_eq!(
            item_details(&discovered_tests(&test)),
            [
                ("TestUsers", DiscoveredTestKind::Class, None),
                (
                    "TestUsers::test_search",
                    DiscoveredTestKind::Function,
                    Some("TestUsers")
                ),
            ]
        );
    }

    fn discovery_test(source: &str) -> CursorTest {
        CursorTest::builder()
            .source(
                "test_users.py",
                format!(
                    r#"{source}
<CURSOR>"#
                ),
            )
            .build()
    }

    fn discovered_tests(test: &CursorTest) -> Vec<DiscoveredTest> {
        let items = discover_tests(&test.db, test.program_file(test.cursor.file));
        let source = source_text(&test.db, test.cursor.file);
        for item in &items {
            assert_eq!(&source[item.range], item.label);
        }
        items
    }

    fn item_details(items: &[DiscoveredTest]) -> Vec<(&str, DiscoveredTestKind, Option<&str>)> {
        items
            .iter()
            .map(|item| (item.id.as_str(), item.kind, item.parent.as_deref()))
            .collect()
    }
}
