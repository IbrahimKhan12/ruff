use std::collections::BTreeMap;

use compact_str::CompactString;
use pep508_rs::Requirement;
use ruff_db::files::File;
use ruff_db::source::source_text;
use ruff_python_ast::script::ScriptSourceMap;
use ruff_text_size::{TextRange, TextSize};
use serde::Deserialize;
use toml::Spanned;
use ty_python_semantic::dependency::DependencyProjectKind;

use crate::Db;
use crate::script::script_tag;

/// A dependency declaration that can be checked without evaluating environment markers.
#[derive(Debug, Clone, PartialEq, Eq, get_size2::GetSize)]
pub(super) struct DependencyDeclaration {
    pub(super) name: CompactString,
    pub(super) range: TextRange,
}

/// Returns unconditional runtime and optional dependency declarations with their source locations.
///
/// Invalid metadata is not evidence that a dependency is unused. Dependency groups and build
/// requirements are excluded because they commonly provide tools rather than imported modules.
pub(super) fn declarations(
    db: &dyn Db,
    file: File,
    kind: DependencyProjectKind,
) -> Option<&[DependencyDeclaration]> {
    match kind {
        DependencyProjectKind::Project => project_declarations(db, file),
        DependencyProjectKind::Script => script_declarations(db, file),
    }
}

#[salsa::tracked(returns(as_deref), heap_size=ruff_memory_usage::heap_size)]
fn project_declarations(db: &dyn Db, file: File) -> Option<Box<[DependencyDeclaration]>> {
    let source = source_text(db, file);
    if source.read_error().is_some() {
        return None;
    }

    parse_project(source.as_str())
}

fn parse_project(source: &str) -> Option<Box<[DependencyDeclaration]>> {
    let metadata: ProjectMetadata = toml::from_str(source).ok()?;
    let project = metadata.project.unwrap_or_default();
    let requirements = project
        .dependencies
        .into_iter()
        .chain(project.optional_dependencies.into_values().flatten());
    parse_requirements(requirements, None)
}

#[salsa::tracked(returns(as_deref), heap_size=ruff_memory_usage::heap_size)]
fn script_declarations(db: &dyn Db, file: File) -> Option<Box<[DependencyDeclaration]>> {
    let tag = script_tag(db, file)?;
    let metadata: ScriptMetadata = toml::from_str(tag.metadata()).ok()?;
    parse_requirements(metadata.dependencies, Some(tag.source_map()))
}

fn parse_requirements(
    requirements: impl IntoIterator<Item = Spanned<String>>,
    source_map: Option<&ScriptSourceMap>,
) -> Option<Box<[DependencyDeclaration]>> {
    let mut declarations = Vec::new();
    for requirement in requirements {
        let parsed: Requirement = requirement.get_ref().parse().ok()?;
        // The dependency graph covers every supported environment. An installed distribution can
        // satisfy another declaration even when this declaration's marker does not apply.
        if !parsed.marker.is_true() {
            continue;
        }

        let span = requirement.span();
        let range = TextRange::new(
            TextSize::try_from(span.start).ok()?,
            TextSize::try_from(span.end).ok()?,
        );
        declarations.push(DependencyDeclaration {
            name: CompactString::new(parsed.name.as_ref()),
            range: source_map.map_or(range, |source_map| source_map.map_range(range)),
        });
    }

    declarations.sort_unstable_by_key(|declaration| declaration.range.start());
    Some(declarations.into_boxed_slice())
}

#[derive(Deserialize)]
struct ProjectMetadata {
    project: Option<ProjectDependencies>,
}

#[derive(Default, Deserialize)]
#[serde(rename_all = "kebab-case")]
struct ProjectDependencies {
    #[serde(default)]
    dependencies: Vec<Spanned<String>>,
    #[serde(default)]
    optional_dependencies: BTreeMap<String, Vec<Spanned<String>>>,
}

#[derive(Deserialize)]
struct ScriptMetadata {
    #[serde(default)]
    dependencies: Vec<Spanned<String>>,
}

#[cfg(test)]
mod tests {
    use anyhow::Context;
    use ruff_db::files::system_path_to_file;
    use ruff_db::system::{DbWithWritableSystem as _, SystemPath, SystemPathBuf};
    use ruff_python_ast::script::ScriptTag;
    use ty_python_semantic::dependency::DependencyProjectKind;

    use crate::ProjectMetadata;
    use crate::db::testing::TestDb;

    use super::{
        DependencyDeclaration, ScriptMetadata, declarations, parse_project, parse_requirements,
    };

    fn names_and_sources<'a>(
        source: &'a str,
        declarations: &'a [DependencyDeclaration],
    ) -> Vec<(&'a str, &'a str)> {
        declarations
            .iter()
            .map(|declaration| (declaration.name.as_str(), &source[declaration.range]))
            .collect()
    }

    #[test]
    fn project_runtime_and_optional_declarations() -> anyhow::Result<()> {
        let source = r#"
[project]
dependencies = ["Some_Package[extra]>=2", "Other.Name @ https://example.com/other.whl"]

[project.optional-dependencies]
z = ["last-package"]
a = ["First.Package"]

[dependency-groups]
dev = ["development-tool"]

[build-system]
requires = ["build-tool"]
"#;
        let declarations = parse_project(source).context("expected valid metadata")?;
        assert_eq!(
            names_and_sources(source, &declarations),
            [
                ("some-package", r#""Some_Package[extra]>=2""#),
                (
                    "other-name",
                    r#""Other.Name @ https://example.com/other.whl""#
                ),
                ("last-package", r#""last-package""#),
                ("first-package", r#""First.Package""#),
            ]
        );
        Ok(())
    }

    #[test]
    fn script_declaration_ranges() -> anyhow::Result<()> {
        let source = "# café\r\n# /// script\r\n# dependencies = [\r\n#     'Some_Package',\r\n#     \"other-package>=2\",\r\n# ]\r\n# ///\r\n";
        let tag = ScriptTag::parse(source.as_bytes()).context("expected valid script metadata")?;
        let metadata: ScriptMetadata = toml::from_str(tag.metadata())?;
        let declarations = parse_requirements(metadata.dependencies, Some(tag.source_map()))
            .context("expected valid requirements")?;
        assert_eq!(
            names_and_sources(source, &declarations),
            [
                ("some-package", "'Some_Package'"),
                ("other-package", r#""other-package>=2""#),
            ]
        );
        Ok(())
    }

    #[test]
    fn conditional_declarations_are_excluded() -> anyhow::Result<()> {
        let source = r#"
[project]
dependencies = ["unconditional", "conditional; sys_platform == 'win32'"]

[project.optional-dependencies]
extra = ["optional; python_version >= '3.12'"]
"#;
        let declarations = parse_project(source).context("expected valid metadata")?;
        assert_eq!(
            names_and_sources(source, &declarations),
            [("unconditional", r#""unconditional""#)]
        );
        Ok(())
    }

    #[test]
    fn invalid_metadata_is_not_checked() {
        for source in [
            "[project",
            "[project]\ndependencies = false",
            "[project]\ndependencies = ['valid', 'invalid requirement']",
            "[project.optional-dependencies]\nextra = ['invalid requirement']",
        ] {
            assert!(parse_project(source).is_none(), "{source}");
        }
    }

    #[test]
    fn source_relocation_updates_cached_declaration_ranges() -> anyhow::Result<()> {
        let mut db = TestDb::new(ProjectMetadata::new(
            "test",
            SystemPathBuf::from("/project"),
        ));
        for (path, kind, source) in [
            (
                "/project/pyproject.toml",
                DependencyProjectKind::Project,
                "[project]\ndependencies = ['dependency']\n",
            ),
            (
                "/project/script.py",
                DependencyProjectKind::Script,
                "# /// script\n# dependencies = ['dependency']\n# ///\n",
            ),
        ] {
            db.write_file(path, source)?;
            let file = system_path_to_file(&db, SystemPath::new(path))?;
            let original = declarations(&db, file, kind)
                .context("expected valid metadata")?
                .to_vec();

            let relocated = format!("# Moved declaration\n{source}");
            db.write_file(path, &relocated)?;
            let updated = declarations(&db, file, kind).context("expected valid metadata")?;
            assert_eq!(original.len(), 1);
            assert_eq!(updated.len(), 1);
            assert_eq!(original[0].name, updated[0].name);
            assert_ne!(original[0].range, updated[0].range);
            assert_eq!(
                names_and_sources(&relocated, updated),
                [("dependency", "'dependency'")]
            );
        }
        Ok(())
    }
}
