//! Enforce workspace layering using Cargo's resolved production/build dependency graph.
use serde::Deserialize;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Debug, thiserror::Error)]
pub enum ArchitectureError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Json(#[from] serde_json::Error),
    #[error("{0}")]
    Invalid(String),
}

#[derive(Debug, Deserialize)]
pub struct Metadata {
    packages: Vec<Package>,
    workspace_members: Vec<String>,
    resolve: Option<Resolve>,
    pub target_directory: PathBuf,
}
#[derive(Debug, Deserialize)]
struct Package {
    id: String,
    name: String,
}
#[derive(Debug, Deserialize)]
struct Resolve {
    nodes: Vec<Node>,
}
#[derive(Debug, Deserialize)]
struct Node {
    id: String,
    deps: Vec<Dependency>,
}
#[derive(Debug, Deserialize)]
struct Dependency {
    pkg: String,
    dep_kinds: Vec<DependencyKind>,
}
#[derive(Debug, Deserialize)]
struct DependencyKind {
    kind: Option<String>,
}

pub fn load(repo: &Path) -> Result<Metadata, ArchitectureError> {
    let output = Command::new("cargo")
        .current_dir(repo)
        .args([
            "metadata",
            "--locked",
            "--all-features",
            "--format-version",
            "1",
        ])
        .output()?;
    if !output.status.success() {
        return Err(ArchitectureError::Invalid(format!(
            "cargo metadata failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(serde_json::from_slice(&output.stdout)?)
}

fn allowed_workspace_dependencies(name: &str) -> Option<&'static [&'static str]> {
    Some(match name {
        "ril-compiler-core" | "ril-runtime-api" | "ril-test" => &[],
        "ril-syntax" | "ril-ir" => &["ril-compiler-core"],
        "ril-codegen" => &["ril-compiler-core", "ril-ir"],
        "ril-compiler" => &["ril-compiler-core", "ril-syntax", "ril-ir", "ril-codegen"],
        "ril-runtime" => &["ril-runtime-api"],
        "ril-cli" => &["ril-compiler", "ril-codegen"],
        "xtask" => &["ril-test"],
        name if is_concrete_backend(name) => &[
            "ril-compiler-core",
            "ril-codegen",
            "ril-ir",
            "ril-runtime-api",
        ],
        _ => return None,
    })
}
fn is_concrete_backend(name: &str) -> bool {
    name.starts_with("ril-codegen-")
}
fn is_cranelift(name: &str) -> bool {
    name == "cranelift" || name.starts_with("cranelift-")
}
fn is_query_engine(name: &str) -> bool {
    name == "salsa" || name.starts_with("salsa-")
}
fn is_frontend(name: &str) -> bool {
    matches!(name, "ril-compiler" | "ril-syntax" | "rowan") || is_query_engine(name)
}

fn forbidden_transitive_dependency(root: &str, dependency: &str) -> bool {
    match root {
        "ril-compiler" => is_concrete_backend(dependency) || is_cranelift(dependency),
        "ril-syntax" => {
            dependency == "ril-compiler"
                || is_query_engine(dependency)
                || is_concrete_backend(dependency)
                || is_cranelift(dependency)
        }
        "ril-runtime-api" | "ril-runtime" => {
            is_frontend(dependency)
                || matches!(
                    dependency,
                    "ril-compiler-core" | "ril-ir" | "ril-codegen" | "ril-cli"
                )
                || is_concrete_backend(dependency)
                || is_cranelift(dependency)
        }
        "ril-compiler-core" | "ril-ir" | "ril-codegen" | "ril-test" | "xtask" => {
            is_frontend(dependency) || is_concrete_backend(dependency) || is_cranelift(dependency)
        }
        name if is_concrete_backend(name) => is_frontend(dependency),
        _ => false,
    }
}

/// Includes optional features and every target in metadata; dev-only edges are exempt.
pub fn check(metadata: &Metadata) -> Result<usize, ArchitectureError> {
    let fail = |message: String| ArchitectureError::Invalid(message);
    if metadata.workspace_members.is_empty() {
        return Err(fail("empty workspace metadata".into()));
    }
    let resolve = metadata.resolve.as_ref().ok_or_else(|| {
        fail("architecture checks require resolved Cargo metadata (without --no-deps)".into())
    })?;
    let packages: HashMap<_, _> = metadata
        .packages
        .iter()
        .map(|p| (p.id.as_str(), p.name.as_str()))
        .collect();
    let nodes: HashMap<_, _> = resolve.nodes.iter().map(|n| (n.id.as_str(), n)).collect();
    let members: HashSet<_> = metadata
        .workspace_members
        .iter()
        .map(String::as_str)
        .collect();
    let mut roots: Vec<_> = members.iter().copied().collect();
    roots.sort_by_key(|id| packages.get(id).copied().unwrap_or(id));
    for root_id in roots {
        let root = *packages
            .get(root_id)
            .ok_or_else(|| fail(format!("missing workspace package {root_id}")))?;
        let allowed = allowed_workspace_dependencies(root).ok_or_else(|| {
            fail(format!(
                "workspace package {root} has no architecture policy"
            ))
        })?;
        let mut queue = VecDeque::from([(root_id, vec![root])]);
        let mut visited = HashSet::from([root_id]);
        while let Some((id, path)) = queue.pop_front() {
            let node = nodes
                .get(id)
                .ok_or_else(|| fail(format!("missing resolved dependency node {id}")))?;
            for dependency in &node.deps {
                if dependency.dep_kinds.is_empty() {
                    return Err(fail(format!(
                        "missing dependency kinds for {}",
                        dependency.pkg
                    )));
                }
                if dependency
                    .dep_kinds
                    .iter()
                    .all(|kind| kind.kind.as_deref() == Some("dev"))
                {
                    continue;
                }
                let next_id = dependency.pkg.as_str();
                let next = *packages
                    .get(next_id)
                    .ok_or_else(|| fail(format!("missing dependency package {next_id}")))?;
                let mut next_path = path.clone();
                next_path.push(next);
                if id == root_id && members.contains(next_id) && !allowed.contains(&next) {
                    return Err(fail(format!(
                        "disallowed workspace dependency: {}",
                        next_path.join(" -> ")
                    )));
                }
                if forbidden_transitive_dependency(root, next) {
                    return Err(fail(format!(
                        "dependency crosses the {root} boundary: {}",
                        next_path.join(" -> ")
                    )));
                }
                if visited.insert(next_id) {
                    queue.push_back((next_id, next_path));
                }
            }
        }
    }
    Ok(members.len())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn graph(members: &[&str], edges: &[(&str, &str, Option<&str>)]) -> Metadata {
        let names: HashSet<_> = members
            .iter()
            .copied()
            .chain(edges.iter().flat_map(|(from, to, _)| [*from, *to]))
            .collect();
        serde_json::from_value(json!({
            "workspace_members": members,
            "target_directory": "target",
            "packages": names.iter().map(|name| json!({"id":name,"name":name})).collect::<Vec<_>>(),
            "resolve": {"nodes": names.iter().map(|name| json!({
                "id":name,
                "deps":edges.iter().filter(|(from,_,_)| from == name).map(|(_,to,kind)| json!({
                    "pkg":to,"dep_kinds":[{"kind":kind}]
                })).collect::<Vec<_>>()
            })).collect::<Vec<_>>()}
        }))
        .unwrap()
    }

    #[test]
    fn accepts_shared_data_interfaces_and_independent_runtime() {
        let metadata = graph(
            &[
                "ril-compiler-core",
                "ril-syntax",
                "ril-ir",
                "ril-codegen",
                "ril-compiler",
                "ril-codegen-cranelift",
                "ril-runtime-api",
                "ril-runtime",
            ],
            &[
                ("ril-syntax", "ril-compiler-core", None),
                ("ril-syntax", "rowan", None),
                ("ril-ir", "ril-compiler-core", None),
                ("ril-codegen", "ril-ir", None),
                ("ril-compiler", "ril-codegen", None),
                ("ril-compiler", "ril-syntax", None),
                ("ril-compiler", "salsa", None),
                ("ril-codegen-cranelift", "ril-codegen", None),
                ("ril-codegen-cranelift", "cranelift-codegen", None),
                ("ril-codegen-cranelift", "ril-runtime-api", None),
                ("ril-runtime", "ril-runtime-api", None),
            ],
        );
        assert_eq!(check(&metadata).unwrap(), 8);
    }

    #[test]
    fn rejects_frontend_dependencies_in_ir_and_concrete_backends() {
        for root in ["ril-ir", "ril-codegen-cranelift"] {
            let metadata = graph(&[root, "ril-compiler"], &[(root, "ril-compiler", None)]);
            assert!(
                check(&metadata)
                    .unwrap_err()
                    .to_string()
                    .contains(&format!("{root} -> ril-compiler"))
            );
        }
    }

    #[test]
    fn rejects_runtime_coupling_to_compiler_or_codegen() {
        for root in ["ril-runtime-api", "ril-runtime"] {
            for dependency in [
                "ril-compiler",
                "ril-compiler-core",
                "ril-syntax",
                "ril-codegen",
                "ril-ir",
            ] {
                assert!(check(&graph(&[root, dependency], &[(root, dependency, None)])).is_err());
                assert!(
                    check(&graph(
                        &[root],
                        &[
                            (root, "external-helper", None),
                            ("external-helper", dependency, None),
                        ]
                    ))
                    .is_err()
                );
            }
        }
    }

    #[test]
    fn rejects_concrete_codegen_in_compiler_including_through_external_helpers() {
        for dependency in ["ril-codegen-cranelift", "cranelift-codegen"] {
            let metadata = graph(
                &["ril-compiler"],
                &[
                    ("ril-compiler", "external-helper", None),
                    ("external-helper", dependency, None),
                ],
            );
            let message = check(&metadata).unwrap_err().to_string();
            assert!(message.contains(&format!("ril-compiler -> external-helper -> {dependency}")));
        }
    }

    #[test]
    fn detects_transitive_parser_and_query_dependencies() {
        for root in ["ril-ir", "ril-codegen-cranelift", "ril-runtime-api"] {
            for dependency in ["rowan", "salsa", "salsa-macros"] {
                assert!(
                    check(&graph(
                        &[root],
                        &[
                            (root, "external-helper", None),
                            ("external-helper", dependency, None),
                        ]
                    ))
                    .is_err()
                );
            }
        }
    }

    #[test]
    fn checks_build_and_target_specific_edges_but_allows_dev_only_edges() {
        let mut metadata = graph(&["ril-ir"], &[("ril-ir", "rowan", Some("dev"))]);
        assert!(check(&metadata).is_ok());
        let node = metadata
            .resolve
            .as_mut()
            .unwrap()
            .nodes
            .iter_mut()
            .find(|node| node.id == "ril-ir")
            .unwrap();
        node.deps[0].dep_kinds.push(DependencyKind {
            kind: Some("build".into()),
        });
        assert!(check(&metadata).is_err());
        let value = json!({
            "workspace_members":["ril-ir"],
            "target_directory":"target",
            "packages":[{"id":"ril-ir","name":"ril-ir"},{"id":"salsa","name":"salsa"}],
            "resolve":{"nodes":[
                {"id":"ril-ir","deps":[{"pkg":"salsa","name":"renamed_query","dep_kinds":[{"kind":null,"target":"cfg(windows)"}]}]},
                {"id":"salsa","deps":[]}
            ]}
        });
        assert!(check(&serde_json::from_value(value).unwrap()).is_err());
    }

    #[test]
    fn incomplete_metadata_and_unclassified_crates_cannot_pass() {
        let mut metadata = graph(&["ril-ir"], &[]);
        metadata.resolve = None;
        assert!(check(&metadata).is_err());
        assert!(check(&graph(&[], &[])).is_err());
        assert!(check(&graph(&["unclassified"], &[])).is_err());
    }
}
