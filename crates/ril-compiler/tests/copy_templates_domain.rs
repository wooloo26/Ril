#[path = "../src/sema/copy_templates.rs"]
mod domain;
use domain::*;
use ril_compiler_core::ids::DefinitionId;
use std::collections::{BTreeMap, BTreeSet};

fn site(owner: Option<u32>, target: u32, start: u32) -> Site {
    Site {
        owner: owner.map(DefinitionId),
        target: DefinitionId(target),
        source: (0, start, start + 1),
    }
}
fn template(sites: &[Site], dependencies: &[u32]) -> Template {
    Template {
        public: false,
        escaped: false,
        sites: sites.iter().cloned().collect(),
        dependencies: dependencies.iter().copied().map(DefinitionId).collect(),
    }
}
fn instance(id: u32, site: Site, qualification: Qualification) -> Instance {
    Instance {
        id: InstanceId(id),
        site,
        qualification,
    }
}

#[test]
fn different_instances_at_one_span_never_borrow_another_success() {
    let call = site(Some(2), 0, 10);
    let templates = [(DefinitionId(0), template(std::slice::from_ref(&call), &[]))].into();
    for failure in [Qualification::Pending, Qualification::Rejected] {
        let instances = [
            instance(0, call.clone(), Qualification::Established),
            instance(1, call.clone(), failure),
        ];
        assert_eq!(
            close(&templates, &instances),
            Err(Failure::UnprovedInstance(InstanceId(1)))
        );
    }
    let checked = close(
        &templates,
        &[
            instance(0, call.clone(), Qualification::Established),
            instance(1, call, Qualification::Established),
        ],
    )
    .unwrap();
    assert_eq!(
        checked.instances[&DefinitionId(0)],
        [InstanceId(0), InstanceId(1)].into()
    );
}

#[test]
fn every_branch_site_and_helper_layer_needs_its_own_actual_proof() {
    let left = site(Some(1), 0, 10);
    let right = site(Some(1), 0, 20);
    let outer = site(None, 1, 30);
    let templates = [
        (
            DefinitionId(0),
            template(&[left.clone(), right.clone()], &[]),
        ),
        (
            DefinitionId(1),
            template(std::slice::from_ref(&outer), &[0]),
        ),
    ]
    .into();
    let mut instances = vec![
        instance(0, left, Qualification::Established),
        instance(1, outer, Qualification::Established),
    ];
    assert_eq!(
        close(&templates, &instances),
        Err(Failure::MissingSite(right.clone()))
    );
    instances.push(instance(2, right, Qualification::Established));
    assert_eq!(
        close(&templates, &instances).unwrap().dependency_order,
        [DefinitionId(0), DefinitionId(1)]
    );
}

#[test]
fn export_extraction_uninstantiated_and_recursive_templates_keep_gates() {
    let call = site(None, 0, 10);
    let mut templates: BTreeMap<_, _> =
        [(DefinitionId(0), template(std::slice::from_ref(&call), &[]))].into();
    assert_eq!(
        close(&templates, &[]),
        Err(Failure::Uninstantiated(DefinitionId(0)))
    );
    let instances = [instance(0, call, Qualification::Established)];
    templates.get_mut(&DefinitionId(0)).unwrap().escaped = true;
    assert_eq!(
        close(&templates, &instances),
        Err(Failure::Exposed(DefinitionId(0)))
    );
    templates.get_mut(&DefinitionId(0)).unwrap().escaped = false;
    templates.get_mut(&DefinitionId(0)).unwrap().public = true;
    assert_eq!(
        close(&templates, &instances),
        Err(Failure::Exposed(DefinitionId(0)))
    );
    templates.get_mut(&DefinitionId(0)).unwrap().public = false;
    templates
        .get_mut(&DefinitionId(0))
        .unwrap()
        .dependencies
        .insert(DefinitionId(1));
    assert_eq!(
        close(&templates, &instances),
        Err(Failure::MissingDependency(DefinitionId(1)))
    );
    templates.get_mut(&DefinitionId(0)).unwrap().dependencies = [DefinitionId(0)].into();
    assert!(matches!(
        close(&templates, &instances),
        Err(Failure::Recursive(_))
    ));
    assert_eq!(
        close(&templates, &[instances[0].clone(), instances[0].clone()]),
        Err(Failure::InvalidInstance(InstanceId(0)))
    );
}

#[test]
fn exhaustive_small_dependency_graphs_match_a_separate_path_oracle() {
    for edges in 0u16..512 {
        let mut templates = BTreeMap::new();
        let mut instances = Vec::new();
        let mut paths = [[false; 3]; 3];
        for (a, row) in paths.iter_mut().enumerate() {
            let call = site(None, a as u32, a as u32);
            let mut dependencies = BTreeSet::new();
            for (b, edge) in row.iter_mut().enumerate() {
                *edge = edges & (1 << (a * 3 + b)) != 0;
                if *edge {
                    dependencies.insert(DefinitionId(b as u32));
                }
            }
            templates.insert(
                DefinitionId(a as u32),
                Template {
                    public: false,
                    escaped: false,
                    sites: [call.clone()].into(),
                    dependencies,
                },
            );
            instances.push(instance(a as u32, call, Qualification::Established));
        }
        for mid in 0..3 {
            for a in 0..3 {
                for b in 0..3 {
                    paths[a][b] |= paths[a][mid] && paths[mid][b];
                }
            }
        }
        let has_cycle = (0..3).any(|node| paths[node][node]);
        assert_eq!(
            close(&templates, &instances).is_ok(),
            !has_cycle,
            "edges={edges}"
        );
    }
}
