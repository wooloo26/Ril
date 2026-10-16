//! Finite classes for copying an already summarized ordinary graph. A class
//! identifies allocation history, never equality of all objects in the class.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Base {
    Allocation(SiteId),
    Formal(Pivot),
    Other(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub(super) struct Shape {
    pub views: Vec<String>,
    pub fields: Vec<(Slot, String)>,
    pub storage: Option<String>,
    pub length: Option<u64>,
    pub fixed: bool,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Key {
    pub file: u32,
    pub start: u32,
    pub context: u32,
    pub source: Base,
    pub readonly: bool,
    /// Coordinates and complete selected constituent types distinguish
    /// incompatible instances without depending on concrete node numbers.
    pub shape: Shape,
}

#[derive(Default)]
pub(super) struct Classes {
    sites: BTreeMap<Key, SiteId>,
    bases: BTreeMap<SiteId, Base>,
}
impl Classes {
    pub(super) fn base(&self, node: NodeId, kind: OriginKind) -> Base {
        match kind {
            OriginKind::Fresh(site) | OriginKind::Older(site) => self
                .bases
                .get(&site)
                .copied()
                .unwrap_or(Base::Allocation(site)),
            OriginKind::Formal(pivot) => Base::Formal(pivot),
            _ => Base::Other(node),
        }
    }
    pub(super) fn site(&mut self, mut key: Key, next: &mut u32) -> SiteId {
        while let Base::Allocation(site) = key.source {
            let Some(base) = self.bases.get(&site) else {
                break;
            };
            key.source = *base;
        }
        if let Some(site) = self.sites.get(&key) {
            return *site;
        }
        let site = SiteId(*next);
        *next = next
            .checked_add(1)
            .expect("semantic allocation site identity exhausted");
        self.bases.insert(site, key.source);
        self.sites.insert(key, site);
        site
    }
}

/// One allocation batch materializes all source nodes in a class together.
/// Collapsing source alternatives cannot assert a singleton target object.
pub(super) fn is_summary(nodes: &[NodeId], relation: impl Fn(NodeId) -> Relation) -> bool {
    nodes.len() != 1
        || nodes
            .iter()
            .any(|node| relation(*node).equal != Condition::TRUE)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repeated_copy_of_copy_uses_one_finite_base_class() {
        let mut classes = Classes::default();
        let mut next = 10;
        let original = SiteId(1);
        let mut source = Base::Allocation(original);
        let mut selected = None;
        for iteration in 0..100 {
            let site = classes.site(
                Key {
                    file: 0,
                    start: 20,
                    context: 1,
                    source,
                    readonly: false,
                    shape: Shape::default(),
                },
                &mut next,
            );
            assert!(selected.is_none_or(|previous| previous == site));
            selected = Some(site);
            source = classes.base(
                NodeId(iteration),
                if iteration % 2 == 0 {
                    OriginKind::Fresh(site)
                } else {
                    OriginKind::Older(site)
                },
            );
            assert_eq!(source, Base::Allocation(original));
        }
        assert_eq!(next, 11);
        let immutable = classes.site(
            Key {
                file: 0,
                start: 20,
                context: 1,
                source,
                readonly: true,
                shape: Shape::default(),
            },
            &mut next,
        );
        assert_ne!(Some(immutable), selected);
    }

    #[test]
    fn quotient_graphs_preserve_every_alias_cycle_and_reachable_old_vertex() {
        // Concrete vertices are independent objects. Exhaust all directed
        // three-node graphs and all binary class assignments. The oracle uses
        // concrete reachability; the abstraction uses class-edge closure.
        for edges in 0u16..512 {
            for classes in 0u8..8 {
                let class = |node: usize| ((classes >> node) & 1) as usize;
                let mut abstract_edges = [[false; 2]; 2];
                let mut members = [0; 2];
                for a in 0..3 {
                    members[class(a)] += 1;
                    for b in 0..3 {
                        if edges & (1 << (a * 3 + b)) != 0 {
                            abstract_edges[class(a)][class(b)] = true;
                        }
                    }
                }
                for root in 0..3 {
                    let mut concrete = [false; 3];
                    concrete[root] = true;
                    let mut abstract_nodes = [false; 2];
                    abstract_nodes[class(root)] = true;
                    for _ in 0..3 {
                        for a in 0..3 {
                            for b in 0..3 {
                                if concrete[a] && edges & (1 << (a * 3 + b)) != 0 {
                                    concrete[b] = true;
                                }
                            }
                        }
                        for a in 0..2 {
                            for b in 0..2 {
                                if abstract_nodes[a] && abstract_edges[a][b] {
                                    abstract_nodes[b] = true;
                                }
                            }
                        }
                    }
                    for node in 0..3 {
                        assert!(!concrete[node] || abstract_nodes[class(node)]);
                    }
                }
                for a in 0..3 {
                    for b in 0..3 {
                        if a != b && class(a) == class(b) {
                            assert!(members[class(a)] > 1);
                        }
                    }
                }
            }
        }
    }
}
