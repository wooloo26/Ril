//! Batch materialization of a closed ordinary copy graph. Source identity and
//! relations are captured before allocation can recycle the same copy class.
use super::*;

impl Checker {
    pub(super) fn canonical_ordinary_clone(
        &mut self,
        source: &Value,
        span: Span,
        owner: ScopeId,
        immutable: bool,
    ) -> Option<Value> {
        self.canonical_ordinary_clone_batch(source, span, owner, immutable)
            .map(|(value, _)| value)
    }

    /// The actual batch mapping is a witness to validate, not an independent
    /// freshness or copy-eligibility proof. Keys describe the frozen input graph.
    pub(super) fn canonical_ordinary_clone_batch(
        &mut self,
        source: &Value,
        span: Span,
        owner: ScopeId,
        immutable: bool,
    ) -> Option<(Value, BTreeMap<NodeId, NodeId>)> {
        if !self.ordinary_loop_value(source, &self.fields) || self.has_window(source) {
            return None;
        }
        let reachable = self.heap.reachable(source.origins.nodes.iter().copied());
        let source_fields: BTreeMap<_, _> = self
            .fields
            .iter()
            .filter(|((node, _), _)| reachable.contains(node))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect();
        let source_nodes: BTreeMap<_, _> = reachable
            .iter()
            .map(|node| (*node, self.heap.nodes[node.0 as usize].clone()))
            .collect();
        let storage: BTreeMap<_, _> = reachable
            .iter()
            .filter_map(|node| self.storage_types.get(node).cloned().map(|ty| (*node, ty)))
            .collect();
        let lengths = self.array_lengths.clone();
        let fixed = self.fixed_arrays.clone();
        let mut frozen_roots = BTreeSet::new();
        self.immutable_clone_roots(source, false, &mut frozen_roots);
        for value in source_fields.values() {
            self.immutable_clone_roots(value, true, &mut frozen_roots);
        }
        let frozen = self.heap.reachable(frozen_roots);
        let mut relations = BTreeMap::new();
        for &a in &reachable {
            for &b in &reachable {
                relations.insert((a, b), self.heap.relation(a, b));
            }
        }
        let mut groups: BTreeMap<copy_classes::Key, Vec<NodeId>> = BTreeMap::new();
        for &node in &reachable {
            let views: BTreeSet<_> = std::iter::once(source)
                .chain(source_fields.values())
                .filter(|value| value.origins.nodes.contains(&node))
                .map(|value| format!("{:?}", value.ty))
                .collect();
            let shape: BTreeSet<_> = source_fields
                .iter()
                .filter(|((parent, _), _)| *parent == node)
                .map(|((_, slot), value)| {
                    (
                        if matches!(slot, Slot::Index(_)) {
                            Slot::AnyIndex
                        } else {
                            slot.clone()
                        },
                        format!("{:?}", value.ty),
                    )
                })
                .collect();
            let key = copy_classes::Key {
                file: span.file.0,
                start: span.start,
                context: self.loop_allocation_context(owner).0,
                source: self.copy_classes.base(node, source_nodes[&node].kind),
                readonly: immutable || frozen.contains(&node),
                shape: copy_classes::Shape {
                    views: views.into_iter().collect(),
                    fields: shape.into_iter().collect(),
                    storage: storage.get(&node).map(|ty| format!("{ty:?}")),
                    length: lengths.get(&node).copied().flatten(),
                    fixed: fixed.contains(&node),
                },
            };
            groups.entry(key).or_default().push(node);
        }
        let mut copies = BTreeMap::new();
        let mut batches = Vec::new();
        for (key, nodes) in groups {
            let summary = copy_classes::is_summary(&nodes, |node| relations[&(node, node)]);
            let site = self.copy_classes.site(key, &mut self.next_site);
            let target = self.allocate_site(span, site, owner);
            if summary {
                self.heap.set_relation(target, target, Relation::UNKNOWN);
            }
            for node in &nodes {
                copies.insert(*node, target);
            }
            if let Some(ty) = storage.get(&nodes[0]) {
                self.storage_types.insert(target, ty.clone());
            }
            if let Some(length) = lengths.get(&nodes[0]) {
                self.array_lengths.insert(target, *length);
            }
            if fixed.contains(&nodes[0]) {
                self.fixed_arrays.insert(target);
            }
            batches.push((target, nodes, summary));
        }
        let mut paths = Vec::new();
        let writable_path = |origins: &Origins| {
            let mut origins = origins.clone();
            origins
                .nodes
                .retain(|node| !immutable && !frozen.contains(node));
            for branches in origins.choices.values_mut() {
                for branch in branches {
                    branch.retain(|node| !immutable && !frozen.contains(node));
                }
            }
            origins
        };
        let root_path = writable_path(&source.origins);
        if !root_path.nodes.is_empty() {
            paths.push(root_path);
        }
        let mut internal = false;
        for ((parent, slot), value) in &source_fields {
            let path = writable_path(&value.origins);
            if path.nodes.is_empty() {
                continue;
            }
            if matches!(slot, Slot::AnyIndex)
                && lengths
                    .get(parent)
                    .copied()
                    .flatten()
                    .is_none_or(|length| length > 1)
            {
                internal = true;
            }
            paths.push(path);
        }
        for (index, a) in paths.iter().enumerate() {
            for b in &paths[index + 1..] {
                if !copied_paths_disjoint(a, b, &relations) {
                    internal = true;
                }
            }
        }
        for (index, (left, left_sources, left_summary)) in batches.iter().enumerate() {
            for (right, right_sources, right_summary) in &batches[index + 1..] {
                let mut relation = Relation::EQUAL;
                relation.disjoint = Condition::TRUE;
                for a in left_sources {
                    for b in right_sources {
                        // Observed fields can be partial projections. Different
                        // coordinate sets are not evidence of distinct objects.
                        relation = relation.join(relations[&(*a, *b)], &mut self.heap.conditions);
                    }
                }
                if *left_summary || *right_summary {
                    relation.equal = Condition::FALSE;
                }
                self.heap.set_relation(*left, *right, relation);
            }
        }
        let mut projected: BTreeMap<(NodeId, Slot), Value> = BTreeMap::new();
        for ((node, slot), mut value) in source_fields {
            copy::rewrite_clone(&mut value, &copies, &frozen, immutable);
            let key = (copies[&node], slot);
            if let Some(previous) = projected.remove(&key) {
                value = previous.join(&value, self.choice(), value.cause);
                loop_graph::forget_choices(&mut value);
            }
            projected.insert(key, value);
        }
        for ((node, slot), value) in projected {
            self.store_field(node, slot, value);
        }
        let mut result = source.clone();
        result.ty = match (&source.ty, immutable) {
            (Ty::Immutable(inner), false) => *inner.clone(),
            (Ty::Immutable(_), true) => source.ty.clone(),
            (_, true) => Ty::Immutable(Box::new(source.ty.clone())),
            _ => source.ty.clone(),
        };
        self.adapt_copy_source_type(source, &mut result, immutable);
        let immutable_output = immutable || self.formal_is_immutable(&result.ty);
        copy::rewrite_clone(&mut result, &copies, &frozen, immutable_output);
        result.internal_aliases = internal;
        result.sources.clear();
        result.scoped.clear();
        result.participants.clear();
        result.marker = false;
        result.through_return = false;
        result.cause=self.cause(CauseKind::Allocation,span,"ordinary copy batch preserves aliases, cycles and readonly qualifications in finite classes",[source.cause]);
        result.unsuffixed_numeric = false;
        result.literal_number = false;
        result.static_coordinate = None;
        Some((result, copies))
    }
}

fn copied_paths_disjoint(
    a: &Origins,
    b: &Origins,
    relations: &BTreeMap<(NodeId, NodeId), Relation>,
) -> bool {
    let disjoint = |a: &BTreeSet<NodeId>, b: &BTreeSet<NodeId>| {
        a.iter().all(|a| {
            b.iter().all(|b| {
                relations
                    .get(&(*a, *b))
                    .is_some_and(|relation| relation.disjoint == Condition::TRUE)
            })
        })
    };
    for (choice, left) in &a.choices {
        if let Some(right) = b.choices.get(choice)
            && left.len() == right.len()
            && left.iter().zip(right).all(|(a, b)| disjoint(a, b))
        {
            return true;
        }
    }
    disjoint(&a.nodes, &b.nodes)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn higher_order_ordinary_copies_have_a_finite_loop_representation() {
        for source in [
            "type Node={value:int,following:?Node}\nfn repeat(values:[]int)->Node{var current=Node.{value:0,following:None};for values as index{current=clone(current)};current}",
            "type Cell={mut count:int}\ntype Wrapper={child:Cell}\nfn example(values:[]int){let mut old=Cell.{count:0};let mut shells:[]Wrapper=[];for values as index{let mut shell=^mut Wrapper.{child:^mut old};shells !> Array::push(^mut shell)};let mut copied=^mut clone(shells);let mut part=^mut copied[0].child;let _=Parallel::join(\\->{old.count+=1},\\->{part.count+=1})}",
            "fn repeat(values:[]int)->[]int{var current=[0];for values as index{current=clone(current)};current}",
            "fn repeat(values:[]int)->[][]int{var current=[[1],[2]];for values as index{current=clone(current)};current}",
            "type Node={mut value:int,mut following:?Node}\nfn repeat(values:[]int){let mut original=Node.{value:0,following:None};original.following=Some(^mut original);var mut current=^mut clone(original);for values as index{current=^mut clone(current);current.value+=index};assert(original.value==0)}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_some(),
                "{source}\n{:?}\n{:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn canonical_classes_preserve_internal_sharing_and_readonly_descendants() {
        for (source, code) in [
            (
                "type Cell={mut a:int,mut b:int}\nfn example(left:Cell,right:Cell){let _=left.a;let _=right.b;let mut copied=^mut clone((left,right));let _=Parallel::join(\\->{copied.0.a+=1},\\->{copied.1.a+=1})}",
                "E0619",
            ),
            (
                "type Cell={mut count:int}\ntype Wrapper={child:Cell}\nfn example(values:[]int){let mut old=Cell.{count:0};let mut shells:[]Wrapper=[];for values as index{let mut shell=^mut Wrapper.{child:^mut old};shells !> Array::push(^mut shell)};let _=Parallel::join(\\->{old.count+=1},\\->shells[0].child.count)}",
                "E0619",
            ),
            (
                "type Cell={mut count:int}\nfn example(values:[]int){let shared=Cell.{count:0};var current=(shared,shared);for values as index{current=clone(current)};let mut copied=^mut clone(current);let _=Parallel::join(\\->{copied.0.count+=1},\\->{copied.1.count+=1})}",
                "E0619",
            ),
            (
                "type Cell={mut count:int}\nfn example(values:[]int){let shared=Cell.{count:0};var current=(shared,shared);for values as index{current=clone(current)};let mut copied=clone(current);copied.0.count+=1}",
                "E0510",
            ),
            (
                "type Wrapper={data:Immut<[]int>}\nfn example(values:[]int){var current=Wrapper.{data:clone_immut([1])};for values as index{current=clone(current)};let mut copied=clone(current);copied.data[0]=2}",
                "E0522",
            ),
            (
                "fn example(handle:File::Handle){let _=clone(handle)}",
                "E0530",
            ),
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "expected {code}: {source}\n{:?}\n{:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        for source in [
            "fn example(values:[]int){let result:Result<int,str>=Ok(1);var current=[result];for values as index{current=clone(current)}}",
            "fn example(values:[]int){let identity=\\x:int->x;var current=.{call:identity};for values as index{current=clone(current)}}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_none(),
                "nonordinary copy families need their own proof"
            );
        }
    }
}

#[cfg(test)]
#[path = "canonical_copy_oracle.rs"]
mod oracle;
