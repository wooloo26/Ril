//! Bounded concrete execution, independent of provenance authorization. Object
//! IDs never recycle. The production copier's mapping is checked as a witness.
use super::*;

#[derive(Clone, Copy, Debug)]
struct Ref {
    object: usize,
    write: bool,
}
#[derive(Clone, Debug)]
struct Object {
    fields: [Option<Ref>; 2],
}
#[derive(Clone, Debug, Default)]
struct Concrete {
    objects: Vec<Object>,
    representation: Vec<NodeId>,
}
impl Concrete {
    fn allocate(&mut self, fields: [Option<Ref>; 2], representation: NodeId) -> Ref {
        let object = self.objects.len();
        self.objects.push(Object { fields });
        self.representation.push(representation);
        Ref {
            object,
            write: true,
        }
    }
    fn project(&self, mut source: Ref, path: &[usize]) -> Option<Ref> {
        for &field in path {
            let next = self.objects[source.object].fields[field]?;
            source = Ref {
                object: next.object,
                write: source.write && next.write,
            };
        }
        Some(source)
    }
    fn reachable(&self, source: usize) -> Vec<usize> {
        // Repeated whole-matrix propagation, deliberately separate from the
        // production heap worklist and its class/recency identities.
        let mut reached = vec![false; self.objects.len()];
        reached[source] = true;
        loop {
            let before = reached.clone();
            for (id, object) in self.objects.iter().enumerate() {
                if before[id] {
                    for edge in object.fields.iter().flatten() {
                        reached[edge.object] = true;
                    }
                }
            }
            if reached == before {
                break;
            }
        }
        reached
            .iter()
            .enumerate()
            .filter_map(|(id, yes)| yes.then_some(id))
            .collect()
    }
    fn copy(
        &mut self,
        source: Ref,
        immutable: bool,
        represented: &BTreeMap<NodeId, NodeId>,
        before: &[NodeId],
    ) -> Ref {
        let reachable = self.reachable(source.object);
        let mut copies = BTreeMap::new();
        for object in &reachable {
            let abstract_source = before[*object];
            let target = *represented
                .get(&abstract_source)
                .expect("every concrete copied object requires a source mapping");
            let copy = self.allocate([None, None], target);
            copies.insert(*object, copy.object);
        }
        for object in &reachable {
            let copied = copies[object];
            for field in 0..2 {
                self.objects[copied].fields[field] =
                    self.objects[*object].fields[field].map(|edge| Ref {
                        object: copies[&edge.object],
                        write: !immutable,
                    });
            }
        }
        Ref {
            object: copies[&source.object],
            write: !immutable,
        }
    }
    fn move_representations(&mut self, moves: &[(NodeId, NodeId)]) {
        // Replay raw allocation events, never the implementation's transport.
        for &(from, to) in moves {
            for node in &mut self.representation {
                if *node == from {
                    *node = to;
                }
            }
        }
    }
}

struct Handle {
    value: EvaluatedValue,
    concrete: [Ref; 2],
}
struct Machine {
    checker: Checker,
    worlds: [Concrete; 2],
    handles: Vec<Handle>,
    span: Span,
}
impl Machine {
    fn new(same_site: bool, graph: usize, permissions: usize) -> Self {
        let declaration =
            ril_syntax::parse("type Node={mut value:int,mut left:?Node,mut right:?Node}");
        assert!(declaration.is_ok());
        let mut checker = Checker::new(FileId(0));
        checker.run(&declaration.program);
        checker.next_site = 3;
        let mut machine = Self {
            checker,
            worlds: std::array::from_fn(|_| Concrete::default()),
            handles: vec![],
            span: Span {
                file: FileId(0),
                start: 100,
                end: 110,
            },
        };
        for site in [SiteId(0), SiteId(if same_site { 0 } else { 1 })] {
            machine.allocate(site, [None, None]);
        }
        let mut edges = graph;
        for object in 0..2 {
            for field in 0..2 {
                let target = edges % 3;
                edges /= 3;
                let edge = (target < 2).then_some(Ref {
                    object: target,
                    write: permissions & (1 << (object * 2 + field)) != 0,
                });
                for world in &mut machine.worlds {
                    world.objects[object].fields[field] = edge;
                }
                let node = machine.worlds[0].representation[object];
                let child = edge.map(|edge| {
                    machine.reference(machine.worlds[0].representation[edge.object], edge.write)
                });
                let value = child
                    .map(|child| machine.checker.wrap_optional(child, Some(true)))
                    .unwrap_or_else(|| {
                        Value::scalar(
                            Ty::Optional(Box::new(Ty::Named("Node".into()))),
                            None,
                            CauseId(0),
                        )
                    });
                machine.checker.store_field(node, slot(field), value);
            }
        }
        machine
    }
    fn reference(&self, node: NodeId, write: bool) -> Value {
        let mut value = Value::reference(node_type(), node, CauseId(0));
        value.permission = if write {
            Permission::Write
        } else {
            Permission::Read
        };
        value.publication = Publication::Live;
        value.construction = false;
        value
    }
    fn move_worlds(&mut self, cursor: usize) {
        for &(from, to) in &self.checker.recency_moves[cursor..] {
            let OriginKind::Fresh(source) = self.checker.heap.nodes[from.0 as usize].kind else {
                panic!("move source is not recent")
            };
            assert_eq!(
                self.checker.heap.nodes[to.0 as usize].kind,
                OriginKind::Older(source)
            );
        }
        for world in &mut self.worlds {
            world.move_representations(&self.checker.recency_moves[cursor..]);
        }
    }
    fn allocate(&mut self, site: SiteId, children: [Option<usize>; 2]) -> usize {
        let cursor = self.checker.recency_moves.len();
        let node = self.checker.allocate_site(self.span, site, ScopeId(0));
        self.move_worlds(cursor);
        let values: [Option<Value>; 2] = std::array::from_fn(|field| {
            children[field].map(|handle| {
                self.handles[handle]
                    .value
                    .current(&self.checker.recency_moves)
            })
        });
        let concrete = std::array::from_fn(|world| {
            let fields = std::array::from_fn(|field| {
                children[field].map(|handle| self.handles[handle].concrete[world])
            });
            self.worlds[world].allocate(fields, node)
        });
        for (field, value) in values.into_iter().enumerate() {
            let optional = value
                .map(|value| self.checker.wrap_optional(value, Some(true)))
                .unwrap_or_else(|| {
                    Value::scalar(
                        Ty::Optional(Box::new(Ty::Named("Node".into()))),
                        None,
                        CauseId(0),
                    )
                });
            self.checker.store_field(node, slot(field), optional);
        }
        self.checker.store_field(
            node,
            Slot::Field("value".into()),
            Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
        );
        let value = self.reference(node, true);
        let index = self.handles.len();
        self.handles.push(Handle {
            value: EvaluatedValue::new(value, self.checker.recency_moves.len()),
            concrete,
        });
        index
    }
    fn branch(&mut self, left: usize, right: usize) -> usize {
        let a = self.handles[left]
            .value
            .current(&self.checker.recency_moves);
        let b = self.handles[right]
            .value
            .current(&self.checker.recency_moves);
        let value = a.join(&b, self.checker.choice(), CauseId(0));
        let concrete = [
            self.handles[left].concrete[0],
            self.handles[right].concrete[1],
        ];
        let index = self.handles.len();
        self.handles.push(Handle {
            value: EvaluatedValue::new(value, self.checker.recency_moves.len()),
            concrete,
        });
        index
    }
    fn clone_handle(&mut self, source: usize, immutable: bool) -> usize {
        let source_value = self.handles[source]
            .value
            .current(&self.checker.recency_moves);
        let domain = self
            .checker
            .heap
            .reachable(source_value.origins.nodes.iter().copied());
        let before = self.worlds.clone();
        let cursor = self.checker.recency_moves.len();
        let (value, mapping) = self
            .checker
            .canonical_ordinary_clone_batch(
                &source_value,
                Span {
                    start: 200,
                    end: 210,
                    ..self.span
                },
                ScopeId(0),
                immutable,
            )
            .expect("closed ordinary graph is in the tested domain");
        assert_eq!(
            mapping.keys().copied().collect::<BTreeSet<_>>(),
            domain,
            "copy mapping must cover the entire frozen source graph"
        );
        self.move_worlds(cursor);
        let concrete = std::array::from_fn(|world| {
            self.worlds[world].copy(
                self.handles[source].concrete[world],
                immutable,
                &mapping,
                &before[world].representation,
            )
        });
        for world in 0..2 {
            for copied in before[world].objects.len()..self.worlds[world].objects.len() {
                let output = self.worlds[world].representation[copied];
                assert!(mapping.values().any(|target| *target == output));
                for old in 0..before[world].objects.len() {
                    assert_eq!(
                        self.checker
                            .heap
                            .relation(output, self.worlds[world].representation[old])
                            .disjoint,
                        Condition::TRUE,
                        "ordinary clone must prove separation from every pre-existing object"
                    );
                }
            }
            if !immutable {
                let mut incoming = BTreeMap::<usize, usize>::new();
                *incoming.entry(concrete[world].object).or_default() += 1;
                for object in self.worlds[world].reachable(concrete[world].object) {
                    for edge in self.worlds[world].objects[object].fields.iter().flatten() {
                        *incoming.entry(edge.object).or_default() += 1;
                    }
                }
                if incoming.values().any(|count| *count > 1) {
                    assert!(
                        value.internal_aliases,
                        "copy cannot grant unmarked writable reception to internal aliases or cycles"
                    );
                }
            }
        }
        let index = self.handles.len();
        self.handles.push(Handle {
            value: EvaluatedValue::new(value, self.checker.recency_moves.len()),
            concrete,
        });
        index
    }
    fn check(&mut self, selected: &[usize]) {
        for world in &self.worlds {
            for (object, fact) in world.objects.iter().enumerate() {
                let represented = world.representation[object];
                for (field, edge) in fact.fields.iter().enumerate() {
                    if let Some(edge) = edge {
                        assert!(
                            self.checker.heap.nodes[represented.0 as usize].fields[&slot(field)]
                                .contains(&world.representation[edge.object]),
                            "concrete field edge was lost"
                        );
                    }
                }
            }
            for (left, a) in world.representation.iter().enumerate() {
                for (right, b) in world.representation.iter().enumerate() {
                    let relation = self.checker.heap.relation(*a, *b);
                    if relation.equal == Condition::TRUE {
                        assert_eq!(
                            left, right,
                            "summary equality cannot stand for distinct concrete objects"
                        );
                    }
                    if relation.disjoint == Condition::TRUE {
                        assert_ne!(
                            left, right,
                            "disjoint proof cannot include one concrete object twice"
                        );
                    }
                }
            }
        }
        let paths: [&[usize]; 7] = [&[], &[0], &[1], &[0, 0], &[0, 1], &[1, 0], &[1, 1]];
        let mut projected = vec![];
        // Closed structural data needs no repeated alias-name evaluation.
        // Cache only observational field projections at this unchanged heap.
        let mut projection_cache = Vec::<(Value, usize, Value)>::new();
        for &handle in selected {
            for path in paths {
                for readonly in [false, true] {
                    let concrete: [Option<Ref>; 2] = std::array::from_fn(|world| {
                        let mut root = self.handles[handle].concrete[world];
                        root.write &= !readonly;
                        self.worlds[world].project(root, path)
                    });
                    if concrete.iter().all(Option::is_none) {
                        continue;
                    }
                    let mut value = self.handles[handle]
                        .value
                        .current(&self.checker.recency_moves);
                    if readonly {
                        value.permission = Permission::Read;
                    }
                    let mut frame = self.checker.frame(BTreeMap::new(), false);
                    for &field in path {
                        if let Some((_, _, cached)) =
                            projection_cache.iter().find(|(before, slot, _)| {
                                *slot == field
                                    && before.same_abstract_value(&value)
                                    && before.construction == value.construction
                            })
                        {
                            value = cached.clone();
                            continue;
                        }
                        let before = value.clone();
                        value =
                            self.checker
                                .project(&value, slot(field), self.span, &mut frame, false);
                        value = self.checker.optional_payload(&value, node_type());
                        projection_cache.push((before, field, value.clone()));
                    }
                    for (world, target) in concrete.iter().enumerate() {
                        if let Some(target) = target {
                            assert!(
                                value
                                    .origins
                                    .nodes
                                    .contains(&self.worlds[world].representation[target.object]),
                                "projected may-source omits a concrete referent"
                            );
                            if value.permission == Permission::Write {
                                assert!(target.write, "read-only path acquired write permission");
                            }
                        }
                    }
                    if !readonly {
                        projected.push((value, concrete));
                    }
                }
            }
        }
        for (index, (left, a)) in projected.iter().enumerate() {
            for (right, b) in &projected[index..] {
                if self.checker.origins_disjoint(&left.origins, &right.origins) {
                    for world in 0..2 {
                        if let (Some(a), Some(b)) = (a[world], b[world]) {
                            assert_ne!(
                                a.object, b.object,
                                "claimed path disjointness/exclusivity conflicts in a concrete branch"
                            );
                        }
                    }
                }
            }
        }
        assert!(
            self.checker.diagnostics.is_empty(),
            "{:?}",
            self.checker.diagnostics
        );
        assert!(
            self.checker.unsupported.is_empty(),
            "{:?}",
            self.checker.unsupported
        );
    }
}
fn slot(field: usize) -> Slot {
    Slot::Field(if field == 0 { "left" } else { "right" }.into())
}
fn node_type() -> Ty {
    Ty::Record(
        [
            ("value".into(), (true, Ty::Int("int".into()))),
            (
                "left".into(),
                (true, Ty::Optional(Box::new(Ty::Named("Node".into())))),
            ),
            (
                "right".into(),
                (true, Ty::Optional(Box::new(Ty::Named("Node".into())))),
            ),
        ]
        .into(),
    )
}

fn cases() -> Vec<(bool, usize, usize)> {
    let mut cases = vec![];
    for graph in 0..81 {
        for permissions in 0..16 {
            let mut edges = graph;
            let mut meaningful = true;
            for field in 0..4 {
                if edges % 3 == 2 && permissions & (1 << field) != 0 {
                    meaningful = false;
                }
                edges /= 3;
            }
            if !meaningful {
                continue;
            }
            for same_site in [false, true] {
                cases.push((same_site, graph, permissions));
            }
        }
    }
    cases
}

fn run_trace(same_site: bool, graph: usize, permissions: usize, full: bool, verbose: bool) {
    let mut machine = Machine::new(same_site, graph, permissions);
    profile(&machine, "constructed", verbose);
    let source = machine.handles[0]
        .value
        .current(&machine.checker.recency_moves);
    let mut frame = machine.checker.frame(BTreeMap::new(), false);
    let selected = machine
        .checker
        .project(&source, slot(0), machine.span, &mut frame, false);
    profile(&machine, "projected", verbose);
    assert!(type_size(&selected.ty) < 4096);
    let copied = machine.clone_handle(0, false);
    profile(&machine, "cloned once", verbose);
    machine.check(&[0, 1, copied]);
    if !full {
        return;
    }
    let shell = machine.allocate(SiteId(2), [Some(0), Some(1)]);
    let mut state = machine.branch(0, shell);
    machine.check(&[0, 1, shell, state]);
    for _ in 0..3 {
        let previous = state;
        state = machine.clone_handle(state, false);
        let shell = machine.allocate(SiteId(2), [Some(0), Some(state)]);
        machine.check(&[0, 1, previous, state, shell]);
    }
    let frozen = machine.clone_handle(state, true);
    machine.check(&[0, 1, state, frozen]);
    profile(&machine, "full trace", verbose);
}

fn type_size(root: &Ty) -> usize {
    let mut pending = vec![root];
    let mut count = 0;
    while let Some(ty) = pending.pop() {
        count += 1;
        if count >= 4096 {
            return count;
        }
        match ty {
            Ty::Immutable(child)
            | Ty::Optional(child)
            | Ty::Array(child)
            | Ty::Set(child)
            | Ty::Range(child) => pending.push(child),
            Ty::Result(a, b) | Ty::Map(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            Ty::Tuple(items) => pending.extend(items),
            Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                pending.extend(fields.values().map(|(_, ty)| ty))
            }
            _ => {}
        }
    }
    count
}
fn profile(machine: &Machine, stage: &str, verbose: bool) {
    let maximum = machine
        .checker
        .fields
        .values()
        .map(|value| type_size(&value.ty))
        .max()
        .unwrap_or(0);
    if verbose {
        eprintln!(
            "stage={stage} nodes={} fields={} max_type_nodes={maximum} bdd={}",
            machine.checker.heap.nodes.len(),
            machine.checker.fields.len(),
            machine.checker.heap.conditions.decisions().count()
        );
    }
    assert!(
        machine.checker.heap.nodes.len() < 256 && maximum < 4096,
        "finite probe exceeded its structural limit"
    );
}

#[test]
fn representative_graph_trace_exercises_a_shared_cycle() {
    assert_eq!(cases().len(), 1250);
    run_trace(true, 0, 0, true, true);
}

/// Explicit audit command: the normal suite runs the representative full trace.
/// This domain has two initial objects, two fields, absent/read/write edges to
/// either object, and either distinct or recycled initial allocation sites.
/// The concrete interpreter covers branch selection, shell reuse, three
/// repeated copies and immutable copying. It excludes resources, Results,
/// callable environments, arbitrary writes and more than two initial objects.
#[test]
#[ignore = "explicit 1250-case concrete execution audit; run with external memory/time limits"]
fn every_two_object_graph_executes_against_the_concrete_model() {
    let cases = cases();
    assert_eq!(cases.len(), 1250);
    let count = std::env::var("RIL_ORACLE_CASES")
        .ok()
        .map(|value| value.parse::<usize>().expect("positive case count"))
        .unwrap_or(cases.len());
    assert!(count > 0 && count <= cases.len());
    let start = std::env::var("RIL_ORACLE_CASE_START")
        .ok()
        .map(|value| value.parse::<usize>().expect("nonnegative case ID"))
        .unwrap_or(0);
    let sample = std::env::var_os("RIL_ORACLE_SAMPLE").is_some();
    assert!(if sample {
        start == 0
    } else {
        start + count <= cases.len()
    });
    let full = std::env::var_os("RIL_ORACLE_INITIAL_ONLY").is_none();
    eprintln!(
        "audit cases={count}/{} start={start} sample={sample} full_trace={full}",
        cases.len()
    );
    for index in 0..count {
        let id = if sample {
            index * cases.len() / count
        } else {
            start + index
        };
        let (same_site, graph, permissions) = cases[id];
        run_trace(same_site, graph, permissions, full, false);
        if (index + 1) % 25 == 0 || index + 1 == count {
            eprintln!("completed={}/{count} last_case_id={id}", index + 1);
        }
    }
}
