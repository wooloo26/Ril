//! Ordinary-data loops use a finite may-graph over site recent/older nodes.
//! Immutable callable environments share this domain; mutable environments,
//! resources, Result duties and unresolved rows retain their other domains.
use super::*;
#[path = "loop_equivalence.rs"]
mod equivalence;

impl Checker {
    pub(super) fn loop_allocation_context(&self, owner: ScopeId) -> ScopeId {
        self.loop_allocation_owners
            .iter()
            .copied()
            .find(|parent| self.scope_is_within(owner, *parent))
            .unwrap_or(owner)
    }
    pub(super) fn allocate_owned(&mut self, span: Span, tag: u32, owner: ScopeId) -> NodeId {
        self.allocate(span, self.loop_allocation_context(owner).0 | tag, owner)
    }
    pub(super) fn ordinary_loop_value(
        &self,
        value: &Value,
        fields: &BTreeMap<(NodeId, Slot), Value>,
    ) -> bool {
        if !self.pending_copy_dependencies(value).is_empty() {
            return false;
        }
        fn shallow(checker: &Checker, value: &Value) -> bool {
            if !value.pending_copies.is_empty()
                || !value.results.is_empty()
                || !value.scoped.is_empty()
                || value.callables.iter().any(|callable| {
                    matches!(callable, Callable::Symbolic(..))
                        || checker.has_retained_handlers(callable)
                })
                || (value.callables.is_empty()
                    && matches!(
                        checker.expanded(&value.ty, &mut BTreeSet::new()),
                        Ty::Callable(..)
                    ))
                || value.mutable_environment
                || value.observer_environment
                || !(checker.ordinary_graph_type(&value.ty, true)
                    || checker.ordinary_loop_sum_carrier(value))
            {
                return false;
            }
            [
                &value.option_payload,
                &value.variant_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            .all(|nested| shallow(checker, nested))
        }
        if !shallow(self, value) {
            return false;
        }
        let nodes = loop_graph::reachable(fields, value.origins.nodes.iter().copied());
        fields
            .iter()
            .all(|((node, _), child)| !nodes.contains(node) || shallow(self, child))
    }

    fn ordinary_loop_sum_carrier(&self, value: &Value) -> bool {
        if value.variant_witnesses.is_empty() && value.variant_tag.is_none() {
            return false;
        }
        if self.resource_scan_type(&value.ty) != resources::ResourceScan::Absent {
            return false;
        }
        match &value.ty {
            Ty::Applied { arguments, .. } => arguments.iter().all(|argument| match argument {
                TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                    self.ordinary_graph_type(ty, true)
                }
                TypeArgument::Static(_) => true,
                TypeArgument::Symbolic(_) => false,
            }),
            Ty::Named(name) => self.types.get(name).is_some_and(|declaration| {
                !declaration.variants.is_empty()
                    || (declaration.nominal && declaration.value.is_some())
            }),
            _ => false,
        }
    }

    /// Type-only data eligibility cannot certify a callable environment.
    pub(super) fn ordinary_data_type(&self, ty: &Ty) -> bool {
        self.ordinary_graph_type(ty, false)
    }

    fn ordinary_graph_type(&self, ty: &Ty, callables: bool) -> bool {
        if self.resource_scan_type(ty) != resources::ResourceScan::Absent {
            return false;
        }
        fn visit(
            checker: &Checker,
            ty: &Ty,
            budget: &mut resources::TypeScanBudget,
            active: &mut BTreeSet<String>,
            complete: &mut BTreeMap<String, bool>,
            callables: bool,
        ) -> bool {
            if !budget.node() {
                return false;
            }
            match ty {
                Ty::Unknown
                | Ty::Result(..)
                | Ty::Generic(_)
                | Ty::OpenRecord { .. }
                | Ty::Projection { .. } => false,
                Ty::Callable(..) => callables,
                Ty::Immutable(inner)
                | Ty::Optional(inner)
                | Ty::Array(inner)
                | Ty::Set(inner)
                | Ty::Range(inner) => visit(checker, inner, budget, active, complete, callables),
                Ty::Map(key, value) => {
                    visit(checker, key, budget, active, complete, callables)
                        && visit(checker, value, budget, active, complete, callables)
                }
                Ty::Tuple(items) => items
                    .iter()
                    .all(|ty| visit(checker, ty, budget, active, complete, callables)),
                Ty::Record(fields) => fields
                    .values()
                    .all(|(_, ty)| visit(checker, ty, budget, active, complete, callables)),
                Ty::Named(_) | Ty::Applied { .. } if !ty.scalar() => {
                    let Some(key) = checker.capability_type_key(ty, budget) else {
                        return false;
                    };
                    if active.contains(&key) {
                        return true;
                    }
                    if let Some(ordinary) = complete.get(&key) {
                        return *ordinary;
                    }
                    if !budget.instance(&key) {
                        return false;
                    }
                    active.insert(key.clone());
                    let ordinary = checker
                        .capability_shallow_type_with_budget(ty, budget)
                        .is_some_and(|expanded| {
                            expanded != *ty
                                && visit(checker, &expanded, budget, active, complete, callables)
                        });
                    active.remove(&key);
                    complete.insert(key, ordinary);
                    ordinary
                }
                _ => ty.scalar(),
            }
        }
        visit(
            self,
            ty,
            &mut resources::TypeScanBudget::default(),
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
            callables,
        )
    }

    pub(super) fn join_ordinary_loop_value(
        &self,
        before: &Value,
        after: &Value,
        choice: u32,
        cause: CauseId,
    ) -> Value {
        let mut merged = before.join(after, choice, cause);
        if before.origins != after.origins {
            loop_graph::forget_choices(&mut merged);
        }
        merged
    }
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
    fn nested_aliases_cycles_and_reassigned_roots_reach_a_finite_may_graph() {
        for source in [
            "fn make(value:int)->[]int{[value]}\nfn example(values:[]int){var state=[0];for values as value{state=if value>0{make(value)}else{make(0)}};assert(len(state)>0)}",
            "type Cell={value:int}\nfn example(values:[]int){let seed=Cell.{value:1};let mut groups:[][]Cell=[];for values as value{groups !> Array::push([seed,Cell.{value:value}])};assert(len(groups)==len(values))}",
            "fn example(values:[]int){var state=[0];for values as value{state=[value,state[0]]};assert(len(state)>0)}",
            "type Node={mut value:int,mut following:?Node}\nfn example(values:[]int){let mut original=Node.{value:0,following:None};original.following=Some(^mut original);let mut copies:[]Node=[];for values as value{let mut copy=^mut clone(original);copy.value=value;copies !> Array::push(^mut copy)};assert(len(copies)==len(values))}",
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
    fn iterator_step_data_keeps_ordinary_transition_effects() {
        let source =
            ril_test::case_source("tests/regressions/ordinary-iteration.ril::effectful-transition");
        let result = crate::Session::new(source.as_bytes().to_vec()).analyze();
        assert!(
            result.status() == crate::AnalysisStatus::Verified,
            "{:?} {:?}",
            result.diagnostics(),
            result.unresolved()
        );
    }
    #[test]
    fn complete_sum_witnesses_do_not_erase_nonordinary_payloads() {
        let checker = Checker::new(FileId(0));
        for payload in [
            Ty::Named("File::Handle".into()),
            Ty::Result(Box::new(Ty::Int("int".into())), Box::new(Ty::Str)),
            Ty::Callable(vec![], Box::new(Ty::Unit)),
        ] {
            let mut value = Value::scalar(
                Ty::Applied {
                    constructor: "Choice".into(),
                    arguments: vec![TypeArgument::Type(Box::new(Ty::Unit))],
                },
                None,
                CauseId(0),
            );
            value.variant_tag = Some("Choice::Wrapped".into());
            value.variant_payload = Some(Box::new(Value::scalar(payload, None, CauseId(0))));
            assert!(!checker.ordinary_loop_value(&value, &checker.fields));
        }
    }
    #[test]
    fn at_most_once_is_not_evidence_that_a_write_will_happen() {
        let result = check(
            "type Cell={mut count:int}\ntype Holder={mut child:Cell}\nfn example(flag:bool){let mut shared=Cell.{count:0};let mut holder=^mut Holder.{child:^mut shared};let range=if flag{0..0}else{0..1};for range as index{holder.child=Cell.{count:index}};let _=Parallel::join(\\->{holder.child.count+=1},\\->{shared.count+=1})}",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0619"),
            "the possible zero-iteration path retains its old alias: {:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn may_selected_writes_cannot_erase_an_unselected_old_alias() {
        for update in [
            "selected.child=Cell.{count:1}",
            "for [1,2] as index{selected.child=Cell.{count:index}}",
        ] {
            let source = format!(
                "type Cell={{mut count:int}}\ntype Holder={{mut child:Cell}}\nfn example(flag:bool){{let mut shared=Cell.{{count:0}};let mut a=^mut Holder.{{child:^mut shared}};let mut b=^mut Holder.{{child:^mut shared}};let mut selected=if flag{{^mut a}}else{{^mut b}};{update};let _=Parallel::join(\\->{{a.child.count+=1}},\\->{{shared.count+=1}})}}"
            );
            let result = check(&source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0619"),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        let result = check(
            "type Cell={mut count:int}\nfn example(values:[]int){let base=Cell.{count:0};var selected=base;for values as value{selected=Cell.{count:value}};selected.count=1}",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0520"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn fresh_record_collection_growth_has_a_finite_regular_summary() {
        let result = check(
            "type Position={value:int,index:int}\nfn example(values:[]int){let mut positions:[]Position=[];var index=0;for values as value{positions !> Array::push(Position.{value:value,index:index});index+=1};assert(len(positions)==len(values))}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for source in [
            "type Cell={value:int}\nfn example(values:[]int){let outside=Cell.{value:1};let mut cells:[]Cell=[];for values as index{cells !> Array::push(outside)}}",
            "type Cell={value:int}\ntype Wrapper={cell:Cell}\nfn example(values:[]int){let outside=Cell.{value:1};let mut wrappers:[]Wrapper=[];for values as index{wrappers !> Array::push(Wrapper.{cell:outside})}}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_some(),
                "ordinary aliases remain representable without gaining authority: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn regular_widening_cannot_restore_permission_or_disjointness() {
        let mut checker = Checker::new(FileId(0));
        let span = Span {
            file: FileId(0),
            start: 1,
            end: 10,
        };
        let node = checker.allocate(span, 0, ScopeId(0));
        let mut reader = Value::reference(
            Ty::Record([("value".into(), (false, Ty::Int("int".into())))].into()),
            node,
            CauseId(0),
        );
        reader.permission = Permission::Read;
        let alias = reader.clone();
        assert!(checker.ordinary_loop_value(&reader, &checker.fields));
        loop_graph::forget_choices(&mut reader);
        assert_eq!(reader.permission, Permission::Read);
        assert!(!checker.origins_disjoint(&reader.origins, &alias.origins));
    }
}
