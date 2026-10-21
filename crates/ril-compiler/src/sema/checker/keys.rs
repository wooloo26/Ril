//! Static product coordinates retain their source sort and the receiver's
//! existing access path; a runtime string is not a static record label.
use super::*;
impl Checker {
    /// A universal coordinate can carry an opaque borrowed row family as a
    /// possibility. It cannot select or inspect that family's Result producers.
    fn borrowed_opaque_coordinate_family(&self, base: &Value) -> bool {
        if !self.universal || base.origins.nodes.is_empty() || !base.scoped.is_empty() {
            return false;
        }
        let receiver = self
            .record_bound_receiver_view(&base.ty)
            .unwrap_or_else(|| self.call_inference_type(&base.ty));
        let Ty::OpenRecord { row, .. } = receiver else {
            return false;
        };
        let slot = Slot::RowTail(row.identity.clone());
        let mut families = BTreeSet::new();
        for node in &base.origins.nodes {
            if !self
                .heap
                .nodes
                .get(node.0 as usize)
                .is_some_and(|node| matches!(node.kind, OriginKind::Formal(_)))
            {
                return false;
            }
            let Some(tail) = self.fields.get(&(*node, slot.clone())) else {
                return false;
            };
            if !matches!(&tail.ty, Ty::OpenRecord { fields, row: actual }
                if fields.is_empty() && actual.identity == row.identity)
                || tail.origins.nodes.is_empty()
                || tail.results.is_empty()
                || !tail.outer_results.is_empty()
                || !tail.must_outer_results.is_empty()
                || !tail.scoped.is_empty()
                || tail.result_tag.is_some()
            {
                return false;
            }
            for origin in &tail.origins.nodes {
                if !self.heap.nodes.get(origin.0 as usize).is_some_and(|node| {
                    matches!(node.kind, OriginKind::Formal(_)) && node.fields.is_empty()
                }) || self.heap.relation(*origin, *origin) != Relation::UNKNOWN
                {
                    return false;
                }
            }
            for producer in &tail.results {
                if !self
                    .result_duties
                    .get(*producer as usize)
                    .is_some_and(|duty| {
                        duty.id == *producer
                            && duty.creation_owner == ScopeId(u32::MAX)
                            && duty.owner == ScopeId(u32::MAX)
                            && !duty.inspected
                            && !duty.covered
                    })
                {
                    return false;
                }
            }
            families.extend(&tail.results);
        }
        base.results.is_subset(&families)
    }
    /// Inspect the current declaration's lexical generic context. A selected
    /// string/integer observation is never a carrier proof; the annotation
    /// itself must resolve to this exact static-key binder.
    pub(super) fn static_key_carrier(&mut self, parameter: &Parameter) -> Option<(String, String)> {
        let PatternKind::Name(name) = &parameter.pattern.kind else {
            return None;
        };
        let syntax = parameter.ty.as_ref()?;
        let ty = self.ty(syntax);
        let Ty::StaticKey(identity) = self.call_inference_type(&ty) else {
            return None;
        };
        self.generic_key_bounds
            .contains_key(&identity)
            .then(|| (identity, name.clone()))
    }
    pub(super) fn static_key_bound_type(&mut self, identity: &str) -> Option<Ty> {
        let bound = self.generic_key_bounds.get(identity)?.clone();
        let context = self.generic_key_contexts.get(identity)?.clone();
        let previous =
            std::mem::replace(&mut self.type_source.environment.generic_context, context);
        let result = self.ty(&bound);
        self.type_source.environment.generic_context = previous;
        Some(result)
    }
    pub(super) fn static_type_projection(
        &self,
        base: &Ty,
        coordinate: &StaticCoordinate,
    ) -> Option<Ty> {
        let base = self
            .record_bound_receiver_view(base)
            .unwrap_or_else(|| self.expanded(base, &mut BTreeSet::new()));
        match (base, coordinate) {
            (
                Ty::Record(fields) | Ty::OpenRecord { fields, .. },
                StaticCoordinate::Label(label),
            ) => fields.get(label).map(|(_, ty)| ty.clone()),
            (Ty::Tuple(items), StaticCoordinate::Index(index)) => usize::try_from(*index)
                .ok()
                .and_then(|index| items.get(index).cloned()),
            (owner @ (Ty::Named(_) | Ty::Applied { .. }), StaticCoordinate::Label(label)) => self
                .constructors
                .values()
                .find(|constructor| {
                    constructor.owner == owner
                        && constructor
                            .tag
                            .rsplit_once("::")
                            .is_some_and(|(_, member)| member == label)
                })
                .map(|constructor| constructor.payload.clone()),
            _ => None,
        }
    }
    pub(super) fn computed_projection(
        &mut self,
        base: &Expr,
        key: &Expr,
        span: Span,
        frame: &mut Frame,
    ) -> Value {
        let mut base = self.expression(base, frame);
        if base.ty == Ty::Never {
            return base;
        }
        let base_recency = self.recency_moves.len();
        let key_value = self.expression(key, frame);
        self.transport_value_since(&mut base, base_recency);
        let coordinate = match &key.kind {
            ExprKind::Literal(Literal::String(text)) => {
                crate::lower::decode_text(&text[1..text.len() - 1])
                    .ok()
                    .map(StaticCoordinate::Label)
            }
            ExprKind::Literal(Literal::RawString(text)) => {
                Some(StaticCoordinate::Label(text[1..text.len() - 1].into()))
            }
            ExprKind::Interpolated(parts)
                if parts.iter().all(|part| matches!(part, StringPart::Text(_))) =>
            {
                Some(StaticCoordinate::Label(
                    parts
                        .iter()
                        .map(|part| {
                            if let StringPart::Text(text) = part {
                                text.as_str()
                            } else {
                                unreachable!()
                            }
                        })
                        .collect(),
                ))
            }
            ExprKind::Literal(Literal::Integer(_)) | ExprKind::Unary { .. } => {
                self.require_type(&key_value, &Ty::Int("int".into()), key.span);
                if let Some(Constant::Integer(index)) = key_value.constant {
                    Some(StaticCoordinate::Index(index))
                } else {
                    None
                }
            }
            _ => {
                if let Ty::StaticKey(identity) = &key_value.ty {
                    self.type_source
                        .environment
                        .static_key_arguments
                        .get(identity)
                        .cloned()
                } else {
                    None
                }
            }
        };
        let Some(coordinate) = coordinate else {
            if let Ty::StaticKey(identity) = &key_value.ty
                && self.generic_key_bounds.contains_key(identity)
            {
                let Some(expected) = self.static_key_bound_type(identity) else {
                    self.unsupported(
                        key.span,
                        "static key receiver has no lexical binder context",
                    );
                    return Value::scalar(Ty::Unknown, None, base.cause);
                };
                if self.expanded(&expected, &mut BTreeSet::new())
                    != self.expanded(&base.ty, &mut BTreeSet::new())
                {
                    self.unsupported(key.span,"static key membership in another symbolic receiver requires an additional constraint proof");
                    return Value::scalar(Ty::Unknown, None, base.cause);
                }
                if !base.scoped.is_empty()
                    || (!base.results.is_empty() && !self.borrowed_opaque_coordinate_family(&base))
                {
                    self.unsupported(span,"symbolic constituent selection requires exact Result/resource membership coverage");
                }
                let mut projected = base.clone();
                projected.ty = Ty::Projection {
                    base: Box::new(base.ty.clone()),
                    key: identity.clone(),
                };
                projected.permission = Permission::Read;
                projected.construction = false;
                projected.marker = false;
                projected.retention_result = false;
                projected.constant = None;
                projected.static_coordinate = None;
                projected.unsuffixed_numeric = false;
                projected.literal_number = false;
                projected.callables.clear();
                projected.callable_bounds.clear();
                projected.callable_returns.clear();
                projected.signature = None;
                projected.variant_tag = None;
                projected.variant_payload = None;
                projected.variant_witnesses.clear();
                projected.option_tag = None;
                projected.option_payload = None;
                projected.option_identity = None;
                projected.result_tag = None;
                projected.result_payload = None;
                projected.result_success = None;
                projected.result_error = None;
                projected.outer_results.clear();
                projected.must_outer_results.clear();
                projected.must_results.clear();
                projected.cause = self.cause(
                    CauseKind::Projection,
                    span,
                    "static coordinate projection retains the receiver's complete origin set",
                    [base.cause, key_value.cause],
                );
                self.access(&base, None, Mode::Read, span, frame);
                return projected;
            }
            if matches!(key_value.ty, Ty::Generic(_)) {
                self.unsupported(
                    key.span,
                    "static keyof parameter requires an instantiated coordinate proof",
                );
            } else {
                self.error(
                    "E0324",
                    key.span,
                    "computed product projection requires a statically known label or position",
                    [key_value.cause],
                );
            }
            return Value::scalar(Ty::Unknown, None, base.cause);
        };
        let receiver = self
            .record_bound_receiver_view(&base.ty)
            .unwrap_or_else(|| self.expanded(&base.ty, &mut BTreeSet::new()));
        let slot = match (receiver, coordinate) {
            (Ty::Record(_) | Ty::OpenRecord { .. }, StaticCoordinate::Label(label)) => {
                Slot::Field(label)
            }
            (Ty::Tuple(_), StaticCoordinate::Index(index)) => {
                let Ok(index) = u32::try_from(index) else {
                    self.error(
                        "E0312",
                        key.span,
                        "tuple coordinate is outside its arity",
                        [key_value.cause],
                    );
                    return self.unit(span);
                };
                Slot::Tuple(index)
            }
            (Ty::Named(_) | Ty::Applied { .. }, StaticCoordinate::Index(index)) => {
                let Ok(index) = u32::try_from(index) else {
                    self.error(
                        "E0312",
                        key.span,
                        "sum coordinate is outside its payload arity",
                        [key_value.cause],
                    );
                    return self.unit(span);
                };
                Slot::Tuple(index)
            }
            (Ty::Generic(_) | Ty::Unknown, _) => {
                self.unsupported(
                    span,
                    "static product shape requires a proved generic constraint",
                );
                return self.unit(span);
            }
            (Ty::Record(_), StaticCoordinate::Index(_))
            | (Ty::Tuple(_), StaticCoordinate::Label(_)) => {
                self.error(
                    "E0324",
                    key.span,
                    "record labels and tuple positions have different coordinate sorts",
                    [key_value.cause],
                );
                return self.unit(span);
            }
            _ => {
                self.error(
                    "E0337",
                    span,
                    "receiver does not expose this product coordinate",
                    [base.cause],
                );
                return self.unit(span);
            }
        };
        self.project(&base, slot, span, frame, true)
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
    fn an_opaque_coordinate_family_requires_its_actual_row_edge_and_borrowed_producer() {
        use crate::sema::model::rows::{OpenTail, RowIdentity};
        let mut checker = Checker::new(FileId(0));
        checker.universal = true;
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let row = OpenTail {
            identity: RowIdentity::Binder("test:row:R".into()),
            lacks: BTreeSet::new(),
        };
        let value = checker.formal_value(
            Ty::OpenRecord {
                fields: BTreeMap::new(),
                row: row.clone(),
            },
            0,
            span,
            &mut BTreeSet::new(),
        );
        assert!(checker.borrowed_opaque_coordinate_family(&value));
        let mut other = value.clone();
        let known = checker.formal_result(
            Ty::Result(Box::new(Ty::Int("int".into())), Box::new(Ty::Str)),
            span,
        );
        other.results.extend(&known.results);
        assert!(!checker.borrowed_opaque_coordinate_family(&other));
        let producer = *value.results.first().unwrap();
        checker.result_duties[producer as usize].creation_owner = ScopeId(0);
        assert!(!checker.borrowed_opaque_coordinate_family(&value));
        checker.result_duties[producer as usize].creation_owner = ScopeId(u32::MAX);
        let origin = *value.origins.nodes.first().unwrap();
        checker
            .fields
            .remove(&(origin, Slot::RowTail(row.identity)));
        assert!(!checker.borrowed_opaque_coordinate_family(&value));
    }

    #[test]
    fn a_symbolic_coordinate_never_inspects_a_different_actual_result_member() {
        let source = "fn get_field<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(key)}\nfn example(){let first:Result<int,str>=Ok(1);let second:Result<int,str>=Ok(2);let selected=get_field(.{first:first,second:second},\"first\");assert(selected is Ok(1))}";
        let outcome = crate::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, crate::CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0720")),
            "{outcome:?}"
        );
    }
    #[test]
    fn static_product_coordinates_preserve_sort_and_authority() {
        let result = check(
            "type User = { id: int, name: str }\nfn example(item: User) { let name = item.(\"name\"); assert(name == item.name); let pair = (1, \"a\"); assert(pair.(1) == \"a\") }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for (source, code) in [
            (
                "fn example(key: str) { let item = .{ value: 1 }; let _ = item.(key) }",
                "E0324",
            ),
            (
                "fn example() { let pair = (1, 2); let _ = pair.(\"0\") }",
                "E0324",
            ),
            (
                "fn example() { let items = [1]; let _ = items.foo }",
                "E0337",
            ),
            (
                "type Cell = { mut value: int }\nfn example() { let item = .{ cell: Cell.{value: 1} }; let mut alias = item.(\"cell\"); alias.value += 1 }",
                "E0520",
            ),
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn static_key_parameters_are_distinct_from_data_types_and_retain_symbolic_origins() {
        let result = check("fn get_field<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(key)}");
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let facts = result.program.unwrap();
        let projection = facts
            .facts()
            .expressions
            .iter()
            .find(|fact| matches!(fact.value.ty, Ty::Projection { .. }))
            .unwrap();
        assert_eq!(projection.value.permission, Permission::Read);
        assert!(!projection.value.origins.nodes.is_empty());
        assert!(!projection.value.construction);
        assert!(!projection.value.marker);
        for source in [
            "fn bad<T,K:keyof T>(record:T,keys:[]K){}",
            "fn bad<T,K:keyof T>(record:T,entry:{key:K}){}",
            "fn bad<T,K:keyof T>(record:T,entry:?K){}",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn instantiated_static_keys_check_membership_sort_and_runtime_availability() {
        let prelude = "fn get_field<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(key)}\n";
        let result = check(&format!(
            "{prelude}fn example(){{let id:int=get_field(.{{id:1}},\"id\");assert(id==1)}}"
        ));
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for (body, code) in [
            (
                "fn example(){let id=get_field(.{id:1},\"missing\")}",
                "E0323",
            ),
            (
                "fn example(key:str){let id=get_field(.{id:1},key)}",
                "E0814",
            ),
            (
                "fn example(){let key=\"id\";let id=get_field(.{id:1},key)}",
                "E0814",
            ),
            ("fn example(){let id=get_field(.{id:1},0)}", "E0323"),
            ("fn example(){let id=get_field((1,2),0)}", "E0301"),
        ] {
            let result = check(&format!("{prelude}{body}"));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{body}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        let parsed = ril_syntax::parse(&format!(
            "{prelude}fn example(){{let id:int=get_field(.{{id:1}},\"id\");assert(id==1)}}"
        ));
        let evaluated = crate::static_eval::evaluate(
            &parsed.program,
            ril_compiler_core::target::TargetLayout::POINTER64,
        );
        assert!(
            evaluated.diagnostics.is_empty() && evaluated.unsupported.is_empty(),
            "{:?} {:?}",
            evaluated.diagnostics,
            evaluated.unsupported
        );
        let result = crate::sema::analyze(&evaluated.program, FileId(0));
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(&format!(
            "type Cell={{mut value:int}}\n{prelude}fn example(mut cell:Cell)&mut{{let record=.{{cell:cell}};let mut alias=^mut get_field(record,\"cell\");alias.value+=1}}"
        ));
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0520"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "fn get_field<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(K)}\nfn example(){let id:int=get_field(.{id:1},\"id\")}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn full_sessions_preserve_static_key_binders_and_distinct_call_coordinates() {
        let source = "fn get_field<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(key)}\nfn example(){let first:int=get_field(.{id:1,name:\"a\"},\"id\");let second:str=get_field(.{id:2,name:\"b\"},\"name\");assert(first==1);assert(second==\"b\")}";
        let verified = crate::session::Session::new(source.as_bytes().to_vec()).verify();
        assert!(verified.is_ok(), "{verified:?}");
        let facts = verified.unwrap();
        assert!(
            facts
                .facts()
                .static_key_checks
                .iter()
                .any(|check| check.coordinate == StaticCoordinate::Label("id".into()))
        );
        let source = "fn member<K:keyof (int,str)>(value:(int,str),key:K)->(int,str).(K){value.(K)}\nfn example(){let first:int=member((1,\"a\"),0);let second:str=member((2,\"b\"),1);assert(first==1);assert(second==\"b\")}";
        let verified = crate::session::Session::new(source.as_bytes().to_vec()).verify();
        assert!(verified.is_ok(), "{verified:?}");
        assert!(
            facts
                .facts()
                .static_key_checks
                .iter()
                .any(|check| check.coordinate == StaticCoordinate::Label("name".into()))
        );
        for (body, code) in [
            (
                "fn example(){let _=get_field(.{id:1},\"missing\")}",
                "E0323",
            ),
            ("fn example(key:str){let _=get_field(.{id:1},key)}", "E0814"),
        ] {
            let source = format!(
                "fn get_field<T:{{..R}},K:keyof T>(record:T,key:K)->T.(K){{record.(key)}}\n{body}"
            );
            let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
            let crate::session::CompilationOutcome::Rejected { diagnostics } = outcome else {
                panic!("{source}: {outcome:?}");
            };
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic.code == code),
                "{source}: {diagnostics:?}"
            );
        }
    }
}
