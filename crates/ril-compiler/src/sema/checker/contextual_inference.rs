//! Result contexts solve only the producing invocation's unselected binders.
use super::*;
use std::sync::Arc;

pub(in crate::sema::checker) fn substitute_inferred_type(
    ty: &Ty,
    selected: &BTreeMap<String, Ty>,
) -> Ty {
    match ty {
        Ty::Generic(identity) => selected
            .get(identity)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        Ty::Immutable(inner) => Ty::Immutable(Box::new(substitute_inferred_type(inner, selected))),
        Ty::Optional(inner) => Ty::Optional(Box::new(substitute_inferred_type(inner, selected))),
        Ty::Array(inner) => Ty::Array(Box::new(substitute_inferred_type(inner, selected))),
        Ty::Set(inner) => Ty::Set(Box::new(substitute_inferred_type(inner, selected))),
        Ty::Range(inner) => Ty::Range(Box::new(substitute_inferred_type(inner, selected))),
        Ty::Result(a, b) => Ty::Result(
            Box::new(substitute_inferred_type(a, selected)),
            Box::new(substitute_inferred_type(b, selected)),
        ),
        Ty::Map(a, b) => Ty::Map(
            Box::new(substitute_inferred_type(a, selected)),
            Box::new(substitute_inferred_type(b, selected)),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .iter()
                .map(|ty| substitute_inferred_type(ty, selected))
                .collect(),
        ),
        Ty::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(name, (mutable, ty))| {
                    (
                        name.clone(),
                        (*mutable, substitute_inferred_type(ty, selected)),
                    )
                })
                .collect(),
        ),
        Ty::OpenRecord { fields, row } => {
            let fields: BTreeMap<_, _> = fields
                .iter()
                .map(|(name, (mutable, ty))| {
                    (
                        name.clone(),
                        (*mutable, substitute_inferred_type(ty, selected)),
                    )
                })
                .collect();
            if let crate::sema::model::rows::RowIdentity::Binder(identity) = &row.identity
                && let Some(selection) = selected.get(identity)
            {
                use crate::sema::model::rows::{Row, Solver};
                let remainder = match selection {
                    Ty::Record(fields) => Some(Row::closed(fields.clone())),
                    Ty::OpenRecord { fields, row } => Some(Row::open(fields.clone(), row.clone())),
                    _ => None,
                };
                if let Some(remainder) = remainder {
                    let mut solver =
                        Solver::new("inferred row substitution", [row.identity.clone()]);
                    if let crate::sema::model::rows::RowTail::Open(tail) = &remainder.tail {
                        let _ =
                            solver.declare_rigid(tail.identity.clone(), tail.lacks.iter().cloned());
                    }
                    if solver
                        .unify(&Row::open(BTreeMap::new(), row.clone()), &remainder)
                        .is_ok()
                        && let Ok(composed) =
                            solver.normalize(&Row::open(fields.clone(), row.clone()))
                    {
                        return Checker::row_type(composed);
                    }
                }
                Ty::OpenRecord {
                    fields,
                    row: row.clone(),
                }
            } else {
                // Only an exact, closed remainder discharges the tail. An
                // unknown or inconsistent selection preserves its obligation.
                Ty::OpenRecord {
                    fields,
                    row: row.clone(),
                }
            }
        }
        Ty::Callable(parameters, result) => Ty::Callable(
            parameters
                .iter()
                .map(|ty| substitute_inferred_type(ty, selected))
                .collect(),
            Box::new(substitute_inferred_type(result, selected)),
        ),
        Ty::Applied {
            constructor,
            arguments,
        } => Ty::Applied {
            constructor: constructor.clone(),
            arguments: arguments
                .iter()
                .map(|argument| match argument {
                    TypeArgument::Type(ty) => {
                        TypeArgument::Type(Box::new(substitute_inferred_type(ty, selected)))
                    }
                    // Canonical arguments were already completely selected. Their
                    // dimension/row identity must never be rebuilt from a bare Ty.
                    other => other.clone(),
                })
                .collect(),
        },
        Ty::Projection { base, key } => Ty::Projection {
            base: Box::new(substitute_inferred_type(base, selected)),
            key: key.clone(),
        },
        _ => ty.clone(),
    }
}

impl Checker {
    pub(in crate::sema::checker) fn unresolved_inference_metas(
        &self,
        roots: impl IntoIterator<Item = String>,
    ) -> BTreeSet<String> {
        fn resolve(
            checker: &Checker,
            identity: &str,
            active: &mut BTreeSet<String>,
            unresolved: &mut BTreeSet<String>,
        ) {
            if !checker.inference_metas.contains(identity) {
                return;
            }
            if !active.insert(identity.into()) {
                unresolved.insert(identity.into());
                return;
            }
            let resolutions: Vec<_> = checker
                .inference_resolutions
                .iter()
                .filter(|resolution| resolution.binder == identity)
                .collect();
            if resolutions.is_empty() {
                unresolved.insert(identity.into());
            }
            for resolution in resolutions {
                let mut nested = BTreeSet::new();
                resolution.selected.generic_names(&mut nested);
                for identity in nested {
                    resolve(checker, &identity, active, unresolved);
                }
            }
            active.remove(identity);
        }
        let mut unresolved = BTreeSet::new();
        for root in roots {
            resolve(self, &root, &mut BTreeSet::new(), &mut unresolved);
        }
        unresolved
    }
    pub(in crate::sema::checker) fn pending_result_binders(
        &self,
        value: &Value,
    ) -> BTreeSet<String> {
        fn visit(
            checker: &Checker,
            value: &Value,
            seen: &mut BTreeSet<NodeId>,
            pending: &mut BTreeSet<String>,
        ) {
            pending.extend(value.pending_inference.iter().cloned());
            for payload in [
                &value.variant_payload,
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            {
                visit(checker, payload, seen, pending);
            }
            for node in &value.origins.nodes {
                if seen.insert(*node) {
                    for ((parent, _), child) in &checker.fields {
                        if parent == node {
                            visit(checker, child, seen, pending);
                        }
                    }
                }
            }
        }
        let mut pending = BTreeSet::new();
        visit(self, value, &mut BTreeSet::new(), &mut pending);
        pending
    }
    pub(in crate::sema::checker) fn contextual_result_inference(
        &mut self,
        value: &mut Value,
        expected: &Ty,
        span: Span,
    ) {
        if value.ty == Ty::Never {
            return;
        }
        let pending = self.pending_result_binders(value);
        if pending.is_empty() {
            return;
        }
        let actual = self.call_inference_type(&value.ty);
        let expected = self.call_inference_type(expected);
        let mut selected = BTreeMap::new();
        if !unify_call_types(&actual, &expected, &pending, &mut selected) {
            self.error(
                "E0301",
                span,
                "result context requires inconsistent generic instantiations",
                [value.cause],
            );
            return;
        }
        let mut work = vec![(value.clone(), expected)];
        let mut seen = BTreeSet::new();
        let mut affected = BTreeSet::new();
        while let Some((current, expected)) = work.pop() {
            let expected = match expected {
                Ty::Immutable(inner) => *inner,
                ty => ty,
            };
            // Option/Result share their selected payload's storage roots;
            // their type wrapper is not a collection shell on those nodes.
            match &expected {
                Ty::Optional(inner) if current.option_payload.is_some() => {
                    work.push((
                        *current.option_payload.as_ref().unwrap().clone(),
                        *inner.clone(),
                    ));
                    continue;
                }
                Ty::Result(ok, error)
                    if current.result_success.is_some()
                        || current.result_error.is_some()
                        || current.result_payload.is_some() =>
                {
                    if let Some(payload) = &current.result_success {
                        work.push((*payload.clone(), *ok.clone()));
                    }
                    if let Some(payload) = &current.result_error {
                        work.push((*payload.clone(), *error.clone()));
                    }
                    if let (Some(payload), Some(success)) =
                        (&current.result_payload, current.result_tag)
                    {
                        work.push((
                            *payload.clone(),
                            if success { *ok.clone() } else { *error.clone() },
                        ));
                    }
                    continue;
                }
                _ => {}
            }
            for node in &current.origins.nodes {
                if !seen.insert((*node, format!("{expected:?}"))) {
                    continue;
                }
                if let Some(previous) = self.storage_types.get(node) {
                    let mut names = BTreeSet::new();
                    previous.generic_names(&mut names);
                    if !names.is_disjoint(&pending) {
                        if !matches!(self.heap.nodes[node.0 as usize].kind, OriginKind::Fresh(_)) {
                            self.unsupported(span,"contextual generic storage inference requires a fresh owned type-variable graph");
                            return;
                        }
                        if !unify_call_types(previous, &expected, &pending, &mut selected) {
                            self.error(
                                "E0301",
                                span,
                                "shared result storage has inconsistent generic type contexts",
                                [value.cause],
                            );
                            return;
                        }
                        affected.insert(*node);
                    }
                }
                for ((parent, slot), child) in &self.fields {
                    if parent != node {
                        continue;
                    }
                    let ty = match (&expected, slot) {
                        (Ty::Array(inner) | Ty::Set(inner), Slot::Index(_) | Slot::AnyIndex) => {
                            Some(*inner.clone())
                        }
                        (Ty::Map(key, _), Slot::Field(name)) if name == "key" => Some(*key.clone()),
                        (Ty::Map(_, element), Slot::Index(_) | Slot::AnyIndex) => {
                            Some(*element.clone())
                        }
                        (Ty::Tuple(items), Slot::Tuple(index)) => {
                            items.get(*index as usize).cloned()
                        }
                        (Ty::Record(fields), Slot::Field(name)) => {
                            fields.get(name).map(|(_, ty)| ty.clone())
                        }
                        _ => None,
                    };
                    if let Some(ty) = ty {
                        work.push((child.clone(), ty));
                    }
                }
            }
            match &expected {
                Ty::Optional(inner) => {
                    if let Some(payload) = &current.option_payload {
                        work.push((*payload.clone(), *inner.clone()));
                    }
                }
                Ty::Result(ok, error) => {
                    if let Some(payload) = &current.result_success {
                        work.push((*payload.clone(), *ok.clone()));
                    }
                    if let Some(payload) = &current.result_error {
                        work.push((*payload.clone(), *error.clone()));
                    }
                    if let (Some(payload), Some(success)) =
                        (&current.result_payload, current.result_tag)
                    {
                        work.push((
                            *payload.clone(),
                            if success { *ok.clone() } else { *error.clone() },
                        ));
                    }
                }
                _ => {}
            }
        }
        fn contains_unknown(ty: &Ty) -> bool {
            match ty {
                Ty::Unknown | Ty::OpenRecord { .. } => true,
                Ty::Array(inner)
                | Ty::Optional(inner)
                | Ty::Immutable(inner)
                | Ty::Set(inner)
                | Ty::Range(inner) => contains_unknown(inner),
                Ty::Result(a, b) | Ty::Map(a, b) => contains_unknown(a) || contains_unknown(b),
                Ty::Tuple(items) => items.iter().any(contains_unknown),
                Ty::Record(fields) => fields.values().any(|(_, ty)| contains_unknown(ty)),
                Ty::Callable(parameters, result) => {
                    parameters.iter().any(contains_unknown) || contains_unknown(result)
                }
                Ty::Applied { arguments, .. } => arguments.iter().any(|argument| match argument {
                    TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                        contains_unknown(ty)
                    }
                    _ => false,
                }),
                Ty::Projection { base, .. } => contains_unknown(base),
                _ => false,
            }
        }
        selected.retain(|_, ty| !contains_unknown(ty));
        if selected.is_empty() {
            return;
        }
        fn rewrite_bound(
            bound: &Arc<CallableReturnBound>,
            selected: &BTreeMap<String, Ty>,
            memo: &mut BTreeMap<usize, Arc<CallableReturnBound>>,
            domain: &super::type_source::TypeSourceDomain,
        ) -> Arc<CallableReturnBound> {
            let pointer = Arc::as_ptr(bound) as usize;
            if let Some(rewritten) = memo.get(&pointer) {
                return rewritten.clone();
            }
            let rewritten = if bound.raw {
                bound.clone()
            } else {
                let Some(mut environment) = domain.copy_environment(&bound.typing_environment)
                else {
                    return bound.clone();
                };
                let mut rewritten = (**bound).clone();
                rewritten.target = substitute_inferred_type(&bound.target, selected);
                for ty in environment.generic_substitutions.values_mut() {
                    *ty = substitute_inferred_type(ty, selected);
                }
                rewritten.typing_environment = environment.freeze();
                for predecessor in &mut rewritten.predecessors {
                    *predecessor = rewrite_bound(predecessor, selected, memo, domain);
                }
                if rewritten.target == bound.target
                    && rewritten.typing_environment == bound.typing_environment
                    && rewritten
                        .predecessors
                        .iter()
                        .zip(&bound.predecessors)
                        .all(|(rewritten, original)| Arc::ptr_eq(rewritten, original))
                {
                    bound.clone()
                } else {
                    Arc::new(rewritten)
                }
            };
            memo.insert(pointer, rewritten.clone());
            rewritten
        }
        fn rewrite(
            value: &mut Value,
            selected: &BTreeMap<String, Ty>,
            memo: &mut BTreeMap<usize, Arc<CallableReturnBound>>,
            domain: &super::type_source::TypeSourceDomain,
        ) {
            value.ty = substitute_inferred_type(&value.ty, selected);
            for bound in &mut value.callable_returns {
                *bound = rewrite_bound(bound, selected, memo, domain);
            }
            value
                .pending_inference
                .retain(|identity| !selected.contains_key(identity));
            value.requires_inference = !value.pending_inference.is_empty();
            for payload in [
                &mut value.variant_payload,
                &mut value.option_payload,
                &mut value.result_payload,
                &mut value.result_success,
                &mut value.result_error,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values_mut())
            {
                rewrite(payload, selected, memo, domain);
            }
        }
        for node in affected {
            let previous = &self.storage_types[&node];
            self.storage_types
                .insert(node, substitute_inferred_type(previous, &selected));
        }
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        let mut bound_memo = BTreeMap::new();
        for ((parent, _), child) in &mut self.fields {
            if reachable.contains(parent) {
                rewrite(child, &selected, &mut bound_memo, &self.type_source);
            }
        }
        rewrite(value, &selected, &mut bound_memo, &self.type_source);
        value.pending_inference = pending
            .into_iter()
            .filter(|identity| !selected.contains_key(identity))
            .collect();
        value.requires_inference = !value.pending_inference.is_empty();
        for (binder, ty) in &selected {
            value.cause = self.record_inference_resolution(binder, ty, span, value.cause);
        }
    }
}

#[cfg(test)]
mod return_contract_tests {
    use super::*;

    #[test]
    fn contextual_inference_preserves_diamonds_and_reuses_unaffected_proofs() {
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        for affected in [false, true] {
            let mut checker = Checker::new(FileId(0));
            let binder = "call:T".to_owned();
            checker.inference_metas.insert(binder.clone());
            let mut value = checker.unit(span);
            value.ty = Ty::Optional(Box::new(Ty::Generic(binder.clone())));
            value.pending_inference.insert(binder.clone());
            let mut root = CallableReturnBound::raw(Callable::Closure(1), span);
            root.raw = false;
            root.target = if affected {
                Ty::Generic(binder)
            } else {
                Ty::Unit
            };
            value.callable_returns.push(Arc::new(root));
            for level in 0..64 {
                let mut left = (*value.callable_returns[0]).clone();
                left.predecessors = value.callable_returns.clone();
                left.span.start = level * 2;
                let mut right = left.clone();
                right.span.start += 1;
                value.callable_returns = vec![Arc::new(left), Arc::new(right)];
            }
            let original = value.callable_returns.clone();
            checker.contextual_result_inference(&mut value, &Ty::Optional(Box::new(Ty::Str)), span);
            let mut work = value.callable_returns.clone();
            let mut seen = BTreeSet::new();
            while let Some(bound) = work.pop() {
                if seen.insert(Arc::as_ptr(&bound) as usize) {
                    assert_eq!(bound.target, if affected { Ty::Str } else { Ty::Unit });
                    work.extend(bound.predecessors.iter().cloned());
                }
            }
            assert_eq!(seen.len(), 129);
            assert_eq!(
                Arc::ptr_eq(&original[0], &value.callable_returns[0]),
                !affected
            );
            assert!(Arc::ptr_eq(
                &value.callable_returns[0].predecessors[0],
                &value.callable_returns[1].predecessors[0]
            ));
        }
    }

    #[test]
    fn result_inference_rewrites_prior_contracts_without_rebuilding_their_syntax_or_origins() {
        let mut checker = Checker::new(FileId(0));
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let binder = "call:T".to_owned();
        checker.inference_metas.insert(binder.clone());
        let mut value = checker.unit(span);
        value.ty = Ty::Callable(
            vec![],
            Box::new(Ty::Optional(Box::new(Ty::Generic(binder.clone())))),
        );
        value.pending_inference.insert(binder.clone());
        let mut prior = CallableReturnBound::raw(Callable::Closure(1), span);
        prior.raw = false;
        prior.target = Ty::Generic(binder.clone());
        prior.syntax = TypeExpr {
            hir_id: None,
            kind: TypeKind::Name {
                path: vec!["T".into()],
                arguments: vec![],
            },
            text: "T".into(),
            span,
        };
        let mut environment = prior.typing_environment.thaw();
        environment
            .generic_context
            .insert("T".into(), "declaration:T".into());
        environment
            .generic_substitutions
            .insert("declaration:T".into(), Ty::Generic(binder));
        environment.contract_bindings.insert("source".into(), 7);
        environment
            .static_key_arguments
            .insert("key".into(), StaticCoordinate::Label("field".into()));
        prior.typing_environment = environment.freeze();
        let prior = Arc::new(prior);
        let mut head = (*prior).clone();
        head.predecessors = vec![
            prior.clone(),
            Arc::new(CallableReturnBound::raw(Callable::Closure(1), span)),
        ];
        value.callable_returns.push(Arc::new(head.clone()));
        head.span.start = 1;
        value.callable_returns.push(Arc::new(head));
        let original = value.clone();
        let expected = Ty::Callable(vec![], Box::new(Ty::Optional(Box::new(Ty::Str))));
        checker.contextual_result_inference(&mut value, &expected, span);
        assert_eq!(value.ty, expected);
        assert!(value.pending_inference.is_empty());
        assert_eq!(value.origins, original.origins);
        assert_eq!(value.permission, original.permission);
        let head = &value.callable_returns[0];
        for bound in [head, &head.predecessors[0]] {
            assert_eq!(bound.target, Ty::Str);
            assert_eq!(
                bound.typing_environment.generic_substitutions["declaration:T"],
                Ty::Str
            );
            assert_eq!(bound.syntax, prior.syntax);
            assert_eq!(
                bound.typing_environment.generic_context,
                prior.typing_environment.generic_context
            );
            assert_eq!(
                bound.typing_environment.contract_bindings(),
                prior.typing_environment.contract_bindings()
            );
            assert_eq!(
                bound.typing_environment.static_key_arguments,
                prior.typing_environment.static_key_arguments
            );
        }
        assert!(head.predecessors[1].raw);
        assert_eq!(head.predecessors[1].target, Ty::Unknown);
        assert!(
            Arc::ptr_eq(
                &head.predecessors[0],
                &value.callable_returns[1].predecessors[0]
            ),
            "inference duplicated a shared return-contract proof"
        );
        assert_eq!(
            prior.target,
            Ty::Generic("call:T".into()),
            "inference modified another value's shared contract"
        );
    }
}
