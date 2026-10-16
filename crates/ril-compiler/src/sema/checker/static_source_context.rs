//! Source coordinates derived from static-key and constructor declarations.
//!
//! These queries never create a ClosedWitness from a semantic Ty. Certified
//! nominal Const slots are erased only in a temporary coordinate comparison;
//! their ordinary sort and exact nominal identity checks remain mandatory.
use super::*;
use crate::sema::effect_identity::ArgumentKey;
use crate::sema::source_reception::{self, Target};
use std::sync::Arc;

const KEY_TOKEN: &str = "\0ril.source.key:";

impl Checker {
    pub(super) fn bounded_static_source_input(&self, syntax: &TypeExpr) -> Option<ArgumentKey> {
        fn admit(key: &ArgumentKey, work: &mut usize, depth: usize) -> Option<()> {
            *work = work.checked_sub(1)?;
            if depth >= 64 {
                return None;
            }
            let text = |work: &mut usize, value: &str| -> Option<()> {
                *work = work.checked_sub(value.len().div_ceil(32))?;
                Some(())
            };
            match key {
                ArgumentKey::Closed(value) => text(work, value)?,
                ArgumentKey::Binder { identity, .. } => text(work, identity)?,
                ArgumentKey::Name { name, arguments } => {
                    text(work, name)?;
                    for argument in arguments {
                        admit(argument, work, depth + 1)?;
                    }
                }
                ArgumentKey::Array { length, element } => {
                    if let Some(length) = length {
                        text(work, length)?;
                    }
                    admit(element, work, depth + 1)?;
                }
                ArgumentKey::Map { key, value } => {
                    admit(key, work, depth + 1)?;
                    admit(value, work, depth + 1)?;
                }
                ArgumentKey::Tuple(items) => {
                    for item in items {
                        admit(item, work, depth + 1)?;
                    }
                }
                ArgumentKey::Record { fields, row } => {
                    for (label, _, key) in fields {
                        text(work, label)?;
                        admit(key, work, depth + 1)?;
                    }
                    if let Some(row) = row {
                        admit(row, work, depth + 1)?;
                    }
                }
                ArgumentKey::Callable {
                    parameters,
                    result,
                    annotations,
                } => {
                    for (_, key) in parameters {
                        admit(key, work, depth + 1)?;
                    }
                    admit(result, work, depth + 1)?;
                    for annotation in annotations {
                        text(work, annotation)?;
                    }
                }
            }
            Some(())
        }
        // bounded_argument_key first admits the recursive normalization itself;
        // this second pass enforces the stricter Source coordinate allowance.
        let key =
            crate::static_eval::effects::bounded_argument_key(syntax, &self.effect_type_binders)?;
        admit(&key, &mut 4096, 0)?;
        Some(key)
    }

    fn genuine_source_key(&self, name: &str) -> Option<String> {
        let identity = name
            .strip_prefix(KEY_TOKEN)
            .map(str::to_owned)
            .or_else(|| self.generic_context.get(name).cloned())?;
        let binder = self.generic_binders.get(&identity)?;
        let function = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)?;
        let parameter = function.syntax.generics.get(binder.index as usize)?;
        if binder.identity != identity
            || binder.name != parameter.name
            || !matches!(
                parameter.bound.as_ref().map(|bound| &bound.kind),
                Some(TypeKind::KeyOf(_))
            )
            || !self.generic_key_bounds.contains_key(&identity)
            || !self.generic_key_contexts.contains_key(&identity)
        {
            return None;
        }
        Some(identity)
    }

    /// Preserve an unresolved projection as an open, identity-bearing source.
    /// This syntax is not a closed type witness and never supplies permissions.
    pub(super) fn freeze_static_source_type(&mut self, syntax: &TypeExpr) -> Option<Arc<TypeExpr>> {
        self.bounded_static_source_input(syntax)?;
        if let TypeKind::ComputedProjection { base, key } = &syntax.kind {
            let ExprKind::Name(name) = &key.kind else {
                return None;
            };
            let identity = self.genuine_source_key(name)?;
            let base = self.effect_argument_syntax(base).ok()?;
            let base_key = crate::static_eval::effects::bounded_argument_key(
                &base,
                &self.effect_type_binders,
            )?;
            source_reception::complete(&base_key, &mut 4096)?;
            if let Some(coordinate) = self.static_key_arguments.get(&identity) {
                let selected = match (&base.kind, coordinate) {
                    (TypeKind::Record { fields, row: None }, StaticCoordinate::Label(label)) => {
                        &fields.iter().find(|field| &field.name == label)?.ty
                    }
                    (TypeKind::Tuple(items), StaticCoordinate::Index(index)) => {
                        items.get(usize::try_from(*index).ok()?)?
                    }
                    _ => return None,
                };
                crate::static_eval::effects::bounded_argument_key(
                    selected,
                    &self.effect_type_binders,
                )?;
                return Some(Arc::new(selected.clone()));
            }
            let mut frozen_key = (**key).clone();
            frozen_key.kind = ExprKind::Name(format!("{KEY_TOKEN}{identity}"));
            return Some(Arc::new(TypeExpr {
                text: String::new(),
                span: syntax.span,
                kind: TypeKind::ComputedProjection {
                    base: Box::new(base),
                    key: Box::new(frozen_key),
                },
            }));
        }
        let frozen = self.effect_argument_syntax(syntax).ok()?;
        let (_, changed) = self.static_coordinate_key(&frozen)?;
        changed.then(|| Arc::new(frozen))
    }

    /// Additional reception for genuinely static source forms. A missing
    /// result retains the ordinary complete-source obligation.
    pub(super) fn check_static_source_reception(
        &mut self,
        target: &Target,
        actual: &Expr,
        value: &Value,
        observed: Option<usize>,
        frame: &Frame,
    ) -> Option<bool> {
        let original = self.static_source_observation(actual, value, observed, frame)?;
        if let Some(TypeExpr {
            kind: TypeKind::ComputedProjection { base, key },
            ..
        }) = target.syntax.as_deref()
        {
            return self.static_projection_reception(base, key, actual, &original, frame);
        }
        let expected_syntax = target.syntax.as_deref()?;
        let (expected, expected_const) = self.static_coordinate_key(expected_syntax)?;
        if let Some(candidates) = self.constructor_callable_source_syntaxes(&original) {
            let fresh = source_reception::construction(actual, &mut 4096)?;
            let mut unknown = false;
            for syntax in candidates {
                let (key, _) = self.static_coordinate_key(&syntax)?;
                match source_reception::compatible(&expected, &key, Some(&fresh), &mut 4096) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => unknown = true,
                }
            }
            return (!unknown).then_some(false);
        }
        if !expected_const {
            return None;
        }
        let actual_syntax = original
            .source_type_witness
            .as_ref()
            .map(|witness| witness.syntax.clone())
            .or_else(|| self.nominal_owner_source_syntax(&original.ty))?;
        let (key, _) = self.static_coordinate_key(&actual_syntax)?;
        source_reception::compatible(
            &expected,
            &key,
            Some(&source_reception::construction(actual, &mut 4096)?),
            &mut 4096,
        )
    }

    fn static_source_observation(
        &self,
        syntax: &Expr,
        value: &Value,
        observed: Option<usize>,
        frame: &Frame,
    ) -> Option<Value> {
        let index = observed?;
        let row = self.invocation_expressions.get(index)?;
        let fact = self.expression_facts.get(index)?;
        if row.expression != index
            || row.context != self.invocation_context(frame.callable_owner)
            || fact.span != syntax.span
            || fact.value.ty != value.ty
            || fact.value.cause != value.cause
        {
            return None;
        }
        Some(fact.value.clone())
    }

    fn static_projection_reception(
        &mut self,
        expected_base: &TypeExpr,
        expected_key: &Expr,
        actual: &Expr,
        value: &Value,
        frame: &Frame,
    ) -> Option<bool> {
        let ExprKind::Name(name) = &expected_key.kind else {
            return None;
        };
        let identity = self.genuine_source_key(name)?;
        let ExprKind::ComputedField { base, key } = &actual.kind else {
            return None;
        };
        let ExprKind::Name(key_name) = &key.kind else {
            return None;
        };
        let parents = self
            .explanations
            .causes
            .get(value.cause.0 as usize)?
            .parents
            .clone();
        if self.explanations.kinds.get(value.cause.0 as usize) != Some(&CauseKind::Projection) {
            return None;
        }
        let context = self.invocation_context(frame.callable_owner);
        let keys: Vec<_> = self
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                if row.context != context {
                    return None;
                }
                let fact = self.expression_facts.get(row.expression)?;
                (fact.span == key.span
                    && parents.contains(&fact.value.cause)
                    && fact.value.ty == Ty::StaticKey(identity.clone()))
                .then_some(&fact.value)
            })
            .collect();
        let [key_value] = keys.as_slice() else {
            return None;
        };
        if let Some(binding_id) = frame.env.get(key_name) {
            let binding = self.bindings.get(*binding_id)?;
            if !binding.parameter
                || binding.owner != frame.owner
                || binding.name != *key_name
                || key_value.sources != BTreeSet::from([*binding_id])
            {
                return None;
            }
            let function = self.functions.iter().find(|function| {
                frame.callable_owner == Some(CallableOwner::Function(function.definition))
            })?;
            let parameter = function.syntax.parameters.iter().find(|parameter|
                parameter.pattern.span == binding.span
                    && matches!(&parameter.pattern.kind, PatternKind::Name(name) if name == key_name))?;
            let TypeKind::Name { path, arguments } = &parameter.ty.as_ref()?.kind else {
                return None;
            };
            if !arguments.is_empty() || self.genuine_source_key(&path.join("::"))? != identity {
                return None;
            }
        } else if self.genuine_source_key(key_name)? != identity || !key_value.sources.is_empty() {
            return None;
        }
        let bases: Vec<_> = self
            .invocation_expressions
            .iter()
            .filter_map(|row| {
                if row.context != context {
                    return None;
                }
                let fact = self.expression_facts.get(row.expression)?;
                (fact.span == base.span && parents.contains(&fact.value.cause))
                    .then_some(fact.value.clone())
            })
            .collect();
        let [base_value] = bases.as_slice() else {
            return None;
        };
        let expected = crate::static_eval::effects::bounded_argument_key(
            expected_base,
            &self.effect_type_binders,
        )?;
        let original = self.original_source_receiving_key(base_value, base, frame)?;
        if expected != original {
            return Some(false);
        }
        let Ty::Projection {
            base: projected,
            key,
        } = &value.ty
        else {
            return None;
        };
        if key != &identity || projected.as_ref() != &base_value.ty {
            return Some(false);
        }
        let bound = self.static_key_bound_type(&identity)?;
        Some(
            self.expanded(&bound, &mut BTreeSet::new())
                == self.expanded(&base_value.ty, &mut BTreeSet::new()),
        )
    }

    pub(super) fn nominal_owner_source_syntax(&self, owner: &Ty) -> Option<TypeExpr> {
        let mut sources = self.constructors.iter().filter_map(|(name, constructor)| {
            (constructor.owner == *owner)
                .then(|| self.constructor_source_syntax.get(name))
                .flatten()
        });
        let first = sources.next()?;
        self.bounded_static_source_input(first)?;
        let key = crate::static_eval::normalized_argument_key(first);
        let mut work = 4096usize;
        for source in sources {
            work = work.checked_sub(1)?;
            self.bounded_static_source_input(source)?;
            if crate::static_eval::normalized_argument_key(source) != key {
                return None;
            }
        }
        Some((**first).clone())
    }

    /// The tuple boundary has exactly its written tuple and its specified
    /// spread callable view. Expected annotations cannot invent a third view.
    pub(super) fn constructor_callable_source_syntaxes(
        &self,
        value: &Value,
    ) -> Option<Vec<TypeExpr>> {
        let [Callable::Constructor(name)] = value.callables.as_slice() else {
            return None;
        };
        let constructor = self.constructors.get(name)?;
        if !constructor.has_payload {
            return None;
        }
        let payload = constructor.payload_syntax.as_ref()?;
        let result = self.constructor_source_syntax.get(name)?.as_ref();
        self.bounded_static_source_input(payload)?;
        self.bounded_static_source_input(result)?;
        let mut views = vec![vec![payload.clone()]];
        if let TypeKind::Tuple(items) = &payload.kind {
            views.push(items.clone());
        }
        Some(
            views
                .into_iter()
                .map(|items| TypeExpr {
                    text: String::new(),
                    span: constructor.span,
                    kind: TypeKind::Callable {
                        parameters: items
                            .into_iter()
                            .enumerate()
                            .map(|(index, ty)| Parameter {
                                mode: ParameterMode::Read,
                                pattern: Pattern {
                                    kind: PatternKind::Name(format!("_{index}")),
                                    span: ty.span,
                                },
                                span: ty.span,
                                ty: Some(ty),
                                default: None,
                            })
                            .collect(),
                        result: Some(Box::new(result.clone())),
                        annotations: vec![],
                    },
                })
                .collect(),
        )
    }

    /// Compare only Array/Fn coordinates. Const slots can be omitted here
    /// only after the real nominal declaration's existing evaluator accepted
    /// every actual argument against its exact finite value sort.
    fn static_coordinate_key(&self, syntax: &TypeExpr) -> Option<(ArgumentKey, bool)> {
        self.bounded_static_source_input(syntax)?;
        fn visit(
            checker: &Checker,
            syntax: &TypeExpr,
            work: &mut usize,
            depth: usize,
            changed: &mut bool,
        ) -> Option<TypeExpr> {
            *work = work.checked_sub(1)?;
            if depth >= 64 {
                return None;
            }
            let mut output = syntax.clone();
            match &mut output.kind {
                TypeKind::Name { arguments, .. }
                    if checker.certified_nominal_const_arguments(syntax) =>
                {
                    arguments.clear();
                    *changed = true;
                }
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    for argument in arguments {
                        *argument = visit(checker, argument, work, depth + 1, changed)?;
                    }
                }
                TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
                    **inner = visit(checker, inner, work, depth + 1, changed)?;
                }
                TypeKind::Map { key, value } => {
                    **key = visit(checker, key, work, depth + 1, changed)?;
                    **value = visit(checker, value, work, depth + 1, changed)?;
                }
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        field.ty = visit(checker, &field.ty, work, depth + 1, changed)?;
                    }
                    if let Some(row) = row {
                        **row = visit(checker, row, work, depth + 1, changed)?;
                    }
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        if let Some(ty) = &mut parameter.ty {
                            *ty = visit(checker, ty, work, depth + 1, changed)?;
                        }
                    }
                    if let Some(result) = result {
                        **result = visit(checker, result, work, depth + 1, changed)?;
                    }
                }
                _ => {}
            }
            Some(output)
        }
        let mut changed = false;
        let syntax = visit(self, syntax, &mut 4096, 0, &mut changed)?;
        super::source_receiving::resolved_symbolic_names(
            &syntax,
            &self.effect_type_binders,
            &self.types,
            &mut 4096,
            0,
        )?;
        let key =
            crate::static_eval::effects::bounded_argument_key(&syntax, &self.effect_type_binders)?;
        source_reception::complete(&key, &mut 4096)?;
        Some((key, changed))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unregistered_static_key_cannot_freeze_a_projection_source() {
        let parsed =
            ril_syntax::parse("fn project<T,K:keyof T>(value:T,key:K)->T.(K){value.(key)}");
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let StmtKind::Function(function) = &parsed.program.statements[0].kind else {
            panic!("function")
        };
        let mut checker = Checker::new(FileId(0));
        checker
            .generic_context
            .insert("K".into(), "unowned:K".into());
        checker.generic_key_bounds.insert(
            "unowned:K".into(),
            function.parameters[0].ty.clone().unwrap(),
        );
        checker
            .generic_key_contexts
            .insert("unowned:K".into(), checker.generic_context.clone());
        assert!(
            checker
                .freeze_static_source_type(function.return_type.as_ref().unwrap())
                .is_none()
        );
    }

    #[test]
    fn static_key_source_checks_do_not_recover_mutable_authority() {
        let source = "type Cell={mut value:int}\nfn get<T:{..R},K:keyof T>(record:T,key:K)->T.(K){record.(key)}\nfn example(mut cell:Cell)&mut{let record=.{cell:cell};let mut alias=^mut get(record,\"cell\");alias.value+=1}";
        let outcome = crate::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,crate::CompilationOutcome::Rejected{diagnostics}
            if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0520")),
            "{outcome:?}"
        );
    }

    #[test]
    fn nominal_const_coordinates_do_not_replace_the_exact_instance_check() {
        let source = "type Point<value:{x:int,y:int}>(int)\nfn example(){let value:Point<.{x:1,y:2}>=Point<.{x:1,y:3}>(7)}";
        let outcome = crate::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,crate::CompilationOutcome::Rejected{diagnostics}
            if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{outcome:?}"
        );
    }
}
