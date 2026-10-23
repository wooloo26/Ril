//! Scalar Meta function constants have value identities, never Type identities.
//! Their universal value remains unknown even when an actual call selects a
//! literal. Dependent type syntax is deliberately outside this scalar stage.
use super::*;
use bounds::{BoundEnvironment, StaticBinderId, StaticParameterSort};

fn normalized_path(path: &[String]) -> String {
    path.strip_prefix(&["Prelude".into()])
        .unwrap_or(path)
        .join("::")
}

pub(in crate::static_eval) fn check_signature(
    evaluator: &Evaluator,
    function: &Function,
    lexical: &generic_calls::TypeEnvironment,
) -> Result<()> {
    let checker = Typer::new(evaluator, None);
    let mut scope = BoundEnvironment {
        const_binders: lexical.visible_consts().clone(),
        ..Default::default()
    };
    for (index, parameter) in function.generics.iter().enumerate() {
        if parameter_sort(parameter)? == StaticParameterSort::ConstInt {
            scope.const_binders.insert(
                parameter.name.clone(),
                Some(StaticBinderId {
                    declaration: function.name.clone(),
                    index: index as u32,
                    sort: StaticParameterSort::ConstInt,
                }),
            );
        } else {
            scope.const_binders.insert(parameter.name.clone(), None);
        }
    }
    for syntax in function
        .parameters
        .iter()
        .filter_map(|parameter| parameter.ty.as_ref())
        .chain(function.return_type.iter())
    {
        checker.reject_const_dependent_type(syntax, &scope)?;
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::static_eval) enum ConstIntSelection {
    Rigid(StaticBinderId),
    Closed(i128),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::static_eval) struct ConstBindingView {
    pub name: String,
    pub id: StaticBinderId,
    pub closed: Option<i128>,
}

pub(in crate::static_eval::typing) struct ConstArgumentSource {
    pub syntax: TypeExpr,
    pub rigid: bool,
}

pub(in crate::static_eval) fn parameter_sort(
    parameter: &GenericParameter,
) -> Result<StaticParameterSort> {
    if parameter
        .name
        .chars()
        .next()
        .is_some_and(char::is_uppercase)
    {
        if parameter.bound.as_ref().is_none_or(|bound| {
            matches!(bound.kind, TypeKind::Record { .. })
                || matches!(&bound.kind, TypeKind::Name { path, arguments }
                    if path == &["Type"] && arguments.is_empty())
        }) {
            return Ok(StaticParameterSort::Type);
        }
    } else if parameter.bound.as_ref().is_some_and(|bound| {
        matches!(&bound.kind, TypeKind::Name { path, arguments }
            if normalized_path(path) == "int" && arguments.is_empty())
    }) {
        return Ok(StaticParameterSort::ConstInt);
    }
    Err(Failure::Unsupported(
        "static Meta function generic sort requires Type, structural Type, or scalar int witness"
            .into(),
    ))
}

fn integer_in_layout(value: i128, layout: TargetLayout) -> Result<i128> {
    let bits = layout.pointer_bytes() * 8;
    let (min, max) = if bits == 32 {
        (i32::MIN as i128, i32::MAX as i128)
    } else {
        (i64::MIN as i128, i64::MAX as i128)
    };
    if value < min || value > max {
        return Err(Failure::Diagnostic(
            "E0323",
            "static int argument exceeds its target layout".into(),
        ));
    }
    Ok(value)
}

pub(in crate::static_eval) fn argument_syntax(value: i128, span: Span) -> TypeExpr {
    let literal = Expr {
        hir_id: None,
        kind: ExprKind::Literal(Literal::Integer(value.unsigned_abs().to_string())),
        span,
    };
    let expression = if value < 0 {
        Expr {
            hir_id: None,
            kind: ExprKind::Unary {
                operator: "-".into(),
                operand: Box::new(literal),
            },
            span,
        }
    } else {
        literal
    };
    TypeExpr {
        hir_id: None,
        text: value.to_string(),
        kind: TypeKind::Computation(Box::new(expression)),
        span,
    }
}

impl Typer<'_> {
    /// Freeze a supplied value argument at callable creation. A later ordinary
    /// same-spelled binding cannot change the selected closed value or binder.
    pub(in crate::static_eval::typing) fn const_argument_source(
        &self,
        syntax: &TypeExpr,
        lexical: &BoundEnvironment,
    ) -> Result<ConstArgumentSource> {
        match self.const_argument(syntax, lexical)? {
            ConstIntSelection::Closed(value) => Ok(ConstArgumentSource {
                syntax: argument_syntax(value, syntax.span),
                rigid: false,
            }),
            ConstIntSelection::Rigid(id) => {
                let name = id.key();
                Ok(ConstArgumentSource {
                    syntax: TypeExpr {
                        hir_id: None,
                        text: name.clone(),
                        kind: TypeKind::Name {
                            path: vec![name],
                            arguments: vec![],
                        },
                        span: syntax.span,
                    },
                    rigid: true,
                })
            }
        }
    }
    pub(super) fn with_const_shadow_scope<T>(
        &self,
        action: impl FnOnce() -> Result<T>,
    ) -> Result<T> {
        let saved = self.const_shadows.borrow().clone();
        let saved_schemas = self.schema_bindings.borrow().clone();
        let result = action();
        *self.const_shadows.borrow_mut() = saved;
        *self.schema_bindings.borrow_mut() = saved_schemas;
        result
    }
    pub(in crate::static_eval::typing) fn has_visible_const(
        &self,
        scope: &BoundEnvironment,
        names: &BTreeSet<String>,
    ) -> bool {
        names
            .iter()
            .any(|name| scope.const_binders.get(name).is_some_and(Option::is_some))
    }

    pub(in crate::static_eval::typing) fn mask_const_values(
        &self,
        scope: &mut BoundEnvironment,
        names: &BTreeSet<String>,
    ) -> Result<()> {
        for name in names {
            if scope.const_binders.get(name).is_some_and(Option::is_some) {
                self.schema_work.work(1 + name.len() as u64)?;
                scope.const_binders.insert(name.clone(), None);
            }
        }
        Ok(())
    }

    pub(super) fn apply_const_shadows(&self, scope: &mut BoundEnvironment) -> Result<()> {
        self.mask_const_values(scope, &self.const_shadows.borrow())
    }

    pub(in crate::static_eval::typing) fn const_binding_views(
        &self,
        scope: &BoundEnvironment,
    ) -> Result<Vec<ConstBindingView>> {
        scope
            .const_binders
            .iter()
            .filter_map(|(name, id)| id.as_ref().map(|id| (name, id)))
            .map(|(name, id)| {
                self.schema_work
                    .work(1 + name.len() as u64 + id.declaration.len() as u64)?;
                let selected = self.const_selection(id, scope)?;
                Ok(ConstBindingView {
                    name: name.clone(),
                    id: id.clone(),
                    closed: match selected {
                        ConstIntSelection::Closed(value) => Some(value),
                        ConstIntSelection::Rigid(_) => None,
                    },
                })
            })
            .collect()
    }

    fn const_selection(
        &self,
        id: &StaticBinderId,
        scope: &BoundEnvironment,
    ) -> Result<ConstIntSelection> {
        let mut current = id;
        let mut visited = BTreeSet::new();
        loop {
            self.schema_work.work(1)?;
            if !visited.insert(current.clone()) {
                return Err(Failure::Unsupported(
                    "static const selection has an unresolved recursive identity".into(),
                ));
            }
            match scope.const_arguments.get(current) {
                Some(ConstIntSelection::Closed(value)) => {
                    return Ok(ConstIntSelection::Closed(*value));
                }
                Some(ConstIntSelection::Rigid(next)) if next != current => current = next,
                _ => return Ok(ConstIntSelection::Rigid(current.clone())),
            }
        }
    }

    /// Run before any source normalization can substitute an actual constant.
    pub(super) fn reject_const_dependent_type(
        &self,
        syntax: &TypeExpr,
        scope: &BoundEnvironment,
    ) -> Result<()> {
        let mut names = BTreeSet::new();
        clone_work::type_syntax(&self.schema_work, syntax)?;
        transform::type_names(syntax, &mut names);
        if names.iter().any(|name| {
            scope.const_binders.get(name).is_some_and(Option::is_some)
                || scope.const_ids.contains_key(name)
        }) {
            return Err(Failure::Unsupported(
                "scalar static int generics do not yet prove dependent type syntax or symbolic array extents".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn select_const_argument(
        &self,
        name: &str,
        syntax: &TypeExpr,
        caller: &BoundEnvironment,
        scope: &mut BoundEnvironment,
    ) -> Result<()> {
        let id = scope
            .const_binders
            .get(name)
            .and_then(Option::as_ref)
            .cloned()
            .ok_or_else(|| {
                Failure::Unsupported("static const argument has no real binder".into())
            })?;
        let selected = self.const_argument(syntax, caller)?;
        if matches!(&selected, ConstIntSelection::Rigid(source) if source.declaration == id.declaration)
        {
            return Err(Failure::Unsupported("same-declaration recursive const forwarding needs activation-indexed value identities".into()));
        }
        if scope
            .const_arguments
            .get(&id)
            .is_some_and(|old| old != &selected)
        {
            return Err(Failure::Diagnostic(
                "E0323",
                "one static int binder has inconsistent selections".into(),
            ));
        }
        scope.const_arguments.insert(id, selected);
        Ok(())
    }

    fn const_argument(
        &self,
        syntax: &TypeExpr,
        caller: &BoundEnvironment,
    ) -> Result<ConstIntSelection> {
        clone_work::type_syntax(&self.schema_work, syntax)?;
        let expression = match &syntax.kind {
            TypeKind::Computation(expression) => (**expression).clone(),
            TypeKind::Name { path, arguments } if arguments.is_empty() => Expr {
                hir_id: None,
                kind: ExprKind::Name(path.join("::")),
                span: syntax.span,
            },
            _ => {
                return Err(Failure::Diagnostic(
                    "E0323",
                    "static argument requires an int value sort".into(),
                ));
            }
        };
        if let Some(name) = expression_name(&expression) {
            if let Some(id) = caller
                .const_binders
                .get(&name)
                .and_then(Option::as_ref)
                .or_else(|| caller.const_ids.get(&name))
            {
                return self.const_selection(id, caller);
            }
            if let Some(ty) = caller.values.get(&name) {
                return match ty {
                    Ty::IntegerConstant(value) => Ok(ConstIntSelection::Closed(integer_in_layout(
                        *value,
                        self.evaluator.layout,
                    )?)),
                    Ty::Number(number) if number == "int" => Err(Failure::Unsupported(
                        "static int argument needs a genuine constant value witness".into(),
                    )),
                    _ => Err(Failure::Diagnostic(
                        "E0323",
                        "static argument does not have int value sort".into(),
                    )),
                };
            }
        }
        let mut values = caller.values.clone();
        match self.expr(&expression, &mut values)? {
            Ty::IntegerConstant(value) => Ok(ConstIntSelection::Closed(integer_in_layout(
                value,
                self.evaluator.layout,
            )?)),
            Ty::Number(number) if number == "int" => Err(Failure::Unsupported(
                "static int computation needs a complete constant witness".into(),
            )),
            _ => Err(Failure::Diagnostic(
                "E0323",
                "static argument does not have int value sort".into(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn evaluator(source: &str) -> Evaluator {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let collected = definitions::collect(&parsed.program);
        Evaluator {
            type_environment: Default::default(),
            type_application_sequence: 0,
            layout: TargetLayout::POINTER64,
            values: BTreeMap::new(),
            global_values: BTreeMap::new(),
            budget: Default::default(),
            declarations: collected.all_types,
            effect_declarations: collected.all_effects,
            functions: collected.all_functions,
            function_environments: BTreeMap::new(),
            environments: vec![],
            alias_instances: BTreeMap::new(),
            static_signatures: BTreeMap::new(),
            active_functions: vec![],
            type_depth: 0,
            call_depth: 0,
            tail_returns: false,
            tail_types: false,
            numeric_return: None,
            results: Default::default(),
            result_site: None,
            expression_depth: 0,
            loop_frames: vec![],
            next_loop_target: 0,
            type_calls: BTreeSet::new(),
            next_collection: 0,
            publications: Default::default(),
            constants: Default::default(),
        }
    }
    fn unexpected<T>(failure: Failure) -> T {
        match failure {
            Failure::Diagnostic(code, message) => panic!("{code}: {message}"),
            Failure::Unsupported(message) => panic!("unsupported: {message}"),
            _ => panic!("unexpected static transfer"),
        }
    }
    fn apply(
        checker: &Typer<'_>,
        name: &str,
        argument: TypeExpr,
        caller: &BoundEnvironment,
    ) -> Result<BoundEnvironment> {
        let plan = application::StaticApplicationPlan::new(&[], std::iter::empty())?;
        checker.check_function_application(
            &checker.evaluator.functions[name],
            applications::TypeApplication {
                actual_types: &[],
                actual_schemas: &[],
                plan: &plan,
                captured: &BoundEnvironment::default(),
                caller,
                explicit: &[argument],
                expected: None,
                instance: 79,
            },
        )
    }
    fn name_argument(name: &str, span: Span) -> TypeExpr {
        TypeExpr {
            hir_id: None,
            text: name.into(),
            kind: TypeKind::Name {
                path: vec![name.into()],
                arguments: vec![],
            },
            span,
        }
    }

    #[test]
    fn scalar_and_type_identity_namespaces_are_distinct_without_changing_old_type_keys() {
        let mut id = StaticBinderId {
            declaration: "item".into(),
            index: 0,
            sort: StaticParameterSort::Type,
        };
        assert_eq!(id.key(), "static:4:item:generic:0");
        let type_id = id.clone();
        id.sort = StaticParameterSort::ConstInt;
        assert_ne!(id, type_id);
        assert_ne!(id.key(), type_id.key());
    }

    #[test]
    fn actual_closed_const_never_changes_the_universal_parameter_value() {
        let evaluator = evaluator("meta fn size<n:int>()->int{n}");
        let checker = Typer::new(&evaluator, None);
        let function = &evaluator.functions["size"];
        let universal = checker
            .function_generic_environment(function, &BoundEnvironment::default())
            .unwrap_or_else(unexpected);
        assert_eq!(universal.values["n"], Ty::Number("int".into()));
        assert_eq!(
            checker
                .const_binding_views(&universal)
                .unwrap_or_else(unexpected)[0]
                .closed,
            None
        );
        let selected = apply(
            &checker,
            "size",
            argument_syntax(-3, function.span),
            &BoundEnvironment::default(),
        )
        .unwrap_or_else(unexpected);
        let view = &checker
            .const_binding_views(&selected)
            .unwrap_or_else(unexpected)[0];
        assert_eq!(view.closed, Some(-3));
        assert_eq!(view.id.sort, StaticParameterSort::ConstInt);
        assert_eq!(selected.values["n"], Ty::Number("int".into()));
        assert_eq!(
            checker
                .const_binding_views(&universal)
                .unwrap_or_else(unexpected)[0]
                .closed,
            None
        );
    }

    #[test]
    fn rigid_forwarding_uses_caller_identity_not_callee_spelling() {
        let evaluator =
            evaluator("meta fn size<n:int>()->int{n}\nmeta fn caller<n:int>()->int{size<n>()}");
        let checker = Typer::new(&evaluator, None);
        let caller = checker
            .function_generic_environment(
                &evaluator.functions["caller"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(unexpected);
        let selected = apply(
            &checker,
            "size",
            name_argument("n", evaluator.functions["size"].span),
            &caller,
        )
        .unwrap_or_else(unexpected);
        let id = selected.const_binders["n"].as_ref().unwrap();
        assert_eq!(
            selected.const_arguments[id],
            ConstIntSelection::Rigid(caller.const_binders["n"].clone().unwrap())
        );
        assert_eq!(
            checker
                .const_binding_views(&selected)
                .unwrap_or_else(unexpected)[0]
                .closed,
            None
        );
    }

    #[test]
    fn local_value_mask_retains_history_and_selects_the_new_literal_value() {
        let evaluator = evaluator("meta fn size<n:int>()->int{n}\nmeta fn caller<n:int>()->int{n}");
        let checker = Typer::new(&evaluator, None);
        let mut caller = checker
            .function_generic_environment(
                &evaluator.functions["caller"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(unexpected);
        let id = caller.const_binders["n"].clone().unwrap();
        caller
            .const_arguments
            .insert(id.clone(), ConstIntSelection::Closed(7));
        let old = caller.clone();
        checker
            .mask_const_values(&mut caller, &BTreeSet::from(["unrelated".into()]))
            .unwrap_or_else(unexpected);
        assert!(caller == old);
        checker
            .mask_const_values(&mut caller, &BTreeSet::from(["n".into()]))
            .unwrap_or_else(unexpected);
        assert!(caller.const_ids.contains_key(&id.key()));
        assert_eq!(caller.const_arguments[&id], ConstIntSelection::Closed(7));
        assert!(
            checker
                .const_binding_views(&caller)
                .unwrap_or_else(unexpected)
                .is_empty()
        );
        caller.values.insert("n".into(), Ty::IntegerConstant(5));
        let selected = apply(
            &checker,
            "size",
            name_argument("n", evaluator.functions["size"].span),
            &caller,
        )
        .unwrap_or_else(unexpected);
        assert_eq!(
            checker
                .const_binding_views(&selected)
                .unwrap_or_else(unexpected)[0]
                .closed,
            Some(5)
        );
    }

    #[test]
    fn closed_actual_const_does_not_normalize_unsupported_dependent_type_syntax() {
        let evaluator = evaluator("meta fn sized<n:int>()->[n]int{[1,2]}");
        let checker = Typer::new(&evaluator, None);
        let function = &evaluator.functions["sized"];
        let mut scope = checker
            .function_generic_environment(function, &BoundEnvironment::default())
            .unwrap_or_else(unexpected);
        let id = scope.const_binders["n"].clone().unwrap();
        scope
            .const_arguments
            .insert(id, ConstIntSelection::Closed(2));
        assert!(matches!(
            checker.complete_source_syntax(function.return_type.as_ref().unwrap(), &scope),
            Err(Failure::Unsupported(_))
        ));
        assert!(matches!(
            checker.result_context(function.return_type.as_ref().unwrap(), &scope),
            Err(Failure::Unsupported(_))
        ));
    }

    #[test]
    fn unresolved_same_declaration_const_forwarding_remains_unproved() {
        let evaluator = evaluator("meta fn size<n:int>()->int{n}");
        let checker = Typer::new(&evaluator, None);
        let function = &evaluator.functions["size"];
        let caller = checker
            .function_generic_environment(function, &BoundEnvironment::default())
            .unwrap_or_else(unexpected);
        assert!(matches!(
            apply(&checker, "size", name_argument("n", function.span), &caller),
            Err(Failure::Unsupported(_))
        ));
    }

    #[test]
    fn frozen_closed_const_callable_argument_does_not_reread_a_later_local_shadow() {
        let evaluator = evaluator("meta fn size<n:int>()->int{n}");
        let checker = Typer::new(&evaluator, None);
        let function = &evaluator.functions["size"];
        let raw = name_argument("n", function.span);
        let mut caller =
            BoundEnvironment::captured(BTreeMap::from([("n".into(), Ty::IntegerConstant(7))]));
        let frozen = checker
            .const_argument_source(&raw, &caller)
            .unwrap_or_else(unexpected);
        assert!(!frozen.rigid);
        caller.values.insert("n".into(), Ty::IntegerConstant(11));
        let selected = apply(&checker, "size", frozen.syntax, &caller).unwrap_or_else(unexpected);
        assert_eq!(
            checker
                .const_binding_views(&selected)
                .unwrap_or_else(unexpected)[0]
                .closed,
            Some(7)
        );
        let reread = apply(&checker, "size", raw, &caller).unwrap_or_else(unexpected);
        assert_eq!(
            checker
                .const_binding_views(&reread)
                .unwrap_or_else(unexpected)[0]
                .closed,
            Some(11)
        );
    }

    #[test]
    fn frozen_rigid_const_callable_argument_keeps_its_historical_identity() {
        let evaluator = evaluator("meta fn size<n:int>()->int{n}\nmeta fn caller<n:int>()->int{n}");
        let checker = Typer::new(&evaluator, None);
        let function = &evaluator.functions["size"];
        let mut caller = checker
            .function_generic_environment(
                &evaluator.functions["caller"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(unexpected);
        let id = caller.const_binders["n"].clone().unwrap();
        let frozen = checker
            .const_argument_source(&name_argument("n", function.span), &caller)
            .unwrap_or_else(unexpected);
        assert!(frozen.rigid);
        assert!(
            matches!(&frozen.syntax.kind, TypeKind::Name{path,arguments} if path==&[id.key()] && arguments.is_empty())
        );
        checker
            .mask_const_values(&mut caller, &BTreeSet::from(["n".into()]))
            .unwrap_or_else(unexpected);
        caller.values.insert("n".into(), Ty::IntegerConstant(11));
        let selected = apply(&checker, "size", frozen.syntax, &caller).unwrap_or_else(unexpected);
        let callee = selected.const_binders["n"].as_ref().unwrap();
        assert_eq!(
            selected.const_arguments[callee],
            ConstIntSelection::Rigid(id)
        );
        assert_eq!(
            checker
                .const_binding_views(&selected)
                .unwrap_or_else(unexpected)[0]
                .closed,
            None
        );
    }
}
