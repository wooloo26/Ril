//! Optional fallback is lazy. Universal typing uses the payload type; evaluated
//! receiving uses complete source schemas, never erased array/callable types.
use super::*;
#[path = "coalescing_control.rs"]
mod control;

pub(super) struct CoalescingOperands<'a> {
    pub left: &'a Expr,
    pub right: &'a Expr,
}

impl Typer<'_> {
    pub(super) fn coalescing_type(
        &self,
        left: &Expr,
        right: &Expr,
        env: &mut Env,
        expected: Option<&Ty>,
        result_context: Option<&applications::ResultContext>,
    ) -> Result<Ty> {
        let context = expected.map(|ty| Ty::Optional(Box::new(ty.clone())));
        let left_context = result_context
            .map(|context| self.optional_result_context(context))
            .transpose()?;
        let left_type =
            self.expr_result_expected(left, env, context.as_ref(), left_context.as_ref())?;
        control::validate(right, &self.schema_work)?;
        if left_type == Ty::Never {
            self.with_reachability(false, || {
                self.expr_result_expected(right, env, expected, result_context)
            })?;
            return Ok(Ty::Never);
        }
        if let Ty::Result(ok, error) = &left_type {
            return self.result_fallback_type(ok, error, right, env);
        }
        let Ty::Optional(payload) = &left_type else {
            return Err(Failure::Diagnostic(
                "E0714",
                "optional fallback requires an Optional left operand".into(),
            ));
        };
        let mut scope = self
            .bound_environment
            .as_deref()
            .cloned()
            .unwrap_or_default();
        scope.values = env.clone();
        self.apply_const_shadows(&mut scope)?;
        let left_source = self.expression_source_schema_expected(
            left,
            &left_type,
            env,
            &scope,
            left_context.as_ref(),
            0,
        )?;
        let left_context = left_source
            .as_ref()
            .map(|source| self.result_context(&source.syntax, &scope))
            .transpose()?;
        let payload_context = self.child_result_context(
            left_context.as_ref(),
            applications::ResultProjection::OptionalPayload,
        )?;
        let source_context = payload_context.as_ref().or(result_context);
        let context = if **payload == Ty::Infer {
            expected
        } else {
            Some(payload.as_ref())
        };
        let fallback = self.expr_result_expected(right, env, context, source_context)?;
        require(&fallback, payload)?;
        if applications::contains_erased_source_information(payload) {
            let scope = self
                .bound_environment
                .as_deref()
                .cloned()
                .unwrap_or_default();
            if self
                .coalescing_source_schema_expected(
                    CoalescingOperands { left, right },
                    payload,
                    env,
                    &scope,
                    result_context,
                    0,
                )?
                .is_none()
            {
                return Err(Failure::Unsupported(
                    "optional fallback needs complete payload source schemas".into(),
                ));
            }
        }
        // A diverging fallback leaves the possible Some path intact.
        join_types(payload, &fallback)
    }

    fn result_fallback_type(&self, ok: &Ty, error: &Ty, right: &Expr, env: &mut Env) -> Result<Ty> {
        let fallback = self.expr(right, env)?;
        let Ty::Callable(parameters, result, _) = fallback else {
            return Err(Failure::Diagnostic(
                "E0711",
                "Result fallback requires an error-consuming callable".into(),
            ));
        };
        if parameters.len() != 1 {
            return Err(Failure::Diagnostic(
                "E0301",
                "Result fallback requires one error parameter".into(),
            ));
        }
        require(error, &parameters[0])?;
        require(&result, ok)?;
        Err(Failure::Unsupported(
            "static Result fallback needs a complete error-consumption proof".into(),
        ))
    }

    pub(super) fn coalescing_source_schema_expected(
        &self,
        operands: CoalescingOperands<'_>,
        actual: &Ty,
        env: &Env,
        scope: &bounds::BoundEnvironment,
        result_context: Option<&applications::ResultContext>,
        depth: usize,
    ) -> Result<Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>> {
        let CoalescingOperands { left, right } = operands;
        let left_context = result_context
            .map(|context| self.optional_result_context(context))
            .transpose()?;
        let left_type = self.expr_result_expected(
            left,
            &mut env.clone(),
            left_context.as_ref().map(|context| context.ordinary()),
            left_context.as_ref(),
        )?;
        let Some(source) = self.expression_source_schema_expected(
            left,
            &left_type,
            env,
            scope,
            left_context.as_ref(),
            depth + 1,
        )?
        else {
            return Ok(None);
        };
        let TypeKind::Optional(payload) = &source.syntax.kind else {
            return Ok(None);
        };
        let Some(required) = self.complete_source_syntax(payload, scope)? else {
            return Ok(None);
        };
        let context = self.result_context(&required.syntax, scope)?;
        let right_type =
            self.expr_result_expected(right, &mut env.clone(), Some(actual), Some(&context))?;
        if right_type == Ty::Never {
            return Ok(Some(required));
        }
        let required_type = self.bound_type(&required.syntax, scope)?;
        require(&right_type, &required_type)?;
        let mut received = self.expression_source_schema_expected(
            right,
            &right_type,
            env,
            scope,
            Some(&context),
            depth + 1,
        )?;
        if let ExprKind::Array(items) = &right.kind
            && let TypeKind::Array {
                length: Some(length),
                ..
            } = &payload.kind
        {
            // A fresh constructor receives a declared fixed schema. Existing
            // arrays never recover a fixed length from their backing count.
            if items.is_empty() {
                return Ok(Some(required));
            }
            if let Some(source) = &received
                && let TypeKind::Array { element, .. } = &source.syntax.kind
            {
                received = self.complete_source_syntax(
                    &TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        span: right.span,
                        kind: TypeKind::Array {
                            length: Some(length.clone()),
                            element: element.clone(),
                        },
                    },
                    scope,
                )?;
            }
        }
        let Some(received) = received else {
            return Ok(None);
        };
        if !applications::schema_receives(&received.syntax, &required.syntax, false, 0) {
            return Err(Failure::Diagnostic(
                "E0301",
                "optional fallback payload source schemas disagree".into(),
            ));
        }
        Ok(Some(required))
    }
}

impl Evaluator {
    pub(in crate::static_eval) fn evaluate_coalescing(
        &mut self,
        left: &Expr,
        right: &Expr,
        tail: bool,
        expected: Option<&TypeExpr>,
    ) -> Result<StaticValue> {
        let context = expected.map(|ty| TypeExpr {
            hir_id: None,
            text: String::new(),
            span: left.span,
            kind: TypeKind::Optional(Box::new(ty.clone())),
        });
        let value = self.expression_expected(left, false, context.as_ref())?;
        control::validate(right, &self.budget)?;
        match &value {
            StaticValue::Variant(name, payload, _)
                if name == "Prelude::Some" && payload.len() == 1 =>
            {
                // This immutable handle copy preserves nested Result identity.
                self.copy_static_value(&payload[0])
            }
            StaticValue::Variant(name, payload, _)
                if name == "Prelude::None" && payload.is_empty() =>
            {
                let context = self.coalescing_payload_schema(left, &value, expected)?;
                self.expression_expected(right, tail, context.as_ref())
            }
            StaticValue::Result(_) => {
                let checker = Typer::new(self, None);
                let mut env = self
                    .values
                    .iter()
                    .map(|(name, value)| {
                        (
                            name.clone(),
                            checker.value_type(value).unwrap_or(Ty::Unknown),
                        )
                    })
                    .collect();
                let Ty::Result(ok, error) = checker.value_type(&value)? else {
                    return Err(Failure::Unsupported(
                        "static Result fallback has no complete result descriptor".into(),
                    ));
                };
                checker
                    .result_fallback_type(&ok, &error, right, &mut env)
                    .and_then(|_| {
                        Err(Failure::Unsupported(
                            "static Result fallback is unresolved".into(),
                        ))
                    })
            }
            _ => Err(Failure::Diagnostic(
                "E0714",
                "optional fallback requires a Prelude Optional value".into(),
            )),
        }
    }

    fn coalescing_payload_schema(
        &self,
        expression: &Expr,
        value: &StaticValue,
        expected: Option<&TypeExpr>,
    ) -> Result<Option<TypeExpr>> {
        if let Some(schema) = self.complete_source_type(value, expression.span)?
            && let TypeKind::Optional(payload) = &schema.syntax.kind
        {
            clone_work::type_syntax(&self.budget, payload)?;
            return Ok(Some(payload.as_ref().clone()));
        }
        if let Some(expected) = expected {
            clone_work::type_syntax(&self.budget, expected)?;
            return Ok(Some(expected.clone()));
        }
        let checker = Typer::new(self, None);
        let mut env = Env::new();
        if self.values.len() > 4096 {
            return Err(Failure::Unsupported(
                "static fallback context exceeds its finite lexical allowance".into(),
            ));
        }
        for (name, value) in &self.values {
            self.budget.work(name.len() as u64 + 1)?;
            let schema = self.complete_source_type(value, expression.span)?;
            let ty = if let Some(schema) = &schema {
                checker.bound_type(&schema.syntax, &bounds::BoundEnvironment::default())?
            } else {
                checker.value_type(value).unwrap_or(Ty::Unknown)
            };
            env.insert(name.clone(), ty);
            // Unknown locals mask globals. This is evaluated receiving context,
            // not a universal body proof borrowed from final actual values.
            checker
                .schema_bindings
                .borrow_mut()
                .insert(name.clone(), schema);
        }
        let actual = checker.expr(expression, &mut env)?;
        let schema = checker.expression_source_schema(
            expression,
            &actual,
            &env,
            &bounds::BoundEnvironment::default(),
            0,
        )?;
        if let Some(schema) = schema
            && let TypeKind::Optional(payload) = &schema.syntax.kind
        {
            clone_work::type_syntax(&self.budget, payload)?;
            return Ok(Some(payload.as_ref().clone()));
        }
        let Ty::Optional(payload) = actual else {
            return Err(Failure::Diagnostic(
                "E0301",
                "static fallback context has no Optional payload type".into(),
            ));
        };
        if *payload == Ty::Infer {
            return Ok(None);
        }
        applications::lossless_syntax(&payload, expression.span)
            .map(Some)
            .ok_or_else(|| {
                Failure::Unsupported(
                    "static fallback needs a complete declared payload schema".into(),
                )
            })
    }
}
