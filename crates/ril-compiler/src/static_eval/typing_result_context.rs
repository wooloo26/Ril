//! Declaration-directed result inference. Result contexts constrain Type parameters only; they do not
//! describe actual objects, tags, producers, access permissions, or freshness.
use super::*;

#[derive(Clone)]
pub(in crate::static_eval) struct ResultContext {
    written: Arc<TypeExpr>,
    source: Arc<TypeExpr>,
    lexical: Arc<BoundEnvironment>,
    ordinary: Ty,
    complete: Option<Arc<SourceTypeWitness>>,
}

impl ResultContext {
    pub(in crate::static_eval) fn ordinary(&self) -> &Ty {
        &self.ordinary
    }

    pub(in crate::static_eval) fn written(&self) -> &TypeExpr {
        &self.written
    }

    pub(in crate::static_eval) fn closed_schema(&self) -> Option<&Arc<SourceTypeWitness>> {
        self.complete.as_ref()
    }
}

pub(in crate::static_eval) enum ResultProjection {
    ArrayElement,
    Tuple(usize),
    Record(String),
    MapKey,
    MapValue,
    OptionalPayload,
    ResultOk,
    ResultError,
}

#[derive(Clone, Copy)]
struct ResultInference<'a> {
    lexical: &'a BoundEnvironment,
    pending: &'a BTreeSet<StaticBinderId>,
    declaration: &'a str,
}

impl Typer<'_> {
    fn normalize_result_source(
        &self,
        written: &TypeExpr,
        lexical: &BoundEnvironment,
    ) -> Result<TypeExpr> {
        fn visit(
            checker: &Typer<'_>,
            source: &mut TypeExpr,
            lexical: &BoundEnvironment,
            depth: usize,
            nodes: &mut usize,
        ) -> Result<()> {
            *nodes += 1;
            checker.schema_work.work(1)?;
            if depth >= 64 || *nodes > 4096 {
                return Err(missing(
                    "static result-source normalization traversal allowance",
                ));
            }
            if let TypeKind::Name { path, arguments } = &source.kind {
                let canonical = path.join("::");
                if let Some(declaration) = checker.evaluator.declarations.get(&canonical)
                    && declaration.name == canonical
                    && !declaration.nominal
                    && !declaration.opaque
                    && declaration.variants.is_empty()
                {
                    let key = types::TypeInstanceKey::new(
                        canonical,
                        checker
                            .evaluator
                            .function_environments
                            .get(&declaration.name)
                            .copied(),
                        arguments,
                    );
                    if let Some(frozen) = checker.evaluator.alias_instances.get(&key) {
                        clone_work::type_syntax(&checker.schema_work, frozen)?;
                        *source = frozen.clone();
                    }
                }
            }
            let mut child =
                |source: &mut TypeExpr| visit(checker, source, lexical, depth + 1, nodes);
            match &mut source.kind {
                TypeKind::Array { element, length } => {
                    if let Some(length) = length {
                        // Normalize the written scalar computation itself. An
                        // ordinary array's backing length is not type evidence.
                        let fact = checker.expr(length, &mut lexical.values.clone())?;
                        require(&fact, &Ty::Number("int".into())).map_err(
                            |failure| match failure {
                                Failure::Diagnostic(_, reason) => {
                                    Failure::Diagnostic("E0323", reason)
                                }
                                other => other,
                            },
                        )?;
                        if let Ty::IntegerConstant(value) = fact {
                            if value < 0 {
                                return Err(Failure::Diagnostic(
                                    "E0815",
                                    "fixed array length is negative".into(),
                                ));
                            }
                            length.kind = ExprKind::Literal(Literal::Integer(value.to_string()));
                        }
                    }
                    child(element)?;
                }
                TypeKind::Optional(inner) => child(inner)?,
                TypeKind::Tuple(items) => {
                    for item in items {
                        child(item)?;
                    }
                }
                TypeKind::Map { key, value } => {
                    child(key)?;
                    child(value)?;
                }
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        child(&mut field.ty)?;
                    }
                    if let Some(row) = row {
                        child(row)?;
                    }
                }
                TypeKind::Name { arguments, .. } => {
                    for argument in arguments {
                        child(argument)?;
                    }
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        if let Some(ty) = &mut parameter.ty {
                            child(ty)?;
                        }
                    }
                    if let Some(result) = result {
                        child(result)?;
                    }
                }
                _ => {}
            }
            Ok(())
        }
        // Only an existing exact instance may expose an alias body here.
        // Cache misses retain the original Name for pure normalization/NI.
        let mut source = self.scoped_source_syntax(written, lexical)?;
        visit(self, &mut source, lexical, 0, &mut 0)?;
        Ok(source)
    }

    pub(in crate::static_eval::typing) fn child_result_context(
        &self,
        context: Option<&ResultContext>,
        projection: ResultProjection,
    ) -> Result<Option<ResultContext>> {
        context
            .map(|context| self.project_result_context(context, projection))
            .transpose()
            .map(Option::flatten)
    }
    pub(in crate::static_eval::typing) fn context_for_syntax(
        &self,
        written: &TypeExpr,
        env: &Env,
    ) -> Result<ResultContext> {
        let mut lexical = self
            .bound_environment
            .as_deref()
            .cloned()
            .unwrap_or_default();
        lexical.values = env.clone();
        self.apply_const_shadows(&mut lexical)?;
        self.result_context(written, &lexical)
    }

    pub(in crate::static_eval::typing) fn project_result_context(
        &self,
        context: &ResultContext,
        projection: ResultProjection,
    ) -> Result<Option<ResultContext>> {
        use ResultProjection::*;
        let source = match (&context.source.kind, projection) {
            (TypeKind::Array { element, .. }, ArrayElement) => Some(element.as_ref()),
            (TypeKind::Tuple(items), Tuple(index)) => items.get(index),
            (TypeKind::Record { fields, .. }, Record(name)) => {
                fields.iter().find(|f| f.name == name).map(|f| &f.ty)
            }
            (TypeKind::Map { key, .. }, MapKey) => Some(key.as_ref()),
            (TypeKind::Map { value, .. }, MapValue) => Some(value.as_ref()),
            (TypeKind::Optional(inner), OptionalPayload) => Some(inner.as_ref()),
            (TypeKind::Name { path, arguments }, OptionalPayload)
                if normalized_path(path) == "Option" =>
            {
                arguments.first()
            }
            (TypeKind::Name { path, arguments }, ResultOk) if normalized_path(path) == "Result" => {
                arguments.first()
            }
            (TypeKind::Name { path, arguments }, ResultError)
                if normalized_path(path) == "Result" =>
            {
                arguments.get(1)
            }
            _ => None,
        };
        source
            .map(|source| self.result_context(source, &context.lexical))
            .transpose()
    }

    pub(in crate::static_eval::typing) fn optional_result_context(
        &self,
        context: &ResultContext,
    ) -> Result<ResultContext> {
        context
            .lexical
            .admit_with_types(&self.schema_work, std::slice::from_ref(&context.ordinary))?;
        clone_work::type_syntax(&self.schema_work, &context.written)?;
        clone_work::type_syntax(&self.schema_work, &context.source)?;
        let wrap = |syntax: TypeExpr| TypeExpr {
            span: syntax.span,
            text: String::new(),
            kind: TypeKind::Optional(Box::new(syntax)),
        };
        let source = wrap((*context.source).clone());
        let complete = if context.complete.is_some() {
            let witness = SourceTypeWitness {
                key: normalized_argument_key(&source),
                syntax: source.clone(),
            };
            if !witness.validate_closed() {
                return Err(missing(
                    "lifted result context lacks a complete closed source",
                ));
            }
            Some(Arc::new(witness))
        } else {
            None
        };
        Ok(ResultContext {
            written: Arc::new(wrap((*context.written).clone())),
            source: Arc::new(source),
            lexical: context.lexical.clone(),
            ordinary: Ty::Optional(Box::new(context.ordinary.clone())),
            complete,
        })
    }

    pub(in crate::static_eval::typing) fn result_context(
        &self,
        written: &TypeExpr,
        lexical: &BoundEnvironment,
    ) -> Result<ResultContext> {
        self.reject_const_dependent_type(written, lexical)?;
        lexical.admit_with_types(&self.schema_work, &[])?;
        clone_work::type_syntax(&self.schema_work, written)?;
        let normalized = self.normalize_result_source(written, lexical)?;
        let complete = self.complete_source_syntax(&normalized, lexical)?;
        let source = if let Some(complete) = &complete {
            clone_work::type_syntax(&self.schema_work, &complete.syntax)?;
            complete.syntax.clone()
        } else {
            let scoped = normalized;
            self.symbolic_alias_syntax(&scoped, lexical)?
                .map_or(scoped, |expanded| expanded.syntax)
        };
        let ordinary = self.bound_type(&source, lexical)?;
        Ok(ResultContext {
            written: Arc::new(written.clone()),
            source: Arc::new(source),
            lexical: Arc::new(lexical.clone()),
            ordinary,
            complete,
        })
    }

    /// Run after explicit/input selection and its bound-dependency fixed point,
    /// before row entailment and the final missing-parameter diagnostics.
    pub(super) fn infer_application_result_context(
        &self,
        function: &Function,
        expected: Option<&ResultContext>,
        scope: &mut BoundEnvironment,
    ) -> Result<()> {
        let (Some(expected), Some(result)) = (expected, &function.return_type) else {
            return Ok(());
        };
        let pending = function
            .generics
            .iter()
            .filter_map(|parameter| scope.type_binders.get(&parameter.name).cloned())
            .filter(|id| !scope.type_arguments.contains_key(id))
            .collect::<BTreeSet<_>>();
        if pending.is_empty() {
            return Ok(());
        }
        expected.lexical.admit_with_types(&self.schema_work, &[])?;
        self.infer_result_syntax(
            result,
            &expected.source,
            scope,
            ResultInference {
                lexical: &expected.lexical,
                pending: &pending,
                declaration: &function.name,
            },
            0,
        )
    }

    fn infer_result_syntax(
        &self,
        formal: &TypeExpr,
        expected: &TypeExpr,
        scope: &mut BoundEnvironment,
        inference: ResultInference<'_>,
        depth: usize,
    ) -> Result<()> {
        let ResultInference {
            lexical,
            pending,
            declaration,
        } = inference;
        self.schema_work.work(1)?;
        if depth >= 64 {
            return Err(missing(
                "static result-context inference traversal allowance",
            ));
        }
        if let TypeKind::Name { path, arguments } = &formal.kind
            && path.len() == 1
            && arguments.is_empty()
            && let Some(id) = scope
                .type_binders
                .get(&path[0])
                .or_else(|| scope.type_ids.get(&path[0]))
                .cloned()
        {
            // The snapshot remains fixed during this walk so two contextual
            // occurrences of a formerly missing T must agree with each other.
            if !pending.contains(&id) {
                return Ok(());
            }
            let actual = self.bound_type(expected, lexical)?;
            if let Ty::Generic(identity) = &actual
                && lexical
                    .type_ids
                    .get(identity)
                    .is_some_and(|caller| caller.declaration == declaration)
            {
                return Err(missing(
                    "recursive result-context selection needs distinct rigid activation identities",
                ));
            }
            let complete = self.complete_source_syntax(expected, lexical)?;
            return self.select_type_argument(&id, &actual, complete, lexical, scope);
        }
        if let Some(expanded) = self.symbolic_alias_syntax(formal, scope)? {
            return self.infer_result_syntax(
                &expanded.syntax,
                expected,
                scope,
                inference,
                depth + 1,
            );
        }
        let mut child = |formal: &TypeExpr, expected: &TypeExpr| {
            self.infer_result_syntax(formal, expected, scope, inference, depth + 1)
        };
        match (&formal.kind, &expected.kind) {
            (
                TypeKind::Array {
                    element: formal, ..
                },
                TypeKind::Array {
                    element: expected, ..
                },
            )
            | (TypeKind::Optional(formal), TypeKind::Optional(expected)) => {
                child(formal, expected)?;
            }
            (TypeKind::Tuple(formals), TypeKind::Tuple(expecteds))
                if formals.len() == expecteds.len() =>
            {
                for (formal, expected) in formals.iter().zip(expecteds) {
                    child(formal, expected)?;
                }
            }
            (
                TypeKind::Record {
                    fields: formals,
                    row: None,
                },
                TypeKind::Record {
                    fields: expecteds,
                    row: None,
                },
            ) if formals.len() == expecteds.len() => {
                for formal in formals {
                    if let Some(expected) = expecteds.iter().find(|f| f.name == formal.name) {
                        child(&formal.ty, &expected.ty)?;
                    }
                }
            }
            (TypeKind::Map { key: fk, value: fv }, TypeKind::Map { key: ek, value: ev }) => {
                child(fk, ek)?;
                child(fv, ev)?;
            }
            (
                TypeKind::Callable {
                    parameters: fp,
                    result: fr,
                    ..
                },
                TypeKind::Callable {
                    parameters: ep,
                    result: er,
                    ..
                },
            ) if fp.len() == ep.len() => {
                for (formal, expected) in fp.iter().zip(ep) {
                    if let (Some(formal), Some(expected)) = (&formal.ty, &expected.ty) {
                        child(formal, expected)?;
                    }
                }
                if let (Some(formal), Some(expected)) = (fr, er) {
                    child(formal, expected)?;
                }
            }
            (
                TypeKind::Name {
                    path: fp,
                    arguments: fa,
                },
                TypeKind::Name {
                    path: ep,
                    arguments: ea,
                },
            ) if normalized_path(fp) == normalized_path(ep) && fa.len() == ea.len() => {
                for (formal, expected) in fa.iter().zip(ea) {
                    child(formal, expected)?;
                }
            }
            (TypeKind::Name { path, arguments }, TypeKind::Optional(expected))
                if normalized_path(path) == "Option" && arguments.len() == 1 =>
            {
                child(&arguments[0], expected)?;
            }
            (TypeKind::Optional(formal), TypeKind::Name { path, arguments })
                if normalized_path(path) == "Option" && arguments.len() == 1 =>
            {
                child(formal, &arguments[0])?;
            }
            _ => {}
        }
        // The walk supplies candidate types only. It does not accept this root
        // as a receiving conversion or rewrite its dimensions/qualifications.
        Ok(())
    }

    /// Run after all selections/row equations/input checks have succeeded.
    /// Callable labels/defaults are still received outside this inference API.
    pub(super) fn check_application_result_context(
        &self,
        function: &Function,
        expected: Option<&ResultContext>,
        scope: &BoundEnvironment,
    ) -> Result<()> {
        let (Some(expected), Some(result)) = (expected, &function.return_type) else {
            return Ok(());
        };
        let resolved = self.normalize_result_source(result, scope)?;
        let actual = if let Some(complete) = self.complete_source_syntax(&resolved, scope)? {
            clone_work::type_syntax(&self.schema_work, &complete.syntax)?;
            complete.syntax.clone()
        } else {
            self.symbolic_alias_syntax(&resolved, scope)?
                .map_or(resolved, |expanded| expanded.syntax)
        };
        if !schema_receives(&actual, &expected.source, false, 0) {
            return Err(mismatch(
                "declared static result does not satisfy its complete expected dimensions, modes or qualifications",
            ));
        }
        require(&self.bound_type(result, scope)?, &expected.ordinary)
    }
}
