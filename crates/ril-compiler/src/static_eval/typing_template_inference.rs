//! Additional structural inference children. Complete callable source syntax
//! carries invocation modes and qualifiers; the erased ordinary Ty cannot
//! supply them. This module does not create callable views or permission facts.
use super::*;

impl Typer<'_> {
    pub(super) fn infer_application_template_children(
        &self,
        formal: &TypeExpr,
        actual: &Ty,
        schema: Option<&Arc<SourceTypeWitness>>,
        inference: ApplicationInference<'_>,
        scope: &mut BoundEnvironment,
        depth: usize,
    ) -> Result<bool> {
        let ApplicationInference { caller, .. } = inference;
        self.schema_work.work(1)?;
        if depth >= 64 {
            return Err(Failure::Unsupported(
                "static template inference exceeds its finite traversal allowance".into(),
            ));
        }
        let closed = schema.map(|witness| &witness.syntax.kind);
        match (&formal.kind, actual) {
            (TypeKind::Map { key, value }, Ty::Map(actual_key, actual_value)) => {
                let source = match closed {
                    Some(TypeKind::Map { key, value }) => {
                        [Some(key.as_ref()), Some(value.as_ref())]
                    }
                    None => [None, None],
                    _ => {
                        return Err(Failure::Unsupported(
                            "static map template requires its consistent root schema".into(),
                        ));
                    }
                };
                for ((formal, actual), source) in [
                    (key.as_ref(), actual_key.as_ref()),
                    (value.as_ref(), actual_value.as_ref()),
                ]
                .into_iter()
                .zip(source)
                {
                    let child = source
                        .map(|syntax| self.complete_source_syntax(syntax, caller))
                        .transpose()?
                        .flatten();
                    self.infer_application_type(
                        formal,
                        actual,
                        child,
                        inference,
                        scope,
                        depth + 1,
                    )?;
                }
                Ok(true)
            }
            (
                TypeKind::Callable {
                    parameters, result, ..
                },
                Ty::Callable(actual_parameters, actual_result, _),
            ) => {
                let Some(TypeKind::Callable {
                    parameters: source_parameters,
                    result: source_result,
                    ..
                }) = closed
                else {
                    return Err(Failure::Unsupported(
                        "static callable template requires complete source modes and qualifiers"
                            .into(),
                    ));
                };
                if parameters.len() != actual_parameters.len()
                    || source_parameters.len() != actual_parameters.len()
                {
                    return Err(Failure::Diagnostic(
                        "E0301",
                        "static callable template parameter counts disagree".into(),
                    ));
                }
                for ((formal, actual), source) in parameters
                    .iter()
                    .zip(actual_parameters)
                    .zip(source_parameters)
                {
                    self.schema_work.work(1)?;
                    if formal.mode != source.mode {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "static callable template parameter modes disagree".into(),
                        ));
                    }
                    let (Some(formal), Some(source)) = (&formal.ty, &source.ty) else {
                        return Err(Failure::Unsupported(
                            "static callable template parameter type is not complete".into(),
                        ));
                    };
                    let child = self.complete_source_syntax(source, caller)?;
                    self.infer_application_type(
                        formal,
                        actual,
                        child,
                        inference,
                        scope,
                        depth + 1,
                    )?;
                }
                if let Some(formal) = result {
                    let child = source_result
                        .as_deref()
                        .map(|source| self.complete_source_syntax(source, caller))
                        .transpose()?
                        .flatten();
                    self.infer_application_type(
                        formal,
                        actual_result,
                        child,
                        inference,
                        scope,
                        depth + 1,
                    )?;
                }
                // The caller still checks the complete root schema, including
                // annotations, after all selected types have been substituted.
                Ok(true)
            }
            _ => Ok(false),
        }
    }
}
