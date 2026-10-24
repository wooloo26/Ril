//! Check immutable source coordinates before any receiving ascription.
//!
//! The caller supplies the actual operand and its recorder-minted expression
//! index. A Name cannot borrow an old literal's construction context through a
//! cause, and an already typed record cannot reopen its member construction.
use super::*;
use crate::sema::{
    effect_identity::ArgumentKey,
    source_reception::{self, SchemaSensitivity, Target},
};
use std::sync::Arc;
#[path = "source_receiving_sensitivity.rs"]
mod sensitivity;

impl Checker {
    /// Call in the annotation's original lexical/static environment. A return
    /// target is frozen before entering the body, not when a Return is read.
    pub(super) fn freeze_source_receiving_target(&mut self, syntax: &TypeExpr) -> Target {
        let environment = self.capture_typing_environment();
        let source = if syntax.hir_id.is_some() {
            let mut work = 16384;
            if crate::static_eval::charge_type_syntax_clone(syntax, &mut work).is_some() {
                Some(source_reception::TargetSource {
                    header: Arc::new(syntax.clone()),
                    path: vec![],
                    environment: environment.clone(),
                })
            } else {
                self.unsupported(
                    syntax.span,
                    "original receiving header exceeds its copy work bound",
                );
                None
            }
        } else {
            None
        };
        match self.freeze_key_projection_target(syntax, source.as_ref(), &environment) {
            Ok(Some(target)) => return target,
            Ok(None) => {}
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("static projection receiving source failed: {error}"),
                );
                return Target {
                    source,
                    static_projection: None,
                    environment,
                    span: syntax.span,
                    schema: None,
                    syntax: None,
                    empty_array_context: None,
                    sensitivity: SchemaSensitivity::Unknown,
                };
            }
        }
        let frozen = self
            .source_type_from_syntax(syntax)
            .and_then(|witness| {
                let key = crate::static_eval::effects::bounded_argument_key(
                    &witness.syntax,
                    &BTreeMap::new(),
                )?;
                source_reception::complete(&key, &mut 4096)?;
                Some((key, Arc::new(witness.syntax.clone())))
            })
            .or_else(|| {
                if !self.type_source.environment.generic_sources.is_empty() {
                    // A captured graph can be recursive and need not have a
                    // finite compatibility syntax. It is substituted below.
                    return None;
                }
                // Bound the source structure before the legacy effect
                // reifier recursively clones it. A failed closed-source
                // attempt does not waive the reconstruction boundary.
                let original = crate::static_eval::effects::bounded_argument_key(
                    syntax,
                    &self.effect_type_binders,
                )?;
                source_reception::complete(&original, &mut 4096)?;
                let syntax = self.effect_argument_syntax(syntax).ok()?;
                let syntax =
                    qualified_source_aliases(self, &syntax, &mut BTreeSet::new(), &mut 4096, 0)?;
                // Qualified callable headers intentionally are not closed raw
                // witnesses. They still need the same genuine standard data
                // schema expansion as the original builtin observation.
                let syntax =
                    super::source_types::expand_builtin_source_syntax(&self.types, &syntax, 0)?;
                let key = crate::static_eval::effects::bounded_argument_key(
                    &syntax,
                    &self.effect_type_binders,
                )?;
                let mut work = 4096;
                resolved_symbolic_names(
                    &syntax,
                    &self.effect_type_binders,
                    &self.types,
                    &mut work,
                    0,
                )?;
                source_reception::complete(&key, &mut work)?;
                Some((key, Arc::new(syntax)))
            });
        let (mut key, mut frozen_syntax) = match frozen {
            Some((key, syntax)) => (Some(key), Some(syntax)),
            None => (None, None),
        };
        if key.is_none()
            && let Some(syntax) = self.freeze_static_source_type(syntax)
        {
            key = crate::static_eval::effects::bounded_argument_key(
                &syntax,
                &self.effect_type_binders,
            )
            .filter(|key| source_reception::complete(key, &mut 4096).is_some());
            frozen_syntax = Some(syntax);
        }
        // A self-consistent nominal key alone does not prove its actual
        // static arguments have the declaration's Type/Const sorts.
        let mut sensitivity =
            sensitivity::annotation(self, frozen_syntax.as_deref().unwrap_or(syntax));
        if sensitivity == SchemaSensitivity::Unknown
            && self.certified_nominal_const_arguments(syntax)
        {
            sensitivity = SchemaSensitivity::NotRequired;
        }
        let empty_array_context = if key.is_none() {
            self.freeze_empty_array_context(syntax)
        } else {
            None
        };
        let schema = (|| {
            use crate::sema::source_types::{SourceTypesError, WorkLimit};
            let mut work = WorkLimit::new(16384);
            let schema = self.original_header_source_schema(syntax, &mut work)?;
            for identity in schema.binder_identities(&mut work)? {
                if let Some(binder) = self.generic_binders.get(&identity) {
                    work.charge(self.functions.len())?;
                    let parameter = self
                        .functions
                        .iter()
                        .find(|function| function.definition == binder.definition)
                        .and_then(|function| function.syntax.generics.get(binder.index as usize))
                        .ok_or(SourceTypesError::Unresolved)?;
                    if !crate::sema::record_bounds::certifies_type_sort(
                        &identity,
                        binder,
                        parameter,
                        &self.record_bounds,
                    ) {
                        return Ok(None);
                    }
                } else {
                    work.charge(self.bound_rows.len())?;
                    if !self.bound_rows.iter().any(|row| matches!(
                        &row.identity, crate::sema::model::rows::RowIdentity::Binder(actual) if actual == &identity
                    )) { return Err(SourceTypesError::Unresolved); }
                }
            }
            let mut selected = BTreeMap::new();
            work.charge(environment.generic_sources.len())?;
            for (identity, source) in &environment.generic_sources {
                if source.environment.is_poisoned() {
                    return Err(SourceTypesError::Unresolved);
                }
                selected.insert(identity.clone(), source.schema.clone());
            }
            // A declaration interpreted in its own actual named activation
            // uses that entry's static equations, including rigid UID choices
            // which have no closed compatibility witness. HIR ownership keeps
            // a callee operand context from borrowing the caller's entry.
            let required = schema.binder_identities(&mut work)?;
            if !required.is_empty()
                && let Some((definition, event, span)) = self
                    .copy_invocation_stack
                    .last()
                    .and_then(|id| self.copy_invocations.get(id.0 as usize))
                    .map(|call| (call.target, call.source_event, call.span))
            {
                work.charge(self.functions.len())?;
                let source_owner = syntax
                    .hir_id
                    .and_then(|id| self.semantic_hir.type_expression(id))
                    .map(|node| node.info.owner);
                let in_original_frame = self
                    .functions
                    .iter()
                    .find(|info| info.definition == definition)
                    .and_then(|info| info.hir_id)
                    .is_some_and(|source| {
                        source_owner == Some(crate::hir::nodes::LexicalOwner::Declaration(source))
                    });
                if in_original_frame {
                    for (identity, source) in
                        self.actual_input_source_schemas(definition, event, span, &mut work)?
                    {
                        if required.contains(&identity) {
                            selected.entry(identity).or_insert(source);
                        }
                    }
                }
            }
            let schema = schema.substitute(&selected, &mut work)?;
            Ok(Some(schema))
        })();
        let schema = match schema {
            Ok(schema) => schema,
            Err(error) => {
                self.unsupported(
                    syntax.span,
                    format!("receiving declaration graph failed: {error}"),
                );
                None
            }
        };
        Target {
            source,
            static_projection: None,
            environment,
            span: syntax.span,
            schema,
            syntax: frozen_syntax,
            empty_array_context,
            sensitivity,
        }
    }

    fn freeze_empty_array_context(&mut self, syntax: &TypeExpr) -> Option<Arc<TypeExpr>> {
        let mut context = self.instantiated_source_syntax(syntax)?;
        let TypeKind::Array { length, element } = &context.kind else {
            return None;
        };
        if sensitivity::annotation(self, element) != SchemaSensitivity::NotRequired {
            return None;
        }
        let shell = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: context.span,
            kind: TypeKind::Array {
                length: length.clone(),
                element: Box::new(TypeExpr {
                    hir_id: None,
                    text: "()".into(),
                    span: context.span,
                    kind: TypeKind::Tuple(vec![]),
                }),
            },
        };
        let shell = self.closed_source_syntax(&shell)?;
        let key = crate::static_eval::effects::bounded_argument_key(&shell, &BTreeMap::new())?;
        if !matches!(&key, ArgumentKey::Array { length, .. } if length.as_ref().is_none_or(|length|length=="const(int:0)"))
        {
            return None;
        }
        let TypeKind::Array {
            length: normalized, ..
        } = shell.kind
        else {
            return None;
        };
        if let TypeKind::Array { length, .. } = &mut context.kind {
            *length = normalized;
        }
        Some(Arc::new(context))
    }

    /// This is an additional source-coordinate check. Existing type, numeric,
    /// effect, default, permission and Result checks must still run unchanged.
    /// In particular, true does not authorize later mutation of a descriptor.
    pub(super) fn require_source_reception(
        &mut self,
        target: &Target,
        actual: &Expr,
        value: &Value,
        observed: Option<usize>,
        frame: &Frame,
    ) -> bool {
        if value.ty == Ty::Never {
            return true;
        }
        if target.sensitivity == SchemaSensitivity::NotRequired {
            return true;
        }
        if let Some(answer) =
            self.check_static_source_reception(target, actual, value, observed, frame)
        {
            if !answer {
                self.error("E0301", actual.span, "original static constructor or projection source does not fit the receiving annotation", [value.cause]);
            }
            return answer;
        }
        if target.empty_array_context.is_some()
            && matches!(&actual.kind, ExprKind::Array(items) if items.is_empty())
            && observed.is_some_and(|index| {
                self.application_effect
                    .expressions
                    .get(index)
                    .is_some_and(|fact| {
                        fact.source_id.is_some()
                            && fact.source_id == actual.hir_id
                            && fact.value == *value
                    })
                    && self
                        .application_effect
                        .contexts
                        .get(index)
                        .is_some_and(|row| {
                            row.expression == index
                                && row.context == self.invocation_context(frame.callable_owner)
                        })
            })
        {
            return true;
        }
        let Some(expected) = target.schema.as_ref() else {
            self.unsupported(
                actual.span,
                "receiving requires its original complete annotation source schema",
            );
            return false;
        };
        let mut work = 4096usize;
        let original = observed.and_then(|index| {
            // These are the two actual append-only recorder arenas. Require
            // their exact common index, not the last expression or a span
            // search. An unpaired recorder entry supplies no observation.
            let context = self.application_effect.contexts.get(index)?;
            let expression = self.application_effect.expressions.get(index)?;
            let matches = context.expression == index
                && context.context == self.invocation_context(frame.callable_owner)
                && expression.source_id.is_some()
                && expression.source_id == actual.hir_id;
            if !matches {
                return None;
            }
            work = work.checked_sub(1)?;
            Some(expression.value.packet().clone())
        });
        let answer = (|| -> Result<bool, String> {
            use crate::sema::source_types::{SourceTypesError, WorkLimit};
            let original = original
                .as_ref()
                .ok_or("original receiving observation is absent")?
                .value();
            let fresh = source_reception::construction(actual, &mut work)
                .ok_or_else(|| SourceTypesError::BudgetExceeded.to_string())?;
            let mut graph_work = WorkLimit::new(16384);
            let original_source = self
                .original_source_receiving_schema(original, actual, frame, &mut graph_work)
                .map_err(|error| format!("original read Source: {error}"))?;
            // Recency transport may change graph identities, but it must not
            // change immutable source coordinates before this boundary. This
            // comparison also rejects passing an unrelated historical token.
            let current_source = self
                .original_source_receiving_schema(value, actual, frame, &mut graph_work)
                .map_err(|error| format!("transported read Source: {error}"))?;
            match (&original_source, &current_source) {
                (Some((original, original_env)), Some((current, current_env))) => {
                    let equivalent = original
                        .equivalent(current, &mut graph_work)
                        .map_err(|error| format!("immutable Source comparison: {error}"))?;
                    let dependent = original
                        .requires_environment(&mut graph_work)
                        .map_err(|error| format!("Source environment dependence: {error}"))?;
                    if original_env.is_poisoned()
                        || current_env.is_poisoned()
                        || !equivalent
                        || (dependent && original_env.id() != current_env.id())
                    {
                        return Err(
                            "read transport changed its immutable Source or frozen environment"
                                .into(),
                        );
                    }
                    target
                        .receive_schema(original, Some(&fresh), &mut graph_work)
                        .map_err(|error| format!("declared Source reception: {error}"))
                }
                (None, None) => expected
                    .empty_context(&fresh, &mut graph_work)
                    .map_err(|error| format!("empty Source reception: {error}"))?
                    .ok_or_else(|| {
                        "receiving has no original Source graph or fresh empty construction".into()
                    }),
                _ => Err("read transport changed Source availability".into()),
            }
        })();
        match answer {
            Ok(true) => true,
            Ok(false) => {
                self.error(
                    "E0301",
                    actual.span,
                    "original array or callable source schema does not fit the receiving annotation",
                    [value.cause],
                );
                false
            }
            Err(error) => {
                self.unsupported(
                    actual.span,
                    format!("receiving lacks its original complete schema and actual Source observation: {error}"),
                );
                false
            }
        }
    }
}

/// Expand only actual zero-parameter transparent declarations, preserving
/// annotations and their original source spans/environment. No `Ty` is used
/// to fill a missing source coordinate. Recursive aliases retain an obligation
/// here; their finite absence-of-sensitive-coordinate proof is separate.
pub(super) fn qualified_source_aliases(
    checker: &Checker,
    syntax: &TypeExpr,
    visiting: &mut BTreeSet<String>,
    work: &mut usize,
    depth: usize,
) -> Option<TypeExpr> {
    qualified_source_aliases_in(
        checker,
        syntax,
        &checker.record_bound_scope(),
        visiting,
        work,
        depth,
    )
}

/// Interpret only original lexical names. Instance substitutions are applied
/// to the resulting Source key, never used to reconstruct an erased Ty here.
pub(super) fn qualified_source_aliases_in(
    checker: &Checker,
    syntax: &TypeExpr,
    scope: &crate::sema::record_bounds::BoundScope,
    visiting: &mut BTreeSet<String>,
    work: &mut usize,
    depth: usize,
) -> Option<TypeExpr> {
    *work = work.checked_sub(1)?;
    if depth >= 64 {
        return None;
    }
    crate::static_eval::effects::bounded_argument_key(syntax, &checker.effect_type_binders)?;
    if let TypeKind::Name { path, arguments } = &syntax.kind {
        let name = path.join("::");
        *work = work.checked_sub(name.len().div_ceil(32))?;
        if scope.types.contains_key(&name)
            || scope.rows.contains_key(&name)
            || checker.effect_type_binders.contains_key(&name)
        {
            return arguments.is_empty().then(|| syntax.clone());
        }
        if let Some(declaration) = checker.types.get(&name)
            && !declaration.nominal
            && !declaration.opaque
            && declaration.variants.is_empty()
        {
            if !arguments.is_empty()
                || !declaration.generics.is_empty()
                || !visiting.insert(name.clone())
            {
                return None;
            }
            crate::static_eval::effects::bounded_argument_key(
                declaration.value.as_ref()?,
                &checker.effect_type_binders,
            )?;
            let body = declaration.value.as_ref()?.clone();
            // A zero-argument alias has no substitution that could bind a free
            // Type name. Keep the original effect reifier's capture rejection
            // without reifying the enclosing function's selected value types.
            if crate::static_eval::effects::type_dependencies(&body)
                .iter()
                .any(|name| scope.types.contains_key(name) || scope.rows.contains_key(name))
            {
                return None;
            }
            let result =
                qualified_source_aliases_in(checker, &body, scope, visiting, work, depth + 1);
            visiting.remove(&name);
            return result;
        }
    }
    let mut child =
        |ty: &TypeExpr| qualified_source_aliases_in(checker, ty, scope, visiting, work, depth + 1);
    let kind = match &syntax.kind {
        TypeKind::Name { path, arguments } => TypeKind::Name {
            path: path.clone(),
            arguments: arguments.iter().map(&mut child).collect::<Option<_>>()?,
        },
        TypeKind::Optional(inner) => TypeKind::Optional(Box::new(child(inner)?)),
        TypeKind::Array { length, element } => TypeKind::Array {
            length: length.clone(),
            element: Box::new(child(element)?),
        },
        TypeKind::Map { key, value } => TypeKind::Map {
            key: Box::new(child(key)?),
            value: Box::new(child(value)?),
        },
        TypeKind::Tuple(items) => {
            TypeKind::Tuple(items.iter().map(&mut child).collect::<Option<_>>()?)
        }
        TypeKind::Record { fields, row } => TypeKind::Record {
            fields: fields
                .iter()
                .map(|field| {
                    Some(TypeField {
                        ty: child(&field.ty)?,
                        ..field.clone()
                    })
                })
                .collect::<Option<_>>()?,
            row: match row {
                Some(row) => Some(Box::new(child(row)?)),
                None => None,
            },
        },
        TypeKind::Callable {
            parameters,
            result,
            annotations,
        } => TypeKind::Callable {
            parameters: parameters
                .iter()
                .map(|parameter| {
                    Some(Parameter {
                        ty: Some(child(parameter.ty.as_ref()?)?),
                        ..parameter.clone()
                    })
                })
                .collect::<Option<_>>()?,
            result: match result {
                Some(result) => Some(Box::new(child(result)?)),
                None => None,
            },
            annotations: annotations.clone(),
        },
        _ => return None,
    };
    Some(TypeExpr {
        hir_id: None,
        text: String::new(),
        kind,
        span: syntax.span,
    })
}

/// Project the already frozen record schema. A field is never re-resolved in
/// the environment reached after evaluating earlier members.
pub(super) fn member_target(target: &Target, name: &str, span: Span) -> Target {
    let source = match target
        .source
        .as_ref()
        .map(|source| {
            source.projected(
                crate::sema::source_types::SourcePath::Field(name.into()),
                &mut crate::sema::source_types::WorkLimit::new(4096),
            )
        })
        .transpose()
    {
        Ok(source) => source,
        Err(_) => return failed_projection_target(target, span),
    };
    let schema = target
        .schema
        .as_ref()
        .and_then(|schema| schema.project_field(name).ok());
    let syntax = (|| {
        let TypeKind::Record { fields, row: None } = &target.syntax.as_ref()?.kind else {
            return None;
        };
        fields
            .iter()
            .find(|field| field.name == name)
            .map(|field| Arc::new(field.ty.clone()))
    })();
    let sensitivity = schema
        .as_ref()
        .map_or(SchemaSensitivity::Unknown, graph_sensitivity);
    Target {
        source,
        static_projection: None,
        environment: target.environment.clone(),
        span,
        schema,
        syntax,
        empty_array_context: None,
        sensitivity,
    }
}

fn failed_projection_target(target: &Target, span: Span) -> Target {
    Target {
        source: None,
        static_projection: None,
        environment: target.environment.clone(),
        span,
        schema: None,
        syntax: None,
        empty_array_context: None,
        sensitivity: SchemaSensitivity::Unknown,
    }
}

/// Project the receiving language-item payload without reinterpreting its
/// declaration in the callee's or a later operand's environment.
pub(super) fn constructor_payload_target(
    target: &Target,
    step: crate::sema::source_types::SourcePath,
    span: Span,
) -> Result<Option<Target>, crate::sema::source_types::SourceTypesError> {
    use crate::sema::source_types::{SourcePath, SourceTypesError, WorkLimit};
    if target.environment.is_poisoned() {
        return Err(SourceTypesError::Unresolved);
    }
    let Some(schema) = &target.schema else {
        return Err(SourceTypesError::Unresolved);
    };
    let mut work = WorkLimit::new(16384);
    let schema = match schema.project_steps(std::slice::from_ref(&step), &mut work) {
        Ok(schema) => schema,
        Err(SourceTypesError::MissingProjection) => return Ok(None),
        Err(error) => return Err(error),
    };
    let source = target
        .source
        .as_ref()
        .map(|source| source.projected(step.clone(), &mut work))
        .transpose()?;
    let syntax = target
        .syntax
        .as_ref()
        .and_then(|syntax| match (&syntax.kind, &step) {
            (TypeKind::Optional(inner), SourcePath::OptionalPayload) => {
                Some(Arc::new((**inner).clone()))
            }
            (TypeKind::Name { path, arguments }, projection) => {
                let name = path.join("::");
                let name = name.strip_prefix("Prelude::").unwrap_or(&name);
                let index = match (name, projection) {
                    ("Option", SourcePath::OptionalPayload) if arguments.len() == 1 => 0,
                    ("Result", SourcePath::ResultSuccess) if arguments.len() == 2 => 0,
                    ("Result", SourcePath::ResultError) if arguments.len() == 2 => 1,
                    _ => return None,
                };
                Some(Arc::new(arguments[index].clone()))
            }
            _ => None,
        });
    Ok(Some(Target {
        source,
        static_projection: None,
        environment: target.environment.clone(),
        span,
        sensitivity: graph_sensitivity(&schema),
        schema: Some(schema),
        syntax,
        empty_array_context: None,
    }))
}

pub(super) fn graph_sensitivity(
    schema: &crate::sema::source_types::SourceSchema,
) -> SchemaSensitivity {
    use crate::sema::source_types::{SourceSensitivity, WorkLimit};
    match schema.sensitivity(&mut WorkLimit::new(16384)) {
        SourceSensitivity::Sensitive { .. } => SchemaSensitivity::Required,
        SourceSensitivity::Absent { .. } => SchemaSensitivity::NotRequired,
        SourceSensitivity::Unknown { .. } => SchemaSensitivity::Unknown,
    }
}

/// `effect_argument_syntax` has already certified synthetic Binder tokens.
/// Every other Name must satisfy the existing source-name policy. In
/// particular, leaving a transparent Alias<T> unexpanded is not a proof that
/// it has no array/callable coordinates.
pub(super) fn resolved_symbolic_names(
    syntax: &TypeExpr,
    binders: &BTreeMap<String, String>,
    declarations: &BTreeMap<String, TypeDeclaration>,
    work: &mut usize,
    depth: usize,
) -> Option<()> {
    *work = work.checked_sub(1)?;
    if depth >= 64 {
        return None;
    }
    let mut children: Vec<&TypeExpr> = Vec::new();
    match &syntax.kind {
        TypeKind::Name { path, arguments } => {
            for segment in path {
                *work = work.checked_sub(segment.len().div_ceil(32))?;
            }
            let full = path.join("::");
            if binders.contains_key(&full) {
                if !arguments.is_empty() {
                    return None;
                }
            } else {
                // Only the head is tested here; each real argument is visited
                // below. Reuse the established nominal/builtin name policy
                // rather than maintaining a second builtin allow-list.
                let head = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Name {
                        path: path.clone(),
                        arguments: vec![],
                    },
                };
                let witness = SourceTypeWitness {
                    key: crate::static_eval::normalized_argument_key(&head),
                    syntax: head,
                };
                if !crate::sema::source_types::legacy::resolved_names(&witness, declarations) {
                    return None;
                }
            }
            children.extend(arguments);
        }
        TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
            children.push(inner);
        }
        TypeKind::Map { key, value } => children.extend([&**key, &**value]),
        TypeKind::Tuple(items) => children.extend(items),
        TypeKind::Record { fields, row } => {
            children.extend(fields.iter().map(|field| &field.ty));
            children.extend(row.iter().map(|row| &**row));
        }
        TypeKind::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                children.push(parameter.ty.as_ref()?);
            }
            children.extend(result.iter().map(|result| &**result));
        }
        _ => return None,
    }
    for child in children {
        resolved_symbolic_names(child, binders, declarations, work, depth + 1)?;
    }
    Some(())
}

#[cfg(test)]
#[path = "source_receiving_tests.rs"]
mod tests;

#[cfg(test)]
fn fixture_key(target: &Target) -> Option<ArgumentKey> {
    target.schema.as_ref()?.key().ok()
}
/// Project the target of an actual tuple construction member. Conditions,
/// intervening statements and unrelated nested blocks never use this target.
pub(super) fn tuple_target(target: &Target, index: usize, span: Span) -> Target {
    let Ok(coordinate) = index.try_into() else {
        return failed_projection_target(target, span);
    };
    let source = match target
        .source
        .as_ref()
        .map(|source| {
            source.projected(
                crate::sema::source_types::SourcePath::Tuple(coordinate),
                &mut crate::sema::source_types::WorkLimit::new(4096),
            )
        })
        .transpose()
    {
        Ok(source) => source,
        Err(_) => return failed_projection_target(target, span),
    };
    let schema = index.try_into().ok().and_then(|index| {
        target
            .schema
            .as_ref()?
            .project(&[crate::sema::source_types::SourcePath::Tuple(index)])
            .ok()
    });
    let syntax = target
        .syntax
        .as_ref()
        .and_then(|syntax| match &syntax.kind {
            TypeKind::Tuple(items) => items.get(index).map(|syntax| Arc::new(syntax.clone())),
            _ => None,
        });
    Target {
        source,
        static_projection: None,
        environment: target.environment.clone(),
        span,
        sensitivity: schema
            .as_ref()
            .map_or(SchemaSensitivity::Unknown, graph_sensitivity),
        schema,
        syntax,
        empty_array_context: None,
    }
}

/// Only the receiving array's element coordinates are projected. Stored
/// arrays retain their invariant original element source; this projection
/// alone is never evidence that the operand is an array literal.
pub(super) fn array_element_target(target: &Target, span: Span) -> Target {
    let source = match target
        .source
        .as_ref()
        .map(|source| {
            source.projected(
                crate::sema::source_types::SourcePath::Element,
                &mut crate::sema::source_types::WorkLimit::new(4096),
            )
        })
        .transpose()
    {
        Ok(source) => source,
        Err(_) => return failed_projection_target(target, span),
    };
    let schema = target.schema.as_ref().and_then(|schema| {
        schema
            .array_parts(&mut crate::sema::source_types::WorkLimit::new(16384))
            .ok()
            .flatten()
            .map(|(_, element)| element)
    });
    let syntax = target
        .syntax
        .as_ref()
        .and_then(|syntax| match &syntax.kind {
            TypeKind::Array { element, .. } => Some(Arc::new((**element).clone())),
            _ => None,
        });
    Target {
        source,
        static_projection: None,
        environment: target.environment.clone(),
        span,
        sensitivity: schema
            .as_ref()
            .map_or(SchemaSensitivity::Unknown, graph_sensitivity),
        schema,
        syntax,
        empty_array_context: None,
    }
}
#[cfg(test)]
mod projection_tests {
    use super::*;

    #[test]
    fn projections_keep_full_nested_coordinates_and_missing_parts_unknown() {
        let mut checker = Checker::new(FileId(0));
        let target =
            super::tests::freeze_fixture_target(&mut checker, "([0][3]int,fn([2]int)->int)");
        let array = tuple_target(&target, 0, target.span);
        let element = array_element_target(&array, target.span);
        assert_eq!(target.environment.id(), array.environment.id());
        assert_eq!(target.environment.id(), element.environment.id());
        let original = target.source.as_ref().unwrap();
        let array_source = array.source.as_ref().unwrap();
        let element_source = element.source.as_ref().unwrap();
        assert!(original.header.hir_id.is_some());
        assert!(Arc::ptr_eq(&original.header, &array_source.header));
        assert!(Arc::ptr_eq(&original.header, &element_source.header));
        assert_eq!(
            array_source.path,
            [crate::sema::source_types::SourcePath::Tuple(0)]
        );
        assert_eq!(
            element_source.path,
            [
                crate::sema::source_types::SourcePath::Tuple(0),
                crate::sema::source_types::SourcePath::Element,
            ]
        );
        assert_eq!(original.environment.id(), array_source.environment.id());
        assert_eq!(original.environment.id(), element_source.environment.id());
        assert!(
            matches!(&fixture_key(&element), Some(ArgumentKey::Array { length: Some(n), .. }) if n=="const(int:3)")
        );
        assert!(matches!(
            &element.syntax.as_ref().unwrap().kind,
            TypeKind::Array { .. }
        ));
        assert!(
            matches!(&fixture_key(&tuple_target(&target, 1, target.span)), Some(ArgumentKey::Callable { parameters, .. }) if matches!(&parameters[0].1, ArgumentKey::Array { length: Some(n), .. } if n=="const(int:2)"))
        );
        for unknown in [
            tuple_target(&target, 2, target.span),
            array_element_target(&target, target.span),
            tuple_target(&array, 0, target.span),
        ] {
            assert!(unknown.schema.is_none() && unknown.syntax.is_none());
            assert_eq!(target.environment.id(), unknown.environment.id());
        }
        let mut exhausted = target.clone();
        exhausted.source.as_mut().unwrap().path =
            vec![crate::sema::source_types::SourcePath::Element; 64];
        let poisoned = tuple_target(&exhausted, 0, target.span);
        assert!(poisoned.source.is_none());
        assert!(poisoned.schema.is_none());
        assert!(poisoned.syntax.is_none());
        assert!(poisoned.empty_array_context.is_none());
        assert_eq!(poisoned.sensitivity, SchemaSensitivity::Unknown);
    }

    #[test]
    fn record_array_projections_keep_the_original_header_path_and_environment() {
        use crate::sema::source_types::{SourcePath, SourceTypesError, WorkLimit};
        let mut checker = Checker::new(FileId(0));
        let target =
            super::tests::freeze_fixture_target(&mut checker, "{callback:[0](fn([2]int)->[2]int)}");
        let original = target.source.as_ref().unwrap();
        let captured = original.environment.id();
        checker
            .type_source
            .environment
            .generic_context
            .insert("later".into(), "unrelated:later".into());
        let field = member_target(&target, "callback", target.span);
        let element = array_element_target(&field, target.span);
        let projected = element.source.as_ref().unwrap();
        assert!(Arc::ptr_eq(&original.header, &projected.header));
        assert_eq!(
            projected.path,
            [SourcePath::Field("callback".into()), SourcePath::Element]
        );
        assert_eq!(projected.environment.id(), captured);
        assert!(element.schema.is_some());
        assert!(matches!(
            original.projected(SourcePath::Element, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(original.path.is_empty());
        let mut exhausted = field.clone();
        exhausted.source.as_mut().unwrap().path = vec![SourcePath::Element; 64];
        let poisoned = array_element_target(&exhausted, target.span);
        assert!(
            poisoned.source.is_none() && poisoned.schema.is_none() && poisoned.syntax.is_none()
        );
        assert_eq!(poisoned.sensitivity, SchemaSensitivity::Unknown);
        let mut exhausted = target.clone();
        exhausted.source.as_mut().unwrap().path = vec![SourcePath::Element; 64];
        let poisoned = member_target(&exhausted, "callback", target.span);
        assert!(
            poisoned.source.is_none() && poisoned.schema.is_none() && poisoned.syntax.is_none()
        );
        assert_eq!(poisoned.sensitivity, SchemaSensitivity::Unknown);
    }

    #[test]
    fn a_receiving_target_keeps_its_original_interpretation_after_context_switches() {
        let mut checker = Checker::new(FileId(0));
        checker
            .type_source
            .environment
            .generic_context
            .insert("T".into(), "declaration:T".into());
        checker
            .type_source
            .environment
            .generic_substitutions
            .insert("declaration:T".into(), Ty::Str);
        let syntax = super::tests::annotation(&mut checker, "T");
        let target = checker.freeze_source_receiving_target(&syntax);
        checker
            .type_source
            .environment
            .generic_context
            .insert("T".into(), "caller:T".into());
        checker
            .type_source
            .environment
            .generic_substitutions
            .insert("caller:T".into(), Ty::Int("int".into()));
        assert_eq!(checker.ty(&syntax), Ty::Int("int".into()));
        let selected =
            checker.with_typing_environment(&target.environment, |checker| checker.ty(&syntax));
        assert_eq!(selected, Ty::Str);
        assert_eq!(checker.ty(&syntax), Ty::Int("int".into()));
    }
}
