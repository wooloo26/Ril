//! Check immutable source coordinates before any receiving ascription.
//!
//! The caller supplies the actual operand and its recorder-minted expression
//! index. A Name cannot borrow an old literal's construction context through a
//! cause, and an already typed record cannot reopen its member construction.
use super::*;
use crate::sema::{
    effect_identity::ArgumentKey,
    source_reception::{self, Construction, SchemaSensitivity, Target},
};
use std::sync::Arc;
#[path = "source_receiving_sensitivity.rs"]
mod sensitivity;

impl Checker {
    /// Call in the annotation's original lexical/static environment. A return
    /// target is frozen before entering the body, not when a Return is read.
    pub(super) fn freeze_source_receiving_target(&mut self, syntax: &TypeExpr) -> Target {
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
        Target {
            span: syntax.span,
            key,
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
            text: String::new(),
            span: context.span,
            kind: TypeKind::Array {
                length: length.clone(),
                element: Box::new(TypeExpr {
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
        let Some(expected) = &target.key else {
            if target.empty_array_context.is_some()
                && matches!(&actual.kind, ExprKind::Array(items) if items.is_empty())
                && observed.is_some_and(|index| {
                    self.expression_facts
                        .get(index)
                        .is_some_and(|fact| fact.span == actual.span && fact.value == *value)
                        && self.invocation_expressions.get(index).is_some_and(|row| {
                            row.expression == index
                                && row.context == self.invocation_context(frame.callable_owner)
                        })
                })
            {
                return true;
            }
            self.unsupported(
                actual.span,
                "receiving requires its original complete annotation source schema",
            );
            return false;
        };
        let mut work = 4096;
        let original = observed.and_then(|index| {
            // These are the two actual append-only recorder arenas. Require
            // their exact common index, not the last expression or a span
            // search. An unpaired recorder entry supplies no observation.
            let context = self.invocation_expressions.get(index)?;
            let expression = self.expression_facts.get(index)?;
            (context.expression == index
                && context.context == self.invocation_context(frame.callable_owner)
                && expression.span == actual.span)
                .then(|| expression.value.clone())
        });
        let answer = original.as_ref().and_then(|original| {
            let fresh = source_reception::construction(actual, &mut work)?;
            let original_key = self.original_source_receiving_key(original, actual, frame);
            // Recency transport may change graph identities, but it must not
            // change immutable source coordinates before this boundary. This
            // comparison also rejects passing an unrelated historical token.
            let current_key = self.original_source_receiving_key(value, actual, frame);
            if original_key != current_key {
                return None;
            }
            match &original_key {
                Some(key) => source_reception::compatible(expected, key, Some(&fresh), &mut work),
                None => empty_array_context(expected, &fresh, &mut work),
            }
        });
        match answer {
            Some(true) => true,
            Some(false) => {
                self.error(
                    "E0301",
                    actual.span,
                    "original array or callable source schema does not fit the receiving annotation",
                    [value.cause],
                );
                false
            }
            None => {
                self.unsupported(
                    actual.span,
                    "receiving lacks its original complete schema and actual Source observation",
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
fn qualified_source_aliases(
    checker: &mut Checker,
    syntax: &TypeExpr,
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
            // Reuse the original alias-capture check before reading its body.
            // A caller environment may not reinterpret a captured binder.
            checker.effect_argument_syntax(syntax).ok()?;
            let result = qualified_source_aliases(checker, &body, visiting, work, depth + 1);
            visiting.remove(&name);
            return result;
        }
    }
    let mut child =
        |ty: &TypeExpr| qualified_source_aliases(checker, ty, visiting, work, depth + 1);
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
        text: String::new(),
        kind,
        span: syntax.span,
    })
}

/// Project the already frozen record schema. A field is never re-resolved in
/// the environment reached after evaluating earlier members.
pub(super) fn member_target(target: &Target, name: &str, span: Span) -> Target {
    let key = target.key.as_ref().and_then(|key| {
        let ArgumentKey::Record { fields, row: None } = key else {
            return None;
        };
        let mut work = 4096usize;
        for (label, _, key) in fields {
            work = work.checked_sub(1 + label.len().max(name.len()).div_ceil(32))?;
            if label == name {
                source_reception::complete(key, &mut work)?;
                return Some(key.clone());
            }
        }
        None
    });
    let syntax = key.as_ref().and_then(|_| {
        let TypeKind::Record { fields, row: None } = &target.syntax.as_ref()?.kind else {
            return None;
        };
        fields
            .iter()
            .find(|field| field.name == name)
            .map(|field| Arc::new(field.ty.clone()))
    });
    let sensitivity = key
        .as_ref()
        .map_or(SchemaSensitivity::Unknown, key_sensitivity);
    Target {
        span,
        key,
        syntax,
        empty_array_context: None,
        sensitivity,
    }
}

fn key_sensitivity(key: &ArgumentKey) -> SchemaSensitivity {
    match source_reception::sensitive(key, &mut 4096) {
        Some(true) => SchemaSensitivity::Required,
        Some(false) if key.is_closed() => SchemaSensitivity::NotRequired,
        _ => SchemaSensitivity::Unknown,
    }
}

fn empty_array_context(
    expected: &ArgumentKey,
    construction: &Construction,
    work: &mut usize,
) -> Option<bool> {
    let (ArgumentKey::Array { length, element }, Construction::Array(items)) =
        (expected, construction)
    else {
        return None;
    };
    if !items.is_empty() {
        return None;
    }
    source_reception::complete(expected, work)?;
    if length
        .as_ref()
        .is_some_and(|length| length != "const(int:0)")
    {
        return Some(false);
    }
    source_reception::complete(element, work)?;
    Some(true)
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
                if !crate::sema::source_type_validation::resolved_names(&witness, declarations) {
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
// Append inside checker/source_receiving.rs when Root's construction wrapper
// is ready. This uses that module's existing imports and freezes no new names.

/// Project the target of an actual tuple construction member. Conditions,
/// intervening statements and unrelated nested blocks never use this target.
pub(super) fn tuple_target(target: &Target, index: usize, span: Span) -> Target {
    let projected = (|| {
        let ArgumentKey::Tuple(keys) = target.key.as_ref()? else {
            return None;
        };
        let TypeKind::Tuple(items) = &target.syntax.as_ref()?.kind else {
            return None;
        };
        if keys.len() != items.len() {
            return None;
        }
        let key = keys.get(index)?;
        let syntax = items.get(index)?;
        source_reception::complete(key, &mut 4096)?;
        Some((key.clone(), Arc::new(syntax.clone())))
    })();
    match projected {
        Some((key, syntax)) => Target {
            span,
            sensitivity: key_sensitivity(&key),
            key: Some(key),
            syntax: Some(syntax),
            empty_array_context: None,
        },
        None => Target {
            span,
            key: None,
            syntax: None,
            empty_array_context: None,
            sensitivity: SchemaSensitivity::Unknown,
        },
    }
}

/// Only the receiving array's element coordinates are projected. Stored
/// arrays retain their invariant original element source; this projection
/// alone is never evidence that the operand is an array literal.
pub(super) fn array_element_target(target: &Target, span: Span) -> Target {
    let projected = (|| {
        let ArgumentKey::Array { element, .. } = target.key.as_ref()? else {
            return None;
        };
        let TypeKind::Array {
            element: syntax, ..
        } = &target.syntax.as_ref()?.kind
        else {
            return None;
        };
        source_reception::complete(element, &mut 4096)?;
        Some(((**element).clone(), Arc::new((**syntax).clone())))
    })();
    match projected {
        Some((key, syntax)) => Target {
            span,
            sensitivity: key_sensitivity(&key),
            key: Some(key),
            syntax: Some(syntax),
            empty_array_context: None,
        },
        None => Target {
            span,
            key: None,
            syntax: None,
            empty_array_context: None,
            sensitivity: SchemaSensitivity::Unknown,
        },
    }
}

// The same append adds this focused test module; no Source pass is claimed.
#[cfg(test)]
mod projection_tests {
    use super::*;

    fn annotation(source: &str) -> TypeExpr {
        let parsed = ril_syntax::parse(&format!("let SOURCE:{source}=[]"));
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        let StmtKind::Binding(binding) = &parsed.program.statements[0].kind else {
            panic!("binding fixture");
        };
        binding.ty.clone().unwrap()
    }

    #[test]
    fn projections_keep_full_nested_coordinates_and_missing_parts_unknown() {
        let mut checker = Checker::new(FileId(0));
        let target =
            checker.freeze_source_receiving_target(&annotation("([0][3]int,fn([2]int)->int)"));
        let array = tuple_target(&target, 0, target.span);
        let element = array_element_target(&array, target.span);
        assert!(
            matches!(&element.key, Some(ArgumentKey::Array { length: Some(n), .. }) if n=="const(int:3)")
        );
        assert!(matches!(
            &element.syntax.as_ref().unwrap().kind,
            TypeKind::Array { .. }
        ));
        assert!(
            matches!(&tuple_target(&target, 1, target.span).key, Some(ArgumentKey::Callable { parameters, .. }) if matches!(&parameters[0].1, ArgumentKey::Array { length: Some(n), .. } if n=="const(int:2)"))
        );
        for unknown in [
            tuple_target(&target, 2, target.span),
            array_element_target(&target, target.span),
            tuple_target(&array, 0, target.span),
        ] {
            assert!(unknown.key.is_none() && unknown.syntax.is_none());
        }
    }
}
