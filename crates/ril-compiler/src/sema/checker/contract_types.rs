//! Callable aliases retain their complete source modes and qualifications when
//! substituting a lexical generic binder. Value-level Ty is not a substitute.
use super::*;

impl Checker {
    pub(super) fn instantiated_callable_alias(&mut self, syntax: &TypeExpr) -> Option<TypeExpr> {
        let TypeKind::Name { path, arguments } = &syntax.kind else {
            return None;
        };
        let declaration = self.types.get(&path.join("::"))?.clone();
        if declaration.generics.is_empty()
            || declaration.nominal
            || !declaration.variants.is_empty()
            || (declaration.opaque && declaration.span.file != syntax.span.file)
        {
            return None;
        }
        let body = declaration.value.as_ref()?;
        if !self.contract_contains_callable(body, &mut BTreeSet::new()) {
            return None;
        }
        let interface_body = body.clone();
        let interface_parameters = declaration.generics.clone();
        let interface_arguments = arguments.clone();
        let selected_interface = self.argument_has_selected_generic(syntax);
        let arguments = match arguments
            .iter()
            .map(|argument| self.effect_argument_syntax(argument))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(message) => {
                self.unsupported(syntax.span, message);
                return None;
            }
        };
        // The normal constructor argument binder already implements static
        // sorts, bounds and defaults. Its nominal payload entry provides an
        // evaluation container only; the actual declaration registry and the
        // source alias's structural identity are unchanged.
        let mut container = declaration;
        container.nominal = true;
        let normalized = match crate::static_eval::normalize_constructor_arguments(
            &container,
            &arguments,
            &self.types,
            self.layout,
        ) {
            Ok(normalized) => normalized,
            Err(crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message)) => {
                self.error(code, syntax.span, message, []);
                return None;
            }
            Err(crate::static_eval::ArgumentNormalizationError::Unsupported(message)) => {
                self.unsupported(syntax.span, message);
                return None;
            }
        };
        let body = normalized.payloads.get(&container.name)?.as_ref()?.clone();
        if !closed_callable_annotations(&body) {
            self.unsupported(syntax.span,"generic callable effect rows and defaults require their own lexical substitution witnesses");
            return None;
        }
        // Normalization proves the type identity. It must not make an inferred
        // T leaf into an explicit callable interface carrying some other
        // activation's labels/default policy from the canonical descriptor.
        let substitutions = interface_parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                (
                    parameter.name.clone(),
                    interface_arguments
                        .get(index)
                        .unwrap_or(&normalized.arguments[index])
                        .clone(),
                )
            })
            .collect();
        if let Some(interface) = interface_substitution(&interface_body, &body, &substitutions)
            && let Some(closed) = self.closed_source_syntax(&interface)
            && crate::static_eval::normalized_argument_key(&closed)
                == crate::static_eval::normalized_argument_key(&body)
        {
            return Some(interface);
        }
        if selected_interface {
            self.unsupported(syntax.span,"a selected generic callable alias needs its original interface positions as well as its complete type identity");
            return None;
        }
        Some(body)
    }

    fn contract_contains_callable(&self, ty: &TypeExpr, seen: &mut BTreeSet<String>) -> bool {
        match &ty.kind {
            TypeKind::Callable { .. } => true,
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                arguments
                    .iter()
                    .any(|argument| self.contract_contains_callable(argument, &mut seen.clone()))
                    || (seen.insert(name.clone())
                        && self.types.get(&name).is_some_and(|declaration| {
                            !declaration.nominal
                                && (!declaration.opaque || declaration.span.file == ty.span.file)
                                && declaration
                                    .value
                                    .as_ref()
                                    .is_some_and(|body| self.contract_contains_callable(body, seen))
                        }))
            }
            TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
                self.contract_contains_callable(inner, seen)
            }
            TypeKind::Map { key, value } => {
                self.contract_contains_callable(key, &mut seen.clone())
                    || self.contract_contains_callable(value, seen)
            }
            TypeKind::Tuple(items) => items
                .iter()
                .any(|item| self.contract_contains_callable(item, &mut seen.clone())),
            TypeKind::Record { fields, row } => {
                fields
                    .iter()
                    .any(|field| self.contract_contains_callable(&field.ty, &mut seen.clone()))
                    || row
                        .as_ref()
                        .is_some_and(|row| self.contract_contains_callable(row, seen))
            }
            _ => false,
        }
    }
}

/// Source-position transport only. The existing normalized body independently
/// supplies the sort/bound/type proof, and canonical identity is checked above.
fn interface_substitution(
    body: &TypeExpr,
    normalized: &TypeExpr,
    arguments: &BTreeMap<String, TypeExpr>,
) -> Option<TypeExpr> {
    fn visit(
        body: &TypeExpr,
        normalized: &TypeExpr,
        arguments: &BTreeMap<String, TypeExpr>,
        depth: usize,
        work: &mut usize,
    ) -> Option<TypeExpr> {
        *work += 1;
        if depth >= 64 || *work > 4096 {
            return None;
        }
        if let TypeKind::Name {
            path,
            arguments: inputs,
        } = &body.kind
            && inputs.is_empty()
            && let Some(argument) = arguments.get(&path.join("::"))
        {
            return Some(argument.clone());
        }
        let mut output = body.clone();
        let mut child =
            |ty: &TypeExpr, proof: &TypeExpr| visit(ty, proof, arguments, depth + 1, work);
        match &mut output.kind {
            TypeKind::Name { arguments, .. } => {
                let proofs = match &normalized.kind {
                    TypeKind::Name { arguments, .. } => Some(arguments),
                    _ => None,
                };
                for (index, argument) in arguments.iter_mut().enumerate() {
                    *argument = child(
                        argument,
                        proofs
                            .and_then(|items| items.get(index))
                            .unwrap_or(argument),
                    )?;
                }
            }
            TypeKind::Tuple(items) => {
                let proofs = match &normalized.kind {
                    TypeKind::Tuple(items) => Some(items),
                    _ => None,
                };
                for (index, item) in items.iter_mut().enumerate() {
                    *item = child(
                        item,
                        proofs.and_then(|items| items.get(index)).unwrap_or(item),
                    )?;
                }
            }
            TypeKind::Optional(inner) => {
                let proof = match &normalized.kind {
                    TypeKind::Optional(inner) => inner.as_ref(),
                    _ => inner.as_ref(),
                };
                **inner = child(inner, proof)?;
            }
            TypeKind::Array { length, element } => {
                let proof = if let TypeKind::Array {
                    length: proved,
                    element,
                } = &normalized.kind
                {
                    *length = proved.clone();
                    element.as_ref()
                } else {
                    element.as_ref()
                };
                **element = child(element, proof)?;
            }
            TypeKind::Map { key, value } => {
                let (a, b) = match &normalized.kind {
                    TypeKind::Map { key, value } => (key.as_ref(), value.as_ref()),
                    _ => (key.as_ref(), value.as_ref()),
                };
                **key = child(key, a)?;
                **value = child(value, b)?;
            }
            TypeKind::Record { fields, row } => {
                let proofs = match &normalized.kind {
                    TypeKind::Record { fields, .. } => Some(fields),
                    _ => None,
                };
                for field in fields {
                    let proof = proofs
                        .and_then(|fields| fields.iter().find(|proved| proved.name == field.name))
                        .map_or(&field.ty, |field| &field.ty);
                    field.ty = child(&field.ty, proof)?;
                }
                if let Some(row) = row {
                    **row = child(row, row)?;
                }
            }
            TypeKind::Callable {
                parameters, result, ..
            } => {
                let (proofs, proved_result) = match &normalized.kind {
                    TypeKind::Callable {
                        parameters, result, ..
                    } => (Some(parameters), result.as_deref()),
                    _ => (None, None),
                };
                for (index, parameter) in parameters.iter_mut().enumerate() {
                    if parameter.default.is_some() {
                        return None;
                    }
                    let ty = parameter.ty.as_ref()?;
                    let proof = proofs
                        .and_then(|items| items.get(index))
                        .and_then(|parameter| parameter.ty.as_ref())
                        .unwrap_or(ty);
                    parameter.ty = Some(child(ty, proof)?);
                }
                if let Some(result) = result {
                    **result = child(result, proved_result.unwrap_or(result))?;
                }
            }
            TypeKind::Computation(expression)
                if matches!(expression.kind, ExprKind::Literal(_)) => {}
            _ => return None,
        }
        Some(output)
    }
    visit(body, normalized, arguments, 0, &mut 0)
}

fn closed_callable_annotations(ty: &TypeExpr) -> bool {
    match &ty.kind {
        TypeKind::Callable {
            parameters,
            result,
            annotations,
        } => {
            annotations.iter().all(|annotation| {
                annotation.kind != AnnotationKind::Effect || annotation.text == "@{}"
            }) && parameters.iter().all(|parameter| {
                parameter.default.is_none()
                    && parameter
                        .ty
                        .as_ref()
                        .is_none_or(closed_callable_annotations)
            }) && result
                .as_ref()
                .is_none_or(|result| closed_callable_annotations(result))
        }
        TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
            arguments.iter().all(closed_callable_annotations)
        }
        TypeKind::Optional(inner) | TypeKind::Array { element: inner, .. } => {
            closed_callable_annotations(inner)
        }
        TypeKind::Map { key, value } => {
            closed_callable_annotations(key) && closed_callable_annotations(value)
        }
        TypeKind::Record { fields, row } => {
            fields
                .iter()
                .all(|field| closed_callable_annotations(&field.ty))
                && row
                    .as_ref()
                    .is_none_or(|row| closed_callable_annotations(row))
        }
        _ => true,
    }
}
