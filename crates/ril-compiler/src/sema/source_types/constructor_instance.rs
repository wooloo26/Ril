//! A declaration instance is a distinct ingress from a written type header.
//! Its owner and payload graphs come from the same bounded interpretation.
use super::*;
use crate::sema::effect_identity::ArgumentKey;

pub(crate) struct ConstructorPayload {
    pub(crate) syntax: TypeExpr,
    pub(crate) schema: SourceSchema,
}

pub(crate) struct DeclaredConstructorInstance {
    pub(crate) schema: SourceSchema,
    pub(crate) payloads: BTreeMap<String, Option<ConstructorPayload>>,
}

/// The caller authenticates which actual constructor selected these instance
/// arguments. This query authenticates its original declaration and sorts;
/// a missing TypeExprId never waives the declaration's actual HIR identity.
pub(crate) fn constructor_instance(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<DeclaredConstructorInstance, SourceTypesError> {
    charge_syntax(syntax, work)?;
    let TypeKind::Name { path, arguments } = &syntax.kind else {
        return Err(SourceTypesError::Unresolved);
    };
    work.charge(path.len() + 1)?;
    for part in path {
        work.text(part)?;
    }
    let name = path.join("::");
    let mut header = Header::new(context)?;
    let (declaration_id, declaration) = header
        .declaration(&name, work)?
        .ok_or(SourceTypesError::MissingNode)?;
    if declaration.opaque || (!declaration.nominal && declaration.variants.is_empty()) {
        return Err(SourceTypesError::Unresolved);
    }
    if let Some(payload) = &declaration.value {
        header.validate_syntax(payload, work)?;
    }
    for variant in &declaration.variants {
        for syntax in variant.payload.iter().chain(&variant.result) {
            header.validate_syntax(syntax, work)?;
        }
    }
    let mut remaining = work.remaining();
    let normalized = static_eval::normalize_constructor_arguments_bounded(
        &declaration,
        arguments,
        context.declarations,
        context.layout,
        &mut remaining,
    );
    work.charge(work.remaining() - remaining)?;
    let normalized = normalized.map_err(|_| SourceTypesError::Unresolved)?;
    if normalized.arguments.len() != declaration.generics.len() {
        return Err(SourceTypesError::Unresolved);
    }
    work.charge(declaration.generics.len())?;
    let constants = declaration
        .generics
        .iter()
        .filter(|parameter| static_eval::const_nominal::static_parameter(parameter))
        .count();
    if constants != 0 && constants != declaration.generics.len() {
        return Err(SourceTypesError::NeedsStaticElaboration);
    }
    let root = if constants != 0 {
        let mut coordinates = Vec::with_capacity(normalized.arguments.len());
        for (parameter, argument) in declaration.generics.iter().zip(&normalized.arguments) {
            if !parameter
                .bound
                .as_ref()
                .is_some_and(static_eval::const_nominal::simple_sort)
            {
                return Err(SourceTypesError::Unresolved);
            }
            charge_syntax(argument, work)?;
            let key = static_eval::effects::bounded_argument_key(argument, &BTreeMap::new())
                .ok_or(SourceTypesError::BudgetExceeded)?;
            if !matches!(key, ArgumentKey::Closed(_)) {
                return Err(SourceTypesError::Unresolved);
            }
            coordinates.push(key);
        }
        SourceSchema::certified_const_nominal(
            &name,
            &coordinates,
            Some(declaration_id),
            None,
            work,
        )?
        .copy_into(&mut header.builder, work)?
    } else {
        work.charge(normalized.arguments.len())?;
        let arguments = normalized
            .arguments
            .iter()
            .map(|argument| header.ty(argument, true, false, work, 0))
            .collect::<Result<_, _>>()?;
        header.builder.insert(
            SourceNode::OpaqueName {
                declaration: Some(NominalDeclaration::Hir(declaration_id)),
                name,
                arguments,
            },
            work,
        )?
    };
    work.charge(normalized.payloads.len())?;
    let mut payloads = Vec::with_capacity(normalized.payloads.len());
    for (tag, payload) in normalized.payloads {
        work.text(&tag)?;
        let original = if declaration.nominal {
            if tag != declaration.name {
                return Err(SourceTypesError::Unresolved);
            }
            declaration.value.as_ref().and_then(|ty| ty.hir_id)
        } else {
            work.charge(declaration.variants.len())?;
            declaration
                .variants
                .iter()
                .find(|variant| format!("{}::{}", declaration.name, variant.name) == tag)
                .ok_or(SourceTypesError::Unresolved)?
                .payload
                .as_ref()
                .and_then(|ty| ty.hir_id)
        };
        let payload = payload
            .map(|syntax| {
                charge_syntax(&syntax, work)?;
                header
                    .ty(&syntax, true, false, work, 0)
                    .map(|root| (syntax, root, original))
            })
            .transpose()?;
        payloads.push((tag, payload));
    }
    let types = header.builder.freeze(work)?;
    super::super::super::reception::complete(&types, root, work)?;
    let schema = SourceSchema::frozen_view(&types, root, None, work)?;
    let mut interpreted = BTreeMap::new();
    for (tag, payload) in payloads {
        work.charge(1)?;
        let payload = payload
            .map(
                |(syntax, root, original)| -> Result<ConstructorPayload, SourceTypesError> {
                    super::super::super::reception::complete(&types, root, work)?;
                    Ok(ConstructorPayload {
                        syntax,
                        schema: SourceSchema::frozen_view(&types, root, original, work)?,
                    })
                },
            )
            .transpose()?;
        interpreted.insert(tag, payload);
    }
    Ok(DeclaredConstructorInstance {
        schema,
        payloads: interpreted,
    })
}
