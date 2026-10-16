//! Frozen static argument identity is checked without reopening an activation's
//! substitutions. Incomplete arguments remain incomplete; syntax and key may
//! not disagree about a selected type or a registered symbolic binder.
use super::{
    SemanticFacts,
    effect_identity::{ArgumentKey, StaticArgumentWitness},
};
use ril_compiler_core::ids::DefinitionId;
use ril_compiler_core::source::Span;
use std::collections::{BTreeMap, BTreeSet};

fn certified_type_binders(facts: &SemanticFacts) -> BTreeMap<String, String> {
    facts
        .generic_binders
        .iter()
        .filter_map(|(identity, binder)| {
            let parameter = facts
                .functions
                .iter()
                .find(|function| function.definition == binder.definition)?
                .syntax
                .generics
                .get(binder.index as usize)?;
            if !super::record_bounds::certifies_type_sort(
                identity,
                binder,
                parameter,
                &facts.record_bounds,
            ) {
                return None;
            }
            Some((format!("\0effect-binder:{identity}"), identity.clone()))
        })
        .collect()
}

fn key_binders(key: &ArgumentKey) -> Option<BTreeSet<String>> {
    fn walk(
        key: &ArgumentKey,
        depth: usize,
        nodes: &mut usize,
        bytes: &mut usize,
        binders: &mut BTreeSet<String>,
    ) -> Option<()> {
        if depth > 128 {
            return None;
        }
        *nodes = nodes.checked_sub(1)?;
        let mut text = |text: &str| {
            *bytes = bytes.checked_sub(text.len())?;
            Some(())
        };
        match key {
            ArgumentKey::Closed(value) => text(value)?,
            ArgumentKey::Binder { identity, .. } => {
                text(identity)?;
                binders.insert(identity.clone());
            }
            ArgumentKey::Name { name, arguments } => {
                text(name)?;
                // Registered symbolic names must be represented by Binder,
                // including inside composites; a Name is never a substitute.
                if name.contains('\0') {
                    return None;
                }
                for key in arguments {
                    walk(key, depth + 1, nodes, bytes, binders)?;
                }
            }
            ArgumentKey::Array { length, element } => {
                if let Some(length) = length {
                    text(length)?;
                }
                walk(element, depth + 1, nodes, bytes, binders)?;
            }
            ArgumentKey::Map { key, value } => {
                walk(key, depth + 1, nodes, bytes, binders)?;
                walk(value, depth + 1, nodes, bytes, binders)?;
            }
            ArgumentKey::Tuple(items) => {
                for key in items {
                    walk(key, depth + 1, nodes, bytes, binders)?;
                }
            }
            ArgumentKey::Record { fields, row } => {
                for (name, _, key) in fields {
                    *bytes = bytes.checked_sub(name.len())?;
                    walk(key, depth + 1, nodes, bytes, binders)?;
                }
                if let Some(row) = row {
                    walk(row, depth + 1, nodes, bytes, binders)?;
                }
            }
            ArgumentKey::Callable {
                parameters,
                result,
                annotations,
            } => {
                for annotation in annotations {
                    text(annotation)?;
                }
                for (_, key) in parameters {
                    walk(key, depth + 1, nodes, bytes, binders)?;
                }
                walk(result, depth + 1, nodes, bytes, binders)?;
            }
        }
        Some(())
    }
    let mut binders = BTreeSet::new();
    walk(key, 0, &mut 4096, &mut 10_000_000, &mut binders)?;
    Some(binders)
}

fn consistent(
    argument: &StaticArgumentWitness,
    facts: &SemanticFacts,
    binders: &BTreeMap<String, String>,
) -> bool {
    let Some(owner) = facts.generic_binders.get(&argument.binder) else {
        return false;
    };
    let parameter = facts
        .functions
        .iter()
        .find(|function| function.definition == owner.definition)
        .and_then(|function| function.syntax.generics.get(owner.index as usize));
    if owner.identity != argument.binder
        || owner.definition != argument.definition
        || owner.index != argument.index
        || parameter.is_none_or(|parameter| parameter.name != owner.name)
    {
        return false;
    }
    match (&argument.syntax, &argument.key) {
        (None, None) => true,
        (Some(syntax), Some(key)) => {
            let Some(recorded_binders) = key_binders(key) else {
                return false;
            };
            let Some(recomputed) =
                crate::static_eval::effects::bounded_argument_key(syntax, binders)
            else {
                return false;
            };
            let Some(recomputed_binders) = key_binders(&recomputed) else {
                return false;
            };
            if key != &recomputed || recorded_binders != recomputed_binders {
                return false;
            }
            let dependencies = crate::static_eval::effects::type_dependencies(syntax);
            let mut expected = BTreeSet::new();
            for name in dependencies {
                if name.starts_with('\0') {
                    let Some(identity) = binders.get(&name) else {
                        return false;
                    };
                    expected.insert(identity.clone());
                } else if facts
                    .generic_binders
                    .values()
                    .any(|binder| binder.name == name)
                    && !facts.external_type_declarations.contains_key(&name)
                {
                    // A frozen symbolic type uses its registered token, never
                    // an unqualified spelling interpreted in a later caller.
                    return false;
                }
            }
            recorded_binders == expected
        }
        _ => false,
    }
}

fn covered(
    target: Option<DefinitionId>,
    arguments: &[StaticArgumentWitness],
    captured: &[StaticArgumentWitness],
    unresolved: &BTreeSet<String>,
    facts: &SemanticFacts,
) -> bool {
    let Some(target) = target else {
        return arguments.is_empty() && captured.is_empty() && unresolved.is_empty();
    };
    let Some(function) = facts
        .functions
        .iter()
        .find(|function| function.definition == target)
    else {
        return false;
    };
    if arguments.len() != function.syntax.generics.len()
        || arguments.iter().enumerate().any(|(index, argument)| {
            argument.definition != target || argument.index as usize != index
        })
    {
        return false;
    }
    let expected: BTreeSet<_> = function
        .typing_environment
        .generic_context
        .iter()
        .filter(|(name, _)| {
            !function
                .syntax
                .generics
                .iter()
                .any(|parameter| parameter.name == **name)
        })
        .map(|(_, identity)| identity.clone())
        .collect();
    let present: BTreeSet<_> = captured
        .iter()
        .map(|argument| argument.binder.clone())
        .collect();
    present.len() == captured.len()
        && present.is_disjoint(unresolved)
        && present.union(unresolved).cloned().collect::<BTreeSet<_>>() == expected
}

pub(crate) fn validate(facts: &SemanticFacts) -> Result<(), (Span, String)> {
    let binders = certified_type_binders(facts);
    let observations = facts
        .effect_invocations
        .iter()
        .map(|event| {
            (
                event.site,
                Some(event.function),
                &event.arguments,
                &event.captured_arguments,
                &event.unresolved_captured_binders,
            )
        })
        .chain(facts.default_uses.iter().map(|event| {
            (
                event.span,
                event.target,
                &event.arguments,
                &event.captured_arguments,
                &event.unresolved_captured_binders,
            )
        }));
    for (span, target, arguments, captured, unresolved) in observations {
        if !covered(target, arguments, captured, unresolved, facts) {
            return Err((span, "static argument observations do not cover their declaration and captured binder environment".into()));
        }
        for argument in arguments.iter().chain(captured) {
            if !consistent(argument, facts, &binders) {
                return Err((
                    span,
                    format!(
                        "static argument {}:{} has an inconsistent frozen syntax, key or binder identity",
                        argument.definition.0, argument.index
                    ),
                ));
            }
        }
    }
    Ok(())
}
