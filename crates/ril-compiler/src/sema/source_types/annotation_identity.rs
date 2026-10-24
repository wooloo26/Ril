//! Callable row identity under two already authenticated frozen contexts.
//! Comparing a lexical coordinate grants no row satisfaction or capability.
use super::{SourceTypesError, WorkLimit};
use crate::sema::{
    context::{FrozenEnvId, FrozenEnvironment},
    model::Mode,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Marker {
    ClosedEffects,
    ClosedCapabilities,
    ParameterMut,
    Retained,
    Closure,
    Capture,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Effect<'a> {
    Generic(FrozenEnvId, &'a str),
    // The environment is part of this conservative lexical reference. This
    // is not a certificate that a named effect declaration exists.
    Lexical(FrozenEnvId, &'a str),
}

#[derive(Debug, Default, PartialEq, Eq)]
struct Rows<'a> {
    original: bool,
    markers: BTreeSet<Marker>,
    states: BTreeMap<(bool, usize), Mode>,
    providers: BTreeSet<(FrozenEnvId, &'a str)>,
    effects: BTreeSet<Effect<'a>>,
}

fn lookup_work(count: usize) -> usize {
    2 + count.checked_ilog2().unwrap_or(0) as usize
}

fn identifier(text: &str) -> bool {
    let mut characters = text.chars();
    characters
        .next()
        .is_some_and(|first| first == '_' || first.is_alphabetic())
        && characters.all(|next| next == '_' || next.is_alphanumeric())
}

fn effect_syntax(text: &str) -> bool {
    // Compound effect applications need their retained typed argument graph.
    // This narrow lexical relation never guesses that graph from text.
    text.split("::").all(identifier)
}

pub(super) fn text_requires_original(text: &str) -> bool {
    let text = text.trim();
    text != "@{}"
        && text
            .strip_prefix('@')
            .is_some_and(|effect| !effect_syntax(effect.trim()))
}

pub(super) fn requires_original(
    annotations: &[String],
    work: &mut WorkLimit,
) -> Result<bool, SourceTypesError> {
    work.charge(annotations.len())?;
    for annotation in annotations {
        work.text(annotation)?;
        work.charge(annotation.len() + 1)?;
        if text_requires_original(annotation) {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(super) enum RowEquality {
    Known(bool),
    Original,
}

fn rows<'a>(
    annotations: &'a [String],
    environment: &'a FrozenEnvironment,
    work: &mut WorkLimit,
) -> Result<Rows<'a>, SourceTypesError> {
    work.charge(annotations.len() + 1)?;
    if environment.is_poisoned() {
        return Err(SourceTypesError::Unresolved);
    }
    let mut result = Rows::default();
    for annotation in annotations {
        // Pay for every token/trim pass before the shared parser walks text.
        work.text(annotation)?;
        work.charge(annotation.len().saturating_mul(2).saturating_add(1))?;
        let text = annotation.trim();
        let marker = match text {
            "@{}" => Some(Marker::ClosedEffects),
            "&{}" => Some(Marker::ClosedCapabilities),
            "&mut" => Some(Marker::ParameterMut),
            "&^mut" => Some(Marker::Retained),
            "&closure" => Some(Marker::Closure),
            "&capture" => Some(Marker::Capture),
            _ => None,
        };
        if let Some(marker) = marker {
            work.charge(lookup_work(result.markers.len()))?;
            result.markers.insert(marker);
        } else if let Some(group) = crate::sema::checker::state_group(text) {
            let captured = group.capture_owner.is_some();
            let mut any = false;
            for item in group.items() {
                work.charge(
                    (1 + item.name.len().div_ceil(32))
                        * lookup_work(environment.contract_bindings().len()),
                )?;
                let binding = environment
                    .contract_bindings()
                    .get(item.name)
                    .copied()
                    .ok_or(SourceTypesError::Unresolved)?;
                work.charge(lookup_work(result.states.len()))?;
                result
                    .states
                    .entry((captured, binding))
                    .and_modify(|mode| *mode = (*mode).max(item.mode))
                    .or_insert(item.mode);
                any = true;
            }
            if !any {
                return Err(SourceTypesError::Unresolved);
            }
        } else if let Some(effect) = text.strip_prefix('@') {
            let effect = effect.trim();
            if !effect_syntax(effect) {
                result.original = true;
                continue;
            }
            work.charge(
                (1 + effect.len().div_ceil(32)) * lookup_work(environment.generic_context.len()),
            )?;
            let identity = if let Some(identity) = environment.generic_context.get(effect) {
                work.text(identity)?;
                if identity.is_empty() {
                    return Err(SourceTypesError::Unresolved);
                }
                Effect::Generic(environment.id(), identity)
            } else {
                Effect::Lexical(environment.id(), effect)
            };
            let key = match &identity {
                Effect::Generic(_, text) | Effect::Lexical(_, text) => text,
            };
            work.charge((1 + key.len().div_ceil(32)) * lookup_work(result.effects.len()))?;
            result.effects.insert(identity);
        } else if let Some(provider) = text.strip_prefix('&') {
            let provider = provider.trim();
            if !identifier(provider) {
                return Err(SourceTypesError::Unresolved);
            }
            work.charge(
                (1 + provider.len().div_ceil(32)) * lookup_work(environment.generic_context.len()),
            )?;
            let identity = environment
                .generic_context
                .get(provider)
                .ok_or(SourceTypesError::Unresolved)?;
            work.text(identity)?;
            if identity.is_empty() {
                return Err(SourceTypesError::Unresolved);
            }
            work.charge((1 + identity.len().div_ceil(32)) * lookup_work(result.providers.len()))?;
            result
                .providers
                .insert((environment.id(), identity.as_str()));
        } else {
            return Err(SourceTypesError::Unresolved);
        }
    }
    Ok(result)
}

pub(super) fn equivalent(
    left: &[String],
    left_environment: &FrozenEnvironment,
    right: &[String],
    right_environment: &FrozenEnvironment,
    work: &mut WorkLimit,
) -> Result<RowEquality, SourceTypesError> {
    let mut left = rows(left, left_environment, work)?;
    let mut right = rows(right, right_environment, work)?;
    work.charge(
        left.markers.len()
            + right.markers.len()
            + left.states.len()
            + right.states.len()
            + left.providers.len()
            + right.providers.len()
            + left.effects.len()
            + right.effects.len()
            + 1,
    )?;
    for (_, provider) in left.providers.iter().chain(&right.providers) {
        work.text(provider)?;
    }
    for effect in left.effects.iter().chain(&right.effects) {
        match effect {
            Effect::Generic(_, text) | Effect::Lexical(_, text) => work.text(text)?,
        }
    }
    let original = left.original || right.original;
    left.original = false;
    right.original = false;
    Ok(if left != right {
        RowEquality::Known(false)
    } else if original {
        RowEquality::Original
    } else {
        RowEquality::Known(true)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{
        context::TypingEnvironment,
        effect_identity::{ArgumentKey, StaticBinderSort},
        source_types::{SourceScalar, SourceSchema},
    };
    use ril_syntax::ast::ParameterMode;

    fn callable(annotations: &[&str]) -> SourceSchema {
        let mut work = WorkLimit::new(4096);
        let int = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        let annotations: Vec<_> = annotations.iter().map(|text| (*text).into()).collect();
        SourceSchema::callable(
            &[(ParameterMode::Read, int.clone())],
            &int,
            &annotations,
            None,
            &mut work,
        )
        .unwrap()
    }

    fn environment(bindings: &[(&str, usize)]) -> FrozenEnvironment {
        TypingEnvironment {
            contract_bindings: bindings
                .iter()
                .map(|(name, id)| ((*name).into(), *id))
                .collect(),
            ..Default::default()
        }
        .freeze()
    }

    #[test]
    fn named_rows_use_binding_ids_in_each_frozen_environment() {
        let source = callable(&["&{mut calls}"]);
        let spaced = callable(&["&{  mut calls  }"]);
        let original = environment(&[("calls", 7)]);
        let shadowed = environment(&[("calls", 8)]);
        let renamed = environment(&[("counter", 7)]);
        assert_eq!(
            source.equivalent_in(&spaced, &original, &original, &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_eq!(
            source.equivalent_in(&source, &original, &shadowed, &mut WorkLimit::new(4096)),
            Ok(false)
        );
        assert_eq!(
            source.equivalent_in(
                &callable(&["&{mut counter}"]),
                &original,
                &renamed,
                &mut WorkLimit::new(4096)
            ),
            Ok(true)
        );
        for other in ["&{calls}", "&{^mut calls}", "&{closure, mut calls}", "&{}"] {
            assert_eq!(
                source.equivalent_in(
                    &callable(&[other]),
                    &original,
                    &original,
                    &mut WorkLimit::new(4096)
                ),
                Ok(false)
            );
        }
        assert_eq!(
            source.equivalent_in(
                &source,
                &original,
                &environment(&[]),
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::Unresolved)
        );
        // The Γ-free relation stays conservative for different row text.
        assert_eq!(
            source.equivalent(&spaced, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        );
    }

    #[test]
    fn contextual_closure_header_does_not_turn_a_named_binding_into_a_group() {
        let source = callable(&["&{closure}"]);
        let original = environment(&[("closure", 4), ("value", 5)]);
        assert_eq!(
            source.equivalent_in(&source, &original, &original, &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_eq!(
            source.equivalent_in(
                &callable(&["&{closure, value}"]),
                &original,
                &original,
                &mut WorkLimit::new(4096)
            ),
            Ok(false)
        );
        assert_eq!(
            callable(&["&{closure outer, value}"]).equivalent_in(
                &callable(&["&{closure, value}"]),
                &original,
                &original,
                &mut WorkLimit::new(4096)
            ),
            Ok(true)
        );
    }

    #[test]
    fn generic_rows_and_opaque_effects_cannot_borrow_another_capture() {
        let original = TypingEnvironment {
            types: crate::sema::context::StaticEnvironment {
                generic_context: BTreeMap::from([
                    ("E".into(), "effect:actual".into()),
                    ("Alias".into(), "effect:actual".into()),
                    ("P".into(), "provider:actual".into()),
                ]),
                ..Default::default()
            },
            ..Default::default()
        }
        .freeze();
        let other = original.thaw().freeze();
        let source = callable(&["@E", "&P"]);
        assert_eq!(
            source.equivalent_in(
                &callable(&["@Alias", "&P"]),
                &original,
                &original,
                &mut WorkLimit::new(4096)
            ),
            Ok(true)
        );
        assert_eq!(
            source.equivalent_in(&source, &original, &other, &mut WorkLimit::new(4096)),
            Ok(false)
        );
        let named = callable(&["@User::Effect"]);
        assert_eq!(
            named.equivalent_in(&named, &original, &original, &mut WorkLimit::new(4096)),
            Ok(true)
        );
        assert_eq!(
            named.equivalent_in(&named, &original, &other, &mut WorkLimit::new(4096)),
            Ok(false)
        );
        assert_eq!(
            source.equivalent_in(
                &source,
                &original,
                &environment(&[]),
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::Unresolved)
        );
        assert_eq!(
            callable(&["&Missing"]).equivalent_in(
                &callable(&["&Missing"]),
                &original,
                &original,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::Unresolved)
        );
        assert_eq!(
            callable(&["@Effect<int>"]).equivalent_in(
                &callable(&["@Effect<int>"]),
                &original,
                &original,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::Unresolved)
        );
    }

    #[test]
    fn graph_dependencies_and_poison_do_not_gain_authority_from_row_equality() {
        let original = environment(&[]);
        let other = environment(&[]);
        let mut work = WorkLimit::new(4096);
        for key in [
            ArgumentKey::Binder {
                identity: "genuine:type".into(),
                sort: StaticBinderSort::Type,
            },
            ArgumentKey::Name {
                name: "OriginalNominal".into(),
                arguments: vec![],
            },
        ] {
            let source = SourceSchema::import(&key, None, &mut work).unwrap();
            assert_eq!(
                source.equivalent_in(&source, &original, &original, &mut work),
                Ok(true)
            );
            assert_eq!(
                source.equivalent_in(&source, &original, &other, &mut work),
                Err(SourceTypesError::Unresolved)
            );
        }
        let scalar = SourceSchema::scalar(SourceScalar::Int, None, &mut work).unwrap();
        assert_eq!(
            scalar.equivalent_in(&scalar, &original, &other, &mut work),
            Ok(true)
        );
        assert_eq!(
            scalar.equivalent_in(
                &scalar,
                &original,
                &FrozenEnvironment::poisoned(),
                &mut work
            ),
            Err(SourceTypesError::Unresolved)
        );
    }

    #[test]
    fn contextual_row_walks_charge_one_shared_budget_before_parsing() {
        let environment = environment(&[("calls", 7)]);
        let source = callable(&["&{mut calls}", "@{}"]);
        let mut work = WorkLimit::new(4096);
        assert!(
            source
                .equivalent_in(&source, &environment, &environment, &mut work)
                .unwrap()
        );
        let used = 4096 - work.remaining();
        let mut exact = WorkLimit::new(used);
        assert!(
            source
                .equivalent_in(&source, &environment, &environment, &mut exact)
                .unwrap()
        );
        assert_eq!(exact.remaining(), 0);
        for short in [0, used - 1] {
            assert_eq!(
                source.equivalent_in(
                    &source,
                    &environment,
                    &environment,
                    &mut WorkLimit::new(short)
                ),
                Err(SourceTypesError::BudgetExceeded)
            );
        }
        assert_eq!(
            source.equivalent_in(&source, &environment, &environment, &mut exact),
            Err(SourceTypesError::BudgetExceeded)
        );
    }
}
