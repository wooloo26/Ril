//! Immutable optional tag identities describe conditional payload presence.
//! They grant no inspection, storage permission, or freshness proof.
use super::{facts::ScopeId, model::Ty};
use ril_compiler_core::{diagnostic::CauseId, ids::OptionalTagId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OptionalTagFact {
    pub id: OptionalTagId,
    /// MAX is admitted only for a borrowed formal, as for Result producers.
    pub creation_owner: ScopeId,
    pub cause: CauseId,
    pub payload_type: Ty,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::model::Value;

    fn unknown(identity: Option<OptionalTagId>) -> Value {
        let inner = Ty::Int("int".into());
        let mut value = Value::scalar(Ty::Optional(Box::new(inner.clone())), None, CauseId(0));
        value.option_identity = identity;
        value.option_payload = Some(Box::new(Value::scalar(inner, None, CauseId(0))));
        value
    }

    #[test]
    fn copied_tags_keep_equality_but_independent_and_unknown_joins_do_not_invent_it() {
        let left = unknown(Some(OptionalTagId(0)));
        let mut alias = left.clone();
        alias.option_tag = Some(true);
        let shared = left.join(&alias, 0, CauseId(0));
        assert_eq!(shared.option_identity, Some(OptionalTagId(0)));
        assert_eq!(shared.option_tag, None);
        assert_eq!(shared.permission, left.permission);
        assert_eq!(shared.publication, left.publication);
        let independent = unknown(Some(OptionalTagId(1)));
        assert!(!left.same_abstract_value(&independent));
        assert_eq!(left.join(&independent, 0, CauseId(0)).option_identity, None);
        assert_eq!(
            left.join(&unknown(None), 0, CauseId(0)).option_identity,
            None
        );
        assert_eq!(
            unknown(None)
                .join(&unknown(None), 0, CauseId(0))
                .option_identity,
            None
        );
    }

    #[test]
    fn projected_optional_views_cannot_replace_their_original_tag_payload_identity() {
        use crate::hir::nodes::ExprKind;
        use crate::sema::validate::{ValidationIssueKind, solved_facts};
        for target in ["pointer32", "pointer64"] {
            let source = ril_test::case_source(
                "tests/regressions/projection-views.ril::optional-child-views-pointer64",
            );
            let program = crate::Session::with_options(
                source.as_bytes().to_vec(),
                crate::CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|error| panic!("{target}: {error:?}"));
            let facts = program.facts();
            let hir = facts.semantic_hir.as_deref().unwrap();
            let (projection, identity) = facts
                .expressions
                .iter()
                .enumerate()
                .find_map(|(index, expression)| {
                    let source = expression.source_id?;
                    if !matches!(
                        hir.expression(source)?.kind,
                        ExprKind::Field { .. } | ExprKind::Index { .. }
                    ) {
                        return None;
                    }
                    let Ty::Optional(inner) = &expression.value.ty else {
                        return None;
                    };
                    matches!(&**inner, Ty::Named(_))
                        .then_some((index, expression.value.option_identity?))
                })
                .expect("a real projection must retain its declared optional child");
            let expanded = Ty::Record([("id".into(), (false, Ty::Int("int".into())))].into());
            for mutation in 0..5 {
                let mut changed = facts.clone();
                match mutation {
                    0 => {
                        changed.expressions[projection]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .ty = Ty::Optional(Box::new(expanded.clone()));
                    }
                    1 => {
                        changed.expressions[projection]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .option_payload
                            .as_mut()
                            .unwrap()
                            .ty = expanded.clone();
                    }
                    2 => changed.optional_tags[identity.0 as usize].payload_type = expanded.clone(),
                    3 => {
                        changed.expressions[projection]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .option_identity = Some(OptionalTagId(u32::MAX));
                    }
                    _ => changed.optional_tags[identity.0 as usize].id = OptionalTagId(u32::MAX),
                }
                let issues = solved_facts(&changed).expect_err("a changed tag must be rejected");
                assert!(
                    issues.iter().any(|issue| matches!(
                        issue.kind,
                        ValidationIssueKind::InvalidOptionalTag(..)
                    )),
                    "{target} mutation {mutation}: {issues:?}"
                );
            }
        }
    }
}
