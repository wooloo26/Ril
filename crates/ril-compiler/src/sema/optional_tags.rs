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
}
