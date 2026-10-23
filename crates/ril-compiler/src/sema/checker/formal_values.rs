//! Symbolic data inputs retain all constructor payloads and their conditional
//! duties. They describe declaration assumptions, never local allocations.
use super::*;

impl Checker {
    pub(super) fn formal_optional_graph(
        &mut self,
        ty: Ty,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) -> Value {
        let Ty::Optional(inner) = &ty else {
            return Value::scalar(
                ty,
                None,
                self.cause(CauseKind::Source, span, "unresolved optional input", []),
            );
        };
        if seen.len() >= 64 || !seen.insert(format!("incoming-optional:{ty:?}")) {
            let cause = self.cause(
                CauseKind::Source,
                span,
                "incomplete recursive optional input",
                [],
            );
            let mut value = if ty.scalar() {
                Value::scalar(ty, None, cause)
            } else {
                let node =
                    self.heap
                        .symbolic(Pivot(self.heap.nodes.len() as u32), ScopeId(0), cause);
                let mut value = Value::reference(ty, node, cause);
                value.permission = Permission::Read;
                value.publication = Publication::Live;
                value
            };
            value.construction = false;
            return value;
        }
        let payload = self.formal_value(*inner.clone(), index, span, seen);
        let mut value = self.standard_option(payload, None, span, ScopeId(u32::MAX));
        if seen.contains("\0optional-member-family") {
            value.option_identity = None;
        }
        value.ty = ty;
        value
    }

    pub(super) fn new_optional_identity(
        &mut self,
        payload_type: Ty,
        cause: CauseId,
        owner: ScopeId,
        span: Span,
    ) -> Option<ril_compiler_core::ids::OptionalTagId> {
        if self.optional_tags.len() >= 4096 {
            self.unsupported(span, "optional constructor identity work bound exceeded");
            return None;
        }
        let id = ril_compiler_core::ids::OptionalTagId(self.optional_tags.len() as u32);
        self.optional_tags
            .push(crate::sema::optional_tags::OptionalTagFact {
                id,
                creation_owner: owner,
                cause,
                payload_type,
            });
        Some(id)
    }

    pub(super) fn formal_result_graph(
        &mut self,
        ty: Ty,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) -> Value {
        let value = self.formal_result(ty.clone(), span);
        let Ty::Result(ok, error) = &ty else {
            return value;
        };
        if seen.len() > 128
            || !seen.insert(format!("incoming-result:{ty:?}"))
            || !self.application_effect.admit(4)
        {
            self.unsupported(
                span,
                "symbolic Result graph exceeds its construction work bound",
            );
            return value;
        }
        let success = self.formal_value(
            *ok.clone(),
            index.wrapping_mul(31).wrapping_add(1),
            span,
            &mut seen.clone(),
        );
        let failure = self.formal_value(
            *error.clone(),
            index.wrapping_mul(31).wrapping_add(2),
            span,
            &mut seen.clone(),
        );
        let admitted: Result<(), crate::sema::source_types::SourceTypesError> =
            self.application_effect.with_work(|work| {
                // Join owns copies of both finite payload trees. Charge their
                // traversal/copying before creating the carrier, including work
                // which a later validation failure will not refund.
                for _ in 0..4 {
                    crate::sema::evaluated::charge_value_export(&success, work)?;
                    crate::sema::evaluated::charge_value_export(&failure, work)?;
                }
                Ok(())
            });
        if let Err(error) = admitted {
            self.unsupported(
                span,
                format!("symbolic Result payload copying failed: {error}"),
            );
            return value;
        }
        let branch = self.choice();
        let joined = success.join(&failure, branch, value.cause);
        let producer = *value
            .outer_results
            .iter()
            .next()
            .expect("incoming Result duty");
        let mut value = Self::result_carrier(joined, ty, value.cause, producer);
        value.permission = Permission::Read;
        value.construction = false;
        if !value.origins.nodes.is_empty() {
            value.publication = Publication::Live;
        }
        value.result_success = Some(Box::new(success));
        value.result_error = Some(Box::new(failure));
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbolic_result_payloads_retain_reachable_storage_and_conditional_duties() {
        let mut checker = Checker::new(FileId(0));
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 1,
        };
        let payload = Ty::Record(
            [
                ("opaque".into(), (false, Ty::Generic("owner:T".into()))),
                (
                    "callback".into(),
                    (false, Ty::Callable(vec![], Box::new(Ty::Unit))),
                ),
                ("file".into(), (false, Ty::Named("File::Handle".into()))),
                (
                    "nested".into(),
                    (
                        false,
                        Ty::Result(Box::new(Ty::Int("int".into())), Box::new(Ty::Str)),
                    ),
                ),
            ]
            .into(),
        );
        let value = checker.formal_value(
            Ty::Result(Box::new(payload), Box::new(Ty::Str)),
            0,
            span,
            &mut BTreeSet::new(),
        );
        let success = value.result_success.as_ref().unwrap();
        let error = value.result_error.as_ref().unwrap();
        assert_eq!(
            value.origins.nodes,
            success
                .origins
                .nodes
                .union(&error.origins.nodes)
                .copied()
                .collect()
        );
        let root = *success.origins.nodes.first().unwrap();
        let nested = &checker.fields[&(root, Slot::Field("nested".into()))];
        assert!(!nested.must_results.is_empty());
        assert!(nested.must_results.is_subset(&value.results));
        assert!(nested.must_results.is_disjoint(&value.must_results));
        assert_eq!(value.must_results, value.outer_results);
        assert!(value.result_payload.is_none() && value.result_tag.is_none());
        assert_eq!(value.permission, Permission::Read);
        let reachable = checker.heap.reachable(value.origins.nodes.iter().copied());
        for name in ["opaque", "callback", "file"] {
            let child = &checker.fields[&(root, Slot::Field(name.into()))];
            assert!(!child.origins.nodes.is_empty());
            assert!(child.origins.nodes.is_subset(&reachable));
        }
    }
}
