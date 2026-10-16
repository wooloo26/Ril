//! The only entry/restore boundary for a complete captured typing environment.
//! Active mutable tables remain an implementation detail during domain migration.
use super::*;
use crate::sema::context::{FrozenEnvironment, TypingEnvironment};

impl Checker {
    pub(super) fn capture_typing_environment(&self) -> FrozenEnvironment {
        TypingEnvironment {
            generic_context: self.generic_context.clone(),
            generic_substitutions: self.generic_substitutions.clone(),
            generic_type_witnesses: self.generic_type_witnesses.clone(),
            static_key_arguments: self.static_key_arguments.clone(),
            bound_row_context: self.bound_row_context.clone(),
            bound_row_selections: self.bound_row_selections.clone(),
            contract_bindings: self.contract_environment.clone(),
        }
        .freeze()
    }

    pub(super) fn restore_typing_environment(&mut self, environment: FrozenEnvironment) {
        let environment = environment.into_typing_environment();
        self.generic_context = environment.generic_context;
        self.generic_substitutions = environment.generic_substitutions;
        self.generic_type_witnesses = environment.generic_type_witnesses;
        self.static_key_arguments = environment.static_key_arguments;
        self.bound_row_context = environment.bound_row_context;
        self.bound_row_selections = environment.bound_row_selections;
        self.contract_environment = environment.contract_bindings;
    }

    pub(super) fn enter_typing_environment(
        &mut self,
        environment: &FrozenEnvironment,
    ) -> FrozenEnvironment {
        let previous = self.capture_typing_environment();
        self.restore_typing_environment(environment.clone());
        previous
    }

    pub(super) fn with_typing_environment<R>(
        &mut self,
        environment: &FrozenEnvironment,
        query: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let previous = self.enter_typing_environment(environment);
        let result = query(self);
        self.restore_typing_environment(previous);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::model::rows::{Row, RowTail};
    use ril_compiler_core::ids::BoundRowId;

    fn environment(identity: &str, selected: Ty, key: &str) -> FrozenEnvironment {
        TypingEnvironment {
            generic_context: [("T".into(), identity.into())].into(),
            generic_substitutions: [(identity.into(), selected)].into(),
            generic_type_witnesses: BTreeMap::new(),
            static_key_arguments: [("selected-key".into(), StaticCoordinate::Label(key.into()))]
                .into(),
            bound_row_context: [("R".into(), BoundRowId(1))].into(),
            bound_row_selections: [(
                BoundRowId(1),
                crate::sema::record_bounds::BoundRowSelection {
                    row: BoundRowId(1),
                    remainder: Row {
                        fields: BTreeMap::new(),
                        tail: RowTail::Closed,
                    },
                    fields: vec![],
                    source_type_witness: None,
                },
            )]
            .into(),
            contract_bindings: [(key.into(), 7)].into(),
        }
        .freeze()
    }

    #[test]
    fn nested_queries_and_early_errors_restore_the_entire_interpretation() {
        let mut checker = Checker::new(FileId(0));
        let caller = environment("caller:T", Ty::Str, "caller");
        let callee = environment("callee:T", Ty::Int("int".into()), "callee");
        checker.restore_typing_environment(caller.clone());
        let syntax = TypeExpr {
            text: "T".into(),
            kind: TypeKind::Name {
                path: vec!["T".into()],
                arguments: vec![],
            },
            span: Span {
                file: FileId(0),
                start: 0,
                end: 1,
            },
        };
        let result: Result<(), ()> = checker.with_typing_environment(&callee, |checker| {
            assert_eq!(checker.ty(&syntax), Ty::Int("int".into()));
            let empty = FrozenEnvironment::default();
            checker.with_typing_environment(&empty, |checker| {
                assert!(checker.generic_context.is_empty());
                assert!(checker.generic_substitutions.is_empty());
                assert!(checker.static_key_arguments.is_empty());
                assert!(checker.bound_row_selections.is_empty());
                assert!(checker.contract_environment.is_empty());
            });
            assert_eq!(checker.capture_typing_environment(), callee);
            Err(())
        });
        assert_eq!(result, Err(()));
        assert_eq!(checker.ty(&syntax), Ty::Str);
        assert_eq!(checker.capture_typing_environment(), caller);
    }

    #[test]
    fn completing_a_declaration_scope_derives_a_new_capture() {
        let original = environment("creator:T", Ty::Str, "original");
        let completed = original.with_contract_bindings([("completed".into(), 19)].into());
        assert_eq!(original.contract_bindings.get("original"), Some(&7));
        assert!(!original.contract_bindings.contains_key("completed"));
        assert_eq!(completed.generic_context, original.generic_context);
        assert_eq!(
            completed.static_key_arguments,
            original.static_key_arguments
        );
        assert_eq!(completed.contract_bindings.get("completed"), Some(&19));
    }
}
