//! Owned type/source interpretation. Entering another callable replaces one
//! complete environment; its lexical contracts cannot be restored piecemeal.
use crate::sema::clone_work;
use crate::sema::context::{FrozenEnvironment, TypingEnvironment};
use crate::sema::context::{FrozenStaticEnvironment, StaticEnvironment};
use crate::sema::model::Env;
use std::cell::{Cell, RefCell};
use std::sync::Weak;

pub(super) struct TypeSourceDomain {
    pub environment: TypingEnvironment,
    pub storage: super::storage_sources::State,
    lexical: RefCell<Option<crate::hir::lexical::LexicalBindings>>,
    work: Cell<usize>,
    pub exhausted: Cell<bool>,
    static_capture: RefCell<Option<Weak<FrozenStaticEnvironment>>>,
}

impl Default for TypeSourceDomain {
    fn default() -> Self {
        Self {
            environment: Default::default(),
            storage: Default::default(),
            lexical: RefCell::new(None),
            work: Cell::new(16 * 1024 * 1024),
            exhausted: Cell::new(false),
            static_capture: RefCell::new(None),
        }
    }
}

impl TypeSourceDomain {
    /// Original HIR replacement invalidates only derived name lookup. Frozen
    /// declaration environments and observed Source graphs remain untouched.
    pub(super) fn reset_header_queries(&self) {
        *self.lexical.borrow_mut() = None;
    }

    pub(super) fn with_header_index<R>(
        &self,
        hir: &crate::hir::HirProgram,
        query: impl FnOnce(
            &crate::hir::lexical::LexicalBindings,
        ) -> Result<R, crate::sema::source_types::SourceTypesError>,
    ) -> Result<R, crate::sema::source_types::SourceTypesError> {
        use crate::sema::source_types::SourceTypesError;
        if self.exhausted.get() {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let mut index = self.lexical.borrow_mut();
        let mut remaining = self.work.get();
        let admitted = match index.as_mut() {
            Some(index) => index.refresh_generated(hir, &mut remaining),
            None => crate::hir::lexical::LexicalBindings::new(hir, &mut remaining)
                .map(|new| *index = Some(new)),
        };
        self.work.set(remaining);
        if let Err(error) = admitted {
            *index = None;
            return Err(match error {
                crate::hir::nodes::LowerError::Budget(_) => {
                    self.exhausted.set(true);
                    SourceTypesError::BudgetExceeded
                }
                _ => SourceTypesError::Unresolved,
            });
        }
        query(index.as_ref().ok_or(SourceTypesError::MissingNode)?)
    }
    fn admit_clone(&self, environment: &StaticEnvironment, bindings: &Env) -> bool {
        if self.exhausted.get() {
            return false;
        }
        let mut work = self.work.get();
        let admitted = clone_work::static_environment(environment, &mut work)
            .and_then(|()| clone_work::bindings(bindings, &mut work))
            .is_some();
        self.work.set(work);
        if !admitted {
            self.exhausted.set(true);
        }
        admitted
    }

    pub(super) fn capture(&self) -> FrozenEnvironment {
        if !self.admit_clone(&self.environment, self.environment.contract_bindings()) {
            return FrozenEnvironment::poisoned();
        }
        let previous = self
            .static_capture
            .borrow()
            .as_ref()
            .and_then(Weak::upgrade);
        let capture = self.environment.clone().freeze_reusing_types(previous);
        *self.static_capture.borrow_mut() = Some(capture.weak_types());
        capture
    }

    pub(super) fn copy_environment(
        &self,
        environment: &FrozenEnvironment,
    ) -> Option<TypingEnvironment> {
        if environment.is_poisoned() {
            self.exhausted.set(true);
            return None;
        }
        self.admit_clone(environment, environment.contract_bindings())
            .then(|| environment.thaw())
    }

    fn replace_bindings(
        &self,
        environment: FrozenEnvironment,
        bindings: &Env,
    ) -> FrozenEnvironment {
        let mut work = self.work.get();
        let admitted = !self.exhausted.get() && clone_work::bindings(bindings, &mut work).is_some();
        self.work.set(work);
        if !admitted {
            self.exhausted.set(true);
            return FrozenEnvironment::poisoned();
        }
        environment.with_contract_bindings(bindings.clone())
    }

    pub(super) fn capture_with_bindings(&self, bindings: &Env) -> FrozenEnvironment {
        self.replace_bindings(self.capture(), bindings)
    }

    pub(super) fn derive_environment(
        &self,
        environment: &FrozenEnvironment,
        bindings: &Env,
    ) -> FrozenEnvironment {
        if environment.is_poisoned() {
            self.exhausted.set(true);
            return FrozenEnvironment::poisoned();
        }
        if !self.admit_clone(environment, environment.contract_bindings()) {
            return FrozenEnvironment::poisoned();
        }
        self.replace_bindings(environment.clone(), bindings)
    }

    pub(super) fn restore(&mut self, environment: FrozenEnvironment) {
        if environment.is_poisoned()
            || (environment.is_shared()
                && !self.admit_clone(&environment, environment.contract_bindings()))
        {
            self.exhausted.set(true);
            self.environment = TypingEnvironment::default();
            *self.static_capture.borrow_mut() = None;
            return;
        }
        *self.static_capture.borrow_mut() = Some(environment.weak_types());
        self.environment = environment.into_typing_environment();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::model::Ty;

    #[test]
    fn captures_share_static_data_only_while_the_complete_selection_is_unchanged() {
        use crate::sema::{model::SourceTypeWitness, source_types::TypeSourceSelection};
        use ril_syntax::ast::StmtKind;
        use std::sync::Arc;
        let mut domain = TypeSourceDomain::default();
        domain
            .environment
            .generic_context
            .insert("T".into(), "decl:T".into());
        let first = domain.capture();
        domain
            .environment
            .contract_bindings
            .insert("value".into(), 7);
        let bound = domain.capture();
        assert_ne!(first.id(), bound.id());
        assert!(first.same_types(&bound));
        assert!(first.contract_bindings().is_empty());
        assert_eq!(bound.contract_bindings().get("value"), Some(&7));

        let array = Ty::Array(Box::new(Ty::Int("int".into())));
        domain
            .environment
            .generic_substitutions
            .insert("decl:T".into(), array);
        let erased = domain.capture();
        assert!(
            !erased.same_types(&domain.capture()),
            "erased Ty equality cannot merge selections"
        );
        let select = |length: u64| {
            let parsed = ril_syntax::parse(&format!("type Chosen=[{length}]int"));
            let StmtKind::Type(declaration) = &parsed.program.statements[0].kind else {
                panic!()
            };
            let syntax = declaration.value.clone().unwrap();
            TypeSourceSelection::from_closed(
                Arc::new(SourceTypeWitness {
                    key: crate::static_eval::normalized_argument_key(&syntax),
                    syntax,
                }),
                FrozenEnvironment::default(),
            )
            .unwrap()
        };
        domain
            .environment
            .generic_sources
            .insert("decl:T".into(), select(2));
        let two = domain.capture();
        domain
            .environment
            .contract_bindings
            .insert("other".into(), 8);
        assert!(two.same_types(&domain.capture()));
        domain
            .environment
            .generic_sources
            .insert("decl:T".into(), select(3));
        let three = domain.capture();
        assert_eq!(two.generic_substitutions, three.generic_substitutions);
        assert!(
            !two.same_types(&three),
            "distinct inner coordinates shared a static interpretation"
        );
        let id = ril_compiler_core::ids::BoundRowId(0);
        let choice = Arc::new(crate::sema::record_bounds::BoundRowSelection {
            row: id,
            remainder: crate::sema::model::rows::Row::closed(
                [(
                    "items".into(),
                    (false, Ty::Array(Box::new(Ty::Int("int".into())))),
                )]
                .into(),
            ),
            fields: vec![],
            source_type_witness: None,
        });
        domain
            .environment
            .bound_row_selections
            .insert(id, choice.clone());
        let chosen = domain.capture();
        assert!(chosen.same_types(&domain.capture()));
        domain
            .environment
            .bound_row_selections
            .insert(id, Arc::new((*choice).clone()));
        let other = domain.capture();
        assert_eq!(chosen.bound_row_selections, other.bound_row_selections);
        assert_ne!(
            chosen, other,
            "frozen equality collapsed two unproved row choices"
        );
        assert!(
            !chosen.same_types(&other),
            "erased row views identified two unproved choices"
        );
    }

    #[test]
    fn header_name_index_is_paid_once_and_queries_keep_their_own_budget() {
        use crate::hir::{lexical::TypeNameBinding, nodes::StmtKind};
        use crate::sema::source_types::SourceTypesError;
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::shadowed-alias-pattern-safe",
        ));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir = crate::hir::HirProgram::lower_identified(
            &mut program,
            crate::hir::nodes::InputOrigin::Source,
        )
        .unwrap();
        let syntax = hir
            .statements()
            .find_map(|(_, statement)| match &statement.kind {
                StmtKind::Function(function) if function.name == "matches_local" => {
                    function.parameters[0].ty
                }
                _ => None,
            })
            .unwrap();
        let domain = TypeSourceDomain::default();
        let query = |index: &crate::hir::lexical::LexicalBindings| {
            index
                .lookup_type(syntax, &mut 4096)
                .map_err(|_| SourceTypesError::Unresolved)
        };
        let original = domain.with_header_index(&hir, query).unwrap();
        assert!(matches!(original, TypeNameBinding::Declaration(_)));
        let remaining = domain.work.get();
        assert!(remaining < 16 * 1024 * 1024);
        // A single remaining domain unit admits the unchanged index lookup;
        // it cannot possibly rewalk this complete original program.
        domain.work.set(1);
        assert_eq!(domain.with_header_index(&hir, query).unwrap(), original);
        assert_eq!(domain.work.get(), 0);
        assert!(matches!(
            domain.with_header_index(&hir, query),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(domain.exhausted.get());
        domain.reset_header_queries();
        assert!(matches!(
            domain.with_header_index(&hir, query),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn replacing_original_header_input_requires_fresh_index_admission() {
        use crate::sema::source_types::SourceTypesError;
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::deferred-arithmetic-safe",
        ));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir = crate::hir::HirProgram::lower_identified(
            &mut program,
            crate::hir::nodes::InputOrigin::Source,
        )
        .unwrap();
        let domain = TypeSourceDomain::default();
        domain.with_header_index(&hir, |_| Ok(())).unwrap();
        domain.reset_header_queries();
        domain.work.set(0);
        assert!(matches!(
            domain.with_header_index(&hir, |_| Ok(())),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn nested_type_capture_is_rejected_before_copying_an_exhausted_environment() {
        let mut domain = TypeSourceDomain::default();
        domain.work.set(8);
        let mut value = Ty::Int("int".into());
        for _ in 0..64 {
            value = Ty::Array(Box::new(value));
        }
        domain
            .environment
            .generic_substitutions
            .insert("decl:T".into(), value);
        let captured = domain.capture();
        assert!(captured.is_poisoned());
        assert!(domain.exhausted.get());
        assert!(captured.generic_substitutions.is_empty());
        assert!(
            domain
                .environment
                .generic_substitutions
                .contains_key("decl:T")
        );
        assert!(
            captured
                .with_contract_bindings(Default::default())
                .is_poisoned()
        );
    }

    #[test]
    fn shared_restore_requires_clone_admission_and_failure_cannot_be_reset() {
        let mut domain = TypeSourceDomain::default();
        domain.work.set(2);
        let captured = domain.capture();
        assert!(!captured.is_poisoned());
        assert_eq!(domain.work.get(), 0);
        domain.restore(captured.clone());
        assert!(domain.exhausted.get());
        assert!(!captured.is_poisoned());
        domain.restore(TypingEnvironment::default().freeze());
        assert!(domain.exhausted.get());
        assert!(domain.capture().is_poisoned());
    }

    #[test]
    fn uniquely_owned_restore_moves_without_requiring_an_owned_copy() {
        let mut domain = TypeSourceDomain::default();
        domain.work.set(2);
        let captured = domain.capture();
        domain.restore(captured);
        assert!(!domain.exhausted.get());
        assert_eq!(domain.work.get(), 0);
    }
}
