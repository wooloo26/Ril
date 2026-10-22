//! Owned type/source interpretation. Entering another callable replaces one
//! complete environment; its lexical contracts cannot be restored piecemeal.
use crate::sema::clone_work;
use crate::sema::context::{FrozenEnvironment, TypingEnvironment};
use crate::sema::model::Env;
use std::cell::{Cell, RefCell};

pub(super) struct TypeSourceDomain {
    pub environment: TypingEnvironment,
    pub storage: super::storage_sources::State,
    lexical: RefCell<Option<crate::hir::lexical::LexicalBindings>>,
    work: Cell<usize>,
    pub exhausted: Cell<bool>,
}

impl Default for TypeSourceDomain {
    fn default() -> Self {
        Self {
            environment: Default::default(),
            storage: Default::default(),
            lexical: RefCell::new(None),
            work: Cell::new(16 * 1024 * 1024),
            exhausted: Cell::new(false),
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
    fn admit_clone(&self, environment: &TypingEnvironment) -> bool {
        if self.exhausted.get() {
            return false;
        }
        let mut work = self.work.get();
        let admitted = clone_work::environment(environment, &mut work).is_some();
        self.work.set(work);
        if !admitted {
            self.exhausted.set(true);
        }
        admitted
    }

    pub(super) fn capture(&self) -> FrozenEnvironment {
        if !self.admit_clone(&self.environment) {
            return FrozenEnvironment::poisoned();
        }
        self.environment.clone().freeze()
    }

    pub(super) fn copy_environment(
        &self,
        environment: &FrozenEnvironment,
    ) -> Option<TypingEnvironment> {
        if environment.is_poisoned() {
            self.exhausted.set(true);
            return None;
        }
        self.admit_clone(environment).then(|| environment.thaw())
    }

    fn replace_bindings(
        &self,
        mut environment: TypingEnvironment,
        bindings: &Env,
    ) -> FrozenEnvironment {
        let mut work = self.work.get();
        let admitted = !self.exhausted.get() && clone_work::bindings(bindings, &mut work).is_some();
        self.work.set(work);
        if !admitted {
            self.exhausted.set(true);
            return FrozenEnvironment::poisoned();
        }
        environment.contract_bindings = bindings.clone();
        environment.freeze()
    }

    pub(super) fn capture_with_bindings(&self, bindings: &Env) -> FrozenEnvironment {
        if !self.admit_clone(&self.environment) {
            return FrozenEnvironment::poisoned();
        }
        self.replace_bindings(self.environment.clone(), bindings)
    }

    pub(super) fn derive_environment(
        &self,
        environment: &FrozenEnvironment,
        bindings: &Env,
    ) -> FrozenEnvironment {
        let Some(environment) = self.copy_environment(environment) else {
            return FrozenEnvironment::poisoned();
        };
        self.replace_bindings(environment, bindings)
    }

    pub(super) fn restore(&mut self, environment: FrozenEnvironment) {
        if environment.is_poisoned() || (environment.is_shared() && !self.admit_clone(&environment))
        {
            self.exhausted.set(true);
            self.environment = TypingEnvironment::default();
            return;
        }
        self.environment = environment.into_typing_environment();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::model::Ty;

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
