//! Owned type/source interpretation. Entering another callable replaces one
//! complete environment; its lexical contracts cannot be restored piecemeal.
use crate::sema::clone_work;
use crate::sema::context::{FrozenEnvironment, TypingEnvironment};
use crate::sema::model::Env;
use std::cell::Cell;

pub(super) struct TypeSourceDomain {
    pub environment: TypingEnvironment,
    pub storage: super::storage_sources::State,
    work: Cell<usize>,
    pub exhausted: Cell<bool>,
}

impl Default for TypeSourceDomain {
    fn default() -> Self {
        Self {
            environment: Default::default(),
            storage: Default::default(),
            work: Cell::new(16 * 1024 * 1024),
            exhausted: Cell::new(false),
        }
    }
}

impl TypeSourceDomain {
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
