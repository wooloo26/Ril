//! Join the storage cells installed by the first matching binding alternative.
use super::*;

impl Emitter<'_, '_> {
    pub(super) fn bind_alternative(
        &mut self,
        patterns: &[Pattern],
        value: Value,
    ) -> Result<(), BackendError> {
        let Some(first) = patterns.first() else {
            return Err(BackendError::InvalidIr("empty binding alternative".into()));
        };
        let mut bindings = BTreeSet::new();
        names(first, &mut bindings);
        for pattern in &patterns[1..] {
            let mut alternative = BTreeSet::new();
            names(pattern, &mut alternative);
            if alternative != bindings {
                return Err(BackendError::InvalidIr(
                    "binding alternatives have different names".into(),
                ));
            }
        }
        let joined = self.builder.create_block();
        for _ in &bindings {
            self.builder.append_block_param(joined, types::I64);
        }
        let saved = self.locals.clone();
        let pending = self.pending.clone();
        for pattern in patterns {
            let accepted = self.builder.create_block();
            let next = self.builder.create_block();
            let matched = self.pattern_test(pattern, value, true)?;
            self.builder.ins().brif(matched, accepted, &[], next, &[]);
            self.switch(accepted);
            self.bind(pattern, value)?;
            let cells = bindings
                .iter()
                .map(|name| self.locals[name].into())
                .collect::<Vec<_>>();
            self.builder.ins().jump(joined, &cells);
            self.locals = saved.clone();
            self.pending = pending.clone();
            self.switch(next);
        }
        // The enclosing match already established success. Keep malformed
        // public IR from continuing with missing or uninitialized storage.
        let message = self.string("nonmatching native binding alternative")?;
        let arguments = self.sequence(1, &[message])?;
        let panic = self.string("panic")?;
        self.handle("ril_rt_builtin", &[panic, arguments])?;
        self.builder.ins().jump(self.failure, &[]);
        self.switch(joined);
        for (index, name) in bindings.into_iter().enumerate() {
            self.locals
                .insert(name.clone(), self.builder.block_params(joined)[index]);
            self.pending.remove(&name);
        }
        Ok(())
    }
}
