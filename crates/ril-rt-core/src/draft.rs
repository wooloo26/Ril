use crate::{GcRuntime, Object, Value};

impl GcRuntime {
    pub fn draft_begin(&mut self, base: Value) -> Result<Value, &'static str> {
        let copy = self.clone_graph(base)?;
        Ok(self.alloc(Object::Draft { copy }))
    }

    pub fn draft_read(&self, draft: Value) -> Result<Value, &'static str> {
        match self.object(draft) {
            Some(Object::Draft { copy }) => Ok(*copy),
            _ => Err("invalid draft"),
        }
    }

    pub fn draft_write(&mut self, draft: Value, value: Value) -> Result<(), &'static str> {
        match self.object_mut(draft) {
            Some(Object::Draft { copy }) => {
                *copy = value;
                Ok(())
            }
            _ => Err("invalid draft"),
        }
    }

    pub fn draft_commit(&mut self, draft: Value) -> Result<Value, &'static str> {
        let copy = self.draft_read(draft)?;
        self.draft_abort(draft)?;
        Ok(copy)
    }

    pub fn draft_abort(&mut self, draft: Value) -> Result<(), &'static str> {
        match self.object_mut(draft) {
            Some(slot @ Object::Draft { .. }) => {
                *slot = Object::Array(Vec::new());
                Ok(())
            }
            _ => Err("invalid draft"),
        }
    }
}
