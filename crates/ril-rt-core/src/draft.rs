use crate::{GcRuntime, Object, Value};

#[derive(PartialEq, Eq)]
pub(crate) enum DraftSlot {
    Field(String),
    Element(usize),
    MapValue(usize),
}

impl DraftSlot {
    fn value_mut<'a>(&self, object: &'a mut Object) -> Option<&'a mut Value> {
        match (self, object) {
            (Self::Field(key), Object::Record(values)) => values.get_mut(key),
            (
                Self::Element(index),
                Object::Array(values) | Object::Tuple(values) | Object::Tag(_, values),
            ) => values.get_mut(*index),
            (Self::MapValue(index), Object::Map(entries)) => {
                entries.get_mut(*index).map(|(_, value)| value)
            }
            _ => None,
        }
    }
}

pub(crate) struct DraftNode {
    pub(crate) draft: Value,
    incoming: Option<(Value, DraftSlot)>,
}

impl GcRuntime {
    pub fn draft_begin(&mut self, base: Value) -> Result<Value, &'static str> {
        let copy = self
            .copy_draft_node(base)
            .ok_or("draft needs a shared object")?;
        let draft = self.alloc(Object::Draft { copy });
        self.mark_draft_root(draft, copy);
        Ok(draft)
    }

    pub fn draft_read(&self, draft: Value) -> Result<Value, &'static str> {
        match self.object(draft) {
            Some(Object::Draft { copy }) => Ok(*copy),
            _ => Err("invalid draft"),
        }
    }

    pub fn draft_write(&mut self, draft: Value, value: Value) -> Result<(), &'static str> {
        self.draft_read(draft)?;
        self.pin(draft);
        let copy = self.copy_draft_node(value);
        self.unpin(draft);
        let copy = copy.ok_or("draft needs a shared object")?;
        let Some(Object::Draft { copy: root }) = self.object_mut(draft) else {
            return Err("invalid draft");
        };
        *root = copy;
        self.mark_draft_root(draft, copy);
        Ok(())
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
                self.draft_nodes.retain(|_, node| node.draft != draft);
                Ok(())
            }
            _ => Err("invalid draft"),
        }
    }

    pub(crate) fn draft_child(
        &mut self,
        parent: Value,
        slot: DraftSlot,
        child: Value,
    ) -> Option<Value> {
        let Some(draft) = self.draft_nodes.get(&parent).map(|node| node.draft) else {
            return Some(child);
        };
        if self.draft_nodes.get(&child).is_some_and(|node| {
            node.draft == draft
                && node
                    .incoming
                    .as_ref()
                    .is_some_and(|(source, key)| *source == parent && *key == slot)
        }) {
            return Some(child);
        }
        // Each inspected edge gets its own shallow copy. Even through a cycle,
        // the remainder of the path can still share the original snapshot.
        self.pin(draft);
        self.pin(parent);
        let copy = self.copy_draft_node(child);
        self.unpin(parent);
        self.unpin(draft);
        let Some(copy) = copy else {
            return Some(child);
        };
        *slot.value_mut(self.object_mut(parent)?)? = copy;
        self.draft_nodes.insert(
            copy,
            DraftNode {
                draft,
                incoming: Some((parent, slot)),
            },
        );
        Some(copy)
    }

    pub(crate) fn draft_insertion(
        &mut self,
        target: Value,
        value: Value,
    ) -> Result<Value, &'static str> {
        if self.draft_nodes.contains_key(&target) && self.draft_nodes.contains_key(&value) {
            // A live working draft value used as data must retain the contents
            // it had at insertion, even if its source path is edited later.
            self.clone_graph(value)
        } else {
            Ok(value)
        }
    }

    fn mark_draft_root(&mut self, draft: Value, copy: Value) {
        self.draft_nodes.insert(
            copy,
            DraftNode {
                draft,
                incoming: None,
            },
        );
    }

    fn copy_draft_node(&mut self, value: Value) -> Option<Value> {
        match self.object(value)? {
            object @ (Object::Array(_)
            | Object::Tuple(_)
            | Object::Record(_)
            | Object::Map(_)
            | Object::Tag(..)) => Some(self.alloc(object.clone())),
            _ => None,
        }
    }
}
