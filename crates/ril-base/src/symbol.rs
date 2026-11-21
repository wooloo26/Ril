use std::{collections::HashMap, sync::Arc};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Symbol(usize);

#[derive(Default)]
pub struct Interner {
    ids: HashMap<Arc<str>, Symbol>,
    strings: Vec<Arc<str>>,
}

impl Interner {
    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = Symbol(self.strings.len());
        let name: Arc<str> = name.into();
        self.strings.push(Arc::clone(&name));
        self.ids.insert(name, id);
        id
    }

    pub fn resolve(&self, symbol: Symbol) -> Option<&str> {
        self.strings.get(symbol.0).map(AsRef::as_ref)
    }
}
