use std::{
    cmp::Ordering,
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
    num::NonZeroU32,
    sync::{OnceLock, RwLock},
};

/// A compact, 4-byte interned identifier with niche optimization (`Option<Symbol>` is 4 bytes).
///
/// Intentionally does not implement `Ord` so callers never accidentally sort or hash
/// symbols by non-deterministic interning order; use [`cmp_str`] or [`Interner::cmp`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Symbol(NonZeroU32);

impl Symbol {
    pub const fn as_u32(self) -> u32 {
        self.0.get()
    }
}

/// Pre-interned language keywords, primitive types, and common standard-library names.
pub const PREINTERNED: &[&str] = &[
    // 29 keywords & contextual keywords
    "let", "var", "mut", "ref", "new", "via", "infer", "fn", "meta", "type", "opaque", "sub", "eff",
    "with", "use", "where", "if", "else", "match", "while", "for", "as", "in", "return", "break",
    "continue", "pub", "pkg", "true", "false", "typeof", "clone", "derive",
    "inner", // 6 primitive types & never
    "bool", "int", "f64", "str", "bytes", "never", // Common stdlib names
    "Option", "Some", "None", "Result", "Ok", "Err", "String", "Array", "Map", "Set", "Fiber",
    "Channel", "Draft", "Type", "Super", "Self", "main", "println", "len", "assert", "panic",
    "inspect",
];

fn hash_str(text: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    text.hash(&mut hasher);
    hasher.finish()
}

/// Arena-backed string interner using a single contiguous UTF-8 text buffer.
pub struct Interner {
    buffer: String,
    spans: Vec<(u32, u32)>,
    buckets: HashMap<u64, Vec<Symbol>>,
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

impl Interner {
    pub fn new() -> Self {
        let mut interner = Self {
            buffer: String::with_capacity(1024),
            spans: Vec::with_capacity(128),
            buckets: HashMap::with_capacity(128),
        };
        for &word in PREINTERNED {
            let _ = interner.intern(word);
        }
        interner
    }

    pub fn intern(&mut self, name: &str) -> Symbol {
        let hash = hash_str(name);
        if let Some(candidates) = self.buckets.get(&hash) {
            for &sym in candidates {
                if self.resolve(sym) == Some(name) {
                    return sym;
                }
            }
        }
        let start = u32::try_from(self.buffer.len()).unwrap_or(u32::MAX);
        self.buffer.push_str(name);
        let end = u32::try_from(self.buffer.len()).unwrap_or(u32::MAX);
        self.spans.push((start, end));
        let raw = u32::try_from(self.spans.len()).unwrap_or(u32::MAX);
        let sym = Symbol(NonZeroU32::new(raw).unwrap_or(NonZeroU32::MIN));
        self.buckets.entry(hash).or_default().push(sym);
        sym
    }

    pub fn resolve(&self, symbol: Symbol) -> Option<&str> {
        let idx = usize::try_from(symbol.0.get().checked_sub(1)?).ok()?;
        let &(start, end) = self.spans.get(idx)?;
        self.buffer.get(start as usize..end as usize)
    }

    pub fn cmp(&self, a: Symbol, b: Symbol) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        self.resolve(a).cmp(&self.resolve(b))
    }

    pub fn len(&self) -> usize {
        self.spans.len()
    }

    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }
}

fn global_interner() -> &'static RwLock<Interner> {
    static GLOBAL: OnceLock<RwLock<Interner>> = OnceLock::new();
    GLOBAL.get_or_init(|| RwLock::new(Interner::new()))
}

pub fn intern(name: &str) -> Symbol {
    let lock = global_interner();
    if let Ok(guard) = lock.read() {
        let hash = hash_str(name);
        if let Some(candidates) = guard.buckets.get(&hash) {
            for &sym in candidates {
                if guard.resolve(sym) == Some(name) {
                    return sym;
                }
            }
        }
    }
    let mut guard = lock
        .write()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    guard.intern(name)
}

pub fn with_str<R>(symbol: Symbol, f: impl FnOnce(&str) -> R) -> R {
    let guard = global_interner()
        .read()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let text = guard.resolve(symbol).unwrap_or("");
    f(text)
}

pub fn resolve_owned(symbol: Symbol) -> String {
    with_str(symbol, str::to_owned)
}

pub fn cmp_str(a: Symbol, b: Symbol) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }
    let guard = global_interner()
        .read()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    guard.cmp(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_is_four_bytes_with_option_niche() {
        assert_eq!(std::mem::size_of::<Symbol>(), 4);
        assert_eq!(std::mem::size_of::<Option<Symbol>>(), 4);
    }

    #[test]
    fn interner_roundtrips_and_orders_by_string_deterministically() {
        let mut interner = Interner::new();
        let z = interner.intern("zebra_field");
        let a = interner.intern("alpha_field");
        assert_eq!(interner.intern("zebra_field"), z);
        assert_eq!(interner.resolve(z), Some("zebra_field"));
        assert_eq!(interner.resolve(a), Some("alpha_field"));
        assert_eq!(interner.cmp(a, z), Ordering::Less);
        assert_eq!(interner.cmp(z, a), Ordering::Greater);
        assert_eq!(interner.cmp(a, a), Ordering::Equal);
    }

    #[test]
    fn global_interner_preinterns_keywords_and_roundtrips() {
        let s1 = intern("let");
        let s2 = intern("let");
        assert_eq!(s1, s2);
        assert_eq!(resolve_owned(s1), "let");
        let custom = intern("r1_test_custom_ident");
        assert_eq!(
            cmp_str(intern("alpha_cmp"), intern("beta_cmp")),
            Ordering::Less
        );
        assert_eq!(resolve_owned(custom), "r1_test_custom_ident");
    }
}
