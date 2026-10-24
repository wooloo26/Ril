//! Versioned Ril sources. The compiler parses and checks these ordinary modules.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct Module {
    pub path: &'static str,
    pub namespace: &'static str,
    pub source: &'static str,
}

pub const MODULES: &[Module] = &[
    Module {
        path: "ril/option",
        namespace: "Options",
        source: include_str!("../modules/option.ril"),
    },
    Module {
        path: "ril/test",
        namespace: "Test",
        source: include_str!("../modules/test.ril"),
    },
];
