/// Initial backend probe subset, not the Ril language or the complete native MIR.
#[derive(Debug, Clone, Default)]
pub struct Module {
    pub specializations: Vec<crate::specialization::Instance>,
    pub constant_graphs: Vec<crate::constants::ConstGraph>,
    /// Published top-level cells; independent of initializer representation.
    pub global_bindings: std::collections::BTreeSet<String>,
    pub external_functions: Vec<crate::foreign::ExternalFunction>,
    pub external_constants: Vec<crate::foreign::ExternalConstant>,
    pub foreign_bindings: Vec<crate::foreign::Binding>,
    pub retained_handlers: Vec<crate::provenance::RetainedHandler>,
    pub closure_sites: Vec<crate::provenance::ClosureSite>,
    pub nonretaining_adapters: Vec<crate::provenance::NonRetainingAdapter>,
    pub budget_entries: std::collections::BTreeMap<String, String>,
    pub functions: Vec<Function>,
    pub constructors: Vec<crate::core::Constructor>,
    pub operations: Vec<crate::core::Operation>,
    pub call_signatures: Vec<crate::core::CallSignature>,
}
/// Private Core identity; source identifiers cannot contain NUL.
pub const GLOBAL_INITIALIZER: &str = "\0ril.globals";
/// A hole in a certified named-argument tuple, never a source constructor.
pub const MISSING_ARGUMENT_TAG: &str = "\0ril.argument.missing";
pub fn budget_entry_name(name: &str) -> String {
    format!("\0ril.budget.{name}")
}
#[derive(Debug, Clone)]
pub struct Function {
    pub symbol: String,
    pub body: Body,
}
#[derive(Debug, Clone)]
pub enum Body {
    ReturnI64(i64),
    /// Managed-value native function with a uniform environment/argument ABI.
    Managed(crate::core::Function),
    /// A checked external declaration, lowered to an explicit CPS adapter by
    /// the backend. It is never treated as an empty Ril implementation body.
    Foreign(crate::foreign::ExternalFunction),
    Cps(std::sync::Arc<crate::cps::Function>),
    CpsBlock {
        function: std::sync::Arc<crate::cps::Function>,
        block: crate::cps::BlockId,
    },
    /// Platform C entry point: initialize the runtime, globals, and selected Ril entry.
    Entry {
        initializer: String,
        entry: String,
    },
}
