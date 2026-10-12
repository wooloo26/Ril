use ril_compiler_core::ids::{DefinitionId, OriginId, TypeId};
use ril_compiler_core::source::Span;
/// Shared semantic identity survives source-language and native lowering.
#[derive(Debug, Clone)]
pub struct Value {
    pub ty: TypeId,
    pub origins: Vec<OriginId>,
    pub span: Span,
}
#[derive(Debug, Clone)]
pub enum Operation {
    Call {
        callee: DefinitionId,
        arguments: Vec<Value>,
    },
    ManagedReference(Value),
    Effect {
        operation: DefinitionId,
        arguments: Vec<Value>,
    },
    Resume(Value),
    Cleanup {
        body: Vec<Operation>,
        cleanup: Vec<Operation>,
    },
    Branch {
        condition: Value,
        then_body: Vec<Operation>,
        else_body: Vec<Operation>,
    },
}
/// Generic type parameters remain symbolic until a backend chooses a representation.
#[derive(Debug, Clone)]
pub struct Function {
    pub definition: DefinitionId,
    pub generic_parameters: Vec<TypeId>,
    pub body: Vec<Operation>,
}
/// Structured IR data. Construction does not certify Ril semantic validity.
#[derive(Debug)]
pub struct Program {
    pub functions: Vec<Function>,
}
impl Program {
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
}
