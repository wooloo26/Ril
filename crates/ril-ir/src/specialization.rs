//! Traceability for closed native instances selected from a verified program.
//! These records present solved evidence; constructing them grants no authority.
use crate::provenance::CopyInstanceId;
use ril_compiler_core::ids::{CallableOwner, DefinitionId, HandlerSiteId};

/// A closed normalized static shape. Lengths, qualifiers and callable modes
/// survive even when the boxed runtime representation does not distinguish them.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArgumentKey {
    Closed(String),
    Name {
        name: String,
        arguments: Vec<Self>,
    },
    Array {
        length: Option<String>,
        element: Box<Self>,
    },
    Map {
        key: Box<Self>,
        value: Box<Self>,
    },
    Tuple(Vec<Self>),
    Record {
        fields: Vec<(String, bool, Self)>,
        row: Option<Box<Self>>,
    },
    Callable {
        parameters: Vec<(ParameterMode, Self)>,
        result: Box<Self>,
        annotations: Vec<String>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ParameterMode {
    Read,
    Mut,
    SharedMut,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Argument {
    pub definition: DefinitionId,
    pub index: u32,
    pub key: ArgumentKey,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnerMap {
    pub source: CallableOwner,
    pub target: CallableOwner,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HandlerMap {
    pub source: HandlerSiteId,
    pub target: HandlerSiteId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefaultUseId(pub u32);

/// Actual applications that determine a private instance's fallback code.
#[derive(Debug, Clone)]
pub struct DefaultSlot {
    pub parameter: u32,
    pub applications: Vec<crate::provenance::CopyCallEventId>,
    /// Empty only when every application supplies this parameter explicitly.
    pub evaluations: Vec<DefaultUseId>,
}

#[derive(Debug, Clone)]
pub struct Instance {
    pub template: DefinitionId,
    pub definition: DefinitionId,
    pub name: String,
    pub arguments: Vec<Argument>,
    pub captured_arguments: Vec<Argument>,
    /// Exact semantic call records; equal source spans never merge invocations.
    pub invocations: Vec<CopyInstanceId>,
    /// Includes the template function and all remapped nested lexical owners.
    /// Normal and metered entries use the same target identities.
    pub owners: Vec<OwnerMap>,
    pub handlers: Vec<HandlerMap>,
    pub defaults: Vec<DefaultSlot>,
}
