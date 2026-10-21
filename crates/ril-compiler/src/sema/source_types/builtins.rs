//! Closed standard declarations. Runtime shapes, legacy syntax and input/output
//! views are projections of these source graphs, never the other way around.
use super::*;
use crate::sema::model::Ty;
use ril_compiler_core::{builtin_types::AtomicBuiltinType as Atom, source::Span};
use ril_syntax::ast::{Parameter, ParameterMode, Pattern, PatternKind, TypeExpr, TypeKind};

#[derive(Debug, Clone, Copy)]
pub(crate) enum Schema {
    Scalar(SourceScalar),
    Nominal(super::standard_data::Nominal),
    Array(&'static Schema),
    Tuple(&'static [Schema]),
    Record(&'static [(&'static str, bool, Schema)]),
    Optional(&'static Schema),
    Result(&'static Schema, &'static Schema),
}

use Schema::*;
const UNIT: Schema = Scalar(SourceScalar::Unit);
const BOOL: Schema = Scalar(SourceScalar::Bool);
const STR: Schema = Scalar(SourceScalar::Str);
const BYTES: Schema = Scalar(SourceScalar::Bytes);
const U16: Schema = Scalar(SourceScalar::U16);
const UNITS: Schema = Array(&U16);
const NATIVE: Schema = Scalar(SourceScalar::Intrinsic(Atom::NativeString));
const PATH: Schema = Scalar(SourceScalar::Intrinsic(Atom::Path));
const ERROR: Schema = Scalar(SourceScalar::Intrinsic(Atom::NativeError));
const PLATFORM: Schema = Scalar(SourceScalar::Intrinsic(Atom::Platform));
const ORDERING: Schema = Scalar(SourceScalar::Intrinsic(Atom::Ordering));
const POSITION: Schema = Scalar(SourceScalar::Intrinsic(Atom::ReadPosition));

pub(crate) struct Definition {
    pub name: &'static str,
    pub inputs: &'static [(&'static str, Schema)],
    pub output: Schema,
    pub deep: bool,
    pub implementation: Implementation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Implementation {
    ImmutableSnapshot,
    Dedicated,
}

static DEFINITIONS: &[Definition] = &[
    Definition {
        name: "Os::platform",
        inputs: &[],
        output: PLATFORM,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::from_string",
        inputs: &[("text", STR)],
        output: NATIVE,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::to_string",
        inputs: &[("value", NATIVE)],
        output: Result(&STR, &ERROR),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::from_posix_bytes",
        inputs: &[("data", BYTES)],
        output: Result(&NATIVE, &ERROR),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::posix_bytes",
        inputs: &[("value", NATIVE)],
        output: Result(&BYTES, &ERROR),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::from_windows_units",
        inputs: &[("units", UNITS)],
        output: Result(&NATIVE, &ERROR),
        deep: true,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::windows_units",
        inputs: &[("value", NATIVE)],
        output: Result(&UNITS, &ERROR),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Os::compare",
        inputs: &[("left", NATIVE), ("right", NATIVE)],
        output: ORDERING,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::from_string",
        inputs: &[("text", STR)],
        output: PATH,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::from_native",
        inputs: &[("value", NATIVE)],
        output: PATH,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::native",
        inputs: &[("path", PATH)],
        output: NATIVE,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::to_string",
        inputs: &[("path", PATH)],
        output: Result(&STR, &ERROR),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::join",
        inputs: &[("base", PATH), ("child", PATH)],
        output: PATH,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::parent",
        inputs: &[("path", PATH)],
        output: Optional(&PATH),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::file_name",
        inputs: &[("path", PATH)],
        output: Optional(&NATIVE),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::extension",
        inputs: &[("path", PATH)],
        output: Optional(&NATIVE),
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::is_absolute",
        inputs: &[("path", PATH)],
        output: BOOL,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::normalize_lexical",
        inputs: &[("path", PATH)],
        output: PATH,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Path::compare",
        inputs: &[("left", PATH), ("right", PATH)],
        output: ORDERING,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Io::read_position",
        inputs: &[],
        output: POSITION,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Io::guard_read",
        inputs: &[("position", POSITION)],
        output: UNIT,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Io::guard_seek",
        inputs: &[("position", POSITION)],
        output: UNIT,
        deep: false,
        implementation: Implementation::ImmutableSnapshot,
    },
    Definition {
        name: "Process::command",
        inputs: &[("program", PATH), ("args", Array(&NATIVE))],
        output: super::standard_data::COMMAND,
        deep: true,
        implementation: Implementation::Dedicated,
    },
    Definition {
        name: "Bytes::to_array",
        inputs: &[("data", BYTES)],
        output: Array(&Scalar(SourceScalar::U8)),
        deep: false,
        implementation: Implementation::Dedicated,
    },
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BuiltinId(u8);

impl BuiltinId {
    pub(crate) fn lookup(name: &str) -> Option<Self> {
        DEFINITIONS
            .iter()
            .position(|entry| entry.name == name)
            .map(|index| Self(index as u8))
    }
    pub(crate) fn definition(self) -> &'static Definition {
        &DEFINITIONS[self.0 as usize]
    }
    pub(crate) fn bit(self) -> u64 {
        1 << (16 + self.0)
    }
}

static CONSTANTS: &[(&str, Schema)] = &[
    ("Os::NativeError::InvalidEncoding", ERROR),
    ("Os::NativeError::WrongPlatform", ERROR),
    ("Os::Platform::Windows", PLATFORM),
    ("Os::Platform::Posix", PLATFORM),
];
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ConstantId(u8);
impl ConstantId {
    pub(crate) fn lookup(name: &str) -> Option<Self> {
        CONSTANTS
            .iter()
            .position(|entry| entry.0 == name)
            .map(|index| Self(index as u8))
    }
    pub(crate) fn definition(self) -> (&'static str, Schema) {
        CONSTANTS[self.0 as usize]
    }
    pub(crate) fn bit(self) -> u64 {
        1 << (48 + self.0)
    }
}
pub(crate) fn constant(name: &str) -> Option<Schema> {
    Some(ConstantId::lookup(name)?.definition().1)
}

pub(crate) struct Header {
    pub types: SourceTypes,
    pub root: SourceTypeId,
    pub result: SourceTypeId,
    pub parameters: Vec<SourceTypeId>,
}

impl Definition {
    pub(crate) fn graph(
        &self,
        work: &mut WorkLimit,
    ) -> std::result::Result<Header, SourceTypesError> {
        work.charge(self.inputs.len() + 1)?;
        let mut builder = SourceBuilder::new()?;
        let parameters = self
            .inputs
            .iter()
            .map(|(_, schema)| schema.insert(&mut builder, work))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let result = self.output.insert(&mut builder, work)?;
        work.charge(parameters.len())?;
        let root = builder.insert(
            SourceNode::Callable {
                parameters: parameters
                    .iter()
                    .map(|&id| (ParameterMode::Read, id))
                    .collect(),
                result,
                annotations: vec![],
            },
            work,
        )?;
        let types = builder.freeze(work)?;
        Ok(Header {
            types,
            root,
            result,
            parameters,
        })
    }
    pub(crate) fn syntax(
        &self,
        span: Span,
        work: &mut WorkLimit,
    ) -> std::result::Result<TypeExpr, SourceTypesError> {
        work.charge(self.inputs.len() + 1)?;
        let parameters = self
            .inputs
            .iter()
            .map(|(name, schema)| {
                work.text(name)?;
                Ok(Parameter {
                    pattern: Pattern {
                        hir_id: None,
                        kind: PatternKind::Name((*name).into()),
                        span,
                    },
                    mode: ParameterMode::Read,
                    ty: Some(schema.syntax(span, work)?),
                    default: None,
                    span,
                })
            })
            .collect::<std::result::Result<_, SourceTypesError>>()?;
        Ok(TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: TypeKind::Callable {
                parameters,
                result: Some(Box::new(self.output.syntax(span, work)?)),
                annotations: vec![],
            },
        })
    }
}

impl Schema {
    pub(crate) fn insert(
        self,
        builder: &mut SourceBuilder,
        work: &mut WorkLimit,
    ) -> std::result::Result<SourceTypeId, SourceTypesError> {
        work.charge(1)?;
        let node = match self {
            Scalar(kind) => SourceNode::Scalar(kind),
            Nominal(identity) => SourceNode::Nominal(identity),
            Tuple(items) => {
                work.charge(items.len())?;
                SourceNode::Tuple(
                    items
                        .iter()
                        .map(|item| item.insert(builder, work))
                        .collect::<std::result::Result<_, _>>()?,
                )
            }
            Record(fields) => {
                work.charge(fields.len())?;
                SourceNode::Record {
                    fields: fields
                        .iter()
                        .map(|(label, mutable, schema)| {
                            work.text(label)?;
                            Ok(SourceField {
                                label: (*label).into(),
                                mutable: *mutable,
                                value: schema.insert(builder, work)?,
                            })
                        })
                        .collect::<std::result::Result<_, SourceTypesError>>()?,
                    row: None,
                }
            }
            Array(element) => SourceNode::Array {
                length: SourceLength::Dynamic,
                element: element.insert(builder, work)?,
            },
            Optional(element) => {
                work.charge(1)?;
                SourceNode::Container {
                    kind: SourceContainer::Option,
                    arguments: vec![element.insert(builder, work)?],
                }
            }
            Result(ok, error) => {
                work.charge(2)?;
                SourceNode::Container {
                    kind: SourceContainer::Result,
                    arguments: vec![ok.insert(builder, work)?, error.insert(builder, work)?],
                }
            }
        };
        builder.insert(node, work)
    }
    pub(crate) fn graph(
        self,
        work: &mut WorkLimit,
    ) -> std::result::Result<(SourceTypes, SourceTypeId), SourceTypesError> {
        let mut builder = SourceBuilder::new()?;
        let root = self.insert(&mut builder, work)?;
        Ok((builder.freeze(work)?, root))
    }
    pub(crate) fn syntax(
        self,
        span: Span,
        work: &mut WorkLimit,
    ) -> std::result::Result<TypeExpr, SourceTypesError> {
        work.charge(1)?;
        let kind = match self {
            Scalar(SourceScalar::Unit) => TypeKind::Tuple(vec![]),
            Scalar(kind) => {
                let name = super::substitution::scalar_name(kind);
                work.text(name)?;
                TypeKind::Name {
                    path: name.split("::").map(str::to_owned).collect(),
                    arguments: vec![],
                }
            }
            Nominal(identity) => {
                work.text(identity.name())?;
                TypeKind::Name {
                    path: identity.name().split("::").map(str::to_owned).collect(),
                    arguments: vec![],
                }
            }
            Tuple(items) => {
                work.charge(items.len())?;
                TypeKind::Tuple(
                    items
                        .iter()
                        .map(|item| item.syntax(span, work))
                        .collect::<std::result::Result<_, _>>()?,
                )
            }
            Record(fields) => {
                work.charge(fields.len())?;
                TypeKind::Record {
                    fields: fields
                        .iter()
                        .map(|(name, mutable, schema)| {
                            work.text(name)?;
                            Ok(ril_syntax::ast::TypeField {
                                name: (*name).into(),
                                mutable: *mutable,
                                ty: schema.syntax(span, work)?,
                                span,
                            })
                        })
                        .collect::<std::result::Result<_, SourceTypesError>>()?,
                    row: None,
                }
            }
            Array(element) => TypeKind::Array {
                length: None,
                element: Box::new(element.syntax(span, work)?),
            },
            Optional(element) => TypeKind::Optional(Box::new(element.syntax(span, work)?)),
            Result(ok, error) => {
                work.text("Result")?;
                work.charge(2)?;
                TypeKind::Name {
                    path: vec!["Result".into()],
                    arguments: vec![ok.syntax(span, work)?, error.syntax(span, work)?],
                }
            }
        };
        Ok(TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind,
        })
    }

    pub(crate) fn has_coordinates(
        self,
        work: &mut WorkLimit,
        depth: usize,
    ) -> std::result::Result<bool, SourceTypesError> {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        Ok(match self {
            Scalar(_) => false,
            Nominal(declaration) => declaration.has_coordinates(work)?,
            Array(_) => true,
            Optional(element) => element.has_coordinates(work, depth + 1)?,
            Result(ok, error) => {
                ok.has_coordinates(work, depth + 1)? || error.has_coordinates(work, depth + 1)?
            }
            Tuple(items) => {
                let mut sensitive = false;
                for item in items {
                    sensitive |= item.has_coordinates(work, depth + 1)?;
                }
                sensitive
            }
            Record(fields) => {
                let mut sensitive = false;
                for (name, _, field) in fields {
                    work.text(name)?;
                    sensitive |= field.has_coordinates(work, depth + 1)?;
                }
                sensitive
            }
        })
    }

    pub(crate) fn erased(self) -> std::result::Result<Ty, SourceTypesError> {
        let mut work = WorkLimit::new(4096);
        let (types, root) = self.graph(&mut work)?;
        erased_type(&types, root, &mut work)
    }
}

pub(crate) fn erased_type(
    types: &SourceTypes,
    id: SourceTypeId,
    work: &mut WorkLimit,
) -> std::result::Result<Ty, SourceTypesError> {
    work.charge(1)?;
    Ok(match types.get(id)? {
        SourceNode::Scalar(SourceScalar::Unit) => Ty::Unit,
        SourceNode::Scalar(SourceScalar::Bool) => Ty::Bool,
        SourceNode::Scalar(SourceScalar::Str) => Ty::Str,
        SourceNode::Scalar(SourceScalar::Bytes) => Ty::Bytes,
        SourceNode::Scalar(SourceScalar::Never) => Ty::Never,
        SourceNode::Scalar(SourceScalar::Intrinsic(identity)) => Ty::Named(identity.name().into()),
        SourceNode::Nominal(identity) => Ty::Named(identity.name().into()),
        SourceNode::Scalar(kind @ (SourceScalar::F32 | SourceScalar::F64)) => {
            Ty::Float(super::substitution::scalar_name(*kind).into())
        }
        SourceNode::Scalar(kind) => Ty::Int(super::substitution::scalar_name(*kind).into()),
        SourceNode::Array { element, .. } => {
            Ty::Array(Box::new(erased_type(types, *element, work)?))
        }
        SourceNode::Tuple(items) => {
            work.charge(items.len())?;
            Ty::Tuple(
                items
                    .iter()
                    .map(|id| erased_type(types, *id, work))
                    .collect::<std::result::Result<_, _>>()?,
            )
        }
        SourceNode::Record { fields, row: None } => {
            work.charge(fields.len())?;
            Ty::Record(
                fields
                    .iter()
                    .map(|field| {
                        work.text(&field.label)?;
                        Ok((
                            field.label.clone(),
                            (field.mutable, erased_type(types, field.value, work)?),
                        ))
                    })
                    .collect::<std::result::Result<_, SourceTypesError>>()?,
            )
        }
        SourceNode::Container {
            kind: SourceContainer::Option,
            arguments,
        } if arguments.len() == 1 => {
            Ty::Optional(Box::new(erased_type(types, arguments[0], work)?))
        }
        SourceNode::Container {
            kind: SourceContainer::Result,
            arguments,
        } if arguments.len() == 2 => Ty::Result(
            Box::new(erased_type(types, arguments[0], work)?),
            Box::new(erased_type(types, arguments[1], work)?),
        ),
        SourceNode::Callable {
            parameters, result, ..
        } => {
            work.charge(parameters.len())?;
            Ty::Callable(
                parameters
                    .iter()
                    .map(|(_, id)| erased_type(types, *id, work))
                    .collect::<std::result::Result<_, _>>()?,
                Box::new(erased_type(types, *result, work)?),
            )
        }
        _ => return Err(SourceTypesError::Unresolved),
    })
}
