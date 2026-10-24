//! Original canonical builtin headers, before any receiving ascription.
//! Pending: this module does not authorize row equality or latent bounds.
//!
//! Source signatures: STD.md 990-991 and 1144-1145. Parameter AST/modes come
//! from standard::builtin_callable_signature. `standard_file_builtin` in
//! standard_file.rs and `standard_process_builtin` in standard_process.rs record
//! Mode::Write on formal zero and both effects/concrete_effects Fiber.
use super::*;
use crate::sema::builtin_sources::BuiltinDeclaration;
use ril_compiler_core::builtin_calls::GenericBuiltin;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Identity {
    FileReadChunk,
    FileWrite,
    ProcessWait,
    ProcessTerminate,
    Closed(crate::sema::source_types::builtins::BuiltinId),
    Constant(crate::sema::source_types::builtins::ConstantId),
    Generic(GenericBuiltin),
    Nullary(ril_compiler_core::builtin_calls::NullaryConstructor),
    Numeric(ril_compiler_core::numeric_builtins::NumericBuiltin),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SystemEffect {
    /// The compiler's concrete system Fiber row, never a caller's raw @name.
    Fiber,
}

pub(super) struct Contract {
    pub identity: Identity,
    /// Complete original header including its qualifications. Preserve this
    /// in the emitter receipt/Core reference, not just a coordinate view.
    pub source: BuiltinDeclaration,
    pub effects: &'static [SystemEffect],
    pub written_formals: &'static [u32],
    /// These four primitives have no lexical captured annotation environment.
    pub captures: BTreeSet<BindingId>,
}

impl Identity {
    fn lookup(name: &str) -> Option<Self> {
        use crate::sema::source_types::builtins;
        if let Some(id) = ril_compiler_core::builtin_calls::NullaryConstructor::lookup(name) {
            return Some(Self::Nullary(id));
        }
        if let Some(id) = ril_compiler_core::numeric_builtins::NumericBuiltin::lookup(name) {
            return Some(Self::Numeric(id));
        }
        if let Some(id) = GenericBuiltin::lookup(name) {
            return Some(Self::Generic(id));
        }
        if let Some(id) = builtins::BuiltinId::lookup(name) {
            return Some(Self::Closed(id));
        }
        if let Some(id) = builtins::ConstantId::lookup(name) {
            return Some(Self::Constant(id));
        }
        Some(match name {
            "File::read_chunk" => Self::FileReadChunk,
            "File::write" => Self::FileWrite,
            "Process::wait" => Self::ProcessWait,
            "Process::terminate" => Self::ProcessTerminate,
            _ => return None,
        })
    }

    pub(super) fn name(self) -> &'static str {
        match self {
            Self::FileReadChunk => "File::read_chunk",
            Self::FileWrite => "File::write",
            Self::ProcessWait => "Process::wait",
            Self::ProcessTerminate => "Process::terminate",
            Self::Closed(id) => id.definition().name,
            Self::Constant(id) => id.definition().0,
            Self::Generic(id) => id.name(),
            Self::Nullary(id) => id.name(),
            Self::Numeric(id) => id.name(),
        }
    }

    pub(super) fn matches_name(self, name: &str) -> bool {
        match self {
            Self::Closed(id) => {
                crate::sema::source_types::builtins::BuiltinId::lookup(name) == Some(id)
            }
            Self::Nullary(id) => {
                ril_compiler_core::builtin_calls::NullaryConstructor::lookup(name) == Some(id)
            }
            _ => self.name() == name,
        }
    }
}

/// Only call at the real unique Builtin mint/observation, after ordinary name
/// resolution. A spelling in an expected type or a later mutated signature is
/// not this operation's source. Unsupported builtin schemas remain absent.
pub(super) fn contract(canonical_name: &str, span: Span) -> Option<Contract> {
    use crate::sema::source_types::WorkLimit;
    let identity = Identity::lookup(canonical_name)?;
    if let Identity::Nullary(id) = identity {
        return Some(Contract {
            identity,
            source: BuiltinDeclaration::Nullary(id),
            effects: &[],
            written_formals: &[],
            captures: BTreeSet::new(),
        });
    }
    if let Identity::Numeric(id) = identity {
        return Some(Contract {
            identity: Identity::Numeric(id),
            source: BuiltinDeclaration::Numeric(id),
            effects: &[],
            written_formals: &[],
            captures: BTreeSet::new(),
        });
    }
    if let Identity::Generic(id) = identity {
        return Some(Contract {
            identity: Identity::Generic(id),
            source: BuiltinDeclaration::Generic(id),
            effects: &[],
            written_formals: crate::sema::source_types::polymorphic::written_formals(id),
            captures: BTreeSet::new(),
        });
    }
    if let Identity::Closed(id) = identity {
        return Some(Contract {
            identity: Identity::Closed(id),
            source: BuiltinDeclaration::Syntax(
                id.definition()
                    .syntax(span, &mut WorkLimit::new(4096))
                    .ok()?,
            ),
            effects: &[],
            written_formals: &[],
            captures: BTreeSet::new(),
        });
    }
    if let Identity::Constant(id) = identity {
        return Some(Contract {
            identity: Identity::Constant(id),
            source: BuiltinDeclaration::Syntax(
                id.definition()
                    .1
                    .syntax(span, &mut WorkLimit::new(4096))
                    .ok()?,
            ),
            effects: &[],
            written_formals: &[],
            captures: BTreeSet::new(),
        });
    }
    // The result Ty is deliberately ignored. In particular, a semantic
    // Callable/Array Ty is never reified into a complete source schema.
    let (_, parameters) = standard::builtin_callable_signature(canonical_name, span)?;
    let named = |name: &str| TypeExpr {
        hir_id: None,
        text: name.into(),
        span,
        kind: TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments: vec![],
        },
    };
    let result = |success: TypeExpr, error: &str| TypeExpr {
        hir_id: None,
        text: String::new(),
        span,
        kind: TypeKind::Name {
            path: vec!["Prelude".into(), "Result".into()],
            arguments: vec![success, named(error)],
        },
    };
    let output = match identity {
        Identity::FileReadChunk => result(named("Io::ReadChunk"), "Io::IoError"),
        Identity::FileWrite => named("Io::WriteProgress"),
        Identity::ProcessWait => result(named("Process::ExitStatus"), "Process::ProcessError"),
        Identity::ProcessTerminate => result(
            TypeExpr {
                hir_id: None,
                text: "()".into(),
                span,
                kind: TypeKind::Tuple(vec![]),
            },
            "Process::ProcessError",
        ),
        Identity::Closed(_)
        | Identity::Constant(_)
        | Identity::Generic(_)
        | Identity::Nullary(_)
        | Identity::Numeric(_) => unreachable!(),
    };
    Some(Contract {
        identity,
        source: BuiltinDeclaration::Syntax(TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: TypeKind::Callable {
                parameters,
                result: Some(Box::new(output)),
                annotations: vec![
                    Annotation {
                        kind: AnnotationKind::Effect,
                        text: "@Fiber".into(),
                        span,
                    },
                    Annotation {
                        kind: AnnotationKind::Capability,
                        text: "&mut".into(),
                        span,
                    },
                ],
            },
        }),
        effects: &[SystemEffect::Fiber],
        written_formals: &[0],
        captures: BTreeSet::new(),
    })
}

pub(super) fn source_key(
    declaration: &BuiltinDeclaration,
) -> Option<crate::sema::effect_identity::ArgumentKey> {
    match declaration {
        BuiltinDeclaration::Numeric(_) | BuiltinDeclaration::Nullary(_) => None,
        BuiltinDeclaration::Generic(id) => Some(
            crate::sema::effect_identity::ArgumentKey::GenericBuiltin(*id),
        ),
        BuiltinDeclaration::Syntax(syntax) => {
            let syntax =
                super::source_types::expand_builtin_source_syntax(&BTreeMap::new(), syntax, 0)?;
            let key = crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())?;
            crate::sema::source_reception::complete(&key, &mut 4096)?;
            Some(key)
        }
    }
}

pub(super) fn source_schema(
    declaration: &BuiltinDeclaration,
    source: Option<ril_compiler_core::ids::ExprId>,
    work: &mut crate::sema::source_types::WorkLimit,
) -> Result<
    Option<crate::sema::source_types::SourceSchema>,
    crate::sema::source_types::SourceTypesError,
> {
    use crate::sema::source_types::{SourceSchema, SourceTypesError};
    if let BuiltinDeclaration::Nullary(id) = declaration {
        return SourceSchema::nullary_constructor(
            *id,
            source.ok_or(SourceTypesError::MissingNode)?,
            work,
        )
        .map(Some);
    }
    if let BuiltinDeclaration::Numeric(id) = declaration {
        return crate::sema::source_types::numeric::definition(*id)
            .map(|definition| definition.schema(work))
            .transpose();
    }
    let key = source_key(declaration).ok_or(SourceTypesError::Unresolved)?;
    SourceSchema::import(
        &key,
        declaration.syntax().and_then(|syntax| syntax.hir_id),
        work,
    )
    .map(Some)
}

pub(super) fn nullary_value(
    declaration: ril_compiler_core::builtin_calls::NullaryConstructor,
    cause: CauseId,
) -> Value {
    match declaration {
        ril_compiler_core::builtin_calls::NullaryConstructor::None => {
            let mut value = Value::scalar(Ty::Optional(Box::new(Ty::Unknown)), None, cause);
            value.option_tag = Some(false);
            value
        }
    }
}

pub(super) fn nullary_descriptor(
    declaration: ril_compiler_core::builtin_calls::NullaryConstructor,
    value: &Value,
    work: &mut usize,
) -> Result<bool, crate::sema::source_types::SourceTypesError> {
    *work = work
        .checked_sub(3)
        .ok_or(crate::sema::source_types::SourceTypesError::BudgetExceeded)?;
    crate::sema::evaluated::same_birth_value(&nullary_value(declaration, value.cause), value, work)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 7,
            end: 19,
        }
    }

    #[test]
    fn four_original_headers_keep_modes_results_and_canonical_rows() {
        for name in [
            "File::read_chunk",
            "File::write",
            "Process::wait",
            "Process::terminate",
        ] {
            let contract = contract(name, span()).unwrap();
            assert_eq!(contract.identity.name(), name);
            assert_eq!(contract.effects, [SystemEffect::Fiber]);
            assert_eq!(contract.written_formals, [0]);
            assert!(contract.captures.is_empty());
            let TypeKind::Callable {
                parameters,
                result,
                annotations,
            } = &contract.source.syntax().unwrap().kind
            else {
                unreachable!()
            };
            assert_eq!(parameters[0].mode, ParameterMode::Mut);
            assert!(
                parameters
                    .iter()
                    .all(|parameter| parameter.ty.is_some() && parameter.default.is_none())
            );
            assert!(result.is_some());
            assert_eq!(
                annotations
                    .iter()
                    .map(|annotation| annotation.text.as_str())
                    .collect::<Vec<_>>(),
                ["@Fiber", "&mut"]
            );
        }
    }

    #[test]
    fn canonical_qualified_header_does_not_claim_a_closed_raw_source_witness() {
        let source = contract("File::write", span())
            .unwrap()
            .source
            .syntax()
            .unwrap()
            .clone();
        let witness = SourceTypeWitness {
            key: crate::static_eval::normalized_argument_key(&source),
            syntax: source,
        };
        assert!(
            !witness.validate_closed(),
            "canonical row needs its dedicated physical receipt, not a raw @Fiber witness"
        );
    }

    #[test]
    fn arbitrary_names_and_unimplemented_schemas_never_borrow_a_known_header() {
        for name in ["write", "My::write", "File::other", "Array::map"] {
            assert!(contract(name, span()).is_none(), "{name}");
        }
    }
}
