//! Original canonical builtin headers, before any receiving ascription.
//! Pending: this module does not authorize row equality or latent bounds.
//!
//! Source signatures: STD.md 990-991 and 1144-1145. Parameter AST/modes come
//! from standard::builtin_callable_signature. `standard_file_builtin` in
//! standard_file.rs and `standard_process_builtin` in standard_process.rs record
//! Mode::Write on formal zero and both effects/concrete_effects Fiber.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Identity {
    FileReadChunk,
    FileWrite,
    ProcessWait,
    ProcessTerminate,
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
    pub source: TypeExpr,
    pub effects: [SystemEffect; 1],
    pub written_formals: [u32; 1],
    /// These four primitives have no lexical captured annotation environment.
    pub captures: BTreeSet<BindingId>,
}

impl Identity {
    pub(super) fn name(self) -> &'static str {
        match self {
            Self::FileReadChunk => "File::read_chunk",
            Self::FileWrite => "File::write",
            Self::ProcessWait => "Process::wait",
            Self::ProcessTerminate => "Process::terminate",
        }
    }
}

/// Only call at the real unique Builtin mint/observation, after ordinary name
/// resolution. A spelling in an expected type or a later mutated signature is
/// not this operation's source. Unsupported builtin schemas remain absent.
pub(super) fn contract(canonical_name: &str, span: Span) -> Option<Contract> {
    let identity = match canonical_name {
        "File::read_chunk" => Identity::FileReadChunk,
        "File::write" => Identity::FileWrite,
        "Process::wait" => Identity::ProcessWait,
        "Process::terminate" => Identity::ProcessTerminate,
        _ => return None,
    };
    // The result Ty is deliberately ignored. In particular, a semantic
    // Callable/Array Ty is never reified into a complete source schema.
    let (_, parameters) = standard::builtin_callable_signature(canonical_name, span)?;
    let named = |name: &str| TypeExpr {
        text: name.into(),
        span,
        kind: TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments: vec![],
        },
    };
    let result = |success: TypeExpr, error: &str| TypeExpr {
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
                text: "()".into(),
                span,
                kind: TypeKind::Tuple(vec![]),
            },
            "Process::ProcessError",
        ),
    };
    Some(Contract {
        identity,
        source: TypeExpr {
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
        },
        effects: [SystemEffect::Fiber],
        written_formals: [0],
        captures: BTreeSet::new(),
    })
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
            } = &contract.source.kind
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
        let source = contract("File::write", span()).unwrap().source;
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
