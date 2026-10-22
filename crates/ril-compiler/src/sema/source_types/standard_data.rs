//! Closed standard data declarations. Their names retain nominal identity;
//! payload schemas provide the complete declaration without consulting Ty.
use super::{SourceScalar, SourceTypesError, WorkLimit, builtins::Schema};
use Schema::{Array, Nominal as NominalRef, Optional, Record, Scalar, Tuple};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Nominal {
    ProcessInput,
    ProcessOutputMode,
    ProcessExitStatus,
    ProcessError,
    IoErrorKind,
    NumError,
}

const UNIT: Schema = Scalar(SourceScalar::Unit);
const STR: Schema = Scalar(SourceScalar::Str);
const BYTES: Schema = Scalar(SourceScalar::Bytes);
const BOOL: Schema = Scalar(SourceScalar::Bool);
const INT: Schema = Scalar(SourceScalar::Int);
const I64: Schema = Scalar(SourceScalar::I64);
const U32: Schema = Scalar(SourceScalar::U32);
const NATIVE: Schema = Scalar(SourceScalar::Intrinsic(
    ril_compiler_core::builtin_types::AtomicBuiltinType::NativeString,
));
const PATH: Schema = Scalar(SourceScalar::Intrinsic(
    ril_compiler_core::builtin_types::AtomicBuiltinType::Path,
));
pub(crate) const IO_ERROR: Schema = Record(&[
    ("kind", false, NominalRef(Nominal::IoErrorKind)),
    ("message", false, STR),
    ("native_code", false, Optional(&I64)),
]);
pub(crate) const READ_CHUNK: Schema = Record(&[("data", false, BYTES), ("end", false, BOOL)]);
pub(crate) const WRITE_PROGRESS: Schema = Record(&[
    ("written", false, INT),
    ("error", false, Optional(&IO_ERROR)),
]);
pub(crate) const COMMAND: Schema = Record(&[
    ("program", false, PATH),
    ("args", false, Array(&NATIVE)),
    ("cwd", false, Optional(&PATH)),
    ("env", false, Optional(&Array(&Tuple(&[NATIVE, NATIVE])))),
    ("input", false, NominalRef(Nominal::ProcessInput)),
    ("stdout", false, NominalRef(Nominal::ProcessOutputMode)),
    ("stderr", false, NominalRef(Nominal::ProcessOutputMode)),
]);
pub(crate) const OUTPUT: Schema = Record(&[
    ("status", false, NominalRef(Nominal::ProcessExitStatus)),
    ("stdout", false, BYTES),
    ("stderr", false, BYTES),
]);

impl Nominal {
    pub(crate) fn lookup(name: &str) -> Option<Self> {
        Some(match name {
            "Process::Input" => Self::ProcessInput,
            "Process::OutputMode" => Self::ProcessOutputMode,
            "Process::ExitStatus" => Self::ProcessExitStatus,
            "Process::ProcessError" => Self::ProcessError,
            "Io::ErrorKind" => Self::IoErrorKind,
            "Num::NumError" => Self::NumError,
            _ => return None,
        })
    }

    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::ProcessInput => "Process::Input",
            Self::ProcessOutputMode => "Process::OutputMode",
            Self::ProcessExitStatus => "Process::ExitStatus",
            Self::ProcessError => "Process::ProcessError",
            Self::IoErrorKind => "Io::ErrorKind",
            Self::NumError => "Num::NumError",
        }
    }

    pub(crate) fn variants(self) -> &'static [(&'static str, Option<Schema>)] {
        match self {
            Self::NumError => &[
                ("InvalidSyntax", None),
                ("OutOfRange", None),
                ("InvalidRadix", None),
            ],
            Self::ProcessInput => &[("Inherit", None), ("Null", None), ("Data", Some(BYTES))],
            Self::ProcessOutputMode => &[("Inherit", None), ("Null", None), ("Capture", None)],
            Self::ProcessExitStatus => &[("Exited", Some(U32)), ("Signaled", Some(INT))],
            Self::ProcessError => &[
                ("InvalidCommand", Some(STR)),
                ("StartFailed", Some(IO_ERROR)),
                ("WaitFailed", Some(IO_ERROR)),
                ("TransferFailed", Some(IO_ERROR)),
                ("CaptureLimit", None),
            ],
            Self::IoErrorKind => &[
                ("NotFound", None),
                ("PermissionDenied", None),
                ("AlreadyExists", None),
                ("InvalidInput", None),
                ("InvalidData", None),
                ("UnexpectedEnd", None),
                ("BrokenPipe", None),
                ("Closed", None),
                ("Unsupported", None),
                ("Other", None),
            ],
        }
    }

    pub(crate) fn has_coordinates(
        self,
        work: &mut WorkLimit,
    ) -> std::result::Result<bool, SourceTypesError> {
        work.charge(1)?;
        for (name, payload) in self.variants() {
            work.charge(1)?;
            work.text(name)?;
            if payload.unwrap_or(UNIT).has_coordinates(work, 0)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

pub(crate) fn schema(name: &str) -> Option<Schema> {
    Some(match name {
        "Process::Command" => COMMAND,
        "Process::Output" => OUTPUT,
        "Io::IoError" => IO_ERROR,
        "Io::ReadChunk" => READ_CHUNK,
        "Io::WriteProgress" => WRITE_PROGRESS,
        name => Schema::Nominal(Nominal::lookup(name)?),
    })
}

pub(crate) fn constructor_payload(tag: &str) -> Option<(Nominal, Schema)> {
    let (owner, tag_name) = tag.rsplit_once("::")?;
    let declaration = Nominal::lookup(owner)?;
    let (_, payload) = declaration
        .variants()
        .iter()
        .find(|(name, _)| *name == tag_name)?;
    Some((declaration, (*payload)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::effect_identity::ArgumentKey;
    use crate::sema::source_types::{SourceBuilder, SourceSensitivity, SourceTypeQueries};

    #[test]
    fn closed_numeric_error_witness_retains_the_catalog_nominal_declaration() {
        let span = ril_compiler_core::source::Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 1,
        };
        let syntax = Schema::Nominal(Nominal::NumError)
            .syntax(span, &mut WorkLimit::new(128))
            .unwrap();
        let mut witness = crate::sema::model::SourceTypeWitness {
            key: crate::static_eval::normalized_argument_key(&syntax),
            syntax,
        };
        assert!(witness.validate_closed());
        assert!(crate::sema::source_type_validation::resolved_names(
            &witness,
            &Default::default()
        ));
        let ril_syntax::ast::TypeKind::Name { arguments, .. } = &mut witness.syntax.kind else {
            unreachable!();
        };
        arguments.push(
            Schema::Scalar(SourceScalar::Unit)
                .syntax(span, &mut WorkLimit::new(128))
                .unwrap(),
        );
        witness.key = crate::static_eval::normalized_argument_key(&witness.syntax);
        assert!(
            !crate::sema::source_type_validation::resolved_names(&witness, &Default::default()),
            "a closed catalog nominal declaration does not invent generic arguments"
        );
    }

    #[test]
    fn closed_nominal_declarations_are_distinct_and_unknown_or_applied_names_stay_unproved() {
        let named = |name: &str, arguments| ArgumentKey::Name {
            name: name.into(),
            arguments,
        };
        let output = named("Process::OutputMode", vec![]);
        let input = named("Process::Input", vec![]);
        assert_eq!(
            crate::sema::source_reception::compatible(&output, &input, None, &mut 4096),
            Some(false)
        );
        let mut builder = SourceBuilder::new().unwrap();
        let known = builder
            .import_key(&output, &mut WorkLimit::new(4096))
            .unwrap();
        let forged = builder
            .import_key(&named("Process::Forged", vec![]), &mut WorkLimit::new(4096))
            .unwrap();
        let types = builder.freeze(&mut WorkLimit::new(4096)).unwrap();
        assert!(matches!(
            types.sensitivity(known, &mut WorkLimit::new(4096)),
            SourceSensitivity::Absent { .. }
        ));
        assert!(matches!(
            types.sensitivity(forged, &mut WorkLimit::new(4096)),
            SourceSensitivity::Unknown { .. }
        ));
        assert!(
            SourceBuilder::new()
                .unwrap()
                .import_key(
                    &named("Process::OutputMode", vec![output]),
                    &mut WorkLimit::new(4096)
                )
                .is_err()
        );
        assert!(
            Nominal::ProcessError
                .has_coordinates(&mut WorkLimit::new(0))
                .is_err()
        );
    }
}
