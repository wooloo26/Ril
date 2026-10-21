//! File operation contracts grant fresh resource authority only at open sites.
//! Resource copying and boundary admission are checked independently.
use super::*;
pub(super) fn file_constant(name: &str) -> Option<Ty> {
    let ty = match name {
        "File::OpenMode::Read"
        | "File::OpenMode::WriteNew"
        | "File::OpenMode::WriteTruncate"
        | "File::OpenMode::ReadWrite"
        | "File::OpenMode::Append" => "File::OpenMode",
        "File::FileKind::Regular"
        | "File::FileKind::Directory"
        | "File::FileKind::Symlink"
        | "File::FileKind::Other" => "File::FileKind",
        "Io::ErrorKind::NotFound"
        | "Io::ErrorKind::PermissionDenied"
        | "Io::ErrorKind::AlreadyExists"
        | "Io::ErrorKind::InvalidInput"
        | "Io::ErrorKind::InvalidData"
        | "Io::ErrorKind::UnexpectedEnd"
        | "Io::ErrorKind::BrokenPipe"
        | "Io::ErrorKind::Closed"
        | "Io::ErrorKind::Unsupported"
        | "Io::ErrorKind::Other" => "Io::ErrorKind",
        _ => return None,
    };
    Some(Ty::Named(ty.into()))
}
pub(super) fn io_error() -> Ty {
    crate::sema::source_types::standard_data::IO_ERROR
        .erased()
        .expect("fixed Io::IoError declaration fits its projection bound")
}
pub(super) fn read_chunk() -> Ty {
    crate::sema::source_types::standard_data::READ_CHUNK
        .erased()
        .expect("fixed Io::ReadChunk declaration fits its projection bound")
}
pub(super) fn write_progress() -> Ty {
    crate::sema::source_types::standard_data::WRITE_PROGRESS
        .erased()
        .expect("fixed Io::WriteProgress declaration fits its projection bound")
}
pub(super) fn file_metadata() -> Ty {
    Ty::Record(
        [
            ("kind".into(), (false, Ty::Named("File::FileKind".into()))),
            ("size".into(), (false, integer("u64"))),
            (
                "modified".into(),
                (false, Ty::Optional(Box::new(temporal::timestamp()))),
            ),
        ]
        .into(),
    )
}
pub(super) fn file_entry() -> Ty {
    Ty::Record(
        [
            ("path".into(), (false, Ty::Named("Path::Path".into()))),
            ("name".into(), (false, Ty::Named("Os::NativeString".into()))),
            ("kind".into(), (false, Ty::Named("File::FileKind".into()))),
        ]
        .into(),
    )
}
fn file_signature(name: &str) -> Option<Signature> {
    use Output::*;
    let path = Ty::Named("Path::Path".into());
    let handle = Ty::Named("File::Handle".into());
    let error = io_error();
    Some(match name {
        "File::open" => signature(vec![Ty::Str], Result(handle, error)),
        "File::open_path" => signature(
            vec![path, Ty::Named("File::OpenMode".into())],
            Result(handle, error),
        ),
        "File::read" => signature(vec![Ty::Str], Result(Ty::Str, Ty::Str)),
        "File::read_chunk" => signature(vec![handle, integer("int")], Result(read_chunk(), error)),
        "File::write" => signature(vec![handle, Ty::Bytes], Value(write_progress())),
        "File::seek" => signature(
            vec![handle, Ty::Named("File::SeekFrom".into())],
            Result(integer("u64"), error),
        ),
        "File::sync" | "File::close" => signature(vec![handle], Result(Ty::Unit, error)),
        "File::SeekFrom::Start" | "File::SeekFrom::Current" | "File::SeekFrom::End" => signature(
            vec![integer("i64")],
            Value(Ty::Named("File::SeekFrom".into())),
        ),
        "File::read_bytes" => signature(vec![path], Result(Ty::Bytes, error)),
        "File::read_text" => signature(vec![path], Result(Ty::Str, error)),
        "File::write_bytes" => signature(vec![path, Ty::Bytes], Result(Ty::Unit, error)),
        "File::write_text" => signature(vec![path, Ty::Str], Result(Ty::Unit, error)),
        "File::metadata" => Signature {
            inputs: vec![path, Ty::Bool],
            minimum: 1,
            output: Result(file_metadata(), error),
            deep: false,
        },
        "File::read_dir" => signature(vec![path], Result(Ty::Array(Box::new(file_entry())), error)),
        "File::create_dir" | "File::create_dir_all" | "File::remove_file" | "File::remove_dir" => {
            signature(vec![path], Result(Ty::Unit, error))
        }
        "File::rename" => signature(vec![path.clone(), path], Result(Ty::Unit, error)),
        "File::canonicalize" => signature(vec![path.clone()], Result(path, error)),
        "File::temp_file" => signature(
            vec![path.clone()],
            Result(Ty::Tuple(vec![path, handle]), error),
        ),
        "Io::stdin_read" => signature(vec![integer("int")], Result(read_chunk(), error)),
        "Io::stdout_write" | "Io::stderr_write" => {
            signature(vec![Ty::Bytes], Value(write_progress()))
        }
        "Io::write_stdout" | "Io::write_stderr" => {
            signature(vec![Ty::Str], Result(Ty::Unit, error))
        }
        "Io::error_text" => signature(vec![error], Value(Ty::Str)),
        "Io::read_buffer" => signature(
            vec![integer("int")],
            Value(Ty::Named("Io::ReadBuffer".into())),
        ),
        "Io::write_buffer" => signature(
            vec![integer("int")],
            Value(Ty::Named("Io::WriteBuffer".into())),
        ),
        _ => return None,
    })
}
pub(super) fn is_file_builtin(name: &str) -> bool {
    file_signature(name).is_some()
}
impl Checker {
    pub(super) fn standard_file_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let signature = file_signature(name)?;
        let writes = matches!(
            name,
            "File::read_chunk" | "File::write" | "File::seek" | "File::sync" | "File::close"
        );
        if writes {
            if args.len() != signature.inputs.len() {
                self.error("E0314", span, "wrong file argument count", []);
            }
            for (index, ((mode, value, argument_span), ty)) in
                args.iter().zip(&signature.inputs).enumerate()
            {
                self.require_type(value, ty, *argument_span);
                let expected = if index == 0 {
                    ParameterMode::Mut
                } else {
                    ParameterMode::Read
                };
                if *mode != expected {
                    self.error(
                        "E0405",
                        *argument_span,
                        "file operation argument mode mismatch",
                        [value.cause],
                    );
                }
                if index == 0 {
                    if value.permission != Permission::Write {
                        self.error(
                            "E0520",
                            *argument_span,
                            "file operation has no mutable authority",
                            [value.cause],
                        );
                    }
                    self.access(value, None, Mode::Write, *argument_span, frame);
                }
            }
        } else {
            self.standard_arguments(name, args, &signature.inputs, signature.minimum, span);
            for (_, value, argument_span) in args {
                if !value.ty.scalar() {
                    self.deep_read(value, *argument_span, frame);
                }
            }
        }
        if !matches!(
            name,
            "File::SeekFrom::Start"
                | "File::SeekFrom::Current"
                | "File::SeekFrom::End"
                | "Io::error_text"
                | "Io::read_buffer"
                | "Io::write_buffer"
        ) {
            frame.obligations.effects.insert("Fiber".into());
            frame.obligations.concrete_effects.insert("Fiber".into());
        }
        Some(match signature.output {
            Output::Value(ty) => self.standard_value(ty, span, frame.owner, 0),
            Output::Result(ok, error) if matches!(name, "File::read_dir" | "File::temp_file") => {
                let payload = if name == "File::read_dir" {
                    self.standard_array(file_entry(), span, frame.owner)
                } else {
                    let node = self.allocate(span, 0, frame.owner);
                    let path =
                        self.standard_value(Ty::Named("Path::Path".into()), span, frame.owner, 1);
                    let handle =
                        self.standard_value(Ty::Named("File::Handle".into()), span, frame.owner, 2);
                    self.store_field(node, Slot::Tuple(0), path);
                    self.store_field(node, Slot::Tuple(1), handle);
                    Value::reference(ok.clone(), node, self.heap.nodes[node.0 as usize].cause)
                };
                let mut value = self.make_result(true, payload, span, frame.owner);
                value.result_error = Some(Box::new(self.standard_value(
                    error.clone(),
                    span,
                    frame.owner,
                    3,
                )));
                value.ty = Ty::Result(Box::new(ok), Box::new(error));
                value.result_tag = None;
                value.result_payload = None;
                value
            }
            Output::Result(ok, error) => self.standard_result(ok, error, span, frame.owner),
            _ => unreachable!(),
        })
    }
}
