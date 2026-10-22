//! Process data is ordinary typed data; a Child is an opaque task-local resource.
use super::*;
pub(super) fn process_type(name: &str) -> Option<Ty> {
    Some(match name {
        "Process::Child"
        | "Process::Input"
        | "Process::OutputMode"
        | "Process::ExitStatus"
        | "Process::ProcessError" => Ty::Named(name.into()),
        "Process::Command" => command_type(),
        "Process::Output" => output_type(),
        _ => return None,
    })
}
fn command_type() -> Ty {
    crate::sema::source_types::standard_data::COMMAND
        .erased()
        .expect("fixed Process::Command declaration fits its projection bound")
}
fn output_type() -> Ty {
    crate::sema::source_types::standard_data::OUTPUT
        .erased()
        .expect("fixed Process::Output declaration fits its projection bound")
}
pub(super) fn is_process_builtin(name: &str) -> bool {
    matches!(
        name,
        "Process::command"
            | "Process::run"
            | "Process::spawn"
            | "Process::wait"
            | "Process::terminate"
            | "Process::success"
    )
}
impl Checker {
    pub(in crate::sema::checker) fn register_standard_process_types(&mut self) {
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        use crate::sema::source_types::{WorkLimit, standard_data::Nominal};
        for declaration in [
            Nominal::ProcessInput,
            Nominal::ProcessOutputMode,
            Nominal::ProcessExitStatus,
            Nominal::ProcessError,
        ] {
            let owner = declaration.name();
            let typing_environment = self.capture_typing_environment();
            for (variant, payload) in declaration.variants() {
                let tag = format!("{owner}::{variant}");
                self.constructors.insert(
                    tag.clone(),
                    ConstructorInfo {
                        typing_environment: typing_environment.clone(),
                        source: None,
                        source_syntax: None,
                        source_type_witness: None,
                        tag,
                        owner: Ty::Named(owner.into()),
                        payload: payload
                            .map(|schema| {
                                schema.erased().expect(
                                    "fixed standard variant payload fits its projection bound",
                                )
                            })
                            .unwrap_or(Ty::Unit),
                        nominal: false,
                        has_payload: payload.is_some(),
                        payload_syntax: payload.map(|schema| {
                            schema
                                .syntax(span, &mut WorkLimit::new(4096))
                                .expect("fixed standard variant payload fits its syntax bound")
                        }),
                        span,
                    },
                );
            }
        }
    }
    pub(super) fn standard_process_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_process_builtin(name) {
            return None;
        }
        let child = Ty::Named("Process::Child".into());
        let error = Ty::Named("Process::ProcessError".into());
        let status = Ty::Named("Process::ExitStatus".into());
        let inputs = match name {
            "Process::command" => vec![
                Ty::Named("Path::Path".into()),
                Ty::Array(Box::new(Ty::Named("Os::NativeString".into()))),
            ],
            "Process::run" => vec![command_type(), integer("int")],
            "Process::spawn" => vec![command_type()],
            "Process::wait" | "Process::terminate" => vec![child.clone()],
            "Process::success" => vec![status.clone()],
            _ => unreachable!(),
        };
        let writes = matches!(name, "Process::wait" | "Process::terminate");
        if writes {
            if args.len() != inputs.len() {
                self.error("E0314", span, "wrong child operation argument count", []);
            }
            if let Some((mode, value, argument_span)) = args.first() {
                self.require_type(value, &child, *argument_span);
                if *mode != ParameterMode::Mut {
                    self.error(
                        "E0405",
                        *argument_span,
                        "child operations require mut reception",
                        [value.cause],
                    );
                }
                if value.permission != Permission::Write {
                    self.error(
                        "E0520",
                        *argument_span,
                        "child operation has no mutable authority",
                        [value.cause],
                    );
                }
                self.access(value, None, Mode::Write, *argument_span, frame);
            }
        } else {
            self.standard_arguments(
                name,
                args,
                &inputs,
                if name == "Process::run" {
                    1
                } else {
                    inputs.len()
                },
                span,
            );
            for (_, value, argument_span) in args {
                self.deep_read(value, *argument_span, frame);
            }
        }
        if !matches!(name, "Process::command" | "Process::success") {
            frame.obligations.effects.insert("Fiber".into());
            frame.obligations.concrete_effects.insert("Fiber".into());
        }
        Some(match name {
            "Process::command" if args.len() == 2 => {
                let ty = command_type();
                let mut program = args[0].1.clone();
                let mut arguments = self.clone_value(&args[1].1, span, frame, false);
                arguments.ty = inputs[1].clone();
                let copied = self.heap.reachable(arguments.origins.nodes.iter().copied());
                for ((node, _), field) in &mut self.fields {
                    if copied.contains(node) {
                        field.permission = Permission::Read;
                        field.publication = Publication::Immutable;
                        field.construction = false;
                    }
                }
                arguments.permission = Permission::Read;
                arguments.publication = Publication::Immutable;
                arguments.construction = false;
                let node = self.allocate(span, 0xC04D_0001, frame.owner);
                self.standard_read_handle(&mut program);
                self.store_field(node, Slot::Field("program".into()), program);
                self.store_field(node, Slot::Field("args".into()), arguments);
                for field in ["cwd", "env", "input", "stdout", "stderr"] {
                    let Ty::Record(fields) = &ty else {
                        unreachable!()
                    };
                    let mut value = if matches!(field, "cwd" | "env") {
                        let mut value = self.none_value(span);
                        value.ty = fields[field].1.clone();
                        value
                    } else {
                        self.constructor_name(
                            if field == "input" {
                                "Process::Input::Inherit"
                            } else {
                                "Process::OutputMode::Inherit"
                            },
                            span,
                            frame,
                        )
                        .expect("standard process constructors registered")
                    };
                    value.permission = Permission::Read;
                    value.publication = Publication::Immutable;
                    value.construction = false;
                    self.store_field(node, Slot::Field(field.into()), value);
                }
                let mut command =
                    Value::reference(ty, node, self.heap.nodes[node.0 as usize].cause);
                command.permission = Permission::Read;
                command.publication = Publication::Immutable;
                command.construction = false;
                command
            }
            "Process::command" => self.unit(span),
            "Process::run" => self.standard_result(output_type(), error, span, frame.owner),
            "Process::spawn" => self.standard_result(child, error, span, frame.owner),
            "Process::wait" => self.standard_result(status, error, span, frame.owner),
            "Process::terminate" => self.standard_result(Ty::Unit, error, span, frame.owner),
            _ => self.standard_value(Ty::Bool, span, frame.owner, 0),
        })
    }
}
