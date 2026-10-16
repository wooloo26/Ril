//! Standard-library contracts are semantic operations, with explicit storage and
//! inspection obligations. Their native implementation does not determine proof.
use super::*;
#[path = "standard_binary.rs"]
mod binary;
#[path = "standard_collections.rs"]
mod collections;
#[path = "standard_environment.rs"]
mod environment;
#[path = "standard_file.rs"]
mod file;
#[path = "standard_native.rs"]
mod native;
#[path = "standard_order.rs"]
mod order;
#[path = "standard_process.rs"]
mod process;
#[path = "standard_temporal.rs"]
mod temporal;
#[path = "standard_variants.rs"]
mod variants;

pub(super) fn is_builtin(name: &str) -> bool {
    super::concurrent::is_builtin(name)
        || super::parallel::is_builtin(name)
        || simple_signature(name).is_some()
        || collections::is_collection_builtin(name)
        || binary::is_binary_builtin(name)
        || variants::is_variant_builtin(name)
        || temporal::is_temporal_builtin(name)
        || order::is_order_builtin(name)
        || native::is_native_builtin(name)
        || file::is_file_builtin(name)
        || environment::is_environment_builtin(name)
        || process::is_process_builtin(name)
        || matches!(
            name,
            "Num::convert"
                | "Io::read_buffered"
                | "Io::write_buffered"
                | "Io::flush"
                | "inner"
                | "Prelude::inner"
                | "StringBuilder::new"
                | "StringBuilder::append"
                | "StringBuilder::append_scalar"
                | "StringBuilder::clear"
                | "StringBuilder::to_string"
        )
}
pub(super) fn file_type(name: &str) -> Option<Ty> {
    if let Some(ty) = super::concurrent::builtin_type(name) {
        return Some(ty);
    }
    if let Some(ty) = process::process_type(name) {
        return Some(ty);
    }
    Some(match name {
        "File::Handle" | "File::OpenMode" | "File::SeekFrom" | "File::FileKind"
        | "Io::ReadBuffer" | "Io::WriteBuffer" => Ty::Named(name.into()),
        "Io::IoError" => file::io_error(),
        "Io::ReadChunk" => file::read_chunk(),
        "Io::WriteProgress" => file::write_progress(),
        "File::Metadata" => file::file_metadata(),
        "File::Entry" => file::file_entry(),
        _ => return None,
    })
}
pub(super) fn builtin_callable_type(name: &str) -> Option<Ty> {
    let input = match name {
        "Order::compare_int" => integer("int"),
        "Order::compare_str" => Ty::Str,
        "Order::compare_bytes" => Ty::Bytes,
        "Order::total_f64" => float("f64"),
        _ => return None,
    };
    Some(Ty::Callable(
        vec![input.clone(), input],
        Box::new(Ty::Named("Order::Ordering".into())),
    ))
}
pub(super) fn storage_callable(name: &str) -> bool {
    matches!(
        name,
        "Array::push" | "Array::insert" | "Array::truncate" | "Map::set"
    )
}
pub(super) fn builtin_callable_signature(name: &str, span: Span) -> Option<(Ty, Vec<Parameter>)> {
    if let Some(parameters) = super::parallel_signatures::parameters(name, span) {
        return Some((
            Ty::Callable(vec![Ty::Unknown; parameters.len()], Box::new(Ty::Unknown)),
            parameters,
        ));
    }
    let (inputs, result) = match name {
        "Io::read_buffer" | "Io::write_buffer" => (
            vec![("capacity", ParameterMode::Read, integer("int"))],
            Ty::Named(
                if name == "Io::read_buffer" {
                    "Io::ReadBuffer"
                } else {
                    "Io::WriteBuffer"
                }
                .into(),
            ),
        ),
        "File::read_chunk" => (
            vec![
                ("file", ParameterMode::Mut, Ty::Named("File::Handle".into())),
                ("max_bytes", ParameterMode::Read, integer("int")),
            ],
            Ty::Result(Box::new(file::read_chunk()), Box::new(file::io_error())),
        ),
        "File::write" => (
            vec![
                ("file", ParameterMode::Mut, Ty::Named("File::Handle".into())),
                ("data", ParameterMode::Read, Ty::Bytes),
            ],
            file::write_progress(),
        ),
        "Process::wait" => (
            vec![(
                "child",
                ParameterMode::Mut,
                Ty::Named("Process::Child".into()),
            )],
            Ty::Result(
                Box::new(Ty::Named("Process::ExitStatus".into())),
                Box::new(Ty::Named("Process::ProcessError".into())),
            ),
        ),
        "Process::terminate" => (
            vec![(
                "child",
                ParameterMode::Mut,
                Ty::Named("Process::Child".into()),
            )],
            Ty::Result(
                Box::new(Ty::Unit),
                Box::new(Ty::Named("Process::ProcessError".into())),
            ),
        ),
        _ => return None,
    };
    let parameters = inputs
        .iter()
        .map(|(name, mode, ty)| {
            let type_name = match ty {
                Ty::Named(name) | Ty::Int(name) => name.as_str(),
                Ty::Bytes => "bytes",
                _ => unreachable!(),
            };
            Parameter {
                pattern: Pattern {
                    hir_id: None,
                    kind: PatternKind::Name((*name).into()),
                    span,
                },
                mode: *mode,
                ty: Some(TypeExpr {
                    hir_id: None,
                    text: type_name.into(),
                    kind: TypeKind::Name {
                        path: type_name.split("::").map(str::to_owned).collect(),
                        arguments: vec![],
                    },
                    span,
                }),
                default: None,
                span,
            }
        })
        .collect();
    Some((
        Ty::Callable(
            inputs.into_iter().map(|(_, _, ty)| ty).collect(),
            Box::new(result),
        ),
        parameters,
    ))
}
pub(super) fn constant_ty(name: &str) -> Option<Ty> {
    if let Some(ty) = file::file_constant(name) {
        return Some(ty);
    }
    if let Some(ty) = native::native_constant(name) {
        return Some(ty);
    }
    if let Some(ty) = order::order_constant(name) {
        return Some(ty);
    }
    if let Some(ty) = temporal::temporal_constant(name) {
        return Some(ty);
    }
    Some(match name {
        "Num::NumError::InvalidSyntax"
        | "Num::NumError::OutOfRange"
        | "Num::NumError::InvalidRadix" => Ty::Named("Num::NumError".into()),
        "Binary::ByteOrder::Little" | "Binary::ByteOrder::Big" => {
            Ty::Named("Binary::ByteOrder".into())
        }
        "Binary::BinaryError::UnexpectedEnd"
        | "Binary::BinaryError::Overflow"
        | "Binary::BinaryError::NonCanonical" => Ty::Named("Binary::BinaryError".into()),
        _ => return None,
    })
}

enum Output {
    Value(Ty),
    Array(Ty),
    Optional(Ty),
    Result(Ty, Ty),
}
struct Signature {
    inputs: Vec<Ty>,
    minimum: usize,
    output: Output,
    deep: bool,
}
fn integer(name: &str) -> Ty {
    Ty::Int(name.into())
}
fn float(name: &str) -> Ty {
    Ty::Float(name.into())
}
fn error_record(field: &str, ty: Ty) -> Ty {
    Ty::Record([(field.into(), (false, ty))].into())
}
fn signature(inputs: Vec<Ty>, output: Output) -> Signature {
    Signature {
        minimum: inputs.len(),
        inputs,
        output,
        deep: false,
    }
}
fn numeric(name: &str) -> Option<Ty> {
    Some(match name {
        "int" | "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "bigint" => {
            integer(name)
        }
        "f32" | "f64" => float(name),
        _ => return None,
    })
}
fn simple_signature(name: &str) -> Option<Signature> {
    use Output::*;
    if let Some(operation) = name.strip_prefix("Num::") {
        if let Some(suffix) = operation.strip_prefix("parse_") {
            let ty = numeric(suffix)?;
            let inputs = if matches!(ty, Ty::Int(_)) {
                vec![Ty::Str, integer("int")]
            } else {
                vec![Ty::Str]
            };
            return Some(Signature {
                inputs,
                minimum: 1,
                output: Result(ty, Ty::Named("Num::NumError".into())),
                deep: false,
            });
        }
        if let Some(suffix) = operation.strip_prefix("format_") {
            let ty = numeric(suffix)?;
            return Some(if matches!(ty, Ty::Int(_)) {
                Signature {
                    inputs: vec![ty, integer("int")],
                    minimum: 1,
                    output: Result(Ty::Str, Ty::Named("Num::NumError".into())),
                    deep: false,
                }
            } else {
                signature(vec![ty], Value(Ty::Str))
            });
        }
    }
    if let Some(operation) = name.strip_prefix("Math::") {
        let (operation, ty) = if let Some(operation) = operation.strip_suffix("_f32") {
            (operation, float("f32"))
        } else {
            (operation, float("f64"))
        };
        return Some(match operation {
            "sqrt" | "floor" | "ceil" | "round" | "abs" => signature(vec![ty.clone()], Value(ty)),
            "is_nan" | "is_finite" => signature(vec![ty], Value(Ty::Bool)),
            "min" | "max" => signature(vec![ty.clone(), ty.clone()], Value(ty)),
            _ => return None,
        });
    }
    Some(match name {
        "print" | "println" | "Prelude::print" | "Prelude::println" => {
            signature(vec![Ty::Str], Value(Ty::Unit))
        }
        "Bytes::from_array" => Signature {
            deep: true,
            ..signature(vec![Ty::Array(Box::new(integer("u8")))], Value(Ty::Bytes))
        },
        "Bytes::to_array" => signature(vec![Ty::Bytes], Array(integer("u8"))),
        "Bytes::slice" => signature(
            vec![Ty::Bytes, integer("int"), integer("int")],
            Optional(Ty::Bytes),
        ),
        "Bytes::concat" => signature(vec![Ty::Bytes, Ty::Bytes], Value(Ty::Bytes)),
        "Bytes::find" => signature(vec![Ty::Bytes, Ty::Bytes], Optional(integer("int"))),
        "Bytes::at" => signature(vec![Ty::Bytes, integer("int")], Optional(integer("u8"))),
        "Hex::encode" => signature(vec![Ty::Bytes], Value(Ty::Str)),
        "Hex::decode" => signature(
            vec![Ty::Str],
            Result(Ty::Bytes, error_record("offset", integer("int"))),
        ),
        "Crypto::sha256" => signature(vec![Ty::Str], Value(Ty::Bytes)),
        "Crypto::sha256_bytes" => signature(vec![Ty::Bytes], Value(Ty::Bytes)),
        "Unicode::decode_utf8" => signature(
            vec![Ty::Bytes],
            Result(Ty::Str, error_record("offset", integer("int"))),
        ),
        "Unicode::from_scalar" => signature(
            vec![integer("u32")],
            Result(Ty::Str, error_record("value", integer("u32"))),
        ),
        "Unicode::is_white_space"
        | "Unicode::is_alphabetic"
        | "Unicode::is_decimal_digit"
        | "Unicode::is_xid_start"
        | "Unicode::is_xid_continue" => signature(vec![integer("u32")], Value(Ty::Bool)),
        "Unicode::lowercase" | "Unicode::uppercase" => signature(vec![Ty::Str], Value(Ty::Str)),
        "String::split" => signature(vec![Ty::Str, Ty::Str], Array(Ty::Str)),
        "String::trim" => signature(vec![Ty::Str], Value(Ty::Str)),
        "String::contains" | "String::starts_with" | "String::ends_with" => {
            signature(vec![Ty::Str, Ty::Str], Value(Ty::Bool))
        }
        "String::replace" => signature(vec![Ty::Str, Ty::Str, Ty::Str], Value(Ty::Str)),
        "String::find" => signature(vec![Ty::Str, Ty::Str], Optional(integer("int"))),
        "String::slice" => signature(
            vec![Ty::Str, integer("int"), integer("int")],
            Optional(Ty::Str),
        ),
        "String::concat" => signature(vec![Ty::Str, Ty::Str], Value(Ty::Str)),
        "String::join" => Signature {
            deep: true,
            ..signature(vec![Ty::Array(Box::new(Ty::Str)), Ty::Str], Value(Ty::Str))
        },
        "String::lines" => signature(vec![Ty::Str], Array(Ty::Str)),
        "String::scalar_at" => signature(vec![Ty::Str, integer("int")], Optional(integer("u32"))),
        "String::scalars" => signature(vec![Ty::Str], Array(integer("u32"))),
        "String::utf8" => signature(vec![Ty::Str], Value(Ty::Bytes)),
        "String::byte_len" => signature(vec![Ty::Str], Value(integer("int"))),
        "String::byte_offset" | "String::scalar_offset" => {
            signature(vec![Ty::Str, integer("int")], Optional(integer("int")))
        }
        _ => return None,
    })
}

impl Checker {
    pub(super) fn standard_typed_builtin(
        &mut self,
        callee: &Value,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if super::parallel::is_builtin(name) {
            return Some(self.parallel_typed_builtin(callee, name, args, span, frame));
        }
        if let Some(value) = self.standard_process_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_environment_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_file_builtin(name, args, span, frame) {
            return Some(value);
        }
        self.standard_order_typed(callee, name, args, span, frame)
    }
    pub(super) fn standard_generic(
        &mut self,
        value: &mut Value,
        arguments: &[TypeExpr],
        span: Span,
    ) {
        if self.external_generic(value, arguments, span) {
            return;
        }
        if self.parallel_generic(value, arguments, span) {
            return;
        }
        if self.concurrent_generic(value, arguments, span) {
            return;
        }
        if self.standard_order_generic(value, arguments, span) {
            return;
        }
        if !value
            .callables
            .iter()
            .any(|callable| matches!(callable, Callable::Builtin(name) if name == "Num::convert"))
        {
            self.unsupported(
                span,
                "explicit generic application requires a checked callable instantiation contract",
            );
            return;
        }
        if arguments.len() != 2 {
            self.error(
                "E0340",
                span,
                "Num::convert requires source and destination numeric types",
                [value.cause],
            );
            return;
        }
        let source = self.ty(&arguments[0]);
        let destination = self.ty(&arguments[1]);
        let source = self.expanded(&source, &mut BTreeSet::new());
        let destination = self.expanded(&destination, &mut BTreeSet::new());
        let primitive = |ty: &Ty| match ty {
            Ty::Int(name) | Ty::Float(name) => numeric(name).map(|_| name.clone()),
            _ => None,
        };
        let (Some(source_name), Some(destination_name)) =
            (primitive(&source), primitive(&destination))
        else {
            self.error(
                "E0301",
                span,
                "Num::convert admits only numeric source and destination types",
                [value.cause],
            );
            return;
        };
        let identity = format!("Num::__convert_{source_name}_to_{destination_name}");
        value.callables = vec![Callable::Builtin(identity)];
        value.ty = Ty::Callable(
            vec![source],
            Box::new(Ty::Result(
                Box::new(destination),
                Box::new(Ty::Named("Num::NumError".into())),
            )),
        );
    }
    pub(super) fn standard_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if matches!(
            name,
            "Io::read_buffered" | "Io::write_buffered" | "Io::flush"
        ) {
            return Some(self.io_buffered(name, args, span, frame));
        }
        if let Some(value) = self.parallel_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_native_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_order_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_temporal_builtin(name, args, span, frame) {
            return Some(value);
        }
        if name.strip_prefix("Prelude::").unwrap_or(name) == "inner" {
            if args.len() != 1 {
                self.error("E0314", span, "inner requires one nominal value", []);
                return Some(self.unit(span));
            }
            if args[0].0 != ParameterMode::Read {
                self.error(
                    "E0405",
                    args[0].2,
                    "inner borrows its nominal value read-only",
                    [args[0].1.cause],
                );
            }
            if let Some(value) = self.standard_duration_inner(&args[0].1, span, frame) {
                return Some(value);
            }
            return Some(self.nominal_inner(&args[0].1, span, frame));
        }
        if let Some(value) = self.standard_collection_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_binary_builtin(name, args, span, frame) {
            return Some(value);
        }
        if let Some(value) = self.standard_variant_builtin(name, args, span, frame) {
            return Some(value);
        }
        if name == "Num::convert" {
            self.unsupported(
                span,
                "numeric conversion requires preserved generic destination type",
            );
            return Some(self.unit(span));
        }
        if let Some(types) = name.strip_prefix("Num::__convert_")
            && let Some((source, destination)) = types.split_once("_to_")
            && let (Some(source), Some(destination)) = (numeric(source), numeric(destination))
        {
            self.standard_arguments(name, args, &[source], 1, span);
            return Some(self.standard_result(
                destination,
                Ty::Named("Num::NumError".into()),
                span,
                frame.owner,
            ));
        }
        if name.starts_with("StringBuilder::") {
            return self.standard_builder(name, args, span, frame);
        }
        let signature = simple_signature(name)?;
        if matches!(
            name.strip_prefix("Prelude::").unwrap_or(name),
            "print" | "println"
        ) {
            frame.obligations.effects.insert("Fiber".into());
            frame.obligations.concrete_effects.insert("Fiber".into());
        }
        self.standard_arguments(name, args, &signature.inputs, signature.minimum, span);
        for (_, value, argument_span) in args {
            if signature.deep {
                self.deep_read(value, *argument_span, frame);
            } else if !value.ty.scalar() {
                self.access(value, None, Mode::Read, *argument_span, frame);
            }
        }
        Some(match signature.output {
            Output::Value(ty) => self.standard_value(ty, span, frame.owner, 0),
            Output::Array(element) => self.standard_array(element, span, frame.owner),
            Output::Optional(ty) => {
                let payload = self.standard_value(ty, span, frame.owner, 0);
                self.standard_option(payload, None, span, frame.owner)
            }
            Output::Result(ok, error) => self.standard_result(ok, error, span, frame.owner),
        })
    }
    fn standard_arguments(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        expected: &[Ty],
        minimum: usize,
        span: Span,
    ) {
        if !(minimum..=expected.len()).contains(&args.len()) {
            self.error(
                "E0314",
                span,
                format!("wrong argument count for {name}"),
                [],
            );
        }
        for ((mode, value, argument_span), ty) in args.iter().zip(expected) {
            if *mode != ParameterMode::Read {
                self.error(
                    "E0405",
                    *argument_span,
                    "standard-library argument mode mismatch",
                    [value.cause],
                );
            }
            self.require_type(value, ty, *argument_span);
            if unknown_type(&value.ty)
                && !self.standard_contextual_storage(value, &mut BTreeSet::new())
            {
                self.unsupported(
                    *argument_span,
                    "standard-library argument type is unresolved",
                );
            }
        }
    }
    fn standard_contextual_storage(&self, value: &Value, seen: &mut BTreeSet<NodeId>) -> bool {
        if !unknown_type(&value.ty) {
            return true;
        }
        match self.expanded(&value.ty, &mut BTreeSet::new()) {
            Ty::Optional(_) if value.option_tag == Some(false) => return true,
            Ty::Optional(_) if value.option_tag == Some(true) => {
                return value
                    .option_payload
                    .as_ref()
                    .is_some_and(|payload| self.standard_contextual_storage(payload, seen));
            }
            Ty::Record(fields) => {
                return !value.origins.nodes.is_empty()
                    && value.origins.nodes.iter().all(|node| {
                        if !seen.insert(*node) {
                            return false;
                        }
                        fields.keys().all(|name| {
                            self.fields
                                .get(&(*node, Slot::Field(name.clone())))
                                .is_some_and(|child| {
                                    self.standard_contextual_storage(child, &mut seen.clone())
                                })
                        })
                    });
            }
            Ty::Tuple(items) => {
                return !value.origins.nodes.is_empty()
                    && value.origins.nodes.iter().all(|node| {
                        if !seen.insert(*node) {
                            return false;
                        }
                        (0..items.len()).all(|index| {
                            self.fields
                                .get(&(*node, Slot::Tuple(index as u32)))
                                .is_some_and(|child| {
                                    self.standard_contextual_storage(child, &mut seen.clone())
                                })
                        })
                    });
            }
            _ => {}
        }
        let selected = self.collection_type(value);
        if unknown_type(&selected)
            || !matches!(self.expanded(&value.ty, &mut BTreeSet::new()), Ty::Array(_))
        {
            return false;
        }
        if self.known_array_length(value) == Some(0) {
            return true;
        }
        if value.origins.nodes.is_empty() {
            return false;
        }
        for node in &value.origins.nodes {
            if !seen.insert(*node) {
                return false;
            }
            let children: Vec<_> = self
                .fields
                .iter()
                .filter(|((parent, slot), _)| {
                    parent == node && matches!(slot, Slot::Index(_) | Slot::AnyIndex)
                })
                .map(|(_, value)| value)
                .collect();
            if children.is_empty()
                || children
                    .iter()
                    .any(|child| !self.standard_contextual_storage(child, &mut seen.clone()))
            {
                return false;
            }
        }
        true
    }
    pub(super) fn standard_value(
        &mut self,
        ty: Ty,
        span: Span,
        owner: ScopeId,
        discriminator: u32,
    ) -> Value {
        let cause = self.cause(CauseKind::Source, span, "standard-library result", []);
        if ty.scalar() {
            return Value::scalar(ty, None, cause);
        }
        let node = self.allocate(span, discriminator, owner);
        let value = Value::reference(ty.clone(), node, cause);
        if matches!(&ty, Ty::Named(name) if name.starts_with("Process::") || name.starts_with("Concurrent::") || name.starts_with("Channel::"))
        {
            let variants: Vec<_> = self
                .constructors
                .values()
                .filter(|constructor| constructor.owner == ty)
                .cloned()
                .collect();
            for (index, constructor) in variants.into_iter().enumerate() {
                let payload = self.standard_value(
                    constructor.payload,
                    span,
                    owner,
                    discriminator
                        .saturating_add(10_000)
                        .saturating_add(index as u32 * 100),
                );
                self.store_field(
                    node,
                    Slot::Field(format!("$variant:{}", constructor.tag)),
                    payload,
                );
            }
        }
        if let Ty::Record(fields) = &ty {
            for (index, (name, (_, ty))) in fields.iter().enumerate() {
                let child = self.standard_value(
                    ty.clone(),
                    span,
                    owner,
                    discriminator
                        .saturating_add(100)
                        .saturating_add(index as u32),
                );
                self.store_field(node, Slot::Field(name.clone()), child);
            }
        }
        if let Ty::Tuple(fields) = ty {
            for (index, ty) in fields.into_iter().enumerate() {
                let child = self.standard_value(
                    ty,
                    span,
                    owner,
                    discriminator
                        .saturating_add(100)
                        .saturating_add(index as u32),
                );
                self.store_field(node, Slot::Tuple(index as u32), child);
            }
        }
        value
    }
    fn standard_array(&mut self, element: Ty, span: Span, owner: ScopeId) -> Value {
        let child = self.standard_value(element.clone(), span, owner, 1);
        let node = self.allocate(span, 0, owner);
        let cause = self.heap.nodes[node.0 as usize].cause;
        self.store_field(node, Slot::AnyIndex, child);
        let mut output = Value::reference(Ty::Array(Box::new(element)), node, cause);
        self.complete_standard_array_source(&mut output, span);
        output
    }
    pub(in crate::sema::checker) fn standard_option(
        &mut self,
        payload: Value,
        known: Option<bool>,
        span: Span,
        owner: ScopeId,
    ) -> Value {
        let cause = self.cause(
            CauseKind::Source,
            span,
            "optional constructor choice",
            [payload.cause],
        );
        if known == Some(false) {
            let mut value = Value::scalar(Ty::Optional(Box::new(payload.ty.clone())), None, cause);
            value.option_tag = known;
            return value;
        }
        let mut value = payload.clone();
        value.cause = cause;
        value.option_identity = if known.is_none() {
            self.new_optional_identity(payload.ty.clone(), cause, owner, span)
        } else {
            None
        };
        value.source_type_witness = None;
        value.ty = Ty::Optional(Box::new(payload.ty.clone()));
        value.constant = None;
        value.static_coordinate = None;
        value.unsuffixed_numeric = false;
        value.literal_number = false;
        value.option_payload = Some(Box::new(payload));
        value.option_tag = known;
        value.callables.clear();
        value.callable_bounds.clear();
        value.callable_returns.clear();
        value.signature = None;
        value.variant_tag = None;
        value.variant_payload = None;
        value.variant_witnesses.clear();
        value.result_tag = None;
        value.result_payload = None;
        value.result_success = None;
        value.result_error = None;
        value.outer_results.clear();
        value.must_outer_results.clear();
        if known != Some(true) {
            value.must_results.clear();
        }
        value
    }
    fn standard_result(&mut self, ok: Ty, error: Ty, span: Span, owner: ScopeId) -> Value {
        let payload = self.standard_value(ok.clone(), span, owner, 0);
        let error_payload = self.standard_value(error.clone(), span, owner, 1);
        let mut value = self.make_result(true, payload, span, owner);
        value.result_error = Some(Box::new(error_payload.clone()));
        value.origins.nodes.extend(error_payload.origins.nodes);
        value.ty = Ty::Result(Box::new(ok), Box::new(error));
        value.result_tag = None;
        value.result_payload = None;
        value
    }
    fn standard_builder(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let ty = Ty::Named("StringBuilder::Builder".into());
        if name == "StringBuilder::new" {
            self.standard_arguments(name, args, &[], 0, span);
            return Some(self.standard_value(ty, span, frame.owner, 0));
        }
        let (inputs, writes) = match name {
            "StringBuilder::append" => (vec![ty, Ty::Str], true),
            "StringBuilder::append_scalar" => (vec![ty, integer("u32")], true),
            "StringBuilder::clear" => (vec![ty], true),
            "StringBuilder::to_string" => (vec![ty], false),
            _ => return None,
        };
        if args.len() != inputs.len() {
            self.error("E0314", span, "wrong builder argument count", []);
        }
        for (index, ((mode, value, argument_span), ty)) in args.iter().zip(&inputs).enumerate() {
            self.require_type(value, ty, *argument_span);
            let expected = if index == 0 && writes {
                ParameterMode::Mut
            } else {
                ParameterMode::Read
            };
            if *mode != expected {
                self.error(
                    "E0405",
                    *argument_span,
                    "builder argument mode mismatch",
                    [value.cause],
                );
            }
            if index == 0 {
                if writes && value.permission != Permission::Write {
                    self.error(
                        "E0520",
                        *argument_span,
                        "builder receiver is read-only",
                        [value.cause],
                    );
                }
                self.access(
                    value,
                    None,
                    if writes { Mode::Write } else { Mode::Read },
                    *argument_span,
                    frame,
                );
            }
        }
        Some(match name {
            "StringBuilder::append_scalar" => self.standard_result(
                Ty::Unit,
                error_record("value", integer("u32")),
                span,
                frame.owner,
            ),
            "StringBuilder::to_string" => self.standard_value(Ty::Str, span, frame.owner, 0),
            _ => self.unit(span),
        })
    }
}
fn unknown_type(ty: &Ty) -> bool {
    match ty {
        Ty::Unknown => true,
        Ty::Array(inner) | Ty::Optional(inner) | Ty::Immutable(inner) | Ty::Set(inner) => {
            unknown_type(inner)
        }
        Ty::Map(a, b) | Ty::Result(a, b) => unknown_type(a) || unknown_type(b),
        Ty::Tuple(items) => items.iter().any(unknown_type),
        Ty::Record(fields) => fields.values().any(|(_, ty)| unknown_type(ty)),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn an_empty_array_can_use_a_selected_storage_type_without_admitting_unknown_formals() {
        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(Env::new(), false);
        let parsed = ril_syntax::parse_expression("[]", FileId(0));
        let empty = checker.expression(&parsed.expression, &mut frame);
        let expected = Ty::Array(Box::new(Ty::Named("Os::NativeString".into())));
        checker.standard_arguments(
            "checked operation",
            &[(ParameterMode::Read, empty, parsed.expression.span)],
            std::slice::from_ref(&expected),
            1,
            parsed.expression.span,
        );
        assert!(
            checker.diagnostics.is_empty() && checker.unsupported.is_empty(),
            "{:?} {:?}",
            checker.diagnostics,
            checker.unsupported
        );
        let unknown = checker.formal_value(
            Ty::Array(Box::new(Ty::Unknown)),
            0,
            parsed.expression.span,
            &mut BTreeSet::new(),
        );
        checker.standard_arguments(
            "checked operation",
            &[(ParameterMode::Read, unknown, parsed.expression.span)],
            &[expected],
            1,
            parsed.expression.span,
        );
        assert!(!checker.unsupported.is_empty());
    }
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        crate::sema::analyze(&parsed.program, FileId(0))
    }
    #[test]
    fn scalar_contracts_check_types_counts_and_result_inspection() {
        let result = check(
            "fn example() { assert(Math::sqrt(4.0) == 2.0); assert(Num::parse_u8(\"2\") is Ok(2u8)); assert(Hex::decode(\"ff\") is Ok(_)); assert(Unicode::decode_utf8(b\"x\") is Ok(\"x\")); let chunks = String::split(\"a,b\", \",\"); assert(len(chunks) == 2) }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for (source, code) in [
            ("fn example() { let _ = Crypto::sha256(1) }", "E0301"),
            ("fn example() { let _ = Math::sqrt(1.0, 2.0) }", "E0314"),
            (
                "fn example() { let r = Num::parse_int(\"1\"); let _ = r }",
                "E0720",
            ),
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "expected {code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn collection_snapshots_and_builder_receivers_track_authority() {
        let result = check(
            "fn example() { let mut data = Bytes::to_array(b\"a\"); data[0] = 2u8; let mut builder = StringBuilder::new(); StringBuilder::append(mut builder, \"hello\"); assert(StringBuilder::to_string(builder) == \"hello\") }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "fn example() { let builder = StringBuilder::new(); StringBuilder::append(mut builder, \"x\") }",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0520"),
            "{:?}",
            result.diagnostics
        );
    }
    #[test]
    fn fresh_outer_arrays_keep_nested_reference_permissions() {
        let result = check(
            "type Cell = { mut value: int }\nfn example() { let base = Cell.{value: 1}; let items = [base]; let mut copied = Array::reverse(items); copied[0].value += 1 }",
        );
        assert!(result.program.is_none());
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520" | "E0522" | "E0528")),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "fn example() { let values = Array::map([1, 2], \\value -> value + 1); assert(Array::first(values) == Some(2)) }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn map_set_types_and_numeric_generic_identity_are_explicit() {
        let result = check(
            "fn example() { let mut table = [\"a\": 1]; Map::set(mut table, \"b\", 2); assert(Map::get(table, \"a\") == Some(1)); let values = Map::values(table); assert(len(values) == 2); let mut members = Set::from([1, 2]); let inserted = Set::insert(mut members, 3); assert(inserted); assert(Set::contains(members, 3)); assert(Num::convert<f64, int>(1.5) is Err(_)) }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        assert!(result.program.unwrap().facts().expressions.iter().any(|fact| fact.value.callables.iter().any(|callable| matches!(callable, Callable::Builtin(name) if name == "Num::__convert_f64_to_int"))));
        for (source, code) in [
            ("fn example() { let _ = Set::from([1.0]) }", "E0328"),
            (
                "fn example() { let mut table = [\"a\": 1]; Map::set(mut table, 1, 2) }",
                "E0301",
            ),
            (
                "fn example() { let _ = Num::convert<str, int>(1) }",
                "E0301",
            ),
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        let parsed = ril_syntax::parse("fn example() { let _ = Num::__convert_f64_to_int(1.5) }");
        assert!(parsed.is_err());
    }
    #[test]
    fn variant_combinators_inspect_inputs_and_preserve_new_nested_duties() {
        let result = check(
            "fn unknown(value: ?int) -> int { Options::unwrap_or_else(value, \\ -> 0) }\nfn checked(value: Result<int, int>) -> Result<int, int> { Results::map(value, \\item -> item + 1) }\nfn example() { assert(Options::map(Some(1), \\item -> item + 1) == Some(2)); assert(Options::and_then(Some(1), \\item -> Some(item + 1)) == Some(2)); let value = Results::map(Ok(1), \\item -> item + 1); assert(value is Ok(2)); let error = Results::map_err(Err(1), \\item -> item + 1); assert(error is Err(2)); let _ = Options::map(None, \\item: int -> Err(\"unvisited\")) }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for source in [
            "fn example() { let _ = Results::map(Ok(1), \\item -> item + 1) }",
            "fn example() { let _ = Options::map(Some(1), \\item -> Err(\"lost\")) }",
            "fn example(value: ?int) { let _ = Options::map(value, \\item -> Err(\"possibly lost\")) }",
            "fn example(value: ?int) { let r = Err(\"still owed on None\"); Options::map(value, \\item -> panic(\"only Some diverges\")); }",
            "fn example() { let value = Results::map(Ok(1), \\item -> Err(\"nested\")); assert(value is Ok(_)) }",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn binary_contracts_keep_cursor_writes_and_result_obligations() {
        let result = check(
            "fn example() { let mut output: []u8 = []; Binary::write_u32(mut output, 1u32, Binary::ByteOrder::Big); let data = Bytes::from_array(output); let mut cursor = Binary::cursor(data); assert(Binary::read_u32(mut cursor, Binary::ByteOrder::Big) is Ok(1u32)); assert(Binary::remaining(cursor) == 0) }",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for (source, code) in [
            (
                "fn example() { let mut cursor = Binary::cursor(b\"a\"); let _ = Binary::read_u8(mut cursor) }",
                "E0720",
            ),
            (
                "fn example() { let cursor = Binary::cursor(b\"a\"); assert(Binary::read_u8(mut cursor) is Ok(_)) }",
                "E0520",
            ),
            (
                "fn example() { let mut cursor = Binary::cursor(b\"a\"); assert(Binary::read_u32(mut cursor, b\"big\") is Ok(_)) }",
                "E0301",
            ),
            (
                "fn example() { let mut cursor = Binary::cursor(b\"a\"); assert(Binary::read_u8(mut cursor, Binary::ByteOrder::Big) is Ok(_)) }",
                "E0314",
            ),
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{code}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
}
