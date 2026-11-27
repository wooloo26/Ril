use std::{path::Path, sync::OnceLock};

use ril_source::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceFile, Span},
};

use ril_syntax::{
    lexer,
    parser::{self, FileKind},
    syntax::{Function, GenericParam, StmtKind, TypeDecl},
};

use super::{File, Intrinsic, PrimitivePhase, StdType};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrimitiveSpec {
    pub module: &'static str,
    pub name: &'static str,
    pub phase: PrimitivePhase,
    pub runtime_symbol: Option<&'static str>,
    pub intrinsic: Option<Intrinsic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrimitiveTypeSpec {
    pub module: &'static str,
    pub name: &'static str,
    pub std_type: StdType,
    pub is_object: bool,
}

const fn prim(
    module: &'static str,
    name: &'static str,
    phase: PrimitivePhase,
    runtime_symbol: Option<&'static str>,
    intrinsic: Option<Intrinsic>,
) -> PrimitiveSpec {
    PrimitiveSpec {
        module,
        name,
        phase,
        runtime_symbol,
        intrinsic,
    }
}

const fn ptype(
    module: &'static str,
    name: &'static str,
    std_type: StdType,
    is_object: bool,
) -> PrimitiveTypeSpec {
    PrimitiveTypeSpec {
        module,
        name,
        std_type,
        is_object,
    }
}

/// Single central manifest of compiler-known standard library types.
pub const PRIMITIVE_TYPES: &[PrimitiveTypeSpec] = {
    use StdType::*;
    &[
        ptype("Prelude", "Option", Option, false),
        ptype("Prelude", "Result", Result, false),
        ptype("Panic", "Report", PanicReport, false),
        ptype("Panic", "Error", PanicError, false),
        ptype("Prelude", "Derived", Derived, true),
        ptype("Reflect", "FieldMode", FieldMode, false),
        ptype("Reflect", "TypeKind", TypeKind, false),
        ptype("Set", "Set", Set, false),
    ]
};

/// Single central manifest of all bodyless standard library primitives.
///
/// Ordinary bodied `.ril` functions in `std/*.ril` are NOT listed here and can
/// be added, edited, or moved without touching compiler code.
pub const PRIMITIVE_FNS: &[PrimitiveSpec] = {
    use Intrinsic::*;
    use PrimitivePhase::{Both, Runtime, Static};
    &[
        // Prelude
        prim("Prelude", "len", Both, Some("ril_rt_len"), Some(Len)),
        prim("Prelude", "inner", Both, None, Some(Inner)),
        prim("Prelude", "clone", Both, Some("ril_rt_clone"), Some(Clone)),
        prim("Prelude", "derive", Both, None, Some(Derive)),
        prim(
            "Prelude",
            "unwind_ctl",
            Runtime,
            Some("ril_rt_abort_ctl"),
            Some(UnwindCtl),
        ),
        prim(
            "Panic",
            "recover",
            Runtime,
            None,
            Some(RecoverPanic),
        ),
        prim(
            "Panic",
            "message",
            Runtime,
            Some("ril_rt_panic_message"),
            Some(PanicMessage),
        ),
        prim("Prelude", "compile_error", Static, None, Some(CompileError)),
        prim(
            "Prelude",
            "compile_error_code",
            Static,
            None,
            Some(CompileErrorCode),
        ),
        prim("Prelude", "panic", Both, Some("ril_rt_panic"), Some(Panic)),
        // Io / File
        prim("Io", "print", Runtime, Some("ril_rt_print"), Some(Print)),
        prim(
            "File",
            "read",
            Runtime,
            Some("ril_rt_file_read"),
            Some(FileRead),
        ),
        prim(
            "File",
            "write",
            Runtime,
            Some("ril_rt_file_write"),
            Some(FileWrite),
        ),
        // Numeric
        prim(
            "Numeric",
            "to_f64",
            Both,
            Some("ril_rt_to_f64"),
            Some(NumericToF64),
        ),
        prim(
            "Numeric",
            "to_int_trunc",
            Both,
            Some("ril_rt_trunc"),
            Some(NumericTrunc),
        ),
        // Array
        prim(
            "Array",
            "push",
            Both,
            Some("ril_rt_append"),
            Some(ArrayPush),
        ),
        prim(
            "Array",
            "pop",
            Both,
            Some("ril_rt_array_pop"),
            Some(ArrayPop),
        ),
        prim(
            "Array",
            "pop_front",
            Both,
            Some("ril_rt_array_pop_front"),
            Some(ArrayPopFront),
        ),
        prim(
            "Array",
            "insert",
            Both,
            Some("ril_rt_array_insert"),
            Some(ArrayInsert),
        ),
        prim(
            "Array",
            "remove",
            Both,
            Some("ril_rt_array_remove"),
            Some(ArrayRemove),
        ),
        // Map
        prim(
            "Map",
            "insert",
            Both,
            Some("ril_rt_map_insert"),
            Some(MapInsert),
        ),
        prim(
            "Map",
            "replace",
            Both,
            Some("ril_rt_map_replace"),
            Some(MapReplace),
        ),
        prim(
            "Map",
            "remove",
            Both,
            Some("ril_rt_map_remove"),
            Some(MapRemove),
        ),
        // String
        prim("String", "inspect", Both, None, Some(StringInspect)),
        prim(
            "String",
            "scalar_at",
            Both,
            Some("ril_rt_str_at"),
            Some(StringAt),
        ),
        prim(
            "String",
            "scalars",
            Both,
            Some("ril_rt_str_scalars"),
            Some(StringScalars),
        ),
        prim(
            "String",
            "from_scalars",
            Both,
            Some("ril_rt_str_from_scalars"),
            Some(StringFromScalars),
        ),
        prim(
            "String",
            "encode_utf8",
            Both,
            Some("ril_rt_encode_utf8"),
            Some(StringEncodeUtf8),
        ),
        prim(
            "String",
            "decode_utf8",
            Both,
            Some("ril_rt_decode_utf8"),
            Some(StringDecodeUtf8),
        ),
        // Bytes
        prim("Bytes", "at", Both, Some("ril_rt_bytes_at"), Some(BytesAt)),
        prim(
            "Bytes",
            "from_array",
            Both,
            Some("ril_rt_bytes_from_array"),
            Some(BytesFromArray),
        ),
        // Reflect
        prim("Reflect", "type_name", Static, None, Some(TypeName)),
        prim("Reflect", "fields", Static, None, Some(Fields)),
        prim("Reflect", "sum_tags", Static, None, Some(SumTags)),
        prim(
            "Reflect",
            "raw_type_kind",
            Static,
            None,
            Some(ReflectRawTypeKind),
        ),
        prim("Reflect", "attrs", Static, None, Some(ReflectAttrs)),
        prim(
            "Reflect",
            "field_attrs",
            Static,
            None,
            Some(ReflectFieldAttrs),
        ),
        prim(
            "Reflect",
            "variant_attrs",
            Static,
            None,
            Some(ReflectVariantAttrs),
        ),
        prim(
            "Reflect",
            "has_default",
            Static,
            None,
            Some(ReflectHasDefault),
        ),
    ]
};

pub(crate) fn lookup_primitive(module_name: &str, name: &str) -> Option<&'static PrimitiveSpec> {
    PRIMITIVE_FNS
        .iter()
        .find(|spec| spec.module == module_name && spec.name == name)
}

pub(super) enum TypeRegistration {
    Object,
    Regular,
}

pub(super) struct StdModule {
    pub(super) module_name: &'static str,
    pub(super) import_key: &'static str,
    pub(super) file: File,
}

const STD_SOURCES: &[(&str, &str, &str, &str)] = &[
    (
        "Prelude",
        "ril/prelude",
        "ril/std/prelude.ril",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../std/prelude.ril"
        )),
    ),
    (
        "Numeric",
        "ril/numeric",
        "ril/std/numeric.ril",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../std/numeric.ril"
        )),
    ),
    (
        "Array",
        "ril/array",
        "ril/std/array.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/array.ril")),
    ),
    (
        "Map",
        "ril/map",
        "ril/std/map.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/map.ril")),
    ),
    (
        "Set",
        "ril/set",
        "ril/std/set.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/set.ril")),
    ),
    (
        "String",
        "ril/string",
        "ril/std/string.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/string.ril")),
    ),
    (
        "Bytes",
        "ril/bytes",
        "ril/std/bytes.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/bytes.ril")),
    ),
    (
        "Reflect",
        "ril/reflect",
        "ril/std/reflect.ril",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../std/reflect.ril"
        )),
    ),
    (
        "Io",
        "ril/io",
        "ril/std/io.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/io.ril")),
    ),
    (
        "File",
        "ril/file",
        "ril/std/file.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/file.ril")),
    ),
    (
        "Math",
        "ril/math",
        "ril/std/math.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/math.ril")),
    ),
    (
        "Panic",
        "ril/panic",
        "ril/std/panic.ril",
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/panic.ril")),
    ),
];

fn render_diagnostic(source: &SourceFile, diag: &Diagnostic) -> String {
    let mut map = ril_source::span::SourceMap::default();
    let _ = map.add_with_id(source.id(), source.path().into(), source.text().as_bytes());
    let mut out = Vec::new();
    let _ = diag.render(&map, &mut out);
    String::from_utf8_lossy(&out).into_owned()
}

fn parse_embedded(path_str: &str, text: &str) -> File {
    let path = Path::new(path_str);
    let id = FileId::from_path(path);
    let source = SourceFile::from_bytes(id, path.into(), text.as_bytes())
        .unwrap_or_else(|error| ril_source::ice!("invalid stdlib source {path_str}: {error}"));
    let tokens = lexer::lex(&source).unwrap_or_else(|error| {
        ril_source::ice!(
            "invalid stdlib tokens in {path_str}:\n{}",
            render_diagnostic(&source, &error)
        )
    });
    let ast = parser::parse(&source, &tokens, FileKind::Module).unwrap_or_else(|error| {
        ril_source::ice!(
            "invalid stdlib AST in {path_str}:\n{}",
            render_diagnostic(&source, &error)
        )
    });
    File::new(source, FileKind::Module, ast, tokens)
}

pub(super) fn stdlib_modules() -> &'static [StdModule] {
    static MODULES: OnceLock<Vec<StdModule>> = OnceLock::new();
    MODULES.get_or_init(|| {
        let mut modules: Vec<StdModule> = STD_SOURCES
            .iter()
            .map(|&(module_name, import_key, path_str, text)| StdModule {
                module_name,
                import_key,
                file: parse_embedded(path_str, text),
            })
            .collect();
        let platform_src = format!(
            "-- Target platform metadata constants.\n\n-- Operating system identifier of the compilation target (for example, \"linux\", \"macos\", or \"windows\").\npub meta let OS: str = {:?}\n\n-- CPU architecture identifier of the compilation target (for example, \"x86_64\" or \"aarch64\").\npub meta let ARCH: str = {:?}\n\n-- Whether the target platform supports POSIX `openat` directory-relative file operations.\npub meta let HAS_OPENAT: bool = {}\n",
            std::env::consts::OS,
            std::env::consts::ARCH,
            cfg!(unix),
        );
        modules.push(StdModule {
            module_name: "Platform",
            import_key: "ril/platform",
            file: parse_embedded("ril/std/platform.ril", &platform_src),
        });
        modules
    })
}

pub(super) fn module(path: &Path) -> Option<&'static str> {
    let raw = path.to_str()?;
    let stem = raw
        .strip_prefix("ril/std/")
        .or_else(|| raw.strip_prefix("ril/"))?
        .strip_suffix(".ril")?;
    if stem == "platform" {
        return Some("Platform");
    }
    STD_SOURCES
        .iter()
        .find(|&&(_, import_key, _, _)| import_key.strip_prefix("ril/") == Some(stem))
        .map(|&(module_name, _, _, _)| module_name)
}

pub(super) fn std_import_key(path: &Path) -> Option<&'static str> {
    let raw = path.to_str()?;
    let stem = raw.strip_prefix("ril/std/")?.strip_suffix(".ril")?;
    if stem == "platform" {
        return Some("ril/platform");
    }
    STD_SOURCES
        .iter()
        .find(|&&(_, import_key, _, _)| import_key.strip_prefix("ril/") == Some(stem))
        .map(|&(_, import_key, _, _)| import_key)
}

pub(super) fn std_type_for(module_name: &str, name: &str) -> Option<StdType> {
    PRIMITIVE_TYPES
        .iter()
        .find(|spec| spec.module == module_name && spec.name == name)
        .map(|spec| spec.std_type)
}

fn is_embedded_std(path: &Path) -> bool {
    path.to_str().is_some_and(|s| s.starts_with("ril/std/"))
}

fn registered_module_file(module_name: &str) -> Option<&'static File> {
    stdlib_modules()
        .iter()
        .find(|m| m.module_name == module_name)
        .map(|m| &m.file)
}

fn signature(
    file: &File,
    start: Span,
    declaration: Span,
    parameters: &[GenericParam],
) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut input = file.token_text(start.join(declaration)).peekable();
    while let Some(token) = input.next() {
        if token == ","
            && input
                .peek()
                .is_some_and(|next| matches!(*next, ")" | ">" | "}"))
        {
            continue;
        }
        if token == ">>" {
            tokens.extend([">".into(), ">".into()]);
        } else if let Some(index) = parameters
            .iter()
            .position(|param| param.name.value == token)
        {
            tokens.push(format!("#{index}"));
        } else {
            tokens.push(token.into());
        }
    }
    tokens
}

pub(super) fn registered_type(
    file: &File,
    declaration: Span,
    actual: &TypeDecl,
) -> Option<Result<TypeRegistration, Diagnostic>> {
    let module_name = module(&file.path)?;
    let is_object = PRIMITIVE_TYPES
        .iter()
        .any(|spec| spec.module == module_name && spec.name == actual.name.value && spec.is_object);
    if is_embedded_std(&file.path) {
        return Some(Ok(if is_object {
            TypeRegistration::Object
        } else {
            TypeRegistration::Regular
        }));
    }
    let registered = registered_module_file(module_name)?;
    let (node, expected) = registered.ast.items.iter().find_map(|&item| {
        let node = registered.ast.stmt(item);
        match &node.value.kind {
            StmtKind::Type(ty) if actual.name.value == ty.name.value => Some((node, ty)),
            _ => None,
        }
    })?;
    if actual.kind != expected.kind
        || signature(file, actual.name.span, declaration, &actual.generics)
            != signature(
                registered,
                expected.name.span,
                node.span,
                &expected.generics,
            )
    {
        return Some(Err(mismatch(actual.name.span)));
    }
    Some(Ok(if is_object {
        TypeRegistration::Object
    } else {
        TypeRegistration::Regular
    }))
}

pub(super) fn bodyless(
    file: &File,
    declaration: Span,
    function: &Function,
) -> Result<PrimitivePhase, Diagnostic> {
    let Some(module_name) = module(&file.path) else {
        return Err(missing_body(function.name.span));
    };
    let name = function.name.value.as_str();
    let Some(spec) = lookup_primitive(module_name, name) else {
        return Err(missing_body(function.name.span));
    };
    if is_embedded_std(&file.path) {
        return Ok(spec.phase);
    }
    let Some(registered) = registered_module_file(module_name) else {
        return Err(missing_body(function.name.span));
    };
    let Some((node, expected)) = registered.ast.items.iter().find_map(|&item| {
        let node = registered.ast.stmt(item);
        match &node.value.kind {
            StmtKind::Function(expected) if expected.name.value == name => Some((node, expected)),
            _ => None,
        }
    }) else {
        return Err(missing_body(function.name.span));
    };
    if function.is_meta == expected.is_meta
        && signature(file, function.name.span, declaration, &function.generics)
            == signature(
                registered,
                expected.name.span,
                node.span,
                &expected.generics,
            )
    {
        Ok(spec.phase)
    } else {
        Err(mismatch(function.name.span))
    }
}

pub(super) fn missing_body(span: Span) -> Diagnostic {
    Diagnostic::error(Code::E0902, span, "function requires a body")
}

fn mismatch(span: Span) -> Diagnostic {
    Diagnostic::error(
        Code::E0909,
        span,
        "declaration differs from the registered primitive signature",
    )
}
