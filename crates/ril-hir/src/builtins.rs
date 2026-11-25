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

use super::{File, PrimitivePhase, StdType};

pub(super) enum TypeRegistration {
    Object,
    Regular,
}

pub(super) struct StdModule {
    pub(super) module_name: &'static str,
    pub(super) import_key: &'static str,
    pub(super) file: File,
}

fn parse_embedded(path_str: &str, text: &str) -> File {
    let path = Path::new(path_str);
    let id = FileId::from_path(path);
    let source = SourceFile::from_bytes(id, path.into(), text.as_bytes())
        .unwrap_or_else(|error| ril_source::ice!("invalid stdlib source {path_str}: {error:?}"));
    let tokens = lexer::lex(&source)
        .unwrap_or_else(|error| ril_source::ice!("invalid stdlib tokens {path_str}: {error:?}"));
    let ast = parser::parse(&source, &tokens, FileKind::Module)
        .unwrap_or_else(|error| ril_source::ice!("invalid stdlib AST in {path_str}: {error:?}"));
    File::new(source, FileKind::Module, ast, tokens)
}

pub(super) fn stdlib_modules() -> &'static [StdModule] {
    static MODULES: OnceLock<Vec<StdModule>> = OnceLock::new();
    MODULES.get_or_init(|| {
        const SOURCES: &[(&str, &str, &str, &str)] = &[
            (
                "Prelude",
                "ril/prelude",
                "ril/std/prelude.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/prelude.ril")),
            ),
            (
                "Numeric",
                "ril/numeric",
                "ril/std/numeric.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/numeric.ril")),
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
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/reflect.ril")),
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
                "Fiber",
                "ril/fiber",
                "ril/std/fiber.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/fiber.ril")),
            ),
            (
                "Channel",
                "ril/channel",
                "ril/std/channel.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/channel.ril")),
            ),
            (
                "Math",
                "ril/math",
                "ril/std/math.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/math.ril")),
            ),
            (
                "Os",
                "ril/os",
                "ril/std/os.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/os.ril")),
            ),
            (
                "Crypto",
                "ril/crypto",
                "ril/std/crypto.ril",
                include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../std/crypto.ril")),
            ),
        ];
        let mut modules: Vec<StdModule> = SOURCES
            .iter()
            .map(|&(module_name, import_key, path_str, text)| StdModule {
                module_name,
                import_key,
                file: parse_embedded(path_str, text),
            })
            .collect();
        let platform_src = format!(
            "-- Target platform metadata constants.\n\npub meta let OS: str = {:?}\npub meta let ARCH: str = {:?}\npub meta let HAS_OPENAT: bool = {}\n",
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
    match path.to_str()? {
        "ril/prelude.ril" | "ril/std/prelude.ril" => Some("Prelude"),
        "ril/array.ril" | "ril/std/array.ril" => Some("Array"),
        "ril/map.ril" | "ril/std/map.ril" => Some("Map"),
        "ril/set.ril" | "ril/std/set.ril" => Some("Set"),
        "ril/string.ril" | "ril/std/string.ril" => Some("String"),
        "ril/bytes.ril" | "ril/std/bytes.ril" => Some("Bytes"),
        "ril/numeric.ril" | "ril/std/numeric.ril" => Some("Numeric"),
        "ril/reflect.ril" | "ril/std/reflect.ril" => Some("Reflect"),
        "ril/io.ril" | "ril/std/io.ril" => Some("Io"),
        "ril/file.ril" | "ril/std/file.ril" => Some("File"),
        "ril/platform.ril" | "ril/std/platform.ril" => Some("Platform"),
        "ril/fiber.ril" | "ril/std/fiber.ril" => Some("Fiber"),
        "ril/channel.ril" | "ril/std/channel.ril" => Some("Channel"),
        "ril/math.ril" | "ril/std/math.ril" => Some("Math"),
        "ril/os.ril" | "ril/std/os.ril" => Some("Os"),
        "ril/crypto.ril" | "ril/std/crypto.ril" => Some("Crypto"),
        _ => None,
    }
}

pub(super) fn std_type_for(module_name: &str, name: &str) -> Option<StdType> {
    use StdType::*;
    match (module_name, name) {
        ("Prelude", "Option") => Some(Option),
        ("Prelude", "Result") => Some(Result),
        ("Reflect", "MemberMode") => Some(MemberMode),
        ("Prelude", "PanicInfo") => Some(PanicInfo),
        ("Prelude", "PanicError") => Some(PanicError),
        ("Prelude", "Draft") => Some(Draft),
        ("Set", "Set") => Some(Set),
        ("Fiber", "Scope") => Some(Scope),
        ("Fiber", "Task") => Some(Task),
        ("Fiber", "TaskFault") => Some(TaskFault),
        ("Fiber", "TimeoutError") => Some(TimeoutError),
        ("Channel", "Sender") => Some(Sender),
        ("Channel", "Receiver") => Some(Receiver),
        ("Channel", "SendError") => Some(SendError),
        ("Channel", "TrySendError") => Some(TrySendError),
        ("Channel", "TryRecvError") => Some(TryRecvError),
        _ => None,
    }
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
    let is_object = matches!(
        (module_name, actual.name.value.as_str()),
        ("Prelude", "Draft")
            | ("Set", "Set")
            | ("Fiber", "Scope" | "Task")
            | ("Channel", "Sender" | "Receiver")
    );
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
    let Some(phase) = stdlib_intrinsic_phase(module_name, name) else {
        return Err(missing_body(function.name.span));
    };
    if is_embedded_std(&file.path) {
        return Ok(phase);
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
        Ok(phase)
    } else {
        Err(mismatch(function.name.span))
    }
}

fn stdlib_intrinsic_phase(module_name: &str, name: &str) -> Option<PrimitivePhase> {
    use PrimitivePhase::{Both, Runtime, Static};
    match (module_name, name) {
        ("Prelude", "len" | "inner" | "clone" | "derive" | "panic" | "assert") => Some(Both),
        ("Prelude", "absorb_panic" | "panic_message" | "print" | "println") => Some(Runtime),
        ("Prelude", "type_name" | "coords" | "variants") => Some(Static),
        ("Reflect", "attrs" | "field_attrs" | "variant_attrs" | "has_default") => Some(Static),
        ("Array", "push" | "pop" | "insert" | "remove" | "sort" | "clear" | "len")
        | ("Map", "get" | "insert" | "remove" | "contains" | "clear" | "keys" | "values" | "len")
        | ("Set", "empty" | "from_array" | "insert" | "remove" | "contains" | "len")
        | (
            "String",
            "raw_encode_utf8" | "raw_decode_utf8" | "inspect" | "len" | "join" | "split"
            | "starts_with" | "ends_with" | "at" | "scalars" | "from_scalars",
        )
        | ("Bytes", "len" | "at" | "to_array" | "from_array")
        | ("Numeric", "to_f64" | "convert" | "trunc") => Some(Both),
        ("Io", "print" | "println")
        | ("File", "read" | "write")
        | (
            "Fiber",
            "run" | "yield_now" | "sleep_ms" | "is_cancelled" | "uncancellable" | "timeout_ms"
            | "scope" | "try_scope" | "supervise" | "spawn" | "join" | "cancel" | "cancel_scope"
            | "zip" | "try_zip" | "map" | "try_map" | "race",
        )
        | (
            "Channel",
            "bounded" | "unbounded" | "clone" | "send" | "try_send" | "recv" | "try_recv" | "close"
            | "close_recv" | "drain",
        ) => Some(Runtime),
        _ => None,
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
