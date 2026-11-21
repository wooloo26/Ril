use std::{path::Path, sync::OnceLock};

use ril_base::{
    diag::{Code, Diagnostic},
    span::{FileId, SourceFile, Span},
};

use crate::{
    lexer,
    parser::{self, FileKind},
    syntax::{Ast, Expr, Function, GenericParam, Mode, StmtKind, Type, TypeDecl, TypeId},
};

use super::{BuiltinSum, File, PrimitivePhase};

pub(super) enum TypeRegistration {
    Object,
    Alias,
    Sum(BuiltinSum),
}

pub(super) fn module(path: &Path) -> Option<&'static str> {
    match path.to_str()? {
        "ril/prelude.ril" => Some("Prelude"),
        "ril/fiber.ril" => Some("Fiber"),
        "ril/channel.ril" => Some("Channel"),
        _ => None,
    }
}

fn declarations(path: &Path) -> Option<&'static File> {
    static PRELUDE: OnceLock<File> = OnceLock::new();
    static FIBER: OnceLock<File> = OnceLock::new();
    static CHANNEL: OnceLock<File> = OnceLock::new();
    let (cache, text) = match module(path)? {
        "Prelude" => (&PRELUDE, include_str!("standard/prelude.ril")),
        "Fiber" => (&FIBER, include_str!("standard/fiber.ril")),
        "Channel" => (&CHANNEL, include_str!("standard/channel.ril")),
        _ => return None,
    };
    Some(cache.get_or_init(|| {
        let source = SourceFile::from_bytes(FileId(usize::MAX), path.into(), text.as_bytes())
            .unwrap_or_else(|error| ril_base::ice!("invalid registered source: {error:?}"));
        let tokens = lexer::lex(&source)
            .unwrap_or_else(|error| ril_base::ice!("invalid registered tokens: {error:?}"));
        let ast = parser::parse(&source, &tokens, FileKind::Module)
            .unwrap_or_else(|error| ril_base::ice!("invalid registered declaration: {error:?}"));
        File::new(source, FileKind::Module, ast, tokens)
    }))
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
    let registered = declarations(&file.path)?;
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
    use BuiltinSum::*;
    let registration = match actual.name.value.as_str() {
        "PanicError" => TypeRegistration::Sum(PanicError),
        "TaskFault" => TypeRegistration::Sum(TaskFault),
        "TimeoutError" => TypeRegistration::Sum(TimeoutError),
        "SendError" => TypeRegistration::Sum(SendError),
        "TrySendError" => TypeRegistration::Sum(TrySendError),
        "TryRecvError" => TypeRegistration::Sum(TryRecvError),
        "ChannelPair" | "Zip" => TypeRegistration::Alias,
        _ => TypeRegistration::Object,
    };
    Some(Ok(registration))
}

pub(super) fn bodyless(
    file: &File,
    declaration: Span,
    function: &Function,
) -> Result<PrimitivePhase, Diagnostic> {
    use PrimitivePhase::{Both, Runtime};
    let path = &file.path;
    let ast = &file.ast;
    if let Some(registered) = declarations(path)
        && let Some((node, expected)) = registered.ast.items.iter().find_map(|&item| {
            let node = registered.ast.stmt(item);
            match &node.value.kind {
                StmtKind::Function(expected) if expected.name.value == function.name.value => {
                    Some((node, expected))
                }
                _ => None,
            }
        })
    {
        return if !function.is_meta
            && signature(file, function.name.span, declaration, &function.generics)
                == signature(
                    registered,
                    expected.name.span,
                    node.span,
                    &expected.generics,
                )
        {
            Ok(Runtime)
        } else {
            Err(mismatch(function.name.span))
        };
    }
    let path_is_prelude = path == Path::new("ril/prelude.ril");
    let name = function.name.value.as_str();
    let sig = &function.signature;
    let routine = match (path.to_str(), name, path_is_prelude) {
        (_, "panic", true) => Some((Both, "never", &["str"][..], &[][..])),
        (_, "assert", true) => Some((Both, "()", &["bool", "str"][..], &[][..])),
        (_, "print" | "println", true) | (Some("ril/io.ril"), "print" | "println", _) => {
            Some((Runtime, "()", &["str"][..], &["io"][..]))
        }
        (_, "len", true) => Some((Both, "int", &["T"][..], &[][..])),
        (_, "panic_message", true) => Some((Runtime, "str", &["PanicInfo"][..], &[][..])),
        (Some("ril/string.ril"), "inspect", _) => Some((Both, "str", &["T"][..], &[][..])),
        _ => None,
    };
    let Some((phase, output, parameters, effects)) = routine else {
        return Err(missing_body(function.name.span));
    };
    let mut valid = sig.params.len() == parameters.len()
        && sig.params.iter().zip(parameters).all(|(param, expected)| {
            param
                .ty
                .is_some_and(|ty| simple_type(ast, ty) == Some(expected))
                && !param.is_meta
                && param.guards.is_empty()
        })
        && sig
            .obligations
            .effects
            .iter()
            .map(|path| {
                path.segments
                    .last()
                    .map_or("", |segment| segment.name.value.as_str())
            })
            .eq(effects.iter().copied())
        && sig.obligations.state.is_empty()
        && !sig.obligations.open_effects
        && !sig.obligations.open_state
        && sig.result_mode == Mode::Plain
        && sig.guards.is_empty()
        && simple_type(ast, sig.result) == Some(output)
        && !function.is_meta;
    let via = name == "len";
    valid &= sig
        .params
        .iter()
        .all(|param| param.mode == if via { Mode::Via } else { Mode::Plain });
    valid &= if matches!(name, "len" | "inspect") {
        matches!(function.generics.as_slice(), [generic] if generic.name.value == "T" && generic.default.is_none()
            && generic.bound.is_empty() && (name == "inspect" || matches!(generic.guards.as_slice(), [guard]
                if guard.segments.last().is_some_and(|name| name.name.value == "LenTarget"))))
    } else {
        function.generics.is_empty()
    };
    valid &= if name == "assert" {
        sig.params.get(1).and_then(|param| param.default).is_some_and(|default| {
            matches!(&ast.expr(default).value, Expr::Literal(lit) if lit.text == "assertion failed")
        })
    } else {
        sig.params.iter().all(|param| param.default.is_none())
    };
    if valid {
        Ok(phase)
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

fn simple_type(ast: &Ast, id: TypeId) -> Option<&str> {
    match &ast.ty(id).value {
        Type::Unit => Some("()"),
        Type::Named(path) => match path.segments.as_slice() {
            [seg] if seg.arguments.is_empty() => Some(seg.name.value.as_str()),
            _ => None,
        },
        _ => None,
    }
}
