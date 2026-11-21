use std::path::Path;

use ril_base::diag::{Code, Diagnostic};

use crate::syntax::{Ast, Expr, Function, Mode, Type, TypeId};

use super::PrimitivePhase;

pub(super) fn bodyless(
    path: &Path,
    ast: &Ast,
    function: &Function,
) -> Result<PrimitivePhase, Diagnostic> {
    use PrimitivePhase::{Both, Runtime};
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
        return Err(Diagnostic::error(
            Code::E0902,
            function.name.span,
            "function requires a body",
        ));
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
        Err(Diagnostic::error(
            Code::E0909,
            function.name.span,
            "declaration differs from the registered primitive signature",
        ))
    }
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
