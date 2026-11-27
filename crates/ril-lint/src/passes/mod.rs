pub mod access;
pub mod hir;
pub mod syntax;
pub mod typed;

use crate::LintContext;

pub fn run_all(ctx: &mut LintContext<'_>) {
    syntax::run(ctx);
    if ctx.hir.is_some() {
        hir::run(ctx);
    }
    if ctx.typed.is_some() {
        typed::run(ctx);
    }
    if ctx.typed.is_some() && ctx.analysis.is_some() {
        access::run(ctx);
    }
}
