//! The program environment supplies system operations, never arbitrary user
//! handlers. A library declaration's upper effect row is not an entry grant.
use super::*;
use crate::{
    hir::VerifiedProgram,
    sema::{facts::CauseKind, model::Ty},
};

pub(crate) fn verify_environment(
    program: &VerifiedProgram,
    name: &str,
    main: bool,
) -> Result<(), CompilationOutcome> {
    let root = program.facts().file.unwrap_or(FileId(0));
    let Some((index, function)) =
        program
            .facts()
            .functions
            .iter()
            .enumerate()
            .find(|(_, function)| {
                function.syntax.name == name
                    && function.syntax.span.file == root
                    && function.owner.is_none()
            })
    else {
        return Err(CompilationOutcome::NotImplemented {
            reason: NotImplemented::new(
                Stage::Provenance,
                format!("entry {name} has no resolved root declaration"),
            ),
        });
    };
    let span = function.syntax.span;
    let fail = |code: &str, message: String| {
        let mut explanations = program.facts().explanations.clone();
        let parents: Vec<_> = explanations
            .causes
            .iter()
            .zip(&explanations.kinds)
            .filter_map(|(cause, kind)| {
                (kind == &CauseKind::Call
                    && cause.span.is_some_and(|source| {
                        source.file == span.file
                            && source.start >= span.start
                            && source.end <= span.end
                    }))
                .then_some(cause.id)
            })
            .collect();
        let cause = explanations.add(CauseKind::MissingProof, Some(span), &message, parents);
        CompilationOutcome::Rejected {
            diagnostics: vec![Diagnostic {
                code: code.into(),
                severity: Severity::Error,
                message: message.clone(),
                labels: vec![Label { span, message }],
                causes: explanations.chain(cause),
            }],
        }
    };
    if !function.syntax.parameters.is_empty()
        || !function.syntax.generics.is_empty()
        || function.syntax.is_meta
        || main && function.syntax.visibility != ril_syntax::ast::Visibility::Public
    {
        return Err(fail(
            "E0904",
            "native entry must be an ordinary function without value or generic parameters".into(),
        ));
    }
    if program
        .facts()
        .copy_template_closure
        .as_ref()
        .is_some_and(|closure| closure.templates.contains_key(&function.definition))
    {
        return Err(CompilationOutcome::NotImplemented {
            reason: NotImplemented::new(
                Stage::Provenance,
                "entry requires its own copy-template argument substitution proof",
            ),
        });
    }
    let checks: Vec<_> = program
        .facts()
        .definition_checks
        .iter()
        .filter(|check| check.function == index && check.span == span)
        .collect();
    if checks.is_empty() {
        return Err(CompilationOutcome::NotImplemented {
            reason: NotImplemented::new(
                Stage::Provenance,
                "entry has no universally checked invocation evidence",
            ),
        });
    }
    let residual: std::collections::BTreeSet<_> = checks
        .iter()
        .flat_map(|check| &check.invocation.effects)
        .filter(|effect| !matches!(effect.as_str(), "Fiber" | "Concurrent" | "Div"))
        .cloned()
        .collect();
    if !residual.is_empty() {
        return Err(fail(
            "E0612",
            format!(
                "program environment has no handler for residual user effects: {}",
                residual.into_iter().collect::<Vec<_>>().join(", ")
            ),
        ));
    }
    if checks.iter().any(|check| {
        !check.invocation.unresolved.is_empty() || !check.invocation.callbacks.is_empty()
    }) {
        return Err(CompilationOutcome::NotImplemented {
            reason: NotImplemented::new(
                Stage::Provenance,
                "entry environment retains unresolved invocation dependencies",
            ),
        });
    }
    if main && checks.iter().any(|check| !matches!(&check.declared, Ty::Unit)
        && !matches!(&check.declared, Ty::Result(ok,error) if **ok==Ty::Unit && **error==Ty::Str))
    {
        return Err(fail("E0904", "main must return () or the language Result<(), str> after transparent alias expansion".into()));
    }
    Ok(())
}
