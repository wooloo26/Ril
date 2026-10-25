//! Retained answer contracts keep three independent obligations:
//! - operation result R checks the resume operand, never the block answer A;
//! - fixed answers agree with both the declaration and each fresh invocation;
//! - a general suffix needs a copy answer; exact identity can transfer data.
//!
//! Parametric identity recognizes an exact binder forwarding proof. It does not
//! bypass ordinary binding reception or change cleanup/effect/loan checking.
use super::*;

#[derive(Clone)]
pub(super) struct PendingUse {
    pub handler: usize,
    pub callable: Callable,
    pub operation: String,
    pub invocation: Ty,
    pub copy: bool,
    pub identity_transport: bool,
    pub parametric: bool,
    pub resumed: bool,
    pub span: Span,
    pub cause: CauseId,
    pub ordinary_transport: bool,
    pub activation: ScopeId,
    pub resumption_steps: Vec<usize>,
}

pub(super) fn identity_suffix(expression: &Expr) -> bool {
    let ExprKind::Block(block) = &expression.kind else {
        return false;
    };
    if !block.where_items.is_empty() {
        return false;
    }
    let Some(index) = post_resume::linear_resume(expression) else {
        return false;
    };
    let StmtKind::Binding(binding) = &block.statements[index].kind else {
        return false;
    };
    if binding.mode != BindingMode::Let
        || binding.is_meta
        || binding.ty.is_some()
        || binding.fallback.is_some()
        || !matches!(
            binding.value.kind,
            ExprKind::Control {
                operation: ControlOperation::Resume,
                ..
            }
        )
    {
        return false;
    }
    let PatternKind::Name(name) = &binding.pattern.kind else {
        return false;
    };
    matches!(&block.statements[index + 1..], [Stmt { kind: StmtKind::Expr { expression: Expr { kind: ExprKind::Name(returned), .. }, terminated: false }, .. }] if returned == name)
}

impl Checker {
    /// Ordinary graph transfer keeps the same provenance. Eligibility alone
    /// does not authorize its binding reception or any suffix access.
    pub(super) fn ordinary_handler_answer(&self, answer: &Value) -> bool {
        !matches!(answer.ty, Ty::Unknown | Ty::Never)
            && self.ordinary_data_type(&answer.ty)
            && self.resource_free(answer)
            && !self.has_unresolved_row(answer)
            && self.ordinary_loop_value(answer, &self.fields)
    }
    pub(super) fn check_retained_callable_answer(
        &mut self,
        value: &Value,
        expected: &Ty,
        span: Span,
    ) {
        if value.callables.is_empty() || self.retained_answer_uses.is_empty() {
            return;
        }
        let Ty::Callable(_, answer) = self.expanded(expected, &mut BTreeSet::new()) else {
            return;
        };
        let incompatible = self
            .retained_handlers
            .iter()
            .filter(|proof| value.callables.contains(&proof.callable))
            .any(|proof| {
                self.retained_answer_uses.iter().any(|pending| {
                    pending.callable == proof.callable
                        && !pending.parametric
                        && proof.handlers.contains(&pending.handler)
                        && !self.compatible(&pending.invocation, &answer)
                })
            });
        if incompatible {
            self.error(
                "E0614",
                span,
                "expected callable answer is incompatible with its selected fixed handler answer",
                [value.cause],
            );
        }
    }
    pub(super) fn copy_handler_answer(&self, answer: &Value) -> bool {
        self.copy_handler_answer_type(&answer.ty)
            && answer.origins.nodes.is_empty()
            && answer.results.is_empty()
            && answer.scoped.is_empty()
            && answer.callables.is_empty()
    }
    pub(super) fn identity_handler_answer(&self, answer: &Value) -> bool {
        let scoped: BTreeSet<_> = self
            .bindings
            .iter()
            .enumerate()
            .filter_map(|(id, binding)| {
                matches!(binding.mode, BindingMode::Scoped | BindingMode::ScopedMut).then_some(id)
            })
            .collect();
        !matches!(answer.ty, Ty::Unknown | Ty::Never)
            && !self.equality_has_generic(&answer.ty)
            && !self.has_unresolved_row(answer)
            && !self.resource_type(&answer.ty)
            && self.resource_free(answer)
            && !self.contains_callable(answer)
            && !self.carries_scoped(answer, &scoped)
    }
    pub(super) fn copy_handler_answer_type(&self, ty: &Ty) -> bool {
        let ty = self.expanded(ty, &mut BTreeSet::new());
        !matches!(ty, Ty::Unknown | Ty::Never)
            && !self.equality_has_generic(&ty)
            && !self.reference_bearing(&ty)
            && !matches!(ty, Ty::Result(..) | Ty::Callable(..))
    }
}
