//! Application structure without fabricated Call nodes. A pipeline's right
//! Call supplies written operands; the Binary remains the application identity.
use super::nodes::{self as hir, HirProgram};
use ril_compiler_core::{ids::ExprId, source::Span};
use ril_syntax::ast::{self, ParameterMode};
const MAX_OPERANDS: usize = 1_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApplicationKind {
    Call,
    Pipeline,
}

/// Physical evaluation order and parameter slot order are distinct relations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EvaluationRole {
    Callee,
    Piped,
    Written(u32),
}

#[derive(Debug, Clone, Copy)]
pub struct Operand<'a, E> {
    pub role: EvaluationRole,
    pub expression: E,
    pub label: Option<&'a str>,
    pub mode: ParameterMode,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Application<'a, E> {
    pub kind: ApplicationKind,
    pub root: E,
    pub callee: E,
    /// The implicit first operand, if any, followed by written source operands.
    /// This is not a mapping to the callee's named/positional parameter slots.
    pub operands: Vec<Operand<'a, E>>,
    pub span: Span,
}

pub type AstApplication<'a> = Application<'a, &'a ast::Expr>;
pub type HirApplication<'a> = Application<'a, ExprId>;

impl<'a, E: Copy> Application<'a, E> {
    pub fn operand(&self, role: EvaluationRole) -> Option<&Operand<'a, E>> {
        match role {
            EvaluationRole::Callee => None,
            EvaluationRole::Piped => self
                .operands
                .first()
                .filter(|operand| operand.role == EvaluationRole::Piped),
            EvaluationRole::Written(index) => self.operands.get(
                (index as usize)
                    .checked_add(usize::from(self.kind == ApplicationKind::Pipeline))?,
            ),
        }
    }

    pub fn expression(&self, role: EvaluationRole) -> Option<E> {
        if role == EvaluationRole::Callee {
            Some(self.callee)
        } else {
            self.operand(role).map(|operand| operand.expression)
        }
    }

    /// Ordinary applications evaluate their callee first. Pipelines preserve
    /// the implementation's left/written/callee order; the computed-callee
    /// position is explicitly tracked as a specification question in README.
    pub fn evaluation_order(&self) -> impl Iterator<Item = EvaluationRole> + '_ {
        (self.kind == ApplicationKind::Call)
            .then_some(EvaluationRole::Callee)
            .into_iter()
            .chain(self.operands.iter().map(|operand| operand.role))
            .chain((self.kind == ApplicationKind::Pipeline).then_some(EvaluationRole::Callee))
    }
}

impl<'a> AstApplication<'a> {
    pub fn from_ast(root: &'a ast::Expr) -> Option<Self> {
        let (kind, piped, callee, written) = match &root.kind {
            ast::ExprKind::Call { callee, arguments } => (
                ApplicationKind::Call,
                None,
                callee.as_ref(),
                arguments.as_slice(),
            ),
            ast::ExprKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "|>" | "!>") => {
                if matches!(right.kind, ast::ExprKind::Derive { base: None, .. }) {
                    return None;
                }
                let (callee, written) = match &right.kind {
                    ast::ExprKind::Call { callee, arguments } => {
                        (callee.as_ref(), arguments.as_slice())
                    }
                    _ => (right.as_ref(), &[][..]),
                };
                (
                    ApplicationKind::Pipeline,
                    Some((left.as_ref(), operator.as_str())),
                    callee,
                    written,
                )
            }
            _ => return None,
        };
        if written.len() >= MAX_OPERANDS {
            return None;
        }
        let mut operands = Vec::with_capacity(written.len() + usize::from(piped.is_some()));
        if let Some((left, operator)) = piped {
            operands.push(Operand {
                role: EvaluationRole::Piped,
                expression: left,
                label: None,
                mode: if operator == "!>" {
                    ParameterMode::Mut
                } else {
                    ParameterMode::Read
                },
                span: left.span,
            });
        }
        for (index, argument) in written.iter().enumerate() {
            operands.push(Operand {
                role: EvaluationRole::Written(u32::try_from(index).ok()?),
                expression: &argument.value,
                label: argument.label.as_deref(),
                mode: argument.mode,
                span: argument.span,
            });
        }
        Some(Self {
            kind,
            root,
            callee,
            operands,
            span: root.span,
        })
    }
}

impl HirProgram {
    /// Missing children and unrepresentable operand ordinals are errors, not a
    /// proof that an application has no relevant work.
    pub fn application(&self, root: ExprId) -> Result<Option<HirApplication<'_>>, &'static str> {
        let node = self.expression(root).ok_or("application root is absent")?;
        let (kind, piped, callee, written) = match &node.kind {
            hir::ExprKind::Call { callee, arguments } => {
                (ApplicationKind::Call, None, *callee, arguments.as_slice())
            }
            hir::ExprKind::Binary {
                operator,
                left,
                right,
            } if matches!(operator.as_str(), "|>" | "!>") => {
                let right_node = self
                    .expression(*right)
                    .ok_or("pipeline right operand is absent")?;
                if matches!(right_node.kind, hir::ExprKind::Derive { base: None, .. }) {
                    return Ok(None);
                }
                let (callee, written) = match &right_node.kind {
                    hir::ExprKind::Call { callee, arguments } => (*callee, arguments.as_slice()),
                    _ => (*right, &[][..]),
                };
                (
                    ApplicationKind::Pipeline,
                    Some((*left, operator.as_str())),
                    callee,
                    written,
                )
            }
            _ => return Ok(None),
        };
        self.expression(callee)
            .ok_or("application callee is absent")?;
        if written.len() >= MAX_OPERANDS {
            return Err("application operand budget exhausted");
        }
        let mut operands = Vec::with_capacity(written.len() + usize::from(piped.is_some()));
        if let Some((left, operator)) = piped {
            let left_node = self
                .expression(left)
                .ok_or("pipeline left operand is absent")?;
            operands.push(Operand {
                role: EvaluationRole::Piped,
                expression: left,
                label: None,
                mode: if operator == "!>" {
                    ParameterMode::Mut
                } else {
                    ParameterMode::Read
                },
                span: left_node.info.span,
            });
        }
        for (index, argument) in written.iter().enumerate() {
            self.expression(argument.value)
                .ok_or("written application operand is absent")?;
            operands.push(Operand {
                role: EvaluationRole::Written(
                    u32::try_from(index)
                        .map_err(|_| "application ordinal exceeds its representation")?,
                ),
                expression: argument.value,
                label: argument.label.as_deref(),
                mode: argument.mode,
                span: argument.span,
            });
        }
        Ok(Some(Application {
            kind,
            root,
            callee,
            operands,
            span: node.info.span,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::source::FileId;

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 1,
            end: 2,
        }
    }
    fn expr(kind: ast::ExprKind) -> ast::Expr {
        ast::Expr {
            hir_id: None,
            kind,
            span: span(),
        }
    }
    fn name(value: &str) -> ast::Expr {
        expr(ast::ExprKind::Name(value.into()))
    }
    fn call() -> ast::Expr {
        expr(ast::ExprKind::Call {
            callee: Box::new(name("callee")),
            arguments: vec![ast::Argument {
                label: Some("last".into()),
                mode: ParameterMode::Read,
                value: name("written"),
                span: span(),
            }],
        })
    }

    #[test]
    fn application_views_keep_real_roots_labels_modes_and_evaluation_order() {
        for (syntax, expected) in [
            (
                call(),
                vec![EvaluationRole::Callee, EvaluationRole::Written(0)],
            ),
            (
                expr(ast::ExprKind::Binary {
                    operator: "!>".into(),
                    left: Box::new(name("left")),
                    right: Box::new(call()),
                }),
                vec![
                    EvaluationRole::Piped,
                    EvaluationRole::Written(0),
                    EvaluationRole::Callee,
                ],
            ),
        ] {
            let mut source = ast::Program {
                statements: vec![ast::Stmt {
                    hir_id: None,
                    span: span(),
                    kind: ast::StmtKind::Expr {
                        expression: syntax,
                        terminated: false,
                    },
                }],
            };
            let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
            let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
                unreachable!()
            };
            let ast_view = AstApplication::from_ast(expression).unwrap();
            let hir_view = hir
                .application(expression.hir_id.unwrap())
                .unwrap()
                .unwrap();
            assert_eq!(ast_view.evaluation_order().collect::<Vec<_>>(), expected);
            assert_eq!(hir_view.evaluation_order().collect::<Vec<_>>(), expected);
            assert_eq!(hir_view.root, expression.hir_id.unwrap());
            for role in expected {
                assert_eq!(
                    ast_view.expression(role).unwrap().hir_id,
                    hir_view.expression(role)
                );
            }
            assert_eq!(
                ast_view.operand(EvaluationRole::Written(0)).unwrap().label,
                Some("last")
            );
            assert!(ast_view.operand(EvaluationRole::Written(1)).is_none());
            if ast_view.kind == ApplicationKind::Pipeline {
                assert_eq!(
                    hir_view.operand(EvaluationRole::Piped).unwrap().mode,
                    ParameterMode::Mut
                );
                let hir::ExprKind::Binary { right, .. } =
                    hir.expression(hir_view.root).unwrap().kind
                else {
                    unreachable!()
                };
                assert_ne!(
                    right, hir_view.root,
                    "the notation Call cannot replace the Binary application"
                );
            }
        }
    }

    #[test]
    fn derive_is_a_separate_operation_and_missing_hir_is_an_error() {
        let mut source = ast::Program {
            statements: vec![ast::Stmt {
                hir_id: None,
                span: span(),
                kind: ast::StmtKind::Expr {
                    expression: expr(ast::ExprKind::Binary {
                        operator: "|>".into(),
                        left: Box::new(name("input")),
                        right: Box::new(expr(ast::ExprKind::Derive {
                            base: None,
                            recipe: Box::new(name("recipe")),
                        })),
                    }),
                    terminated: false,
                },
            }],
        };
        let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
        let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
            unreachable!()
        };
        assert!(AstApplication::from_ast(expression).is_none());
        assert!(
            hir.application(expression.hir_id.unwrap())
                .unwrap()
                .is_none()
        );
        assert!(hir.application(ExprId(u32::MAX)).is_err());
    }
}
