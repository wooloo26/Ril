//! Static call occurrences and dynamic observations are different identities.
//! This replay follows HIR child IDs; spans only locate a failed obligation.
use super::{
    ExpressionFact, SemanticFacts,
    copy_contract::{CopyCallEvent, CopyCallEventId},
    default_uses::{ArgumentSource, CallArguments, DefaultOrigin},
    effect_identity::{InvocationContext, InvocationExpression},
    model::Ty,
};
use crate::hir::nodes::{self as hir, HirProgram, LexicalOwner};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{CallableOwner, ClosureSiteId, DefinitionId, ExprId, StmtId},
    source::{FileId, Span},
};
use ril_syntax::ast::PatternKind;
use std::collections::{BTreeMap, BTreeSet};

type Failure = (Span, Option<CauseId>, String);
type Check<T = ()> = Result<T, String>;
const LIMIT: usize = 1_000_000;

fn require(condition: bool, reason: &str) -> Check {
    condition.then_some(()).ok_or_else(|| reason.to_owned())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Module,
    Function(StmtId),
    Lambda(ExprId),
}

struct Replay<'a> {
    facts: &'a SemanticFacts,
    hir: &'a HirProgram,
    observations: BTreeMap<usize, &'a InvocationExpression>,
    preparations: BTreeMap<CopyCallEventId, &'a CallArguments>,
    functions: BTreeMap<DefinitionId, Vec<Option<StmtId>>>,
    closures: BTreeMap<ClosureSiteId, Vec<Option<ExprId>>>,
}

impl Replay<'_> {
    fn pattern_value_sources(&self) -> Check<BTreeSet<ExprId>> {
        require(
            self.hir.generated_roots().len() <= LIMIT,
            "generated pattern source replay budget exhausted",
        )?;
        let mut patterns = BTreeMap::new();
        let mut values = BTreeSet::new();
        for (ordinal, &id) in self.hir.generated_roots().iter().enumerate() {
            let expression = self
                .hir
                .expression(id)
                .ok_or("generated root is outside HIR")?;
            let hir::NodeOrigin::Generated {
                generation,
                anchor,
                kind: hir::GeneratedKind::PatternValue,
            } = expression.info.origin
            else {
                continue;
            };
            let hir::NodeId::Pattern(pattern_id) = anchor else {
                return Err("generated pattern value has no actual PatternId anchor".into());
            };
            let pattern = self
                .hir
                .pattern(pattern_id)
                .ok_or("generated pattern anchor is absent")?;
            require(
                generation as usize == ordinal && expression.info.owner == pattern.info.owner,
                "generated pattern value changed its generation or lexical owner",
            )?;
            require(
                patterns.insert(pattern_id, id).is_none(),
                "one static pattern minted multiple static value expressions",
            )?;
            let same = match (&pattern.kind, &expression.kind) {
                (hir::PatternKind::Name(a), hir::ExprKind::Name(b)) => a == b,
                (hir::PatternKind::Literal(a), hir::ExprKind::Literal(b)) => a == b,
                (
                    hir::PatternKind::Constructor {
                        path,
                        arguments,
                        parenthesized,
                    },
                    hir::ExprKind::Path(actual),
                ) => arguments.is_empty() && !parenthesized && path == actual,
                _ => false,
            };
            require(
                same,
                "generated pattern value differs from its original HIR pattern recipe",
            )?;
            values.insert(id);
        }
        Ok(values)
    }

    fn observation(
        &self,
        index: usize,
        source: ExprId,
    ) -> Check<(&ExpressionFact, InvocationContext)> {
        let value = self
            .facts
            .expressions
            .get(index)
            .ok_or("call observation is outside its arena")?;
        let context = self
            .observations
            .get(&index)
            .ok_or("call observation lost its unique full context")?
            .context;
        require(
            value.source_id == Some(source),
            "call observation belongs to another static HIR occurrence",
        )?;
        Ok((value, context))
    }
    fn static_owner(&self, mut owner: LexicalOwner) -> Check<Owner> {
        for _ in 0..256 {
            owner = match owner {
                LexicalOwner::Module => return Ok(Owner::Module),
                LexicalOwner::Lambda(id) => {
                    require(
                        self.hir
                            .expression(id)
                            .is_some_and(|node| matches!(node.kind, hir::ExprKind::Lambda { .. })),
                        "call HIR lambda owner is absent",
                    )?;
                    return Ok(Owner::Lambda(id));
                }
                LexicalOwner::Declaration(id) => {
                    let node = self
                        .hir
                        .statement(id)
                        .ok_or("call HIR declaration owner is absent")?;
                    if matches!(node.kind, hir::StmtKind::Function(_)) {
                        return Ok(Owner::Function(id));
                    }
                    require(
                        matches!(
                            node.kind,
                            hir::StmtKind::Type { .. } | hir::StmtKind::Effect { .. }
                        ),
                        "call HIR owner is not a declaration",
                    )?;
                    node.info.owner
                }
                LexicalOwner::HandlerArm { statement, index } => {
                    let node = self
                        .hir
                        .statement(statement)
                        .ok_or("call HIR handler owner is absent")?;
                    require(
                        matches!(&node.kind, hir::StmtKind::Handler(arms) if (index as usize) < arms.len()),
                        "call HIR handler arm is absent",
                    )?;
                    node.info.owner
                }
                LexicalOwner::Variant { declaration, index } => {
                    let node = self
                        .hir
                        .statement(declaration)
                        .ok_or("call HIR variant owner is absent")?;
                    require(
                        matches!(&node.kind, hir::StmtKind::Type { variants, .. } if (index as usize) < variants.len()),
                        "call HIR variant is absent",
                    )?;
                    node.info.owner
                }
                LexicalOwner::TypeFunction(id) | LexicalOwner::CallableType(id) => {
                    self.hir
                        .type_expression(id)
                        .ok_or("call HIR type owner is absent")?
                        .info
                        .owner
                }
            };
        }
        Err("call HIR lexical ancestry exceeds its budget".into())
    }
    fn dynamic_owner(&self, context: InvocationContext) -> Check<Owner> {
        match context.owner {
            Some(CallableOwner::Global) => Ok(Owner::Module),
            Some(CallableOwner::Function(id)) => {
                let declarations = self
                    .functions
                    .get(&id)
                    .ok_or("call's named owner is absent")?;
                let first = declarations
                    .first()
                    .copied()
                    .flatten()
                    .ok_or("call's named owner has no HIR identity")?;
                require(
                    declarations.iter().all(|id| *id == Some(first)),
                    "copies of a named owner disagree on their static HIR identity",
                )?;
                require(
                    self.hir
                        .statement(first)
                        .is_some_and(|node| matches!(node.kind, hir::StmtKind::Function(_))),
                    "call's named HIR owner is not a function",
                )?;
                Ok(Owner::Function(first))
            }
            Some(CallableOwner::Lambda(site)) => {
                let occurrences = self
                    .closures
                    .get(&site)
                    .ok_or("call's closure site is absent")?;
                let first = occurrences
                    .first()
                    .copied()
                    .flatten()
                    .ok_or("call's closure owner has no HIR identity")?;
                require(
                    occurrences.iter().all(|id| *id == Some(first)),
                    "closure objects at one site disagree on their static HIR identity",
                )?;
                // Defaults and retained handler arms can keep a different
                // caller closure in their dynamic ancestry. The lexical site
                // resolves through its own declarations, not that caller.
                Ok(Owner::Lambda(first))
            }
            None => Err("call observation has no lexical owner".into()),
        }
    }

    fn event(&self, event: &CopyCallEvent) -> Check<usize> {
        let source = event
            .source_id
            .ok_or("call event has no static HIR identity")?;
        let syntax = self
            .hir
            .expression(source)
            .ok_or("call event HIR identity is outside its arena")?;
        let hir::ExprKind::Call { callee, arguments } = &syntax.kind else {
            return Err("call event HIR identity is not a Call".into());
        };
        let callee_index = event
            .callee_expression
            .ok_or("call event lost its actual callee observation")?;
        let result_index = event
            .result_expression
            .ok_or("call event lost its actual root observation")?;
        require(
            callee_index < result_index,
            "call result precedes its actual callee",
        )?;
        let (callee_value, context) = self.observation(callee_index, *callee)?;
        let (result_value, result_context) = self.observation(result_index, source)?;
        require(
            context.owner == event.owner
                && context.invocation == event.parent
                && context == result_context,
            "call callee and result belong to different full invocation contexts",
        )?;
        require(
            self.static_owner(syntax.info.owner)? == self.dynamic_owner(context)?,
            "call static HIR owner differs from its actual lexical owner",
        )?;
        if callee_value.value.ty == Ty::Never {
            require(
                !self.preparations.contains_key(&event.id) && result_value.value.ty == Ty::Never,
                "abrupt callee claims evaluated arguments or a normal result",
            )?;
            return Ok(result_index);
        }
        let preparation = self
            .preparations
            .get(&event.id)
            .ok_or("normal callee lost its actual argument preparation")?;
        require(
            preparation.target == event.target,
            "argument preparation belongs to another call target",
        )?;
        let signature = callee_value.value.signature.as_ref();
        let count = signature.map_or(arguments.len(), Vec::len);
        require(
            count <= LIMIT && arguments.len() <= LIMIT && preparation.slots.len() == count,
            "call argument slots differ from the actual public signature",
        )?;
        let mut labels = BTreeMap::new();
        if let Some(signature) = signature {
            for (index, parameter) in signature.iter().enumerate() {
                if let PatternKind::Name(name) = &parameter.pattern.kind {
                    require(
                        labels.insert(name.as_str(), index).is_none(),
                        "public callable signature repeats an argument label",
                    )?;
                }
            }
        }
        let mut occupied = BTreeSet::new();
        let mut written = Vec::new();
        let mut next = 0usize;
        for argument in arguments {
            let slot = if let Some(label) = &argument.label {
                *labels
                    .get(label.as_str())
                    .ok_or("written argument label is absent from its public signature")?
            } else {
                while occupied.contains(&next) {
                    next += 1;
                }
                next
            };
            require(
                slot < count && occupied.insert(slot),
                "written arguments duplicate or exceed an actual parameter slot",
            )?;
            written.push((slot, argument.value));
        }
        let mut consumed = BTreeSet::new();
        let mut previous = callee_index;
        let mut epoch = 0usize;
        let mut abrupt = false;
        for (slot, source) in written {
            let token = preparation.supplied.get(&(slot as u32));
            if abrupt {
                require(
                    token.is_none(),
                    "a supplied argument was evaluated after an abrupt earlier operand",
                )?;
                continue;
            }
            let token = token.ok_or("a written argument lost its own physical observation")?;
            require(
                preparation.slots.get(slot) == Some(&ArgumentSource::Supplied)
                    && previous < token.expression
                    && token.expression < result_index
                    && epoch <= token.allocation_epoch
                    && token.allocation_epoch <= self.facts.allocation_history.len(),
                "supplied operand changed slot, evaluation order or allocation epoch",
            )?;
            let (actual, actual_context) = self.observation(token.expression, source)?;
            require(
                actual_context == context
                    && self.observations[&token.expression].argument_of
                        == Some((event.id, slot as u32)),
                "supplied operand belongs to another full invocation or call event",
            )?;
            consumed.insert(slot as u32);
            previous = token.expression;
            epoch = token.allocation_epoch;
            abrupt = actual.value.ty == Ty::Never;
        }
        require(
            consumed.len() == preparation.supplied.len(),
            "call preparation includes an unwritten or foreign supplied operand",
        )?;
        let supplied_abrupt = abrupt;
        for (slot, origin) in preparation.slots.iter().enumerate() {
            match origin {
                ArgumentSource::Supplied => require(
                    consumed.contains(&(slot as u32)),
                    "supplied slot has no actual operand",
                )?,
                ArgumentSource::Missing => require(
                    !preparation.evaluation_complete,
                    "complete preparation has a missing parameter",
                )?,
                ArgumentSource::Default(id) => {
                    require(
                        !supplied_abrupt && !occupied.contains(&slot),
                        "default replaced a supplied or unevaluated written operand",
                    )?;
                    let default = self
                        .facts
                        .default_uses
                        .get(id.0 as usize)
                        .filter(|row| row.id == *id)
                        .ok_or("default slot has no actual use")?;
                    require(
                        default.origin == DefaultOrigin::Call(event.id)
                            && default.parameter as usize == slot
                            && default.caller == context,
                        "default slot borrowed another call's evaluation",
                    )?;
                    let original = signature
                        .and_then(|parameters| parameters.get(slot))
                        .and_then(|parameter| parameter.default.as_ref())
                        .and_then(|expression| expression.hir_id)
                        .ok_or("default descriptor lost its original HIR expression")?;
                    let index = default
                        .result_expression
                        .ok_or("default lost its actual result root")?;
                    let observed_epoch = default
                        .result_allocation_epoch
                        .ok_or("default lost its actual result epoch")?;
                    require(
                        !abrupt
                            && previous < index
                            && index < result_index
                            && epoch <= observed_epoch
                            && observed_epoch <= self.facts.allocation_history.len(),
                        "default was evaluated outside its actual operand interval",
                    )?;
                    let (actual, default_context) = self.observation(index, original)?;
                    require(
                        default_context.default_use == Some(*id)
                            && default_context.owner == default.owner,
                        "default root belongs to another default-use context",
                    )?;
                    abrupt = actual.value.ty == Ty::Never;
                    require(
                        default.evaluation_complete == !abrupt,
                        "default completion disagrees with its actual root",
                    )?;
                    previous = index;
                    epoch = observed_epoch;
                }
            }
        }
        require(
            preparation.evaluation_complete == !abrupt,
            "argument completion lacks a real normal or abrupt evaluation proof",
        )?;
        if abrupt {
            require(
                result_value.value.ty == Ty::Never,
                "abrupt arguments claim a normal call result",
            )?;
        }
        Ok(result_index)
    }
}

pub fn validate(facts: &SemanticFacts) -> Result<(), Failure> {
    let fallback = facts
        .file
        .map(|file| Span {
            file,
            start: 0,
            end: 0,
        })
        .unwrap_or(Span {
            file: FileId(0),
            start: 0,
            end: 0,
        });
    let fail = |message: String| (fallback, None, message);
    require(
        facts.expressions.len() <= LIMIT
            && facts.invocation_expressions.len() <= LIMIT
            && facts.copy_call_events.len() <= LIMIT
            && facts.call_arguments.len() <= LIMIT
            && facts.functions.len() <= LIMIT
            && facts.closures.len() <= LIMIT,
        "evaluation identity replay budget exhausted",
    )
    .map_err(fail)?;
    let Some(hir) = facts.semantic_hir.as_deref() else {
        return require(
            facts.copy_call_events.is_empty()
                && facts
                    .expressions
                    .iter()
                    .all(|expression| expression.source_id.is_none()),
            "evaluation identities have no owning semantic HIR",
        )
        .map_err(fail);
    };
    let mut replay = Replay {
        facts,
        hir,
        observations: BTreeMap::new(),
        preparations: BTreeMap::new(),
        functions: BTreeMap::new(),
        closures: BTreeMap::new(),
    };
    for row in &facts.invocation_expressions {
        require(
            row.expression < facts.expressions.len()
                && replay.observations.insert(row.expression, row).is_none(),
            "evaluation observation is duplicated or outside its arena",
        )
        .map_err(fail)?;
    }
    for row in &facts.call_arguments {
        require(
            facts
                .copy_call_events
                .get(row.source_event.0 as usize)
                .is_some_and(|event| event.id == row.source_event)
                && replay.preparations.insert(row.source_event, row).is_none(),
            "argument preparation is duplicated or has no actual call event",
        )
        .map_err(fail)?;
    }
    for row in &facts.invocation_expressions {
        if let Some((event, slot)) = row.argument_of {
            require(
                replay
                    .preparations
                    .get(&event)
                    .and_then(|preparation| preparation.supplied.get(&slot))
                    .is_some_and(|token| token.expression == row.expression),
                "an actual argument root lost its exact call/slot preparation",
            )
            .map_err(fail)?;
        }
    }
    for function in &facts.functions {
        replay
            .functions
            .entry(function.definition)
            .or_default()
            .push(function.hir_id);
    }
    for closure in &facts.closures {
        if let Some(site) = closure.site {
            replay
                .closures
                .entry(site)
                .or_default()
                .push(closure.hir_id);
        }
    }
    let pattern_values = replay.pattern_value_sources().map_err(fail)?;
    let mut results = BTreeSet::new();
    for (index, event) in facts.copy_call_events.iter().enumerate() {
        require(
            event.id.0 as usize == index,
            "call event identity differs from its arena slot",
        )
        .map_err(|message| (event.span, None, message))?;
        let result = replay
            .event(event)
            .map_err(|message| (event.span, None, message))?;
        require(
            results.insert(result),
            "two call events claim one physical root observation",
        )
        .map_err(|message| (event.span, None, message))?;
    }
    // A source Call may run many times. Its dynamic root observations, not a
    // uniqueness check on ExprId or the mutable event list, require coverage.
    for (index, expression) in facts.expressions.iter().enumerate() {
        let id = expression.source_id.ok_or_else(|| {
            (
                expression.span,
                Some(expression.value.cause),
                "actual expression observation has no static HIR identity".into(),
            )
        })?;
        let source = hir.expression(id).ok_or_else(|| {
            (
                expression.span,
                Some(expression.value.cause),
                "expression source identity is outside semantic HIR".into(),
            )
        })?;
        if pattern_values.contains(&id) {
            let context = replay
                .observations
                .get(&index)
                .ok_or_else(|| {
                    (
                        expression.span,
                        Some(expression.value.cause),
                        "pattern value has no actual observation context".into(),
                    )
                })?
                .context;
            require(
                replay.static_owner(source.info.owner).map_err(fail)?
                    == replay.dynamic_owner(context).map_err(fail)?,
                "pattern value observation borrowed another lexical owner",
            )
            .map_err(|message| (expression.span, Some(expression.value.cause), message))?;
        }
        if matches!(source.kind, hir::ExprKind::Call { .. }) {
            require(
                results.contains(&index),
                "an actual HIR Call root lost its dynamic call event",
            )
            .map_err(|message| (expression.span, Some(expression.value.cause), message))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{default_uses::SuppliedArgument, model::Value};
    use ril_syntax::ast::{self, ParameterMode};
    use std::sync::Arc;

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 1,
            end: 2,
        }
    }
    fn context() -> InvocationContext {
        InvocationContext {
            invocation: None,
            owner: Some(CallableOwner::Global),
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        }
    }
    fn syntax(arguments: usize) -> ast::Expr {
        ast::Expr {
            hir_id: None,
            span: span(),
            kind: ast::ExprKind::Call {
                callee: Box::new(ast::Expr {
                    hir_id: None,
                    span: span(),
                    kind: ast::ExprKind::Name("callee".into()),
                }),
                arguments: (0..arguments)
                    .map(|index| ast::Argument {
                        label: None,
                        mode: ParameterMode::Read,
                        span: span(),
                        value: ast::Expr {
                            hir_id: None,
                            span: span(),
                            kind: ast::ExprKind::Literal(ast::Literal::Integer(index.to_string())),
                        },
                    })
                    .collect(),
            },
        }
    }
    fn model(arguments: usize, events: usize, repeat: bool) -> SemanticFacts {
        let mut source = ast::Program {
            statements: (0..if repeat { 1 } else { events })
                .map(|_| ast::Stmt {
                    hir_id: None,
                    span: span(),
                    kind: ast::StmtKind::Expr {
                        expression: syntax(arguments),
                        terminated: true,
                    },
                })
                .collect(),
        };
        let hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
        let mut facts = SemanticFacts::default();
        for ordinal in 0..events {
            let ast::StmtKind::Expr { expression, .. } =
                &source.statements[if repeat { 0 } else { ordinal }].kind
            else {
                unreachable!()
            };
            let ast::ExprKind::Call { callee, arguments } = &expression.kind else {
                unreachable!()
            };
            let id = CopyCallEventId(ordinal as u32);
            let callee_index = facts.expressions.len();
            facts.expressions.push(ExpressionFact {
                source_id: callee.hir_id,
                span: span(),
                value: Value::scalar(Ty::Unknown, None, CauseId(0)),
            });
            facts.invocation_expressions.push(InvocationExpression {
                context: context(),
                expression: callee_index,
                argument_of: None,
            });
            let mut supplied = BTreeMap::new();
            for (slot, argument) in arguments.iter().enumerate() {
                let index = facts.expressions.len();
                supplied.insert(
                    slot as u32,
                    SuppliedArgument {
                        expression: index,
                        allocation_epoch: 0,
                    },
                );
                facts.expressions.push(ExpressionFact {
                    source_id: argument.value.hir_id,
                    span: span(),
                    value: Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
                });
                facts.invocation_expressions.push(InvocationExpression {
                    context: context(),
                    expression: index,
                    argument_of: Some((id, slot as u32)),
                });
            }
            let result = facts.expressions.len();
            facts.expressions.push(ExpressionFact {
                source_id: expression.hir_id,
                span: span(),
                value: Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
            });
            facts.invocation_expressions.push(InvocationExpression {
                context: context(),
                expression: result,
                argument_of: None,
            });
            facts.copy_call_events.push(CopyCallEvent {
                source_id: expression.hir_id,
                id,
                callee_expression: Some(callee_index),
                result_expression: Some(result),
                owner: Some(CallableOwner::Global),
                parent: None,
                span: span(),
                target: None,
                direct: false,
                copy_operation: None,
                references: vec![],
            });
            facts.call_arguments.push(CallArguments {
                source_event: id,
                target: None,
                slots: vec![ArgumentSource::Supplied; arguments.len()],
                supplied,
                evaluation_complete: true,
            });
        }
        facts.semantic_hir = Some(Arc::new(hir));
        facts.source_program = Some(Arc::new(source));
        facts
    }

    fn pattern_model(pattern: ast::PatternKind, expected: ast::ExprKind) -> SemanticFacts {
        let mut source = ast::Program {
            statements: vec![ast::Stmt {
                hir_id: None,
                span: span(),
                kind: ast::StmtKind::Expr {
                    expression: ast::Expr {
                        hir_id: None,
                        span: span(),
                        kind: ast::ExprKind::Is {
                            value: Box::new(ast::Expr {
                                hir_id: None,
                                span: span(),
                                kind: ast::ExprKind::Literal(ast::Literal::Bool(true)),
                            }),
                            pattern: ast::Pattern {
                                hir_id: None,
                                span: span(),
                                kind: pattern,
                            },
                        },
                    },
                    terminated: false,
                },
            }],
        };
        let mut hir = HirProgram::lower_identified(&mut source, hir::InputOrigin::Source).unwrap();
        let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
            unreachable!()
        };
        let ast::ExprKind::Is { pattern, .. } = &expression.kind else {
            unreachable!()
        };
        let mut generated = ast::Expr {
            hir_id: None,
            span: span(),
            kind: expected,
        };
        let id = hir
            .mint_generated_identified_expr(
                &mut generated,
                hir::NodeId::Pattern(pattern.hir_id.unwrap()),
                hir::GeneratedKind::PatternValue,
                LexicalOwner::Module,
                hir::HirLimits::default(),
            )
            .unwrap();
        let mut facts = SemanticFacts::default();
        facts.expressions.push(ExpressionFact {
            source_id: Some(id),
            span: span(),
            value: Value::scalar(Ty::Bool, None, CauseId(0)),
        });
        facts.invocation_expressions.push(InvocationExpression {
            context: context(),
            expression: 0,
            argument_of: None,
        });
        facts.source_program = Some(Arc::new(source));
        facts.semantic_hir = Some(Arc::new(hir));
        facts
    }

    #[test]
    fn generated_pattern_reads_reconstruct_names_literals_and_nullary_paths() {
        for (pattern, valid, invalid) in [
            (
                ast::PatternKind::Name("expected".into()),
                ast::ExprKind::Name("expected".into()),
                ast::ExprKind::Name("another".into()),
            ),
            (
                ast::PatternKind::Literal(ast::Literal::Bool(true)),
                ast::ExprKind::Literal(ast::Literal::Bool(true)),
                ast::ExprKind::Literal(ast::Literal::Bool(false)),
            ),
            (
                ast::PatternKind::Constructor {
                    path: vec!["Binary".into(), "ByteOrder".into(), "Little".into()],
                    arguments: vec![],
                    parenthesized: false,
                },
                ast::ExprKind::Path(vec!["Binary".into(), "ByteOrder".into(), "Little".into()]),
                ast::ExprKind::Path(vec!["Binary".into(), "ByteOrder".into(), "Big".into()]),
            ),
        ] {
            assert!(validate(&pattern_model(pattern.clone(), valid)).is_ok());
            assert!(validate(&pattern_model(pattern, invalid)).is_err());
        }
    }

    #[test]
    fn pattern_reads_cannot_mint_another_static_copy_or_use_an_expression_as_anchor() {
        let facts = pattern_model(
            ast::PatternKind::Name("expected".into()),
            ast::ExprKind::Name("expected".into()),
        );
        let root = facts.semantic_hir.as_ref().unwrap().generated_roots()[0];
        let hir::NodeOrigin::Generated { anchor, .. } = facts
            .semantic_hir
            .as_ref()
            .unwrap()
            .expression(root)
            .unwrap()
            .info
            .origin
        else {
            unreachable!()
        };
        let mut duplicate = facts.clone();
        let mut generated = ast::Expr {
            hir_id: None,
            span: span(),
            kind: ast::ExprKind::Name("expected".into()),
        };
        Arc::make_mut(duplicate.semantic_hir.as_mut().unwrap())
            .mint_generated_identified_expr(
                &mut generated,
                anchor,
                hir::GeneratedKind::PatternValue,
                LexicalOwner::Module,
                hir::HirLimits::default(),
            )
            .unwrap();
        assert!(
            validate(&duplicate).is_err(),
            "repeated evaluation reminted a static pattern ID"
        );
        let mut wrong_anchor = facts;
        Arc::make_mut(wrong_anchor.semantic_hir.as_mut().unwrap())
            .mint_generated_identified_expr(
                &mut generated,
                hir::NodeId::Expr(root),
                hir::GeneratedKind::PatternValue,
                LexicalOwner::Module,
                hir::HirLimits::default(),
            )
            .unwrap();
        assert!(
            validate(&wrong_anchor).is_err(),
            "a generated expression replaced the original PatternId anchor"
        );
    }

    #[test]
    fn repeated_real_pattern_reads_share_one_static_generated_expression() {
        let source = ril_test::case_source(
            "tests/regressions/evaluation-identity.ril::repeated-pattern-value-read",
        );
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        assert!(validate(facts).is_ok());
        let hir = facts.semantic_hir.as_ref().unwrap();
        let reads: Vec<_> = hir
            .generated_roots()
            .iter()
            .copied()
            .filter(|id| {
                matches!(
                    hir.expression(*id).unwrap().info.origin,
                    hir::NodeOrigin::Generated {
                        kind: hir::GeneratedKind::PatternValue,
                        ..
                    }
                )
            })
            .collect();
        assert_eq!(reads.len(), 1);
        assert!(
            facts
                .expressions
                .iter()
                .filter(|expression| expression.source_id == Some(reads[0]))
                .count()
                >= 2
        );
    }

    #[test]
    fn equal_spans_cannot_substitute_another_call_callee_argument_or_result_identity() {
        let facts = model(1, 2, false);
        assert!(validate(&facts).is_ok());
        for mutation in 0..5 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.copy_call_events[0].source_id = changed.copy_call_events[1].source_id,
                1 => changed.expressions[0].source_id = changed.expressions[3].source_id,
                2 => changed.expressions[1].source_id = changed.expressions[4].source_id,
                3 => changed.expressions[2].source_id = changed.expressions[5].source_id,
                4 => changed.copy_call_events[0].source_id = None,
                _ => unreachable!(),
            }
            assert!(
                validate(&changed).is_err(),
                "same-span identity mutation {mutation}"
            );
        }
    }

    #[test]
    fn one_static_call_can_have_several_dynamic_events_but_never_share_a_root() {
        let facts = model(1, 2, true);
        assert_eq!(
            facts.copy_call_events[0].source_id,
            facts.copy_call_events[1].source_id
        );
        assert!(validate(&facts).is_ok());
        let mut changed = facts.clone();
        changed.copy_call_events[1].result_expression =
            changed.copy_call_events[0].result_expression;
        assert!(validate(&changed).is_err());
        let mut deleted = facts;
        deleted.copy_call_events.clear();
        deleted.call_arguments.clear();
        for row in &mut deleted.invocation_expressions {
            row.argument_of = None;
        }
        assert!(
            validate(&deleted).is_err(),
            "joint receipt deletion hid evaluated Call roots"
        );
    }

    #[test]
    fn deleting_events_preparations_and_root_ids_cannot_hide_actual_scalar_calls() {
        let mut facts = model(1, 2, false);
        assert!(validate(&facts).is_ok());
        for event in &facts.copy_call_events {
            facts.expressions[event.result_expression.unwrap()].source_id = None;
        }
        facts.copy_call_events.clear();
        facts.call_arguments.clear();
        for observation in &mut facts.invocation_expressions {
            observation.argument_of = None;
        }
        let error =
            validate(&facts).expect_err("joint deletion erased actual scalar-call obligations");
        assert!(error.2.contains("no static HIR identity"), "{error:?}");
    }

    #[test]
    fn never_operands_keep_partial_evaluation_without_inventing_later_arguments() {
        let mut facts = model(2, 1, false);
        facts.expressions[1].value.ty = Ty::Never;
        facts.expressions[3].value.ty = Ty::Never;
        facts.call_arguments[0].evaluation_complete = false;
        facts.call_arguments[0].slots[1] = ArgumentSource::Missing;
        facts.call_arguments[0].supplied.remove(&1);
        assert!(
            validate(&facts).is_err(),
            "orphan later argument observation must remain visible"
        );
        facts.expressions.remove(2);
        facts.invocation_expressions.remove(2);
        facts.invocation_expressions[2].expression = 2;
        facts.copy_call_events[0].result_expression = Some(2);
        assert!(validate(&facts).is_ok());
        let mut forged = facts.clone();
        forged.call_arguments[0].evaluation_complete = true;
        assert!(validate(&forged).is_err());
        facts.expressions.remove(1);
        facts.invocation_expressions.remove(1);
        facts.invocation_expressions[1].expression = 1;
        facts.copy_call_events[0].result_expression = Some(1);
        facts.call_arguments.clear();
        facts.expressions[0].value.ty = Ty::Never;
        assert!(
            validate(&facts).is_ok(),
            "a Never callee has no actual argument preparation"
        );
    }

    #[test]
    fn actual_sources_keep_call_identities_across_repetition_and_generated_steps() {
        for case in ["repeated-named-call", "generated-adapter-per-call"] {
            let source = ril_test::case_source(&format!(
                "tests/regressions/evaluation-identity.ril::{case}"
            ));
            let program = crate::Session::new(source.as_bytes().to_vec())
                .verify()
                .unwrap_or_else(|outcome| panic!("{case}: {outcome:?}"));
            let facts = program.facts();
            assert!(validate(facts).is_ok());
            assert!(!facts.copy_call_events.is_empty());
            if case == "generated-adapter-per-call" {
                let hir = facts.semantic_hir.as_ref().unwrap();
                let index = facts
                    .copy_call_events
                    .iter()
                    .position(|event| {
                        event
                            .source_id
                            .and_then(|id| hir.expression(id))
                            .is_some_and(|node| {
                                matches!(node.info.origin, hir::NodeOrigin::Generated { .. })
                            })
                    })
                    .expect("actual generated step invocation must retain its explicit HIR origin");
                let mut changed = facts.clone();
                changed.copy_call_events[index].source_id = None;
                assert!(validate(&changed).is_err());
                let foreign = facts
                    .copy_call_events
                    .iter()
                    .find_map(|event| {
                        (event.source_id != facts.copy_call_events[index].source_id)
                            .then_some(event.source_id)
                            .flatten()
                    })
                    .unwrap();
                changed.copy_call_events[index].source_id = Some(foreign);
                assert!(
                    validate(&changed).is_err(),
                    "generated builtin Call borrowed a different source occurrence"
                );
            }
        }
    }
}
