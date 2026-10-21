//! Static call occurrences and dynamic observations are different identities.
//! This replay follows HIR child IDs; spans only locate a failed obligation.
use super::{
    ExpressionFact, SemanticFacts,
    copy_contract::{CopyCallEvent, CopyCallEventId},
    default_uses::{ArgumentSource, CallArguments, DefaultOrigin},
    effect_identity::{InvocationContext, InvocationExpression},
    model::{Callable, Ty},
};
use crate::hir::nodes::{self as hir, HirProgram, LexicalOwner};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{CallableOwner, ClosureSiteId, DefinitionId, ExprId, StmtId},
    source::{FileId, Span},
};
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
    closures: BTreeMap<ClosureSiteId, ExprId>,
}

impl Replay<'_> {
    fn pattern_value_sources(&self) -> Check<BTreeSet<ExprId>> {
        require(
            self.hir.generated_roots().len() <= LIMIT,
            "generated pattern source replay budget exhausted",
        )?;
        let mut patterns = BTreeMap::new();
        let mut values = BTreeSet::new();
        for (ordinal, &node) in self.hir.generated_roots().iter().enumerate() {
            let hir::NodeId::Expr(id) = node else {
                continue;
            };
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
        self.lexical_owner(context.owner)
    }
    fn lexical_owner(&self, owner: Option<CallableOwner>) -> Check<Owner> {
        match owner {
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
                let source = self
                    .closures
                    .get(&site)
                    .ok_or("call's closure site is absent")?;
                // Defaults and retained handler arms can keep a different
                // caller closure in their dynamic ancestry. The lexical site
                // resolves through its own declarations, not that caller.
                Ok(Owner::Lambda(*source))
            }
            None => Err("call observation has no lexical owner".into()),
        }
    }

    fn closure_coverage(&self) -> Check {
        let mut work = 4 * LIMIT;
        work = work
            .checked_sub(self.facts.closure_sites.len())
            .ok_or("closure site replay budget exhausted")?;
        for site in &self.facts.closure_sites {
            let syntax = self
                .hir
                .expression(site.source)
                .ok_or("closure site HIR source is absent")?;
            require(
                matches!(syntax.kind, hir::ExprKind::Lambda { .. }),
                "closure site source is not an actual HIR lambda",
            )?;
            require(
                self.static_owner(syntax.info.owner)? == self.lexical_owner(Some(site.owner))?,
                "closure site changed its original HIR lexical owner",
            )?;
            require(
                !matches!(site.owner, CallableOwner::Lambda(parent) if parent.0 >= site.id.0),
                "closure site has a cyclic or future lexical parent",
            )?;
        }
        let mut inhabited = BTreeSet::new();
        for closure in &self.facts.closures {
            work = work
                .checked_sub(closure.parameters.len().saturating_add(1))
                .ok_or("closure object replay budget exhausted")?;
            let site = closure
                .site
                .and_then(|id| self.facts.closure_sites.get(id.0 as usize))
                .ok_or("closure object lost its original static site")?;
            inhabited.insert(site.id);
            require(
                closure.hir_id == Some(site.source),
                "closure object borrowed a different static HIR site",
            )?;
            let Some(hir::Expr {
                kind:
                    hir::ExprKind::Lambda {
                        parameters, body, ..
                    },
                ..
            }) = self.hir.expression(site.source)
            else {
                return Err("closure object has no original HIR lambda".into());
            };
            require(
                closure.body.hir_id == Some(*body)
                    && closure.parameters.len() == parameters.len()
                    && closure
                        .parameters
                        .iter()
                        .zip(parameters)
                        .all(|(actual, original)| {
                            actual.pattern.hir_id == Some(original.pattern)
                                && actual.mode == original.mode
                        }),
                "closure object changed its original HIR body or formal parameters",
            )?;
        }
        require(
            inhabited.len() == self.facts.closure_sites.len(),
            "closure site has no actual creation object",
        )?;
        // A real lambda emission owns a closure object even if every producer
        // site row or callable tag has been deleted. Generated adapter recipes
        // have their separate actual HIR origin and are checked as objects above.
        let _remaining = work
            .checked_sub(self.facts.expressions.len())
            .ok_or("closure emission replay budget exhausted")?;
        for (index, fact) in self.facts.expressions.iter().enumerate() {
            let Some(source) = fact.source_id else {
                continue;
            };
            if !self
                .hir
                .expression(source)
                .is_some_and(|node| matches!(node.kind, hir::ExprKind::Lambda { .. }))
            {
                continue;
            }
            let [Callable::Closure(object)] = fact.value.callables.as_slice() else {
                return Err("actual HIR lambda emission lost its closure object".into());
            };
            let closure = self
                .facts
                .closures
                .get(*object)
                .ok_or("actual HIR lambda refers to an absent closure object")?;
            let site = closure
                .site
                .and_then(|id| self.facts.closure_sites.get(id.0 as usize))
                .ok_or("actual HIR lambda lost its lexical site")?;
            let context = self
                .observations
                .get(&index)
                .ok_or("actual HIR lambda lost its full creation context")?
                .context;
            require(
                site.source == source
                    && Some(site.owner) == context.owner
                    && closure.creation_invocation == context.invocation
                    && closure.creation_closure == context.closure_invocation
                    && closure.creation_default == context.default_use,
                "actual HIR lambda borrowed another source or creation activation",
            )?;
        }
        Ok(())
    }

    fn event(&self, event: &CopyCallEvent) -> Check<usize> {
        use crate::hir::application::EvaluationRole;
        let source = event
            .source_id
            .ok_or("application event has no static HIR identity")?;
        let syntax = self
            .hir
            .expression(source)
            .ok_or("application HIR identity is absent")?;
        let application = self
            .hir
            .application(source)?
            .ok_or("event HIR identity is not an application")?;
        let result_index = event
            .result_expression
            .ok_or("application lost its actual root observation")?;
        let (result_value, context) = self.observation(result_index, source)?;
        require(
            context.owner == event.owner && context.invocation == event.parent,
            "application result belongs to another full invocation context",
        )?;
        require(
            self.static_owner(syntax.info.owner)? == self.dynamic_owner(context)?,
            "application HIR owner differs from its actual lexical owner",
        )?;
        let preparation = self
            .preparations
            .get(&event.id)
            .ok_or("application lost its reserved preparation")?;
        require(
            preparation.target == event.target,
            "application preparation resolved target differs from its actual event",
        )?;
        require(
            !preparation.evaluated.is_empty() && preparation.evaluated.len() <= LIMIT,
            "application preparation has no real evaluated prefix",
        )?;
        let mut order = application.evaluation_order();
        let mut previous = None;
        let mut epoch = 0usize;
        let mut abrupt = false;
        let mut callee = None;
        let mut operands = BTreeMap::new();
        for evaluation in &preparation.evaluated {
            require(
                !abrupt && order.next() == Some(evaluation.role),
                "application evaluation is not its actual ordered prefix",
            )?;
            let expected = application
                .expression(evaluation.role)
                .ok_or("application prefix role is absent from HIR")?;
            let token = evaluation.observation;
            require(
                previous.is_none_or(|index| index < token.expression)
                    && token.expression < result_index
                    && epoch <= token.allocation_epoch
                    && token.allocation_epoch <= self.facts.allocation_history.len(),
                "application prefix changed its physical order or allocation epoch",
            )?;
            let (actual, observed_context) = self.observation(token.expression, expected)?;
            require(
                observed_context == context && actual.allocation_epoch == token.allocation_epoch,
                "application prefix borrowed another full invocation context",
            )?;
            if evaluation.role == EvaluationRole::Callee {
                require(
                    self.observations[&token.expression].argument_of.is_none(),
                    "callee root claims a parameter slot",
                )?;
                callee = Some((token.expression, actual));
            } else {
                require(
                    operands.insert(evaluation.role, token).is_none(),
                    "application operand was evaluated twice",
                )?;
            }
            previous = Some(token.expression);
            epoch = token.allocation_epoch;
            abrupt = actual.value.ty == Ty::Never;
        }
        let prefix_complete = order.next().is_none();
        require(
            prefix_complete || abrupt,
            "application omitted evaluation without an actual Never result",
        )?;
        require(
            event.callee_expression == callee.map(|(index, _)| index),
            "application callee differs from its actual evaluated prefix",
        )?;
        if callee.is_none() {
            require(
                event.target.is_none()
                    && !event.direct
                    && event.copy_operation.is_none()
                    && event.references.is_empty(),
                "application before callee evaluation claims a resolved target or copy operation",
            )?;
        }
        if !preparation.slots_bound {
            require(
                abrupt
                    && !preparation.evaluation_complete
                    && preparation.slots.is_empty()
                    && preparation.supplied.is_empty()
                    && result_value.value.ty == Ty::Never,
                "unbound application claims normal completion or received parameter slots",
            )?;
            for token in operands.values() {
                require(
                    self.observations[&token.expression].argument_of.is_none(),
                    "unbound operand claims a parameter slot",
                )?;
            }
            return Ok(result_index);
        }
        let (_, callee_value) = callee.ok_or("bound parameter slots have no actual callee")?;
        require(
            callee_value.value.ty != Ty::Never,
            "abrupt callee claims parameter binding",
        )?;
        let signature = callee_value.value.signature.as_ref();
        let labels = if let Some(signature) = signature {
            crate::hir::application::parameter_labels(signature)
        } else if let Some(id) = super::builtin_sources::generic_reference(&callee_value.value) {
            super::source_types::polymorphic::parameter_labels(id)
        } else {
            vec![None; application.operands.len()]
        };
        let count = labels.len();
        require(
            count <= LIMIT && preparation.slots.len() == count,
            "application slots differ from its public signature",
        )?;
        let mut names = BTreeSet::new();
        for name in labels.iter().flatten() {
            require(
                names.insert(name),
                "public callable signature repeats a label",
            )?;
        }
        let mut occupied = BTreeSet::new();
        let mut consumed = BTreeSet::new();
        let mapping = crate::hir::application::bind_slots(
            &labels,
            application.operands.iter().map(|operand| operand.label),
        );
        for (operand, slot) in application.operands.iter().zip(mapping) {
            let slot = slot.map_err(|code| {
                format!("application violates its original parameter binding: {code}")
            })?;
            require(
                slot < count && occupied.insert(slot),
                "application duplicates or exceeds a parameter slot",
            )?;
            if let Some(token) = operands.get(&operand.role) {
                require(
                    preparation.slots.get(slot) == Some(&ArgumentSource::Supplied)
                        && preparation.supplied.get(&(slot as u32)) == Some(token)
                        && self.observations[&token.expression].argument_of
                            == Some((event.id, slot as u32)),
                    "bound supplied slot differs from its real prefix observation",
                )?;
                consumed.insert(slot as u32);
            } else {
                require(
                    abrupt && !preparation.supplied.contains_key(&(slot as u32)),
                    "unreached operand claims a supplied parameter",
                )?;
            }
        }
        require(
            consumed.len() == preparation.supplied.len(),
            "application contains a foreign supplied operand",
        )?;
        let prefix_abrupt = abrupt;
        let mut previous = previous.unwrap();
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
                        prefix_complete && !prefix_abrupt && !occupied.contains(&slot),
                        "default replaced a supplied or unreached operand",
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
                        "default slot borrowed another application's evaluation",
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
                        "default is outside its actual evaluation interval",
                    )?;
                    let (actual, default_context) = self.observation(index, original)?;
                    let expected_context = InvocationContext {
                        owner: default.owner,
                        default_use: Some(*id),
                        ..context
                    };
                    require(
                        default_context == expected_context && default.span == actual.span,
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
            "parameter completion lacks actual normal or abrupt evaluation evidence",
        )?;
        if abrupt {
            require(
                result_value.value.ty == Ty::Never,
                "abrupt application prefix/default claims a normal result",
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
            && facts.default_uses.len() <= LIMIT
            && facts.copy_invocations.len() <= LIMIT
            && facts.closure_invocations.len() <= LIMIT
            && facts.functions.len() <= LIMIT
            && facts.closures.len() <= LIMIT
            && facts.closure_sites.len() <= LIMIT,
        "evaluation identity replay budget exhausted",
    )
    .map_err(fail)?;
    let Some(hir) = facts.semantic_hir.as_deref() else {
        return require(
            facts.source_program.is_none()
                && facts.copy_call_events.is_empty()
                && facts.closures.is_empty()
                && facts.closure_sites.is_empty()
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
    let mut evaluated_roots = BTreeSet::new();
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
        require(
            row.evaluated.len() <= LIMIT,
            "application prefix exceeds its work bound",
        )
        .map_err(fail)?;
        for step in &row.evaluated {
            require(
                evaluated_roots.insert(step.observation.expression),
                "two application prefixes claim the same actual evaluation root",
            )
            .map_err(fail)?;
        }
    }
    // These are reverse obligations. The last supplied operand may have
    // stopped before defaults/body entry, even when it was the complete written
    // prefix. An abrupt default itself still owns its genuine earlier defaults
    // and its own slot, so completion alone must not erase their evidence.
    for (index, default) in facts.default_uses.iter().enumerate() {
        let DefaultOrigin::Call(event) = default.origin else {
            continue;
        };
        require(
            default.id.0 as usize == index
                && replay.preparations.get(&event).is_some_and(|preparation| {
                    preparation.slots_bound
                        && preparation.slots.get(default.parameter as usize)
                            == Some(&ArgumentSource::Default(default.id))
                }),
            "actual default lost its exact application's reached parameter slot",
        )
        .map_err(|message| (default.span, None, message))?;
    }
    for (source_event, span) in facts
        .copy_invocations
        .iter()
        .filter_map(|invocation| {
            invocation
                .source_event
                .map(|event| (event, invocation.span))
        })
        .chain(facts.closure_invocations.iter().filter_map(|invocation| {
            invocation
                .source_event
                .map(|event| (event, invocation.site))
        }))
    {
        require(
            replay
                .preparations
                .get(&source_event)
                .is_some_and(|preparation| {
                    preparation.slots_bound && preparation.evaluation_complete
                }),
            "an incomplete application preparation claims an entered callable body",
        )
        .map_err(|message| (span, None, message))?;
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
    let mut site_sources = BTreeSet::new();
    for (index, site) in facts.closure_sites.iter().enumerate() {
        require(
            site.id.0 as usize == index
                && site_sources.insert((site.owner, site.source))
                && replay.closures.insert(site.id, site.source).is_none(),
            "closure site repeats or changes its static HIR identity",
        )
        .map_err(|message| (site.span, None, message))?;
    }
    replay.closure_coverage().map_err(fail)?;
    let pattern_values = replay.pattern_value_sources().map_err(fail)?;
    let mut results = BTreeSet::new();
    let mut previous_occurrences = BTreeMap::new();
    for (index, event) in facts.copy_call_events.iter().enumerate() {
        require(
            event.id.0 as usize == index,
            "call event identity differs from its arena slot",
        )
        .map_err(|message| (event.span, None, message))?;
        let result = replay
            .event(event)
            .map_err(|message| (event.span, None, message))?;
        let context = replay.observations[&result].context;
        let key = (
            event.source_id,
            context.owner,
            context.invocation.map(|id| id.0),
            context.closure,
            context.closure_invocation.map(|id| id.0),
            context.budget_validation,
            context.default_use.map(|id| id.0),
        );
        if let Some(previous) = previous_occurrences.insert(key, result) {
            require(
                previous
                    < replay.preparations[&event.id].evaluated[0]
                        .observation
                        .expression,
                "repeated application prefix borrowed an earlier occurrence",
            )
            .map_err(|message| (event.span, None, message))?;
        }
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
        if hir
            .application(id)
            .map_err(|message| {
                (
                    expression.span,
                    Some(expression.value.cause),
                    message.to_owned(),
                )
            })?
            .is_some()
        {
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
    use crate::sema::{
        default_uses::{ApplicationEvaluation, EvaluationRole, SuppliedArgument},
        model::Value,
    };
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
        application_model(arguments, events, repeat, false)
    }
    fn application_model(
        arguments: usize,
        events: usize,
        repeat: bool,
        pipeline: bool,
    ) -> SemanticFacts {
        use crate::hir::application::AstApplication;
        let mut source = ast::Program {
            statements: (0..if repeat { 1 } else { events })
                .map(|_| {
                    let mut expression = syntax(arguments);
                    if pipeline {
                        expression = ast::Expr {
                            hir_id: None,
                            span: span(),
                            kind: ast::ExprKind::Binary {
                                operator: "|>".into(),
                                left: Box::new(ast::Expr {
                                    hir_id: None,
                                    span: span(),
                                    kind: ast::ExprKind::Literal(ast::Literal::Integer("0".into())),
                                }),
                                right: Box::new(expression),
                            },
                        };
                    }
                    ast::Stmt {
                        hir_id: None,
                        span: span(),
                        kind: ast::StmtKind::Expr {
                            expression,
                            terminated: true,
                        },
                    }
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
            let application = AstApplication::from_ast(expression).unwrap();
            let id = CopyCallEventId(ordinal as u32);
            let mut callee = None;
            let mut evaluated = Vec::new();
            let mut supplied = BTreeMap::new();
            for role in application.evaluation_order() {
                let root = application.expression(role).unwrap();
                let index = facts.expressions.len();
                let token = SuppliedArgument {
                    expression: index,
                    allocation_epoch: 0,
                };
                evaluated.push(ApplicationEvaluation {
                    role,
                    observation: token,
                });
                let argument_of = match role {
                    EvaluationRole::Callee => {
                        callee = Some(index);
                        None
                    }
                    EvaluationRole::Piped => {
                        supplied.insert(0, token);
                        Some((id, 0))
                    }
                    EvaluationRole::Written(index) => {
                        let slot = index + u32::from(pipeline);
                        supplied.insert(slot, token);
                        Some((id, slot))
                    }
                };
                facts.expressions.push(ExpressionFact {
                    allocation_epoch: 0,
                    source_id: root.hir_id,
                    span: span(),
                    value: Value::scalar(
                        if role == EvaluationRole::Callee {
                            Ty::Unknown
                        } else {
                            Ty::Int("int".into())
                        },
                        None,
                        CauseId(0),
                    ),
                });
                facts.invocation_expressions.push(InvocationExpression {
                    context: context(),
                    expression: index,
                    argument_of,
                });
            }
            let result = facts.expressions.len();
            facts.expressions.push(ExpressionFact {
                allocation_epoch: 0,
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
                callee_expression: callee,
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
                evaluated,
                slots_bound: true,
                slots: vec![ArgumentSource::Supplied; application.operands.len()],
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
            allocation_epoch: 0,
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
        let hir::NodeId::Expr(root) = facts.semantic_hir.as_ref().unwrap().generated_roots()[0]
        else {
            unreachable!()
        };
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
            .filter_map(|node| match node {
                hir::NodeId::Expr(id) => Some(id),
                _ => None,
            })
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
    fn pipeline_uses_its_binary_identity_and_exact_prefix_before_binding_slots() {
        let facts = application_model(1, 1, false, true);
        assert!(validate(&facts).is_ok());
        let source = facts.copy_call_events[0].source_id.unwrap();
        assert!(matches!(
            facts
                .semantic_hir
                .as_ref()
                .unwrap()
                .expression(source)
                .unwrap()
                .kind,
            hir::ExprKind::Binary { .. }
        ));
        assert_eq!(
            facts.call_arguments[0]
                .evaluated
                .iter()
                .map(|step| step.role)
                .collect::<Vec<_>>(),
            [
                EvaluationRole::Piped,
                EvaluationRole::Callee,
                EvaluationRole::Written(0)
            ]
        );
        for mutation in 0..4 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.call_arguments[0].evaluated.swap(0, 2),
                1 => {
                    let foreign = changed.call_arguments[0].evaluated[1].observation;
                    changed.call_arguments[0].supplied.insert(0, foreign);
                }
                2 => {
                    changed.call_arguments[0].slots_bound = false;
                    changed.call_arguments[0].slots.clear();
                    changed.call_arguments[0].supplied.clear();
                }
                3 => changed.copy_call_events[0].callee_expression = None,
                _ => unreachable!(),
            }
            assert!(validate(&changed).is_err(), "pipeline mutation {mutation}");
        }
        let mut early = facts;
        let result = early.expressions.pop().unwrap();
        early.expressions.truncate(1);
        early.expressions.push(result);
        early.expressions[0].value.ty = Ty::Never;
        early.expressions[1].value.ty = Ty::Never;
        early.invocation_expressions.truncate(1);
        early.invocation_expressions[0].argument_of = None;
        early.invocation_expressions.push(InvocationExpression {
            context: context(),
            expression: 1,
            argument_of: None,
        });
        early.copy_call_events[0].callee_expression = None;
        early.copy_call_events[0].result_expression = Some(1);
        let preparation = &mut early.call_arguments[0];
        preparation.evaluated.truncate(1);
        preparation.slots_bound = false;
        preparation.evaluation_complete = false;
        preparation.slots.clear();
        preparation.supplied.clear();
        assert!(
            validate(&early).is_ok(),
            "an abrupt piped prefix must retain no invented callee"
        );
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
    fn deleting_hir_and_all_dynamic_application_identities_cannot_hide_real_source() {
        let mut facts = model(1, 2, false);
        assert!(validate(&facts).is_ok());
        assert!(facts.source_program.is_some());
        facts.semantic_hir = None;
        facts.copy_call_events.clear();
        facts.call_arguments.clear();
        for expression in &mut facts.expressions {
            expression.source_id = None;
        }
        for row in &mut facts.invocation_expressions {
            row.argument_of = None;
        }
        assert!(
            validate(&facts)
                .unwrap_err()
                .2
                .contains("no owning semantic HIR")
        );
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
        facts.call_arguments[0].evaluated.pop();
        assert!(validate(&facts).is_ok());
        let mut forged = facts.clone();
        forged.call_arguments[0].evaluation_complete = true;
        assert!(validate(&forged).is_err());
        facts.expressions.remove(1);
        facts.invocation_expressions.remove(1);
        facts.invocation_expressions[1].expression = 1;
        facts.copy_call_events[0].result_expression = Some(1);
        facts.call_arguments[0].evaluated.truncate(1);
        facts.call_arguments[0].slots_bound = false;
        facts.call_arguments[0].slots.clear();
        facts.call_arguments[0].supplied.clear();
        facts.expressions[0].value.ty = Ty::Never;
        assert!(
            validate(&facts).is_ok(),
            "a Never callee retains only its reserved evaluation prefix"
        );
    }

    #[test]
    fn an_abrupt_operand_cannot_start_defaults_or_enter_any_callable_body() {
        use crate::sema::copy_contract::{CopyInvocation, CopyInvocationStatus};
        use crate::sema::copy_templates::InstanceId;
        use crate::sema::default_uses::{DefaultUse, DefaultUseId};
        use crate::sema::effect_identity::{ClosureInvocation, ClosureInvocationId};
        use crate::sema::facts::ScopeId;
        let mut facts = model(1, 1, false);
        facts.expressions[1].value.ty = Ty::Never;
        facts.expressions[2].value.ty = Ty::Never;
        facts.call_arguments[0].evaluation_complete = false;
        assert!(validate(&facts).is_ok());
        let event = CopyCallEventId(0);
        let mut changed = facts.clone();
        changed.default_uses.push(DefaultUse {
            id: DefaultUseId(0),
            origin: DefaultOrigin::Call(event),
            target: None,
            parameter: 0,
            caller: context(),
            owner: context().owner,
            span: span(),
            arguments: vec![],
            captured_arguments: vec![],
            unresolved_captured_binders: BTreeSet::new(),
            evaluation_complete: false,
            status: CopyInvocationStatus::Incomplete,
            entered: vec![],
            result: None,
            result_expression: None,
            result_allocation_epoch: None,
        });
        assert!(
            validate(&changed)
                .unwrap_err()
                .2
                .contains("reached parameter slot")
        );
        let mut changed = facts.clone();
        changed.copy_invocations.push(CopyInvocation {
            id: InstanceId(0),
            entry: crate::sema::application_effect::CallableEntry {
                parent: None,
                caller_context: context(),
                origin: crate::sema::application_effect::EntryOrigin::Unresolved,
                allocation_epoch: 0,
                arguments: vec![],
            },
            parent: None,
            caller: None,
            caller_owner: context().owner,
            caller_activation: None,
            target: DefinitionId(0),
            span: span(),
            declaration_probe: false,
            direct: false,
            source_event: Some(event),
            boundaries: BTreeSet::new(),
            result: None,
            resource_copies: vec![],
            status: CopyInvocationStatus::Incomplete,
        });
        assert!(
            validate(&changed)
                .unwrap_err()
                .2
                .contains("entered callable body")
        );
        let mut changed = facts;
        changed.closure_invocations.push(ClosureInvocation {
            id: ClosureInvocationId(0),
            entry: crate::sema::application_effect::CallableEntry {
                parent: None,
                caller_context: context(),
                origin: crate::sema::application_effect::EntryOrigin::Unresolved,
                allocation_epoch: 0,
                arguments: std::sync::Arc::new(vec![]),
            },
            source_event: Some(event),
            caller_activation: ScopeId(0),
            activation: Some(ScopeId(1)),
            closure: 0,
            parent_named: None,
            parent_closure: None,
            caller_owner: context().owner,
            site: span(),
            probe: false,
            budget_validation: false,
            status: CopyInvocationStatus::Incomplete,
        });
        assert!(
            validate(&changed)
                .unwrap_err()
                .2
                .contains("entered callable body")
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
