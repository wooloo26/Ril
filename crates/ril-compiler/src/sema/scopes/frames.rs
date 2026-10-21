//! Independent receiver replay over canonical frame records and original HIR.
use super::*;
use crate::hir::nodes::{self as hir, LexicalOwner};
use crate::sema::{
    SemanticFacts,
    model::{HandlerFact, OperationFact},
};
use ril_compiler_core::ids::StmtId;

pub(crate) struct FrameIndex<'a> {
    facts: &'a SemanticFacts,
    operations: BTreeMap<u64, &'a OperationFact>,
    first_parent: BTreeMap<ScopeId, Option<ActivationEpochId>>,
    preparations: BTreeMap<ScopeId, Vec<&'a crate::sema::default_uses::DefaultUse>>,
    signatures: super::signatures::SignatureIndex<'a>,
}

pub(crate) struct OperationFrame<'a> {
    pub entry: &'a OperationEntry,
    pub handler: &'a HandlerFact,
    pub operation: &'a OperationFact,
    pub arm: &'a ril_syntax::ast::HandlerArm,
    pub owner: (StmtId, u32),
}

fn require(condition: bool, message: &str) -> Result<(), String> {
    condition.then_some(()).ok_or_else(|| message.to_owned())
}

impl<'a> FrameIndex<'a> {
    pub(crate) fn preparations(
        &self,
        scope: ScopeId,
    ) -> &[&'a crate::sema::default_uses::DefaultUse] {
        self.preparations
            .get(&scope)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub(crate) fn signature(
        &self,
        operation: &OperationFact,
        selector: ril_compiler_core::ids::ExprId,
        context: InvocationContext,
    ) -> Result<super::signatures::Signature, String> {
        self.signatures.signature(
            operation,
            selector,
            super::signatures::SignatureContext::Evaluation(context),
        )
    }
    pub(crate) fn receiver_signature(
        &self,
        frame: &OperationFrame<'_>,
    ) -> Result<super::signatures::Signature, String> {
        self.signatures.signature(
            frame.operation,
            frame
                .arm
                .operation
                .hir_id
                .ok_or("operation receiver lost its selector")?,
            super::signatures::SignatureContext::Declaration(&frame.handler.typing_environment),
        )
    }
    pub(crate) fn new(facts: &'a SemanticFacts) -> Result<Self, String> {
        require(
            facts.scopes.records().count() <= 1_000_000 && facts.operations.len() <= 1_000_000,
            "frame receiver index exceeds its work bound",
        )?;
        let mut operations = BTreeMap::new();
        for operation in facts.operations.values() {
            require(
                operations.insert(operation.identity, operation).is_none(),
                "operation receiver has duplicate declaration identities",
            )?;
        }
        require(
            facts.activations.len() <= 1_000_000,
            "frame activation index exceeds its work bound",
        )?;
        let mut first_parent = BTreeMap::new();
        for activation in &facts.activations {
            first_parent
                .entry(activation.scope)
                .or_insert(activation.parent);
        }
        require(
            facts.default_uses.len() <= 1_000_000,
            "frame preparation index exceeds its work bound",
        )?;
        let mut preparations = BTreeMap::<_, Vec<_>>::new();
        for receipt in &facts.default_uses {
            if let Some(root) = receipt
                .result_expression
                .and_then(|index| facts.evaluations.get(index))
            {
                preparations.entry(root.scope).or_default().push(receipt);
            }
        }
        Ok(Self {
            facts,
            signatures: super::signatures::SignatureIndex::new(facts)?,
            operations,
            first_parent,
            preparations,
        })
    }

    pub(crate) fn operation(&self, scope: ScopeId) -> Result<Option<OperationFrame<'a>>, String> {
        let Some(ScopeRecord {
            origin: ScopeOrigin::Operation(entry),
            parent: scope_parent,
            ..
        }) = self.facts.scopes.get(&scope)
        else {
            return Ok(None);
        };
        let facts = self.facts;
        require(
            self.first_parent.get(&scope) == Some(&entry.parent),
            "operation frame changed its first actual evaluation parent",
        )?;
        let handler = facts
            .handlers
            .get(entry.handler)
            .filter(|handler| handler.id == entry.handler)
            .ok_or("operation frame lost its original handler")?;
        let operation = self
            .operations
            .get(&entry.operation)
            .copied()
            .ok_or("operation frame lost its operation declaration")?;
        require(
            entry.context.owner == handler.callable_owner
                && handler.operations.contains(&entry.operation)
                && scope_parent.is_some_and(|parent| facts.scopes.contains(&parent))
                && entry.allocation_epoch <= facts.allocation_history.len(),
            "operation receiver changed its handler, scope or declaration context",
        )?;
        let body = entry
            .body
            .ok_or("operation frame has no original HIR body")?;
        let hir = facts
            .semantic_hir
            .as_deref()
            .ok_or("operation frame has no canonical HIR")?;
        let owner = match hir.expression(body).map(|node| node.info.owner) {
            Some(LexicalOwner::HandlerArm { statement, index }) => (statement, index),
            _ => return Err("operation receiver body has no original handler arm".into()),
        };
        let Some(hir::Stmt {
            kind: hir::StmtKind::Handler(arms),
            ..
        }) = hir.statement(owner.0)
        else {
            return Err("operation receiver lost its original handler statement".into());
        };
        let original = arms
            .get(owner.1 as usize)
            .ok_or("operation receiver names a missing original arm")?;
        let mut matches = handler
            .arms
            .iter()
            .filter(|arm| arm.body.hir_id == Some(body));
        let arm = matches
            .next()
            .ok_or("operation receiver borrowed another handler body")?;
        self.signatures.signature(
            operation,
            original.operation,
            super::signatures::SignatureContext::Declaration(&handler.typing_environment),
        )?;
        require(
            matches.next().is_none()
                && original.body == body
                && arm.operation.hir_id == Some(original.operation)
                && original.parameters.len() == arm.parameters.len()
                && arm
                    .parameters
                    .iter()
                    .zip(&original.parameters)
                    .all(|(a, b)| a.pattern.hir_id == Some(b.pattern) && a.mode == b.mode)
                && operation.parameters.len() == original.parameters.len()
                && operation
                    .parameters
                    .iter()
                    .zip(&original.parameters)
                    .all(|((mode, _), param)| *mode == param.mode),
            "operation receiver changed its genuine arm header or parameter modes",
        )?;
        if let Some(source) = &operation.source {
            let Some(hir::Stmt {
                kind:
                    hir::StmtKind::Effect {
                        operations,
                        generics,
                        name,
                        ..
                    },
                ..
            }) = hir.statement(source.effect)
            else {
                return Err("operation declaration lost its HIR effect owner".into());
            };
            let header = operations
                .get(source.index as usize)
                .and_then(|id| hir.statement(*id));
            let Some(hir::Stmt {
                kind: hir::StmtKind::Function(header),
                ..
            }) = header
            else {
                return Err("operation declaration lost its original HIR signature".into());
            };
            require(
                !source.environment.is_poisoned()
                    && header.name == operation.name.rsplit("::").next().unwrap_or("")
                    && header.parameters.len() == operation.parameters.len()
                    && header
                        .parameters
                        .iter()
                        .zip(&operation.parameters)
                        .all(|(a, (mode, _))| a.mode == *mode)
                    && (generics.is_empty() && *name == operation.effect
                        || !generics.is_empty()
                            && facts.effect_instances.iter().any(|instance| {
                                instance.name == operation.effect
                                    && instance.key.name == *name
                                    && instance.operations.contains(&operation.identity)
                            })),
                "operation receiver borrowed another effect declaration or instance",
            )?;
        } else {
            require(
                operation.parameters.is_empty()
                    && matches!(
                        (operation.identity, operation.name.as_str()),
                        (u64::MAX, "Fiber::yield") | (18446744073709551614, "Div::exhausted")
                    ),
                "operation receiver has no original or intrinsic declaration",
            )?;
        }
        let parent = entry
            .parent
            .and_then(|id| facts.activations.get(id.0 as usize));
        require(
            entry
                .parent
                .is_none_or(|id| parent.is_some_and(|parent| parent.id == id))
                && entry.context
                    == InvocationContext {
                        owner: handler.callable_owner,
                        ..entry.caller_context
                    },
            "operation receiver borrowed another full caller context",
        )?;
        match &entry.origin {
            EntryOrigin::Application(id) => {
                let parent = parent.ok_or("operation receiver has no actual evaluation parent")?;
                require(
                    parent.context == entry.caller_context,
                    "operation call parent changed its caller context",
                )?;
                let event = facts
                    .copy_call_events
                    .get(id.0 as usize)
                    .filter(|event| event.id == *id)
                    .ok_or("operation receiver lost its actual source application")?;
                let callee = event
                    .callee_expression
                    .and_then(|index| {
                        facts
                            .expressions
                            .get(index)
                            .zip(facts.evaluations.get(index))
                    })
                    .ok_or("operation receiver lost its physical callee")?;
                require(
                    parent.source == event.source_id
                        && parent.result.map(|id| id.0 as usize) == event.result_expression
                        && event.owner == entry.caller_context.owner
                        && event.parent == entry.caller_context.invocation
                        && callee.1.context == entry.caller_context
                        && matches!(callee.0.value.callables.as_slice(), [crate::sema::model::Callable::Builtin(name)] if *name == operation.name),
                    "operation receiver borrowed another physical effect invocation",
                )?;
            }
            EntryOrigin::DeclarationProbe => {
                let creation = scope_parent
                    .and_then(|id| facts.scopes.get(&id))
                    .ok_or("operation probe lost its creation frame")?;
                let direct = parent.is_some_and(|parent| parent.scope == creation.id);
                let creator = if direct {
                    parent.and_then(|parent|parent.source).and_then(|id|hir.expression(id)).is_some_and(|node|
                        matches!(&node.kind, hir::ExprKind::Block(block) if block.statements.contains(&owner.0) || block.where_items.contains(&owner.0)))
                } else {
                    match &creation.origin {
                        ScopeOrigin::Named(id) => facts
                            .copy_invocations
                            .get(id.0 as usize)
                            .is_some_and(|call| {
                                call.id == *id
                                    && call.entry.parent == entry.parent
                                    && entry.caller_context.invocation == Some(*id)
                                    && entry.caller_context.owner
                                        == Some(ril_compiler_core::ids::CallableOwner::Function(
                                            call.target,
                                        ))
                            }),
                        ScopeOrigin::Closure(id) => facts
                            .closure_invocations
                            .get(id.0 as usize)
                            .is_some_and(|call| {
                                call.id == *id
                                    && call.activation == Some(creation.id)
                                    && entry.caller_context.closure_invocation == Some(*id)
                            }),
                        ScopeOrigin::Module => {
                            creation.id == ScopeId(0)
                                && entry.parent.is_none()
                                && hir.roots().contains(&owner.0)
                                && entry.caller_context.owner
                                    == Some(ril_compiler_core::ids::CallableOwner::Global)
                        }
                        _ => false,
                    }
                };
                require(
                    creator && entry.caller_context.owner == handler.callable_owner,
                    "operation declaration probe borrowed another creation scope",
                )?;
            }
            EntryOrigin::Generated {
                anchor,
                callee,
                inputs,
            } => {
                let parent = parent.ok_or("generated operation receiver lost its actual parent")?;
                let value = facts
                    .expressions
                    .get(callee.0 as usize)
                    .ok_or("generated operation callee is absent")?;
                require(
                    *anchor == parent.id
                        && inputs.is_empty()
                        && operation.name == "Div::exhausted"
                        && matches!(value.value.callables.as_slice(), [crate::sema::model::Callable::Builtin(name)] if name == "Div::budget")
                        && facts
                            .evaluations
                            .get(callee.0 as usize)
                            .is_some_and(|record| record.context == entry.caller_context),
                    "generated exhaustion receiver lost its actual budget application",
                )?;
            }
            _ => return Err("operation receiver has an unresolved entry origin".into()),
        }
        Ok(Some(OperationFrame {
            entry,
            handler,
            operation,
            arm,
            owner,
        }))
    }
}

pub(crate) fn validate(facts: &SemanticFacts) -> Result<(), String> {
    let index = FrameIndex::new(facts)?;
    let mut frames = BTreeMap::new();
    for record in facts.scopes.records() {
        if let Some(frame) = index.operation(record.id)? {
            frames.insert(record.id, frame);
        }
    }
    if let Some(hir) = facts.semantic_hir.as_deref() {
        let mut work = 1_000_000usize;
        for (expression, record) in facts.expressions.iter().zip(&facts.evaluations) {
            work = work
                .checked_sub(1)
                .ok_or("operation occurrence coverage exhausted its work bound")?;
            let Some(LexicalOwner::HandlerArm { statement, index }) = expression
                .source_id
                .and_then(|id| hir.expression(id))
                .map(|node| node.info.owner)
            else {
                continue;
            };
            let frame = frames
                .get(&record.scope)
                .ok_or("original handler HIR occurrence has no operation receiver")?;
            require(
                frame.owner == (statement, index) && frame.entry.context == record.context,
                "handler HIR occurrence borrowed another operation activation",
            )?;
        }
    }
    Ok(())
}
