//! Readonly lexical syntax and actual-ID row indexes for channel evidence.
//! Instance callee, argument, borrowing and custody proofs remain separate.
use super::{Bounds, Check, Node, children};
use crate::hir::application::AstApplication;
use crate::sema::{
    SemanticFacts,
    copy_contract::{CopyCallEvent, CopyCallEventId},
    copy_templates::InstanceId,
    effect_identity::InvocationCall,
};
use ril_compiler_core::{
    ids::{CallableOwner, ExprId},
    source::Span,
};
use ril_syntax::ast::{Expr, Function, PatternKind, StmtKind};
use std::collections::{BTreeMap, btree_map::Entry};

#[derive(Clone, Copy)]
pub(super) enum Role {
    Expression,
    Call,
}

type SpanKey = (u32, u32, u32);
type Found<'a> = (&'a Expr, Bounds);

#[derive(Clone, Copy, Default)]
enum Match<'a> {
    #[default]
    Missing,
    One(Found<'a>),
    Ambiguous,
}
impl<'a> Match<'a> {
    fn add(&mut self, found: Found<'a>) {
        *self = match self {
            Self::Missing => Self::One(found),
            Self::One(_) | Self::Ambiguous => Self::Ambiguous,
        };
    }
    fn get(self) -> Check<Found<'a>> {
        match self {
            Self::One(found) => Ok(found),
            Self::Ambiguous => Err("channel source application syntax is ambiguous".into()),
            Self::Missing => {
                Err("channel source application is absent from its actual callable syntax".into())
            }
        }
    }
}

#[derive(Default)]
struct AtSpan<'a> {
    expression: Match<'a>,
    call: Match<'a>,
}

#[derive(Default)]
struct OwnerSyntax<'a> {
    locations: BTreeMap<SpanKey, AtSpan<'a>>,
    applications: BTreeMap<ExprId, Match<'a>>,
}

pub(super) struct Index<'a> {
    facts: &'a SemanticFacts,
    owners: BTreeMap<CallableOwner, OwnerSyntax<'a>>,
    caller_rows: Option<BTreeMap<InstanceId, Vec<&'a InvocationCall>>>,
}

fn charge(work: &mut usize) -> Check {
    *work = work
        .checked_sub(1)
        .ok_or("channel execution-bound analysis exceeds its work bound")?;
    Ok(())
}

impl<'a> Index<'a> {
    pub(super) fn new(facts: &'a SemanticFacts) -> Self {
        Self {
            facts,
            owners: BTreeMap::new(),
            caller_rows: None,
        }
    }

    pub(super) fn lookup(
        &mut self,
        owner: Option<CallableOwner>,
        span: Span,
        role: Role,
        work: &mut usize,
    ) -> Check<Found<'a>> {
        charge(work)?;
        let owner = owner.ok_or(
            "channel source callable has no closed syntax for execution-bound reconstruction",
        )?;
        let source = match self.owners.entry(owner) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let source = Self::build(self.facts, owner, work)?;
                // A failed or partial construction is never published.
                entry.insert(source)
            }
        };
        let key = (span.file.0, span.start, span.end);
        let found = source
            .locations
            .get(&key)
            .map(|at| match role {
                Role::Expression => at.expression,
                Role::Call => at.call,
            })
            .unwrap_or_default();
        found.get()
    }

    /// Application bounds are reconstructed under their actual lexical owner
    /// and selected by static HIR identity, never recovered from a source span.
    pub(super) fn application_syntax(
        &mut self,
        id: CopyCallEventId,
        work: &mut usize,
    ) -> Check<Found<'a>> {
        let event = self.application(id, work)?;
        let owner = event
            .owner
            .ok_or("channel application has no lexical owner")?;
        let source_id = event
            .source_id
            .ok_or("channel application has no HIR identity")?;
        let source = match self.owners.entry(owner) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Self::build(self.facts, owner, work)?),
        };
        let found = source
            .applications
            .get(&source_id)
            .copied()
            .unwrap_or_default()
            .get()?;
        if found.0.hir_id != Some(source_id) || found.0.span != event.span {
            return Err("channel application disagrees with its original HIR source".into());
        }
        Ok(found)
    }

    /// An application remains identified by its physical arena position.
    /// No owner/span lookup can recover or substitute a missing actual ID.
    pub(super) fn application(
        &self,
        id: CopyCallEventId,
        work: &mut usize,
    ) -> Check<&'a CopyCallEvent> {
        charge(work)?;
        self.facts
            .copy_call_events
            .get(id.0 as usize)
            .filter(|event| event.id == id)
            .ok_or_else(|| "channel source application is missing".into())
    }

    /// Retrieve every actual-ID row, without choosing or inferring a caller.
    /// Returned references retain instance fields for validation at each use.
    pub(super) fn caller_links(
        &mut self,
        instance: InstanceId,
        work: &mut usize,
    ) -> Check<Vec<&'a InvocationCall>> {
        charge(work)?;
        if self.caller_rows.is_none() {
            let mut rows = BTreeMap::<_, Vec<_>>::new();
            for row in &self.facts.invocation_calls {
                charge(work)?;
                rows.entry(row.invocation).or_default().push(row);
            }
            self.caller_rows = Some(rows);
        }
        let rows = self
            .caller_rows
            .as_ref()
            .and_then(|rows| rows.get(&instance));
        let length = rows.map_or(0, Vec::len);
        *work = work
            .checked_sub(length)
            .ok_or("channel execution-bound analysis exceeds its work bound")?;
        Ok(rows.cloned().unwrap_or_default())
    }

    fn build(
        facts: &'a SemanticFacts,
        owner: CallableOwner,
        work: &mut usize,
    ) -> Check<OwnerSyntax<'a>> {
        let mut stack = Vec::new();
        match owner {
            CallableOwner::Global => {
                return Err("channel source callable has no closed syntax for execution-bound reconstruction".into());
            }
            CallableOwner::Function(id) => {
                let mut canonical: Option<&'a Function> = None;
                for candidate in &facts.functions {
                    charge(work)?;
                    if candidate.definition != id {
                        continue;
                    }
                    if canonical.is_some_and(|source| source != &candidate.syntax) {
                        return Err("channel source owner has inconsistent duplicate function headers/bodies".into());
                    }
                    canonical.get_or_insert(&candidate.syntax);
                }
                let source = canonical.ok_or("channel source callable definition is missing")?;
                if let Some(body) = &source.body {
                    stack.push(Node::Block(body, Bounds::default()));
                }
                for statement in &source.signature_where {
                    stack.push(Node::Stmt(statement, Bounds::default()));
                }
                for parameter in &source.parameters {
                    if let Some(default) = &parameter.default {
                        stack.push(Node::Expr(default, Bounds::default()));
                    }
                }
            }
            CallableOwner::Lambda(site) => {
                let mut canonical: Option<&'a crate::sema::model::ClosureInfo> = None;
                for candidate in &facts.closures {
                    charge(work)?;
                    if candidate.site != Some(site) {
                        continue;
                    }
                    if canonical.is_some_and(|source| {
                        source.parameters != candidate.parameters || source.body != candidate.body
                    }) {
                        return Err("channel source owner has inconsistent duplicate closure headers/bodies".into());
                    }
                    canonical.get_or_insert(candidate);
                }
                let source = canonical.ok_or("channel source closure syntax is missing")?;
                stack.push(Node::Expr(&source.body, Bounds::default()));
            }
        }
        let mut output = OwnerSyntax::default();
        while let Some(node) = stack.pop() {
            charge(work)?;
            match node {
                Node::Expr(expression, bounds) => {
                    let span = expression.span;
                    let at = output
                        .locations
                        .entry((span.file.0, span.start, span.end))
                        .or_default();
                    at.expression.add((expression, bounds));
                    if AstApplication::from_ast(expression).is_some() {
                        at.call.add((expression, bounds));
                        if let Some(id) = expression.hir_id {
                            output
                                .applications
                                .entry(id)
                                .or_default()
                                .add((expression, bounds));
                        }
                    }
                    children(expression, bounds, &mut stack);
                }
                Node::Block(block, bounds) => {
                    for statement in block.statements.iter().chain(&block.where_items) {
                        stack.push(Node::Stmt(statement, bounds));
                    }
                }
                Node::Stmt(statement, bounds) => match &statement.kind {
                    StmtKind::Binding(binding) => {
                        stack.push(Node::Expr(&binding.value, bounds));
                        if let Some(fallback) = &binding.fallback {
                            stack.push(Node::Expr(fallback, bounds));
                        }
                        stack.push(Node::Pattern(&binding.pattern, bounds));
                    }
                    StmtKind::Assignment { target, value, .. } => {
                        stack.push(Node::Expr(target, bounds));
                        stack.push(Node::Expr(value, bounds));
                    }
                    StmtKind::Expr { expression, .. }
                    | StmtKind::HandlerApplication(expression) => {
                        stack.push(Node::Expr(expression, bounds));
                    }
                    StmtKind::Handler(arms) => {
                        for arm in arms {
                            stack.push(Node::Expr(&arm.body, bounds));
                        }
                    }
                    StmtKind::Function(_)
                    | StmtKind::Type(_)
                    | StmtKind::Effect(_)
                    | StmtKind::Use(_) => {}
                },
                Node::Pattern(pattern, bounds) => match &pattern.kind {
                    PatternKind::Value(value) => stack.push(Node::Expr(value, bounds)),
                    PatternKind::Tuple(values)
                    | PatternKind::Alternative(values)
                    | PatternKind::Constructor {
                        arguments: values, ..
                    } => {
                        for value in values {
                            stack.push(Node::Pattern(value, bounds));
                        }
                    }
                    PatternKind::Record { fields, .. } => {
                        for field in fields {
                            stack.push(Node::Pattern(&field.pattern, bounds));
                        }
                    }
                    PatternKind::Mode { pattern, .. } => stack.push(Node::Pattern(pattern, bounds)),
                    _ => {}
                },
            }
            if stack.len() > *work {
                return Err("channel syntax traversal exceeds its pending work bound".into());
            }
        }
        Ok(output)
    }
}

#[cfg(test)]
#[path = "channel_source_index_tests.rs"]
mod tests;
