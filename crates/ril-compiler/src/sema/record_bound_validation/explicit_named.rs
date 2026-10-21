//! Source-grounded replay of immediate named Type prefixes. There is no stored
//! application token: the actual Call/Generic/Name observations and the existing
//! own static argument rows must independently agree at every occurrence.
use super::*;
use crate::sema::{
    copy_contract::{CopyCallEvent, CopyInvocation},
    effect_identity::{InvocationContext, StaticArgumentWitness},
    model::Callable,
};
use ril_syntax::ast::{Block, Pattern, PatternKind, RecordMember};

struct Site<'a> {
    owner: CallableOwner,
    call: Option<&'a Expr>,
    generic: &'a Expr,
    base: &'a Expr,
    arguments: &'a [TypeExpr],
}

pub(super) struct CallSite<'a> {
    pub owner: CallableOwner,
    pub expression: &'a Expr,
}

pub(super) struct BindingSite<'a> {
    pub owner: CallableOwner,
    pub binding: &'a ril_syntax::ast::Binding,
}

pub(super) struct FunctionSite<'a> {
    pub owner: CallableOwner,
    pub function: &'a ril_syntax::ast::Function,
}

pub(super) struct AssignmentSite<'a> {
    pub owner: CallableOwner,
    pub target: &'a Expr,
    pub operator: &'a str,
    pub value: &'a Expr,
}

pub(super) struct SourceSites<'a> {
    pub expressions: BTreeMap<ril_compiler_core::ids::ExprId, &'a Expr>,
    generic: Vec<Site<'a>>,
    pub calls: Vec<CallSite<'a>>,
    pub bindings: Vec<BindingSite<'a>>,
    pub assignments: Vec<AssignmentSite<'a>>,
    pub lambdas: Vec<CallSite<'a>>,
    pub functions: Vec<FunctionSite<'a>>,
}

enum Pending<'a> {
    Statement(CallableOwner, &'a Stmt, usize),
    Expression(CallableOwner, &'a Expr, Option<&'a Expr>, usize),
    Pattern(CallableOwner, &'a Pattern, usize),
}

fn declaration_only(function: &ril_syntax::ast::Function) -> bool {
    function
        .parameters
        .iter()
        .all(|parameter| parameter.default.is_none())
        && function.signature_where.is_empty()
        && function.body.as_ref().is_none_or(|body| {
            body.where_items.is_empty()
                && body.statements.iter().all(|statement| {
                    matches!(&statement.kind, StmtKind::Expr { expression, .. }
                        if matches!(expression.kind, ExprKind::Name(_) | ExprKind::Literal(_)))
                })
        })
}

pub(super) fn source_sites(facts: &SemanticFacts) -> Check<SourceSites<'_>> {
    source_sites_inner(facts, true)
}

pub(super) fn source_sites_base(facts: &SemanticFacts) -> Check<SourceSites<'_>> {
    source_sites_inner(facts, false)
}

fn source_sites_inner(facts: &SemanticFacts, include_generated: bool) -> Check<SourceSites<'_>> {
    let mut generated = if include_generated {
        super::super::checker::checked_generated_source_roots(facts)?
    } else {
        Vec::new()
    }
    .into_iter();
    let mut pending = Vec::new();
    if generated.len() == 0
        && facts
            .functions
            .iter()
            .all(|function| declaration_only(&function.syntax))
        && facts.source_program.as_deref().is_none_or(|program| {
            program
                .statements
                .iter()
                .all(|statement| match &statement.kind {
                    StmtKind::Function(function) => declaration_only(function),
                    StmtKind::Use(_) | StmtKind::Type(_) | StmtKind::Effect(_) => true,
                    _ => false,
                })
        })
    {
        // Declaration-only model facts do not claim an application receipt.
        // The source predicate, rather than an empty/mutable arena, proves that
        // no executable Call or Generic expression needs coverage here.
        return Ok(SourceSites {
            expressions: BTreeMap::new(),
            generic: Vec::new(),
            calls: Vec::new(),
            bindings: Vec::new(),
            assignments: Vec::new(),
            lambdas: Vec::new(),
            functions: Vec::new(),
        });
    }
    let mut headers: BTreeMap<DefinitionId, &FunctionInfo> = BTreeMap::new();
    for function in &facts.functions {
        if let Some(previous) = headers.insert(function.definition, function) {
            require(
                previous.syntax == function.syntax,
                "explicit named source has inconsistent copies of one declaration",
            )?;
        }
    }
    let program = facts
        .source_program
        .as_deref()
        .ok_or_else(|| "named input replay has no frozen actual Program".to_owned())?;
    pending.extend(
        program
            .statements
            .iter()
            .map(|statement| Pending::Statement(CallableOwner::Global, statement, 0)),
    );
    let mut work = LIMIT;
    let mut result = Vec::new();
    let mut calls = Vec::new();
    let mut bindings = Vec::new();
    let mut assignments = Vec::new();
    let mut lambdas = Vec::new();
    let mut functions = Vec::new();
    let mut expressions = BTreeMap::new();
    loop {
        let node = match pending.pop() {
            Some(node) => node,
            None => match generated.next() {
                Some((owner, expression)) => Pending::Expression(owner, expression, None, 0),
                None => break,
            },
        };
        work = work
            .checked_sub(1)
            .ok_or_else(|| "explicit named source walk exceeds its work bound".to_owned())?;
        match node {
            Pending::Statement(owner, statement, depth) => {
                require(
                    depth < 128,
                    "explicit named statement nesting exceeds its bound",
                )?;
                match &statement.kind {
                    StmtKind::Binding(binding) => {
                        bindings.push(BindingSite { owner, binding });
                        pending.push(Pending::Expression(owner, &binding.value, None, depth + 1));
                        pending.push(Pending::Pattern(owner, &binding.pattern, depth + 1));
                        pending.extend(binding.fallback.iter().map(|expression| {
                            Pending::Expression(owner, expression, None, depth + 1)
                        }));
                    }
                    StmtKind::Assignment {
                        target,
                        operator,
                        value,
                    } => {
                        assignments.push(AssignmentSite {
                            owner,
                            target,
                            operator,
                            value,
                        });
                        pending.push(Pending::Expression(owner, target, None, depth + 1));
                        pending.push(Pending::Expression(owner, value, None, depth + 1));
                    }
                    StmtKind::Expr { expression, .. }
                    | StmtKind::HandlerApplication(expression) => {
                        pending.push(Pending::Expression(owner, expression, None, depth + 1));
                    }
                    StmtKind::Handler(arms) => {
                        for arm in arms {
                            pending.push(Pending::Expression(
                                owner,
                                &arm.operation,
                                None,
                                depth + 1,
                            ));
                            pending.push(Pending::Expression(owner, &arm.body, None, depth + 1));
                        }
                    }
                    StmtKind::Function(function) => {
                        if function.is_meta {
                            continue;
                        }
                        let matching: Vec<_> = headers
                            .values()
                            .filter(|header| {
                                header.syntax == *function
                                    && header.hir_id.is_some()
                                    && header.hir_id == statement.hir_id
                                    && header.lexical_owner.unwrap_or(CallableOwner::Global)
                                        == owner
                            })
                            .collect();
                        if matching.is_empty() && function.body.is_none() {
                            continue;
                        }
                        let [header] = matching.as_slice() else {
                            return Err(
                                "named input Source has no unique actual function identity".into(),
                            );
                        };
                        require(
                            header.syntax == *function
                                && header.lexical_owner.unwrap_or(CallableOwner::Global) == owner,
                            "named input function header or lexical owner differs from the actual Program",
                        )?;
                        let owner = CallableOwner::Function(header.definition);
                        functions.push(FunctionSite { owner, function });
                        if let Some(body) = &function.body {
                            push_block(&mut pending, owner, body, depth + 1);
                        }
                        pending.extend(
                            function
                                .signature_where
                                .iter()
                                .map(|statement| Pending::Statement(owner, statement, depth + 1)),
                        );
                        for parameter in &function.parameters {
                            pending.push(Pending::Pattern(owner, &parameter.pattern, depth + 1));
                            pending.extend(
                                parameter.default.iter().map(|value| {
                                    Pending::Expression(owner, value, None, depth + 1)
                                }),
                            );
                        }
                    }
                    StmtKind::Type(_) | StmtKind::Effect(_) | StmtKind::Use(_) => {}
                }
            }
            Pending::Pattern(owner, pattern, depth) => {
                require(
                    depth < 128,
                    "explicit named pattern nesting exceeds its bound",
                )?;
                match &pattern.kind {
                    PatternKind::Value(value) => {
                        pending.push(Pending::Expression(owner, value, None, depth + 1))
                    }
                    PatternKind::Mode { pattern, .. } => {
                        pending.push(Pending::Pattern(owner, pattern, depth + 1))
                    }
                    PatternKind::Tuple(items)
                    | PatternKind::Alternative(items)
                    | PatternKind::Constructor {
                        arguments: items, ..
                    } => {
                        pending.extend(
                            items
                                .iter()
                                .map(|item| Pending::Pattern(owner, item, depth + 1)),
                        );
                    }
                    PatternKind::Record { fields, .. } => {
                        pending.extend(
                            fields
                                .iter()
                                .map(|field| Pending::Pattern(owner, &field.pattern, depth + 1)),
                        );
                    }
                    _ => {}
                }
            }
            Pending::Expression(owner, expression, parent_call, depth) => {
                if let Some(id) = expression.hir_id {
                    require(
                        expressions.insert(id, expression).is_none(),
                        "original expression index repeats a HIR identity",
                    )?;
                }
                require(
                    depth < 128,
                    "explicit named expression nesting exceeds its bound",
                )?;
                let mut children = Vec::new();
                match &expression.kind {
                    ExprKind::Generic { base, arguments } => {
                        result.push(Site {
                            owner,
                            call: parent_call,
                            generic: expression,
                            base,
                            arguments,
                        });
                        children.push(base.as_ref());
                    }
                    ExprKind::Call { callee, arguments } => {
                        calls.push(CallSite { owner, expression });
                        pending.push(Pending::Expression(
                            owner,
                            callee,
                            Some(expression),
                            depth + 1,
                        ));
                        children.extend(arguments.iter().map(|argument| &argument.value));
                    }
                    ExprKind::Lambda {
                        parameters, body, ..
                    } => {
                        lambdas.push(CallSite { owner, expression });
                        let matching: Vec<_> = facts
                            .closure_sites
                            .iter()
                            .filter(|site| {
                                site.owner == owner && Some(site.source) == expression.hir_id
                            })
                            .collect();
                        let [site] = matching.as_slice() else {
                            return Err(
                                "explicit named source lambda has no unique lexical identity"
                                    .into(),
                            );
                        };
                        for closure in facts
                            .closures
                            .iter()
                            .filter(|closure| closure.site == Some(site.id))
                        {
                            require(
                                closure.parameters.len() == parameters.len()
                                    && closure.body == **body
                                    && closure.parameters.iter().zip(parameters).all(
                                        |(stored, written)| {
                                            stored.mode == written.mode
                                                && stored.pattern == written.pattern
                                                && written
                                                    .ty
                                                    .as_ref()
                                                    .is_none_or(|ty| stored.ty.as_ref() == Some(ty))
                                        },
                                    ),
                                "call input lambda registry changed its real Source header or body",
                            )?;
                        }
                        let owner = CallableOwner::Lambda(site.id);
                        pending.push(Pending::Expression(owner, body, None, depth + 1));
                        for parameter in parameters {
                            pending.push(Pending::Pattern(owner, &parameter.pattern, depth + 1));
                            pending.extend(
                                parameter.default.iter().map(|value| {
                                    Pending::Expression(owner, value, None, depth + 1)
                                }),
                            );
                        }
                    }
                    ExprKind::Block(block) | ExprKind::Loop(block) => {
                        push_block(&mut pending, owner, block, depth + 1)
                    }
                    ExprKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        children.extend([condition.as_ref(), then_branch.as_ref()]);
                        children.extend(else_branch.iter().map(Box::as_ref));
                    }
                    ExprKind::Match { value, arms, .. } => {
                        children.push(value.as_ref());
                        for arm in arms {
                            children.push(&arm.body);
                            children.extend(arm.guard.iter());
                            pending.push(Pending::Pattern(owner, &arm.pattern, depth + 1));
                        }
                    }
                    ExprKind::Is { value, pattern } => {
                        children.push(value.as_ref());
                        pending.push(Pending::Pattern(owner, pattern, depth + 1));
                    }
                    ExprKind::Unary { operand, .. } => children.push(operand.as_ref()),
                    ExprKind::Field { base, .. } => children.push(base.as_ref()),
                    ExprKind::Binary {
                        left,
                        operator,
                        right,
                    } if matches!(operator.as_str(), "!>" | "|>") => {
                        let application = AstApplication::from_ast(expression);
                        if application.is_some() {
                            calls.push(CallSite { owner, expression });
                        }
                        children.push(left.as_ref());
                        if let ExprKind::Call { callee, arguments } = &right.kind {
                            // This is the pipeline's application notation. Its
                            // callee and real operands are evaluated directly;
                            // the wrapper is not a separate Call occurrence.
                            pending.push(Pending::Expression(
                                owner,
                                callee,
                                application.as_ref().map(|_| expression),
                                depth + 1,
                            ));
                            children.extend(arguments.iter().map(|argument| &argument.value));
                        } else {
                            pending.push(Pending::Expression(
                                owner,
                                right,
                                application.as_ref().map(|_| expression),
                                depth + 1,
                            ));
                        }
                    }
                    ExprKind::Binary { left, right, .. }
                    | ExprKind::Index {
                        base: left,
                        index: right,
                        ..
                    }
                    | ExprKind::ComputedField {
                        base: left,
                        key: right,
                    } => children.extend([left.as_ref(), right.as_ref()]),
                    ExprKind::While { condition, body } => {
                        children.push(condition.as_ref());
                        push_block(&mut pending, owner, body, depth + 1);
                    }
                    ExprKind::For {
                        iterable,
                        pattern,
                        body,
                    } => {
                        children.push(iterable.as_ref());
                        pending.push(Pending::Pattern(owner, pattern, depth + 1));
                        push_block(&mut pending, owner, body, depth + 1);
                    }
                    ExprKind::Control { value, .. } => {
                        children.extend(value.iter().map(Box::as_ref))
                    }
                    ExprKind::Derive { base, recipe } => {
                        children.extend(base.iter().map(Box::as_ref));
                        children.push(recipe.as_ref());
                    }
                    ExprKind::Range { start, end, .. } => {
                        children.extend(start.iter().map(Box::as_ref));
                        children.extend(end.iter().map(Box::as_ref));
                    }
                    ExprKind::Tuple(items) | ExprKind::Array(items) => children.extend(items),
                    ExprKind::Map(items) => {
                        for (key, value) in items {
                            children.extend([key, value]);
                        }
                    }
                    ExprKind::Record { members, .. } => {
                        for member in members {
                            match member {
                                RecordMember::Field(field) => children.push(&field.value),
                                RecordMember::Spread(value) => children.push(value),
                            }
                        }
                    }
                    ExprKind::Interpolated(parts) => {
                        for part in parts {
                            if let StringPart::Interpolation { expression, .. } = part {
                                children.push(expression);
                            }
                        }
                    }
                    ExprKind::Name(_)
                    | ExprKind::Path(_)
                    | ExprKind::Literal(_)
                    | ExprKind::Accessor(_)
                    | ExprKind::TypeValue(_)
                    | ExprKind::KeyOf(_)
                    | ExprKind::Ambient
                    | ExprKind::Error => {}
                }
                pending.extend(
                    children
                        .into_iter()
                        .map(|child| Pending::Expression(owner, child, None, depth + 1)),
                );
            }
        }
        require(
            pending.len() <= work.saturating_add(1),
            "explicit named pending source exceeds its work bound",
        )?;
    }
    Ok(SourceSites {
        expressions,
        generic: result,
        calls,
        bindings,
        assignments,
        lambdas,
        functions,
    })
}

fn push_block<'a>(
    pending: &mut Vec<Pending<'a>>,
    owner: CallableOwner,
    block: &'a Block,
    depth: usize,
) {
    pending.extend(
        block
            .statements
            .iter()
            .chain(&block.where_items)
            .map(|statement| Pending::Statement(owner, statement, depth)),
    );
}

/// Use this Source gate before the parent's no-record-arenas early return.
/// Failure cannot become `false`, and missing call/static rows cannot erase it.
pub(super) fn has_sources(facts: &SemanticFacts) -> Check<bool> {
    Ok(source_sites(facts)?.generic.iter().any(|site| {
        let name = match &site.base.kind {
            ExprKind::Name(name) => Some(name.as_str()),
            ExprKind::Path(path) if path.len() == 1 => Some(path[0].as_str()),
            _ => None,
        };
        facts.functions.iter().any(|function| {
            function.syntax.body.is_some() && name == Some(function.syntax.name.as_str())
        })
    }))
}

impl Replay<'_> {
    fn explicit_source_target(&self, site: &Site<'_>) -> Check<Option<DefinitionId>> {
        let name = match &site.base.kind {
            ExprKind::Name(name) => name.as_str(),
            ExprKind::Path(path) if path.len() == 1 => &path[0],
            _ => return Ok(None),
        };
        let CallableOwner::Function(owner) = site.owner else {
            return Ok(None);
        };
        let mut chain = self.owner_chain(owner)?;
        chain.reverse();
        let mut lexical = chain
            .into_iter()
            .map(CallableOwner::Function)
            .collect::<Vec<_>>();
        lexical.push(CallableOwner::Global);
        for owner in lexical {
            let matching: Vec<_> = self
                .functions
                .values()
                .filter(|function| {
                    function.syntax.name == name
                        && function.syntax.body.is_some()
                        && function.lexical_owner.unwrap_or(CallableOwner::Global) == owner
                })
                .collect();
            require(
                matching.len() <= 1,
                "explicit named source has ambiguous declaration lookup",
            )?;
            if let Some(function) = matching.first() {
                return Ok(Some(function.definition));
            }
        }
        Ok(None)
    }

    fn explicit_observation<'a>(
        &'a self,
        event: &CopyCallEvent,
        expression: usize,
        syntax: &Expr,
        context: InvocationContext,
        target: DefinitionId,
    ) -> Check<&'a Value> {
        let expression = self
            .facts
            .expressions
            .get(expression)
            .ok_or_else(|| "explicit named expression token is outside its arena".to_owned())?;
        require(
            expression.source_id.is_some() && expression.source_id == syntax.hir_id,
            "explicit named expression token names another actual AST node",
        )?;
        let [Callable::Named(index)] = expression.value.callables.as_slice() else {
            return Err("explicit named expression lacks a unique named target".into());
        };
        require(
            self.facts
                .functions
                .get(*index)
                .is_some_and(|function| function.definition == target),
            "explicit named expression borrowed another callee",
        )?;
        require(
            self.facts
                .invocation_expressions
                .iter()
                .filter(|row| {
                    self.facts
                        .expressions
                        .get(row.expression)
                        .is_some_and(|actual| std::ptr::eq(actual, expression))
                        && row.context == context
                })
                .count()
                == 1,
            "explicit named expression has no unique actual caller observation",
        )?;
        require(
            event.owner == context.owner && event.parent == context.invocation,
            "explicit named caller namespace differs from its actual call event",
        )?;
        Ok(&expression.value)
    }

    fn explicit_static_rows<'a>(
        &'a self,
        invocation: &CopyInvocation,
    ) -> Check<&'a [StaticArgumentWitness]> {
        let matching: Vec<_> = self
            .facts
            .effect_invocations
            .iter()
            .filter(|row| row.invocation == Some(invocation.id))
            .collect();
        let [row] = matching.as_slice() else {
            return Err(
                "explicit named instance has no unique complete static argument observation".into(),
            );
        };
        let function = self.function(invocation.target)?;
        require(
            row.function == invocation.target
                && row.site == invocation.span
                && row.arguments.len() == function.syntax.generics.len(),
            "explicit named static arguments do not cover the genuine declaration",
        )?;
        for (index, argument) in row.arguments.iter().enumerate() {
            let binder = self.binder(invocation.target, index as u32)?;
            require(
                argument.definition == invocation.target
                    && argument.index as usize == index
                    && argument.binder == binder.identity,
                "explicit named static row changed an owned binder or position",
            )?;
        }
        Ok(&row.arguments)
    }

    fn explicit_caller_selections(
        &self,
        context: InvocationContext,
        scope: &BoundScope,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let id = context
            .invocation
            .ok_or_else(|| "explicit named source has no actual named caller".to_owned())?;
        let caller = self
            .facts
            .copy_invocations
            .get(id.0 as usize)
            .filter(|caller| caller.id == id)
            .ok_or_else(|| "explicit caller instance is missing".to_owned())?;
        require(
            context.owner == Some(CallableOwner::Function(caller.target)),
            "explicit caller Type namespace borrowed another callable owner",
        )?;
        let rows = self.explicit_static_rows(caller)?;
        let mut selected = BTreeMap::new();
        for argument in rows {
            if scope
                .types
                .values()
                .any(|identity| identity == &argument.binder)
                && let Some(key) = &argument.key
            {
                selected.insert(argument.binder.clone(), key.clone());
            }
        }
        let effect = self
            .facts
            .effect_invocations
            .iter()
            .find(|row| row.invocation == Some(id))
            .expect("unique caller static row");
        for argument in &effect.captured_arguments {
            if scope
                .types
                .values()
                .any(|identity| identity == &argument.binder)
                && let Some(key) = &argument.key
            {
                selected.insert(argument.binder.clone(), key.clone());
            }
        }
        Ok(selected)
    }

    pub(super) fn explicit_named_applications(&self) -> Result<(), Failure> {
        for site in source_sites(self.facts)
            .map_err(|message| {
                (
                    self.facts
                        .functions
                        .first()
                        .map(|function| function.syntax.span)
                        .unwrap_or(Span {
                            file: ril_compiler_core::source::FileId(0),
                            start: 0,
                            end: 0,
                        }),
                    None,
                    message,
                )
            })?
            .generic
        {
            let check = || -> Check {
                if !self.facts.expressions.iter().any(|observed| {
                    observed.source_id.is_some() && observed.source_id == site.generic.hir_id
                }) {
                    return Ok(());
                }
                let Some(target) = self.explicit_source_target(&site)? else {
                    return Ok(());
                };
                let call_syntax = site.call.ok_or_else(|| {
                    "stored or escaped named generic application has no direct-call proof"
                        .to_owned()
                })?;
                let events: Vec<_> = self
                    .facts
                    .copy_call_events
                    .iter()
                    .filter(|event| {
                        event.owner == Some(site.owner) && event.matches_source(call_syntax)
                    })
                    .collect();
                require(
                    !events.is_empty(),
                    "actual explicit named source has no physical application coverage",
                )?;
                for event in events {
                    let preparation = self
                        .facts
                        .call_arguments
                        .iter()
                        .find(|row| row.source_event == event.id)
                        .ok_or_else(|| {
                            "explicit application has no evaluation preparation".to_owned()
                        })?;
                    if !preparation.evaluation_complete {
                        require(
                            !self
                                .facts
                                .copy_invocations
                                .iter()
                                .any(|call| call.source_event == Some(event.id)),
                            "abrupt explicit application claims a body instance",
                        )?;
                        continue;
                    }
                    require(
                        event.direct && event.target == Some(target),
                        "explicit named source changed its real declaration target",
                    )?;
                    let instances: Vec<_> = self
                        .facts
                        .copy_invocations
                        .iter()
                        .filter(|invocation| invocation.source_event == Some(event.id))
                        .collect();
                    let [invocation] = instances.as_slice() else {
                        return Err("explicit named call has no unique actual instance".into());
                    };
                    require(
                        invocation.target == target
                            && invocation.caller_owner == Some(site.owner)
                            && invocation.parent == event.parent
                            && invocation.span == event.span
                            && invocation.status == CopyInvocationStatus::Completed,
                        "explicit named application borrowed another instance or incomplete result",
                    )?;
                    let caller_rows: Vec<_> = self
                        .facts
                        .invocation_calls
                        .iter()
                        .filter(|row| row.invocation == invocation.id)
                        .collect();
                    let [caller] = caller_rows.as_slice() else {
                        return Err(
                            "explicit named call has no unique original caller context".into()
                        );
                    };
                    let context = InvocationContext {
                        owner: caller.caller_owner,
                        invocation: invocation.parent,
                        closure: caller.caller_closure,
                        closure_invocation: caller.caller_closure_invocation,
                        default_use: caller.default_use,
                        budget_validation: false,
                    };
                    require(
                        context.default_use.is_none(),
                        "explicit named default scope needs separate source proof",
                    )?;
                    let expression = event.callee_expression.ok_or_else(|| {
                        "explicit named call lacks its actual Generic emission token".to_owned()
                    })?;
                    self.explicit_observation(event, expression, site.generic, context, target)?;
                    require(
                        event.references.len() == 2,
                        "explicit named call lost a genuine Generic/Name reference layer",
                    )?;
                    let mut base_value = None;
                    let mut outer = 0;
                    for id in &event.references {
                        let reference = self
                            .facts
                            .copy_references
                            .get(id.0 as usize)
                            .filter(|reference| reference.id == *id)
                            .ok_or_else(|| {
                                "explicit named reference identity is missing".to_owned()
                            })?;
                        require(
                            reference.target == target
                                && reference.direct_call == Some(event.id)
                                && reference.owner == Some(site.owner)
                                && reference.parent == event.parent,
                            "explicit named reference belongs to another physical call",
                        )?;
                        if reference.expression == expression {
                            outer += 1;
                        } else {
                            require(
                                base_value.is_none(),
                                "explicit named base observation is duplicated",
                            )?;
                            base_value = Some(self.explicit_observation(
                                event,
                                reference.expression,
                                site.base,
                                context,
                                target,
                            )?);
                        }
                    }
                    require(
                        outer == 1,
                        "explicit named Generic observation is missing or duplicated",
                    )?;
                    let base_value = base_value
                        .ok_or_else(|| "explicit named base observation is absent".to_owned())?;
                    require(
                        base_value.sources.len() == 1
                            && base_value
                                .sources
                                .iter()
                                .next()
                                .and_then(|id| self.facts.bindings.get(*id))
                                .is_some_and(|binding| {
                                    !binding.parameter
                                        && binding.span
                                            == self
                                                .function(target)
                                                .expect("actual target")
                                                .syntax
                                                .span
                                        && binding.name
                                            == self
                                                .function(target)
                                                .expect("actual target")
                                                .syntax
                                                .name
                                }),
                        "explicit named Source names an alias instead of its real declaration binding",
                    )?;
                    let function = self.function(target)?;
                    require(
                        !site.arguments.is_empty()
                            && site.arguments.len() <= function.syntax.generics.len(),
                        "explicit named source prefix has invalid arity",
                    )?;
                    let CallableOwner::Function(owner) = site.owner else {
                        return Err("explicit named caller has no Type namespace".into());
                    };
                    let scope = self.scope(owner)?;
                    let selected = self.explicit_caller_selections(context, &scope)?;
                    let rows = self.explicit_static_rows(invocation)?;
                    for (index, syntax) in site.arguments.iter().enumerate() {
                        let binder = self.binder(target, index as u32)?;
                        self.type_binder(&binder.identity)?;
                        let expected =
                            select_key(&self.normalized_key(syntax, &scope)?, &selected, 0)?;
                        let argument = &rows[index];
                        require(
                            argument.key.as_ref() == Some(&expected) && argument.syntax.is_some(),
                            "explicit named Type source differs from its complete owned static argument",
                        )?;
                    }
                }
                Ok(())
            };
            check().map_err(|message| (site.generic.span, None, message))?;
        }
        Ok(())
    }
}
