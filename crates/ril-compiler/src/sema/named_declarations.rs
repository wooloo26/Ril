//! Every real named declaration keeps its original introducer, including
//! historical bindings which no later Name or call happens to consume.
use super::*;
use crate::hir::nodes::{LexicalOwner, StmtKind};
use crate::sema::{
    effect_identity::InvocationContext,
    model::{BindingInfo, Callable, FunctionInfo},
    scopes::ScopeOrigin,
};
use ril_compiler_core::ids::{DefinitionId, StmtId};
use ril_syntax::ast::BindingMode;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Original<T> {
    Declared(T),
    Conflict,
}

struct Index<'a> {
    facts: &'a SemanticFacts,
    definitions: BTreeMap<DefinitionId, Original<Option<StmtId>>>,
    statements: BTreeMap<StmtId, Original<DefinitionId>>,
}

fn charge(work: &mut usize, count: usize) -> Result<(), String> {
    match work.checked_sub(count) {
        Some(remaining) => {
            *work = remaining;
            Ok(())
        }
        None => {
            *work = 0;
            Err("named declaration coverage exceeds its shared work bound".into())
        }
    }
}
fn require(valid: bool, message: &str) -> Result<(), String> {
    valid.then_some(()).ok_or_else(|| message.to_owned())
}
fn lookup(count: usize) -> usize {
    1 + count.checked_ilog2().unwrap_or(0) as usize
}

impl<'a> Index<'a> {
    fn new(facts: &'a SemanticFacts, work: &mut usize) -> Result<Self, String> {
        charge(work, 1 + facts.functions.len())?;
        let mut index = Self {
            facts,
            definitions: BTreeMap::new(),
            statements: BTreeMap::new(),
        };
        for function in &facts.functions {
            charge(
                work,
                lookup(index.definitions.len()) + lookup(index.statements.len()) + 2,
            )?;
            index
                .definitions
                .entry(function.definition)
                .and_modify(|previous| {
                    if *previous != Original::Declared(function.hir_id) {
                        *previous = Original::Conflict;
                    }
                })
                .or_insert(Original::Declared(function.hir_id));
            if let Some(statement) = function.hir_id {
                index
                    .statements
                    .entry(statement)
                    .and_modify(|previous| {
                        if *previous != Original::Declared(function.definition) {
                            *previous = Original::Conflict;
                        }
                    })
                    .or_insert(Original::Declared(function.definition));
            }
        }
        Ok(index)
    }

    fn owner(
        &self,
        mut original: LexicalOwner,
        actual: Option<CallableOwner>,
        work: &mut usize,
    ) -> Result<(), String> {
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("named declaration owner has no HIR")?;
        for _ in 0..128 {
            charge(work, 2)?;
            match (original, actual) {
                (LexicalOwner::Module, Some(CallableOwner::Global)) => return Ok(()),
                (
                    LexicalOwner::Declaration(statement),
                    Some(CallableOwner::Function(definition)),
                ) => {
                    charge(work, lookup(self.definitions.len()))?;
                    return require(
                        self.definitions.get(&definition)
                            == Some(&Original::Declared(Some(statement)))
                            && hir
                                .statement(statement)
                                .is_some_and(|node| matches!(node.kind, StmtKind::Function(_))),
                        "named declaration borrowed another canonical function owner",
                    );
                }
                (LexicalOwner::Lambda(source), Some(CallableOwner::Lambda(site))) => {
                    return require(
                        self.facts
                            .closure_sites
                            .get(site.0 as usize)
                            .is_some_and(|record| record.id == site && record.source == source),
                        "named declaration borrowed another canonical lambda owner",
                    );
                }
                (LexicalOwner::HandlerArm { statement, .. }, _) => {
                    original = hir
                        .statement(statement)
                        .ok_or("named declaration handler owner is absent")?
                        .info
                        .owner;
                }
                _ => return Err("named declaration has another original lexical owner".into()),
            }
        }
        Err("named declaration owner ancestry exceeds its depth bound".into())
    }

    fn creation(
        &self,
        binding: &BindingInfo,
        original: LexicalOwner,
        work: &mut usize,
    ) -> Result<(), String> {
        charge(work, 3 + lookup(self.facts.scopes.records().len()))?;
        let record = self
            .facts
            .scopes
            .get(&binding.owner)
            .ok_or("named declaration creation scope is absent")?;
        let context = binding.context;
        match &record.origin {
            ScopeOrigin::Module => require(
                binding.owner == ScopeId(0)
                    && context
                        == InvocationContext {
                            owner: Some(CallableOwner::Global),
                            invocation: None,
                            closure: None,
                            closure_invocation: None,
                            default_use: None,
                            budget_validation: false,
                        },
                "named declaration has another module creation context",
            ),
            ScopeOrigin::Named(id) => {
                let call = self
                    .facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == *id)
                    .ok_or("named declaration creation invocation is absent")?;
                let expected = InvocationContext {
                    owner: Some(CallableOwner::Function(call.target)),
                    invocation: Some(*id),
                    ..call.entry.caller_context
                };
                require(
                    context == expected,
                    "named declaration borrowed another actual named creation",
                )
            }
            ScopeOrigin::Closure(id) => {
                let call = self
                    .facts
                    .closure_invocations
                    .get(id.0 as usize)
                    .filter(|call| call.id == *id && call.activation == Some(binding.owner))
                    .ok_or("named declaration closure creation invocation is absent")?;
                let closure = self
                    .facts
                    .closures
                    .get(call.closure)
                    .ok_or("named declaration creation closure is absent")?;
                let owner = closure.site.map(CallableOwner::Lambda);
                let expected = InvocationContext {
                    owner,
                    invocation: call.parent_named,
                    closure: Some(call.closure),
                    closure_invocation: Some(*id),
                    budget_validation: call.budget_validation,
                    ..call.entry.caller_context
                };
                require(
                    owner.is_some() && context == expected,
                    "named declaration borrowed another actual closure creation",
                )
            }
            ScopeOrigin::Operation(entry) => {
                let hir = self
                    .facts
                    .semantic_hir
                    .as_deref()
                    .ok_or("named operation declaration has no HIR")?;
                require(
                    entry.context == context
                        && entry
                            .body
                            .and_then(|body| hir.expression(body))
                            .is_some_and(|body| body.info.owner == original),
                    "named declaration borrowed another actual handler arm creation",
                )
            }
            ScopeOrigin::Unresolved => Err("named declaration creation scope is unresolved".into()),
        }
    }

    fn binding(&self, id: usize, work: &mut usize) -> Result<(), String> {
        charge(work, 5)?;
        let binding = self
            .facts
            .bindings
            .get(id)
            .ok_or("named declaration binding is absent")?;
        if binding.parameter || binding.pattern.is_some() || binding.birth.is_some() {
            return require(
                binding.declaration.is_none(),
                "a parameter or pattern alias borrowed a named declaration introducer",
            );
        }
        let [Callable::Named(target)] = binding.value.callables.as_slice() else {
            return require(
                binding.declaration.is_none(),
                "a non-named binding claims a named declaration introducer",
            );
        };
        let function = self
            .facts
            .functions
            .get(*target)
            .ok_or("named declaration targets an absent function")?;
        let statement = binding
            .declaration
            .ok_or("named declaration lost its original statement introducer")?;
        charge(
            work,
            lookup(self.definitions.len()) + lookup(self.statements.len()),
        )?;
        require(
            function.hir_id == Some(statement)
                && self.definitions.get(&function.definition)
                    == Some(&Original::Declared(Some(statement)))
                && self.statements.get(&statement)
                    == Some(&Original::Declared(function.definition)),
            "named declaration changed its canonical statement or definition identity",
        )?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("named declaration has no canonical HIR")?;
        let node = hir
            .statement(statement)
            .ok_or("named declaration statement is absent")?;
        let StmtKind::Function(header) = &node.kind else {
            return Err("named declaration introducer is not a function".into());
        };
        let name_work = 1 + binding
            .name
            .len()
            .max(function.syntax.name.len())
            .max(header.name.len())
            .div_ceil(32);
        charge(
            work,
            name_work
                .checked_mul(
                    3 + lookup(function.lexical.len())
                        + lookup(function.typing_environment.contract_bindings().len()),
                )
                .ok_or("named declaration lexical lookup work overflow")?,
        )?;
        require(
            binding.mode == BindingMode::Let
                && binding.owner == function.owner.unwrap_or(ScopeId(0))
                && binding.lexical_scope == function.lexical_scope
                && binding.context.owner == function.lexical_owner
                && binding.name == function.syntax.name
                && header.name == binding.name
                && function.lexical.get(&header.name) == Some(&id)
                && !function.typing_environment.is_poisoned()
                && !binding.typing_environment.is_poisoned()
                && function
                    .typing_environment
                    .contract_bindings()
                    .get(&header.name)
                    == Some(&id),
            "named declaration lost its actual creation scope, self binding or frozen environment",
        )?;
        self.owner(node.info.owner, function.lexical_owner, work)?;
        self.creation(binding, node.info.owner, work)?;
        self.header(function, header, work)
    }

    fn header(
        &self,
        function: &FunctionInfo,
        original: &crate::hir::nodes::Function,
        work: &mut usize,
    ) -> Result<(), String> {
        let syntax = &function.syntax;
        charge(
            work,
            original.parameters.len()
                + syntax.parameters.len()
                + original.generics.len()
                + syntax.generics.len()
                + original.annotations.len()
                + syntax.annotations.len()
                + original.signature_where.len()
                + syntax.signature_where.len()
                + 1,
        )?;
        require(
            original.visibility == syntax.visibility
                && original.is_meta == syntax.is_meta
                && original.is_halt == syntax.is_halt
                && original.generics.len() == syntax.generics.len()
                && original
                    .generics
                    .iter()
                    .zip(&syntax.generics)
                    .all(|(id, parameter)| Some(*id) == parameter.hir_id)
                && original.parameters.len() == syntax.parameters.len()
                && original
                    .parameters
                    .iter()
                    .zip(&syntax.parameters)
                    .all(|(parameter, syntax)| {
                        parameter.mode == syntax.mode
                            && Some(parameter.pattern) == syntax.pattern.hir_id
                            && parameter.ty == syntax.ty.as_ref().and_then(|ty| ty.hir_id)
                            && parameter.default
                                == syntax.default.as_ref().and_then(|value| value.hir_id)
                    })
                && original.return_type == syntax.return_type.as_ref().and_then(|ty| ty.hir_id)
                && original.signature_where.len() == syntax.signature_where.len()
                && original
                    .signature_where
                    .iter()
                    .zip(&syntax.signature_where)
                    .all(|(id, statement)| Some(*id) == statement.hir_id),
            "named declaration header lost its original HIR coordinates",
        )?;
        require(
            original.annotations.len() == syntax.annotations.len(),
            "named declaration changed its original annotations",
        )?;
        for (original, actual) in original.annotations.iter().zip(&syntax.annotations) {
            charge(
                work,
                original.text.len().div_ceil(32) + actual.text.len().div_ceil(32),
            )?;
            require(
                original.kind == actual.kind && original.text == actual.text,
                "named declaration changed its original annotation identity",
            )?;
        }
        match (&original.body, &syntax.body) {
            (Some(original), Some(actual)) => {
                charge(
                    work,
                    original.statements.len()
                        + original.where_items.len()
                        + actual.statements.len()
                        + actual.where_items.len(),
                )?;
                require(
                    original.statements.len() == actual.statements.len()
                        && original.where_items.len() == actual.where_items.len()
                        && original
                            .statements
                            .iter()
                            .zip(&actual.statements)
                            .all(|(id, statement)| Some(*id) == statement.hir_id)
                        && original
                            .where_items
                            .iter()
                            .zip(&actual.where_items)
                            .all(|(id, statement)| Some(*id) == statement.hir_id),
                    "named declaration body lost its original HIR statement identities",
                )
            }
            (None, None) => Ok(()),
            _ => Err("named declaration changed its original body role".into()),
        }
    }
}

pub(super) fn validate(facts: &SemanticFacts, work: &mut usize) -> Result<(), String> {
    charge(work, facts.bindings.len())?;
    let index = Index::new(facts, work)?;
    for id in 0..facts.bindings.len() {
        index.binding(id, work)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckOptions, Session};

    fn fixture(layout: &str) -> SemanticFacts {
        let source = ril_test::case_bytes(
            "tests/regressions/callable-inputs.ril::named-empty-header-scopes",
        );
        Session::with_options(
            source.to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{layout}: {error:?}"))
        .facts()
        .clone()
    }

    #[test]
    fn named_declaration_coverage_keeps_unused_historical_creations() {
        for layout in ["pointer32", "pointer64"] {
            let facts = fixture(layout);
            let bindings: Vec<_> = facts
                .bindings
                .iter()
                .enumerate()
                .filter_map(|(id, binding)| {
                    let statement = binding.declaration?;
                    let [Callable::Named(target)] = binding.value.callables.as_slice() else {
                        return None;
                    };
                    let function = &facts.functions[*target];
                    (function.owner.is_some()
                        && function.syntax.parameters.is_empty()
                        && function.syntax.generics.is_empty())
                    .then_some((id, statement, *target))
                })
                .collect();
            let returns =
                |target: usize, expected: &str| {
                    facts.functions[target].syntax.return_type.as_ref().is_some_and(|syntax| {
                    matches!(&syntax.kind, ril_syntax::ast::TypeKind::Name { path, arguments }
                        if path == &[expected] && arguments.is_empty())
                })
                };
            let integer_headers: Vec<_> = bindings
                .iter()
                .filter(|(_, _, target)| returns(*target, "int"))
                .collect();
            assert!(
                integer_headers.len() >= 4,
                "the two original integer declarations must have historical activations"
            );
            assert_eq!(
                integer_headers
                    .iter()
                    .map(|(_, statement, _)| *statement)
                    .collect::<BTreeSet<_>>()
                    .len(),
                2
            );
            let observed: BTreeSet<_> = facts
                .expressions
                .iter()
                .flat_map(|fact| fact.value.sources.iter().copied())
                .collect();
            let spare: Vec<_> = bindings
                .iter()
                .filter(|(_, _, target)| returns(*target, "bool"))
                .collect();
            assert!(
                spare.len() >= 2,
                "the spare declaration must have multiple real creation activations"
            );
            assert_eq!(
                spare
                    .iter()
                    .map(|(_, statement, _)| *statement)
                    .collect::<BTreeSet<_>>()
                    .len(),
                1
            );
            assert!(
                spare.iter().all(|(id, _, _)| !observed.contains(id)),
                "every spare declaration binding must really remain unobserved"
            );
            validate(&facts, &mut 4_000_000).unwrap();
            for &(id, statement, target) in &bindings {
                let &(sibling, sibling_statement, sibling_target) = bindings
                    .iter()
                    .find(|(other_id, other, _)| {
                        *other != statement
                            && facts.bindings[*other_id].context != facts.bindings[id].context
                    })
                    .expect("the substituted declaration must belong to another actual context");
                for mutation in 0..9 {
                    let mut changed = facts.clone();
                    match mutation {
                        0 => changed.bindings[id].declaration = None,
                        1 => changed.bindings[id].declaration = Some(sibling_statement),
                        2 => {
                            changed.functions[target]
                                .lexical
                                .remove(&facts.bindings[id].name);
                        }
                        3 => {
                            changed.functions[target].typing_environment =
                                facts.functions[sibling_target].typing_environment.clone()
                        }
                        4 => changed.bindings[id].owner = ScopeId(0),
                        5 => changed.bindings[id].context = facts.bindings[sibling].context,
                        6 => changed.functions[target].hir_id = Some(sibling_statement),
                        7 => {
                            changed.functions[target].definition =
                                facts.functions[sibling_target].definition
                        }
                        8 => {
                            changed.bindings[id].pattern =
                                Some(ril_compiler_core::ids::PatternId(u32::MAX))
                        }
                        _ => unreachable!(),
                    }
                    assert!(
                        validate(&changed, &mut 4_000_000).is_err(),
                        "{layout}: historical binding {id}, mutation {mutation} was accepted"
                    );
                }
            }
            let mut spans = facts.clone();
            for binding in &mut spans.bindings {
                binding.span = Span {
                    file: ril_compiler_core::source::FileId(77),
                    start: 0,
                    end: 0,
                };
            }
            validate(&spans, &mut 4_000_000).unwrap();
        }
    }

    #[test]
    fn named_declaration_coverage_spends_one_exact_shared_allowance() {
        let facts = fixture("pointer64");
        let mut work = 4_000_000;
        validate(&facts, &mut work).unwrap();
        let used = 4_000_000 - work;
        assert!(used > 0);
        let mut exact = used;
        validate(&facts, &mut exact).unwrap();
        assert_eq!(exact, 0);
        for mut short in [0, used - 1] {
            assert!(validate(&facts, &mut short).is_err());
            assert_eq!(short, 0);
        }
    }
}
