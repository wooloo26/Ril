//! Formal borrowing ends at its actual invocation boundary. Captured values
//! retain their source authority, not an indefinitely active callee participant.
use super::{
    copy_templates::InstanceId,
    effect_identity::ClosureInvocationId,
    facts::{LoanId, Participant, ScopeId},
    model::{Origins, Value},
};
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{CallableOwner, DefinitionId, PatternId, StmtId},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct InvocationLoanStart {
    pub loan: LoanId,
    pub activation: ScopeId,
    pub owner: Option<CallableOwner>,
    pub named: Option<InstanceId>,
    pub closure: Option<ClosureInvocationId>,
    pub parameter: u32,
    pub retained: bool,
    pub origins: Origins,
    pub source: Value,
    pub parents: BTreeSet<Participant>,
    pub bindings: BTreeSet<usize>,
    pub allocation_epoch: usize,
    pub cause: CauseId,
    pub span: Span,
}

fn charge(work: &mut usize, count: usize) -> Result<(), String> {
    *work = work
        .checked_sub(count)
        .ok_or_else(|| "formal loan binding coverage exceeds its work bound".to_owned())?;
    Ok(())
}

/// Borrowed declaration/birth lookup, shared by every formal loan in this
/// replay. Final values may already have had their ended loans normalized.
struct FormalBindings<'a> {
    facts: &'a super::SemanticFacts,
    named: BTreeMap<DefinitionId, Option<StmtId>>,
    bindings: BTreeMap<(ScopeId, PatternId, &'a str), usize>,
    patterns: BTreeMap<PatternId, Vec<crate::hir::nodes::PatternBinding>>,
}

impl<'a> FormalBindings<'a> {
    fn new(facts: &'a super::SemanticFacts, work: &mut usize) -> Result<Self, String> {
        charge(work, facts.functions.len())?;
        charge(work, facts.bindings.len())?;
        let mut named = BTreeMap::new();
        for function in &facts.functions {
            if named
                .insert(function.definition, function.hir_id)
                .is_some_and(|previous| previous != function.hir_id)
            {
                return Err(
                    "formal loan declaration has inconsistent original HIR identities".into(),
                );
            }
        }
        let mut bindings = BTreeMap::new();
        for (id, binding) in facts.bindings.iter().enumerate() {
            if !binding.parameter {
                continue;
            }
            let Some(pattern) = binding.pattern else {
                continue;
            };
            charge(work, binding.name.len().div_ceil(32))?;
            if bindings
                .insert((binding.owner, pattern, binding.name.as_str()), id)
                .is_some()
            {
                return Err(
                    "formal loan has duplicate binding births for one receiver pattern".into(),
                );
            }
        }
        Ok(Self {
            facts,
            named,
            bindings,
            patterns: BTreeMap::new(),
        })
    }

    fn hir(&self) -> Result<&'a crate::hir::nodes::HirProgram, String> {
        self.facts
            .semantic_hir
            .as_deref()
            .ok_or_else(|| "formal loan has no canonical HIR declarations".to_owned())
    }

    fn named_parameters(
        &self,
        owner: DefinitionId,
        work: &mut usize,
    ) -> Result<&'a [crate::hir::nodes::Parameter], String> {
        charge(work, 1)?;
        let hir = self.hir()?;
        let declaration = self
            .named
            .get(&owner)
            .copied()
            .flatten()
            .and_then(|id| hir.statement(id))
            .ok_or("formal loan has no original named declaration")?;
        let crate::hir::nodes::StmtKind::Function(function) = &declaration.kind else {
            return Err("formal loan named header is not an original function".into());
        };
        Ok(&function.parameters)
    }

    fn closure_parameters(
        &self,
        call: &super::effect_identity::ClosureInvocation,
        work: &mut usize,
    ) -> Result<&'a [crate::hir::nodes::Parameter], String> {
        charge(work, 2)?;
        let closure = self
            .facts
            .closures
            .get(call.closure)
            .ok_or("formal loan closure object is absent")?;
        let site = closure
            .site
            .and_then(|id| {
                self.facts
                    .closure_sites
                    .get(id.0 as usize)
                    .filter(|site| site.id == id)
            })
            .ok_or("formal loan closure has no original site")?;
        if closure.hir_id != Some(site.source) {
            return Err("formal loan closure borrowed another original header".into());
        }
        let original = self
            .hir()?
            .expression(site.source)
            .ok_or("formal loan original lambda is absent")?;
        let crate::hir::nodes::ExprKind::Lambda { parameters, .. } = &original.kind else {
            return Err("formal loan closure header is not an original lambda".into());
        };
        Ok(parameters)
    }

    fn expected(
        &mut self,
        activation: ScopeId,
        pattern: PatternId,
        context: super::effect_identity::InvocationContext,
        work: &mut usize,
    ) -> Result<BTreeSet<usize>, String> {
        charge(work, 1)?;
        if !self.patterns.contains_key(&pattern) {
            let plan = self
                .hir()?
                .pattern_bindings(pattern, work)
                .map_err(|error| format!("formal loan original parameter pattern: {error}"))?;
            self.patterns.insert(pattern, plan);
        }
        let plan = &self.patterns[&pattern];
        charge(work, plan.len())?;
        let mut expected = BTreeSet::new();
        for leaf in plan {
            charge(work, leaf.name.len().div_ceil(32))?;
            let id = self
                .bindings
                .get(&(activation, leaf.pattern, leaf.name.as_str()))
                .copied()
                .ok_or("formal loan parameter is missing an original binding birth")?;
            if self.facts.bindings[id].context != context {
                return Err(
                    "formal loan binding belongs to another actual invocation context".into(),
                );
            }
            expected.insert(id);
        }
        Ok(expected)
    }
}

pub fn validate(facts: &super::SemanticFacts) -> Result<(), (Span, Option<CauseId>, String)> {
    use super::copy_contract::CopyInvocationStatus;
    let fallback = facts
        .invocation_loan_starts
        .first()
        .map(|start| start.span)
        .or_else(|| facts.copy_invocations.first().map(|call| call.span))
        .or_else(|| facts.closure_invocations.first().map(|call| call.site))
        .unwrap_or(Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        });
    let mut work = 4_000_000usize;
    let mut formal =
        FormalBindings::new(facts, &mut work).map_err(|message| (fallback, None, message))?;
    let mut starts = BTreeMap::new();
    let mut named_starts = BTreeMap::new();
    let mut closure_starts = BTreeMap::new();
    for start in &facts.invocation_loan_starts {
        let fail = |message: &str| (start.span, Some(start.cause), message.to_owned());
        charge(&mut work, 1 + start.bindings.len() + start.parents.len())
            .map_err(|message| fail(&message))?;
        if starts.insert(start.loan, start).is_some()
            || facts.loan_parents.get(&start.loan) != Some(&start.parents)
            || start.source.participants != start.parents
            || start.source.origins != start.origins
            || !facts.scopes.contains(&start.activation)
            || start.allocation_epoch > facts.allocation_history.len()
        {
            return Err(fail(
                "formal loan entry does not match its actual source and loan registry",
            ));
        }
        let (mode, pattern, context) = match start.owner {
            Some(CallableOwner::Function(owner)) => {
                let call = start
                    .named
                    .and_then(|id| facts.copy_invocations.get(id.0 as usize))
                    .filter(|call| {
                        Some(call.id) == start.named
                            && call.target == owner
                            && call.status == CopyInvocationStatus::Completed
                            && start.closure == call.entry.caller_context.closure_invocation
                            && start.allocation_epoch >= call.entry.allocation_epoch
                    })
                    .ok_or_else(|| {
                        fail("formal loan has no matching completed named invocation")
                    })?;
                if !facts.scopes.get(&start.activation).is_some_and(|scope|
                    matches!(scope.origin, super::scopes::ScopeOrigin::Named(id) if Some(id) == start.named))
                    || named_starts.insert((call.id, start.parameter), start).is_some()
                {
                    return Err(fail("formal loan borrowed another named receiver or duplicated its slot"));
                }
                let parameter = formal
                    .named_parameters(owner, &mut work)
                    .map_err(|message| fail(&message))?
                    .get(start.parameter as usize)
                    .ok_or_else(|| {
                        fail("formal loan parameter is outside its original named header")
                    })?;
                (
                    parameter.mode,
                    parameter.pattern,
                    super::effect_identity::InvocationContext {
                        owner: start.owner,
                        invocation: start.named,
                        ..call.entry.caller_context
                    },
                )
            }
            Some(CallableOwner::Lambda(site)) => {
                let call = start
                    .closure
                    .and_then(|id| facts.closure_invocations.get(id.0 as usize))
                    .filter(|call| {
                        Some(call.id) == start.closure
                            && call.parent_named == start.named
                            && call.status == CopyInvocationStatus::Completed
                            && call.activation == Some(start.activation)
                            && start.allocation_epoch >= call.entry.allocation_epoch
                    })
                    .ok_or_else(|| {
                        fail("formal loan has no matching completed closure invocation")
                    })?;
                if !facts.closures.get(call.closure).is_some_and(|closure| closure.site == Some(site))
                    || !facts.scopes.get(&start.activation).is_some_and(|scope|
                        matches!(scope.origin, super::scopes::ScopeOrigin::Closure(id) if id == call.id))
                    || closure_starts.insert((call.id, start.parameter), start).is_some()
                {
                    return Err(fail("formal loan borrowed another closure receiver or duplicated its slot"));
                }
                let parameter = formal
                    .closure_parameters(call, &mut work)
                    .map_err(|message| fail(&message))?
                    .get(start.parameter as usize)
                    .ok_or_else(|| {
                        fail("formal loan parameter is outside its original lambda header")
                    })?;
                (
                    parameter.mode,
                    parameter.pattern,
                    super::effect_identity::InvocationContext {
                        owner: start.owner,
                        invocation: call.parent_named,
                        closure: Some(call.closure),
                        closure_invocation: Some(call.id),
                        ..call.entry.caller_context
                    },
                )
            }
            _ => return Err(fail("formal loan has no original callable owner")),
        };
        if mode
            != if start.retained {
                ril_syntax::ast::ParameterMode::SharedMut
            } else {
                ril_syntax::ast::ParameterMode::Mut
            }
        {
            return Err(fail(
                "formal loan parameter or lexical owner differs from the declaration",
            ));
        }
        let expected = formal
            .expected(start.activation, pattern, context, &mut work)
            .map_err(|message| fail(&message))?;
        charge(&mut work, expected.len()).map_err(|message| fail(&message))?;
        if start.bindings != expected {
            return Err(fail(
                "formal loan binding coverage differs from its original receiver parameter",
            ));
        }
    }
    let mut ended = BTreeMap::new();
    for end in &facts.invocation_loan_ends {
        let fail = |message: &str| (end.span, Some(end.cause), message.to_owned());
        charge(&mut work, 1 + end.loans.len()).map_err(|message| fail(&message))?;
        if end.loans.is_empty() || !facts.scopes.contains(&end.activation) {
            return Err(fail("invocation loan end has no actual local loans"));
        }
        for (loan, parents) in &end.loans {
            charge(&mut work, parents.len()).map_err(|message| fail(&message))?;
            let start = starts
                .get(loan)
                .ok_or_else(|| fail("invocation loan end has no formal entry"))?;
            if start.activation != end.activation
                || start.owner != end.owner
                || start.named != end.named
                || start.closure != end.closure
                || start.parents != *parents
                || ended.insert(*loan, parents.clone()).is_some()
            {
                return Err(fail(
                    "invocation loan end differs from its exact entry context",
                ));
            }
            if normalize(&[Participant::Loan(*loan)].into(), &ended).is_err() {
                return Err(fail("invocation loan ends form a cycle"));
            }
        }
    }
    for (loan, start) in starts {
        if !ended.contains_key(&loan) {
            return Err((
                start.span,
                Some(start.cause),
                "completed invocation did not end its formal loan".into(),
            ));
        }
    }
    for call in &facts.copy_invocations {
        if call.status != CopyInvocationStatus::Completed {
            continue;
        }
        let parameters = formal
            .named_parameters(call.target, &mut work)
            .map_err(|message| (call.span, None, message))?;
        charge(&mut work, parameters.len()).map_err(|message| (call.span, None, message))?;
        for (index, parameter) in parameters.iter().enumerate() {
            if parameter.mode == ril_syntax::ast::ParameterMode::Read {
                continue;
            }
            if !named_starts.contains_key(&(call.id, index as u32)) {
                return Err((
                    call.span,
                    None,
                    "completed named invocation lacks its unique formal loan entry".into(),
                ));
            }
        }
    }
    for call in &facts.closure_invocations {
        if call.status != CopyInvocationStatus::Completed {
            continue;
        }
        let parameters = formal
            .closure_parameters(call, &mut work)
            .map_err(|message| (call.site, None, message))?;
        charge(&mut work, parameters.len()).map_err(|message| (call.site, None, message))?;
        for (index, parameter) in parameters.iter().enumerate() {
            if parameter.mode == ril_syntax::ast::ParameterMode::Read {
                continue;
            }
            if !closure_starts.contains_key(&(call.id, index as u32)) {
                return Err((
                    call.site,
                    None,
                    "completed closure invocation lacks its unique formal loan entry".into(),
                ));
            }
        }
    }
    Ok(())
}

#[derive(Debug, Clone)]
pub struct InvocationLoanEnd {
    pub activation: ScopeId,
    pub owner: Option<CallableOwner>,
    pub named: Option<InstanceId>,
    pub closure: Option<ClosureInvocationId>,
    pub loans: BTreeMap<LoanId, BTreeSet<Participant>>,
    pub cause: CauseId,
    pub span: Span,
}

/// Only explicitly ended loans are replaced. Unknown or still-active loans
/// remain independent participants; malformed cycles are never erased.
pub fn normalize(
    participants: &BTreeSet<Participant>,
    ended: &BTreeMap<LoanId, BTreeSet<Participant>>,
) -> Result<BTreeSet<Participant>, LoanId> {
    fn visit(
        participant: Participant,
        ended: &BTreeMap<LoanId, BTreeSet<Participant>>,
        active: &mut BTreeSet<LoanId>,
        output: &mut BTreeSet<Participant>,
    ) -> Result<(), LoanId> {
        if let Participant::Loan(loan) = participant
            && let Some(parents) = ended.get(&loan)
        {
            if !active.insert(loan) {
                return Err(loan);
            }
            for parent in parents {
                visit(*parent, ended, active, output)?;
            }
            active.remove(&loan);
        } else {
            output.insert(participant);
        }
        Ok(())
    }
    let mut output = BTreeSet::new();
    for participant in participants {
        visit(*participant, ended, &mut BTreeSet::new(), &mut output)?;
    }
    Ok(output)
}

pub(crate) fn normalize_value(value: &mut Value, ended: &BTreeMap<LoanId, BTreeSet<Participant>>) {
    if let Ok(participants) = normalize(&value.participants, ended) {
        value.participants = participants;
    }
    for nested in [
        &mut value.result_payload,
        &mut value.result_success,
        &mut value.result_error,
        &mut value.option_payload,
        &mut value.variant_payload,
    ]
    .into_iter()
    .flatten()
    .chain(value.variant_witnesses.values_mut())
    {
        normalize_value(nested, ended);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::facts::RootId;
    #[test]
    fn ending_one_reborrow_preserves_active_parent_and_unrelated_ambient_roots() {
        let ended = [(LoanId(2), [Participant::Loan(LoanId(1))].into())].into();
        let input = [
            Participant::Loan(LoanId(2)),
            Participant::Root(RootId(7)),
            Participant::Loan(LoanId(3)),
        ]
        .into();
        assert_eq!(
            normalize(&input, &ended).unwrap(),
            [
                Participant::Loan(LoanId(1)),
                Participant::Root(RootId(7)),
                Participant::Loan(LoanId(3))
            ]
            .into()
        );
        let mut ended = ended;
        ended.insert(LoanId(1), [Participant::Root(RootId(4))].into());
        assert_eq!(
            normalize(&input, &ended).unwrap(),
            [
                Participant::Root(RootId(4)),
                Participant::Root(RootId(7)),
                Participant::Loan(LoanId(3))
            ]
            .into()
        );
        ended.insert(LoanId(1), [Participant::Loan(LoanId(2))].into());
        assert!(normalize(&input, &ended).is_err());
    }

    #[test]
    fn nested_transport_changes_only_ended_participants_not_authority_or_duties() {
        use crate::sema::{
            copy_contract::CopyBoundaryId,
            facts::{NodeId, Permission},
            model::Ty,
        };
        let mut source = Value::scalar(Ty::Unknown, None, CauseId(9));
        source.origins = Origins::one(NodeId(8));
        source.participants = [Participant::Loan(LoanId(2))].into();
        source.permission = Permission::Write;
        source.temporary = true;
        source.scoped.insert(7);
        source.results.insert(11);
        source.must_results.insert(11);
        source.pending_copies.insert(CopyBoundaryId(4));
        let mut outer = source.clone();
        outer.option_payload = Some(Box::new(source.clone()));
        outer.result_error = Some(Box::new(source.clone()));
        outer
            .variant_witnesses
            .insert("Item".into(), Box::new(source.clone()));
        let mut expected = outer.clone();
        let parent: BTreeSet<Participant> = [Participant::Loan(LoanId(1))].into();
        expected.participants = parent.clone();
        expected.option_payload.as_mut().unwrap().participants = parent.clone();
        expected.result_error.as_mut().unwrap().participants = parent.clone();
        expected
            .variant_witnesses
            .get_mut("Item")
            .unwrap()
            .participants = parent.clone();
        normalize_value(&mut outer, &[(LoanId(2), parent)].into());
        assert_eq!(outer, expected);
    }
}
