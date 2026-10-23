//! Primitive identity follows original reads, independently of the selected
//! callable interface. This query publishes no Source or value authority.
use super::*;
use crate::hir::nodes::{ExprKind as HirExpr, PatternKind as HirPattern, StmtKind as HirStmt};
use crate::sema::application_effect::ActivationKind;
use crate::sema::facts::{CauseKind, Participant, Permission, Publication, RootId};
use ril_compiler_core::diagnostic::CauseId;
use ril_syntax::ast::BindingMode;

fn charge(work: &mut usize, units: usize) -> Check {
    match work.checked_sub(units) {
        Some(remaining) => {
            *work = remaining;
            Ok(())
        }
        None => {
            *work = 0;
            Err("primitive identity read exceeds its shared work bound".into())
        }
    }
}

/// All edges strictly precede the read they explain. The fixed depth bound
/// also applies when malformed facts attempt to give a cycle another token.
pub(super) fn authenticate<'a>(
    sources: &OriginalOperandSources<'a>,
    mut observation: usize,
    identity: &str,
    work: &mut usize,
) -> Check<PrimitiveRead<'a>> {
    let replay = &sources.replay;
    let facts = replay.facts;
    let hir = facts
        .semantic_hir
        .as_deref()
        .ok_or("primitive identity has no HIR")?;
    let lexical = replay
        .lexical
        .as_ref()
        .ok_or("primitive identity has no lexical index")?;
    let mut reads: Vec<(usize, usize, RootId)> = Vec::new();
    for _ in 0..64 {
        charge(work, 13 + identity.len().div_ceil(32))?;
        let fact = facts
            .expressions
            .get(observation)
            .ok_or("primitive identity has no physical value")?;
        let record = facts
            .evaluations
            .get(observation)
            .ok_or("primitive identity has no evaluation")?;
        let source = fact
            .source_id
            .ok_or("primitive identity has no original HIR")?;
        let occurrence = record
            .identity
            .ok_or("primitive identity has no original occurrence")?;
        let entered = facts
            .activations
            .get(occurrence.activation.0 as usize)
            .ok_or("primitive identity has no actual activation")?;
        let original = hir
            .expression(source)
            .ok_or("primitive identity source is outside HIR")?;
        let coordinates = fact.value.packet().birth_coordinates();
        require(
            record.id.0 as usize == observation
                && occurrence.source == source
                && fact.allocation_epoch == record.allocation_epoch
                && record.allocation_epoch <= facts.allocation_history.len()
                && entered.id == occurrence.activation
                && entered.source == Some(source)
                && entered.result == Some(record.id)
                && entered.kind == ActivationKind::Expression
                && entered.context == record.context
                && entered.scope == record.scope
                && coordinates.observation == Some(observation)
                && coordinates.identity == Some(occurrence)
                && coordinates.context == Some(record.context)
                && coordinates.allocation_epoch == record.allocation_epoch
                && coordinates.environment.is_some()
                && coordinates.environment == record.environment
                && fact.value.packet().current_epoch() == record.allocation_epoch,
            "primitive identity borrowed another physical observation, environment or epoch",
        )?;
        require(
            replay.observations.row(observation, work)?.context == record.context,
            "primitive identity has another actual caller context",
        )?;
        let environment = graph_sources::schema_work(work, |budget| {
            facts.source_types.environment(
                record
                    .environment
                    .ok_or(crate::sema::source_types::SourceTypesError::MissingNode)?,
                budget,
            )
        })?;
        require(
            !environment.is_poisoned(),
            "primitive identity has a poisoned birth environment",
        )?;
        charge(work, fact.value.callables.len())?;
        let [Callable::Builtin(target)] = fact.value.callables.as_slice() else {
            return Err("primitive identity is not a unique actual primitive target".into());
        };
        charge(work, target.len().div_ceil(32))?;
        require(
            target == identity,
            "primitive identity changed its actual callable target",
        )?;
        require(
            matches!(original.kind, HirExpr::Name(_) | HirExpr::Path(_)),
            "primitive identity has no supported original read role",
        )?;
        if fact.value.sources.is_empty() {
            replay.builtin_source_names(work)?.actual_name(
                record.context.owner,
                source,
                identity,
                work,
            )?;
            charge(work, 2)?;
            require(
                facts.explanations.kinds.get(fact.value.cause.0 as usize)
                    == Some(&CauseKind::Source)
                    && facts
                        .explanations
                        .causes
                        .get(fact.value.cause.0 as usize)
                        .is_some_and(|cause| {
                            cause.id == fact.value.cause && cause.parents.is_empty()
                        }),
                "primitive declaration lost its original source cause",
            )?;
            let declaration = fact.value.value();
            let mut value =
                crate::sema::evaluated::transport_value_at(declaration, &[], 0, 0, work)
                    .map_err(|error| error.to_string())?;
            let mut epoch = record.allocation_epoch;
            for (read, binding, root) in reads.into_iter().rev() {
                charge(work, 2)?;
                let actual = facts
                    .expressions
                    .get(read)
                    .ok_or("primitive alias read disappeared")?;
                let target_epoch = actual.allocation_epoch;
                value = crate::sema::evaluated::transport_value_at(
                    &value,
                    &facts.allocation_history,
                    epoch,
                    target_epoch,
                    work,
                )
                .map_err(|error| error.to_string())?;
                immutable_name_read(&mut value, binding, root, work)?;
                value = replay_immutable_joins(facts, value, actual.value.cause, work)?;
                if !crate::sema::evaluated::same_birth_value(&value, actual.value.value(), work)
                    .map_err(|error| error.to_string())?
                {
                    let field = crate::sema::evaluated::value_difference(
                        &value,
                        actual.value.value(),
                        work,
                    )
                    .map_err(|error| error.to_string())?;
                    charge(work, 4)?;
                    return Err(format!(
                        "primitive alias changed its complete original value or receiving duties: {field} (binding {binding}, observation {read})"
                    ));
                }
                epoch = target_epoch;
            }
            return Ok(PrimitiveRead { declaration, value });
        }
        require(
            matches!(original.kind, HirExpr::Name(_)),
            "primitive alias has no original local Name read",
        )?;
        let pattern = lexical
            .lookup(source, work)
            .map_err(|error| error.to_string())?;
        charge(work, fact.value.sources.len())?;
        require(
            fact.value.sources.len() == 1,
            "primitive alias has no unique actual binding",
        )?;
        let id = *fact
            .value
            .sources
            .first()
            .ok_or("primitive alias has no binding")?;
        let binding = facts
            .bindings
            .get(id)
            .ok_or("primitive alias binding is absent")?;
        require(
            !binding.parameter
                && binding.declaration.is_none()
                && binding.mode == BindingMode::Let
                && binding.cell.is_none()
                && binding.pattern.is_some()
                && binding.pattern == pattern,
            "primitive alias is not its original immutable local binding",
        )?;
        charge(
            work,
            2 + replay.storage_bindings.len().checked_ilog2().unwrap_or(0) as usize,
        )?;
        let row = replay
            .storage_bindings
            .get(&id)
            .copied()
            .ok_or("primitive alias has no original initializer receipt")?;
        let owner = row
            .context
            .owner
            .ok_or("primitive alias initializer has no lexical owner")?;
        let declaration = sources.sites.binding_site(owner, row.declaration, work)?;
        let syntax = declaration.binding;
        let statement = hir
            .statement(declaration.statement)
            .ok_or("primitive alias declaration is absent")?;
        let introducer = hir
            .pattern(row.declaration)
            .ok_or("primitive alias introducer is absent")?;
        charge(work, binding.name.len().div_ceil(32))?;
        require(
            matches!(&statement.kind, HirStmt::Binding { pattern, mode, value, ty, .. }
                if *pattern == row.declaration && *mode == BindingMode::Let
                    && Some(*value) == syntax.value.hir_id
                    && *ty == syntax.ty.as_ref().and_then(|ty| ty.hir_id))
                && matches!(&introducer.kind, HirPattern::Name(name) if name == &binding.name)
                && introducer.info.owner == statement.info.owner
                && syntax.pattern.hir_id == Some(row.declaration)
                && syntax.mode == binding.mode
                && !syntax.is_meta
                && syntax.fallback.is_none()
                && syntax.ty.is_none()
                && row.binding == id
                && row.activation == binding.owner
                && row.context == binding.context
                && row.declared == syntax.ty.is_some()
                && binding.pattern == Some(row.declaration)
                && row.path.as_ref().is_some_and(Vec::is_empty),
            "primitive alias changed its original declaration or binding projection",
        )?;
        let root =
            RootId(u32::try_from(id).map_err(|_| "primitive alias root is outside its arena")?);
        require(
            binding.root == root,
            "primitive alias borrowed another receiving root",
        )?;
        // A captured/assigned receiver needs its own historical value transfer.
        // Neither a final BindingInfo.value nor a same-shaped Source supplies it.
        require(
            record.context == row.context && record.scope == row.activation,
            "primitive alias read has no same-activation historical binding receipt",
        )?;
        charge(work, 4)?;
        let initial = facts
            .expressions
            .get(row.initializer.expression)
            .ok_or("primitive alias initializer is absent")?;
        let birth = facts
            .evaluations
            .get(row.initializer.expression)
            .ok_or("primitive alias initializer has no actual occurrence")?;
        require(
            row.initializer.expression < observation
                && binding.birth.is_some()
                && birth.identity == binding.birth
                && birth.id.0 as usize == row.initializer.expression
                && birth.context == row.context
                && birth.scope == row.activation
                && birth.allocation_epoch == row.initializer.allocation_epoch
                && initial.allocation_epoch == birth.allocation_epoch
                && birth.allocation_epoch <= record.allocation_epoch
                && initial.source_id == syntax.value.hir_id
                && birth
                    .identity
                    .is_some_and(|id| Some(id.source) == syntax.value.hir_id)
                && hir
                    .expression(
                        birth
                            .identity
                            .ok_or("primitive alias initializer lost HIR")?
                            .source,
                    )
                    .is_some_and(|node| node.info.owner == statement.info.owner),
            "primitive alias borrowed another initializer occurrence, context or epoch",
        )?;
        // Charge the new element and any relocation of the existing prefix
        // before the vector can allocate. This is temporary query state only.
        charge(work, reads.len() + 1)?;
        reads.push((observation, id, root));
        observation = row.initializer.expression;
    }
    Err("primitive identity read chain exceeds its depth bound".into())
}

/// Repeated execution may join an unchanged immutable primitive binding. Its
/// exact causal history is replayed rather than erased for descriptor equality.
fn replay_immutable_joins(
    facts: &SemanticFacts,
    base: Value,
    target: CauseId,
    work: &mut usize,
) -> Check<Value> {
    if base.cause == target {
        return Ok(base);
    }
    require(
        base.origins.nodes.is_empty()
            && base.origins.choices.is_empty()
            && base.result_payload.is_none()
            && base.result_success.is_none()
            && base.result_error.is_none()
            && base.option_payload.is_none()
            && base.variant_payload.is_none()
            && base.variant_witnesses.is_empty(),
        "primitive binding join has a reference-bearing payload requiring its original branch coordinate",
    )?;
    charge(work, 1)?;
    let mut pending = vec![(target, false, 0usize)];
    let mut values = BTreeMap::<u32, Value>::new();
    while let Some((id, ready, depth)) = pending.pop() {
        charge(work, 2 + values.len().checked_ilog2().unwrap_or(0) as usize)?;
        require(
            depth < 128,
            "primitive binding join exceeds its causal depth bound",
        )?;
        if values.contains_key(&id.0) {
            continue;
        }
        if id == base.cause {
            let value = crate::sema::evaluated::transport_value_at(&base, &[], 0, 0, work)
                .map_err(|error| error.to_string())?;
            charge(work, 1 + values.len().checked_ilog2().unwrap_or(0) as usize)?;
            values.insert(id.0, value);
            continue;
        }
        charge(work, 3)?;
        let node = facts
            .explanations
            .causes
            .get(id.0 as usize)
            .ok_or("primitive binding join cause is absent")?;
        require(
            node.id == id
                && facts.explanations.kinds.get(id.0 as usize) == Some(&CauseKind::BranchJoin)
                && node.parents.len() == 2
                && node.parents.iter().all(|parent| parent.0 < id.0),
            "primitive binding join is not an original acyclic two-parent join",
        )?;
        if !ready {
            charge(work, pending.len() + 3)?;
            pending.reserve(3);
            pending.push((id, true, depth));
            for parent in node.parents.iter().rev() {
                pending.push((*parent, false, depth + 1));
            }
            continue;
        }
        charge(
            work,
            3 * (1 + values.len().checked_ilog2().unwrap_or(0) as usize),
        )?;
        let left = values
            .get(&node.parents[0].0)
            .ok_or("primitive binding join lost its first actual parent")?;
        let right = values
            .get(&node.parents[1].0)
            .ok_or("primitive binding join lost its second actual parent")?;
        for _ in 0..3 {
            crate::sema::evaluated::charge_value_export(left, work)
                .map_err(|error| error.to_string())?;
            crate::sema::evaluated::charge_value_export(right, work)
                .map_err(|error| error.to_string())?;
        }
        // Both complete parents descend from the same immutable primitive.
        // Empty origin/payload graphs make the branch coordinate unobservable;
        // no ChoiceId or physical evaluation is minted or retained here.
        let joined = left.join(right, 0, id);
        values.insert(id.0, joined);
    }
    charge(work, 1 + values.len().checked_ilog2().unwrap_or(0) as usize)?;
    values
        .remove(&target.0)
        .ok_or_else(|| "primitive binding join has no reconstructed result".into())
}

fn immutable_name_read(value: &mut Value, binding: usize, root: RootId, work: &mut usize) -> Check {
    charge(work, 3)?;
    value.permission = Permission::Read;
    value.publication = Publication::Immutable;
    value.construction = false;
    value.marker = false;
    value.retention_result = false;
    value.unsuffixed_numeric = false;
    value.static_coordinate = None;
    value.sources.clear();
    value.sources.insert(binding);
    if value.participants.is_empty() {
        value.participants.insert(Participant::Root(root));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckOptions, Session};
    use ril_compiler_core::ids::PatternId;

    fn fixture(layout: &str) -> SemanticFacts {
        let source = ril_test::case_bytes(
            "tests/regressions/closed-standard-data.ril::primitive-alias-read-chain",
        );
        let verified = Session::with_options(
            source.to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{layout}: {error:?}"));
        crate::lower::lower_core(&verified).unwrap();
        verified.facts().clone()
    }

    fn aliases(facts: &SemanticFacts) -> Vec<usize> {
        facts.copy_call_events.iter().filter_map(|event| event.callee_expression)
            .filter(|&token| {
                let fact = &facts.expressions[token];
                fact.value.sources.first().and_then(|id| facts.bindings.get(*id))
                    .is_some_and(|binding| binding.name == "alias")
                    && matches!(fact.value.callables.as_slice(), [Callable::Builtin(name)] if name == "Io::read_all")
            }).collect()
    }

    fn query(facts: &SemanticFacts, token: usize) -> Check {
        let mut work = 4_000_000;
        let sources = OriginalOperandSources::new_with_work(facts, &mut work)?;
        sources
            .primitive_read(token, "Io::read_all", &mut work)
            .map(|_| ())
    }

    #[test]
    fn primitive_alias_identity_keeps_original_occurrences_and_callable_targets() {
        for layout in ["pointer32", "pointer64"] {
            let facts = fixture(layout);
            let tokens = aliases(&facts);
            let &token = tokens
                .first()
                .expect("the real application must use its alias");
            let binding = *facts.expressions[token].value.sources.first().unwrap();
            let row = facts
                .binding_sources
                .iter()
                .position(|row| row.binding == binding)
                .unwrap();
            let sibling = tokens
                .iter()
                .copied()
                .find(|&other| {
                    facts.evaluations[other].context != facts.evaluations[token].context
                        && facts.expressions[other].source_id == facts.expressions[token].source_id
                })
                .expect("the same HIR alias must be called in two actual activations");
            let sibling_binding = *facts.expressions[sibling].value.sources.first().unwrap();
            let sibling_row = facts
                .binding_sources
                .iter()
                .find(|row| row.binding == sibling_binding)
                .unwrap();
            query(&facts, token).unwrap();
            for mutation in 0..20 {
                let mut changed = facts.clone();
                match mutation {
                    0 => {
                        changed.binding_sources.remove(row);
                    }
                    1 => {
                        changed.binding_sources[row].initializer = sibling_row.initializer;
                    }
                    2 => {
                        changed.bindings[binding].pattern = None;
                    }
                    3 => {
                        changed.binding_sources[row].declaration = PatternId(u32::MAX);
                    }
                    4 => {
                        changed.binding_sources[row].initializer.allocation_epoch += 1;
                    }
                    5 => {
                        changed.binding_sources[row].context = sibling_row.context;
                    }
                    6 => {
                        changed.bindings[binding].birth = changed.bindings[sibling_binding].birth;
                    }
                    7 => {
                        changed.binding_sources[row].initializer.expression = token;
                    }
                    8 => {
                        changed.bindings[binding].mode = BindingMode::Var;
                    }
                    9 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .sources = [sibling_binding].into();
                    }
                    10 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .callables = vec![Callable::Builtin("Io::write_all".into())];
                    }
                    11 => {
                        changed.evaluations[token].environment = None;
                    }
                    12 => {
                        // Even a consistently forged target chain must end at
                        // the original canonical HIR declaration, not its tags.
                        for fact in &mut changed.expressions {
                            if matches!(fact.value.callables.as_slice(), [Callable::Builtin(name)] if name == "Io::read_all")
                            {
                                fact.value.corrupt_value(&mut 4_000_000).unwrap().callables =
                                    vec![Callable::Builtin("Io::write_all".into())];
                            }
                        }
                    }
                    13 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .publication = Publication::Live;
                    }
                    14 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .participants
                            .clear();
                    }
                    15 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .pending_copies
                            .insert(crate::sema::copy_contract::CopyBoundaryId(u32::MAX));
                    }
                    16 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .scoped
                            .insert(binding);
                    }
                    17 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .marker = true;
                    }
                    18 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .permission = Permission::Write;
                    }
                    19 => {
                        changed.expressions[token]
                            .value
                            .corrupt_value(&mut 4_000_000)
                            .unwrap()
                            .result_payload = Some(Box::new(Value::scalar(
                            Ty::Unit,
                            None,
                            facts.expressions[token].value.cause,
                        )));
                    }
                    _ => unreachable!(),
                }
                let mut work = 4_000_000;
                let rejected = OriginalOperandSources::new_with_work(&changed, &mut work)
                    .and_then(|sources| {
                        sources.primitive_read(
                            token,
                            if mutation == 12 {
                                "Io::write_all"
                            } else {
                                "Io::read_all"
                            },
                            &mut work,
                        )
                    })
                    .is_err();
                assert!(
                    rejected,
                    "{layout}: primitive alias mutation {mutation} was accepted"
                );
            }
            let mut work = 4_000_000;
            let sources = OriginalOperandSources::new_with_work(&facts, &mut work).unwrap();
            assert!(
                sources
                    .primitive_read(token, "Io::write_all", &mut work)
                    .is_err()
            );
        }
    }

    #[test]
    fn primitive_alias_identity_uses_one_exact_work_allowance() {
        let facts = fixture("pointer64");
        let token = aliases(&facts)[0];
        let mut work = 4_000_000;
        let sources = OriginalOperandSources::new_with_work(&facts, &mut work).unwrap();
        let before = work;
        sources
            .primitive_read(token, "Io::read_all", &mut work)
            .unwrap();
        let spent = before - work;
        assert!(spent > 0);
        let mut exact = spent;
        sources
            .primitive_read(token, "Io::read_all", &mut exact)
            .unwrap();
        assert_eq!(exact, 0);
        for mut short in [0, spent - 1] {
            assert!(
                sources
                    .primitive_read(token, "Io::read_all", &mut short)
                    .is_err()
            );
        }
        query(&facts, token).unwrap();
    }

    #[test]
    fn primitive_alias_joins_replay_the_original_cause_dag_with_shared_work() {
        let mut facts = fixture("pointer64");
        let token = aliases(&facts)[0];
        let mut work = 4_000_000;
        let base = OriginalOperandSources::new_with_work(&facts, &mut work)
            .unwrap()
            .primitive_read(token, "Io::read_all", &mut work)
            .unwrap()
            .value;
        let foreign =
            facts
                .explanations
                .add(CauseKind::Source, None, "an unrelated primitive source", []);
        let mut root = base.cause;
        for _ in 0..32 {
            root = facts.explanations.add(
                CauseKind::BranchJoin,
                None,
                "a generated shared DAG model for repeated immutable binding state",
                [root, root],
            );
        }
        let mut work = 1_000_000;
        let joined = replay_immutable_joins(&facts, base.clone(), root, &mut work).unwrap();
        assert_eq!(joined.cause, root);
        let used = 1_000_000 - work;
        assert!(
            used > 0 && used < 50_000,
            "a shared cause DAG must not unfold its paths: {used}"
        );
        let mut exact = used;
        let expected = replay_immutable_joins(&facts, base.clone(), root, &mut exact).unwrap();
        assert_eq!(exact, 0);
        assert_eq!(expected, joined);
        for mut short in [0, used - 1] {
            assert!(replay_immutable_joins(&facts, base.clone(), root, &mut short).is_err());
        }
        facts.expressions[token]
            .value
            .corrupt_value(&mut 4_000_000)
            .unwrap()
            .cause = root;
        query(&facts, token).unwrap();
        for mutation in 0..6 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.explanations.kinds[root.0 as usize] = CauseKind::Projection,
                1 => changed.explanations.causes[root.0 as usize].parents[0] = foreign,
                2 => changed.explanations.causes[root.0 as usize].parents[0] = root,
                3 => {
                    changed.explanations.causes[root.0 as usize].parents.pop();
                }
                4 => changed.explanations.causes[root.0 as usize].id = foreign,
                5 => changed.explanations.causes[root.0 as usize].parents[0] = CauseId(u32::MAX),
                _ => unreachable!(),
            }
            assert!(
                query(&changed, token).is_err(),
                "forged immutable join mutation {mutation} was accepted"
            );
        }
    }
}
