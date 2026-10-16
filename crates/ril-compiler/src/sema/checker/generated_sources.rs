//! A generated body is admitted through its actual canonical adapter creation,
//! not through a synthetic file, a reserved name, or a successful later call.
use super::*;
use crate::sema::{effect_identity::ArgumentKey, generated_sources::GeneratedSource};
#[path = "../generated_source_syntax.rs"]
mod syntax;
pub(super) use syntax::iterator_lambda as iterator_syntax;

type Failure = (Span, Option<CauseId>, String);
fn require(condition: bool, message: &str) -> Result<(), String> {
    condition.then_some(()).ok_or_else(|| message.into())
}

/// A read-only captured binding may pass through later branch joins. Those
/// joins change its explanation, but may not introduce a different operand.
fn same_capture_cause(facts: &SemanticFacts, actual: CauseId, original: CauseId) -> bool {
    if facts
        .explanations
        .causes
        .get(original.0 as usize)
        .map(|cause| cause.id)
        != Some(original)
    {
        return false;
    }
    let mut pending = vec![actual];
    let mut seen = BTreeSet::new();
    let mut work = 4096usize;
    while let Some(cause) = pending.pop() {
        if cause == original || !seen.insert(cause.0) {
            continue;
        }
        let Some(remaining) = work.checked_sub(1) else {
            return false;
        };
        work = remaining;
        let Some(entry) = facts.explanations.causes.get(cause.0 as usize) else {
            return false;
        };
        // Charge all edges before scanning or adding them to the worklist.
        // Counting only distinct nodes leaves a very wide join unbounded.
        let Some(remaining) = work.checked_sub(entry.parents.len()) else {
            return false;
        };
        work = remaining;
        if entry.id != cause
            || facts.explanations.kinds.get(cause.0 as usize) != Some(&CauseKind::BranchJoin)
            || entry.parents.is_empty()
            || entry.parents.iter().any(|parent| parent.0 >= cause.0)
        {
            return false;
        }
        pending.extend(entry.parents.iter().copied());
    }
    true
}

fn same_capture_origins(
    facts: &SemanticFacts,
    original: &Origins,
    actual: &Origins,
    epoch: usize,
) -> bool {
    fn admit(origins: &Origins, work: &mut usize) -> Option<usize> {
        *work = work.checked_sub(origins.nodes.len())?;
        *work = work.checked_sub(origins.choices.len())?;
        let mut sets = 1usize;
        for branches in origins.choices.values() {
            *work = work.checked_sub(branches.len())?;
            sets = sets.checked_add(branches.len())?;
            for branch in branches {
                *work = work.checked_sub(branch.len())?;
            }
        }
        Some(sets)
    }
    let Some(moves) = facts.allocation_history.get(epoch..) else {
        return false;
    };
    let mut work = 4096usize;
    let Some(sets) = admit(original, &mut work) else {
        return false;
    };
    if admit(actual, &mut work).is_none() {
        return false;
    }
    // Each remap visits the root set and every correlated alternative. Admit
    // this work and both finite structures before cloning either source.
    if moves
        .len()
        .checked_mul(sets)
        .and_then(|cost| work.checked_sub(cost))
        .is_none()
    {
        return false;
    }
    let mut transported = original.clone();
    for &(recent, older) in moves {
        transported.remap(recent, older);
    }
    &transported == actual
}

fn key(facts: &SemanticFacts, syntax: &TypeExpr) -> Result<ArgumentKey, String> {
    let layout = facts
        .target_layout
        .ok_or("generated source has no frozen layout")?;
    let syntax = normalize_closed_source_syntax(syntax, &facts.external_type_declarations, layout)
        .ok_or("generated source schema lacks its complete closed declaration")?;
    let key = crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())
        .ok_or("generated source schema exceeds its syntax budget")?;
    crate::sema::source_reception::complete(&key, &mut 4096)
        .ok_or("generated source schema is incomplete")?;
    Ok(key)
}

fn adapter_name(adapter: iter::AdapterKind) -> &'static str {
    match adapter {
        iter::AdapterKind::Indexed => "Iter::indexed",
        iter::AdapterKind::Map => "Iter::map",
        iter::AdapterKind::Filter => "Iter::filter",
        iter::AdapterKind::Take => "Iter::take",
    }
}

fn source_parts(key: &ArgumentKey) -> Result<(ArgumentKey, ArgumentKey), String> {
    let ArgumentKey::Record { fields, row: None } = key else {
        return Err("generated adapter input has no complete source record".into());
    };
    let (_, mutable, step) = fields
        .iter()
        .find(|(name, _, _)| name == "step")
        .ok_or("generated adapter input lost its original step field")?;
    let ArgumentKey::Callable {
        parameters, result, ..
    } = step
    else {
        return Err("generated adapter original step is not a complete callable".into());
    };
    let [(ParameterMode::Read, input)] = parameters.as_slice() else {
        return Err("generated adapter step requires its original readonly state parameter".into());
    };
    let ArgumentKey::Name { name, arguments } = result.as_ref() else {
        return Err("generated adapter step lost its nominal result source".into());
    };
    require(
        !mutable && name == "Iter::Step" && arguments.len() == 2 && input == &arguments[0],
        "generated adapter state and successor source identities differ",
    )?;
    Ok((arguments[0].clone(), arguments[1].clone()))
}

/// Small ordinary scalar inference for an unannotated map result. This never
/// reifies Array/Fn, evaluates a branch, or borrows an actual input payload.
fn scalar_body(
    body: &Expr,
    name: &str,
    input: &ArgumentKey,
    work: &mut usize,
    depth: usize,
) -> Option<ArgumentKey> {
    *work = work.checked_sub(1)?;
    if depth >= 64 {
        return None;
    }
    let named = |name: &str| ArgumentKey::Name {
        name: name.into(),
        arguments: vec![],
    };
    match &body.kind {
        ExprKind::Name(actual) if actual == name => Some(input.clone()),
        ExprKind::Literal(Literal::Integer(_)) => Some(named("int")),
        ExprKind::Literal(Literal::Bool(_)) => Some(named("bool")),
        ExprKind::Literal(Literal::String(_) | Literal::RawString(_)) => Some(named("str")),
        ExprKind::Binary {
            left,
            operator,
            right,
        } if matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") => {
            let left = scalar_body(left, name, input, work, depth + 1)?;
            let right = scalar_body(right, name, input, work, depth + 1)?;
            (left == named("int") && right == left).then_some(left)
        }
        ExprKind::Block(block) if block.where_items.is_empty() && block.statements.len() == 1 => {
            let StmtKind::Expr {
                expression,
                terminated: false,
            } = &block.statements[0].kind
            else {
                return None;
            };
            scalar_body(expression, name, input, work, depth + 1)
        }
        _ => None,
    }
}

fn map_result(
    facts: &SemanticFacts,
    source: &GeneratedSource,
    actual: &Expr,
    input: &ArgumentKey,
) -> Result<ArgumentKey, String> {
    if let ExprKind::Lambda {
        parameters,
        return_type,
        body,
        ..
    } = &actual.kind
    {
        let [parameter] = parameters.as_slice() else {
            return Err("generated map callback arity differs".into());
        };
        require(
            parameter.mode == ParameterMode::Read,
            "generated map callback is not readonly",
        )?;
        if let Some(syntax) = &parameter.ty {
            require(
                key(facts, syntax)? == *input,
                "generated map callback original item source differs",
            )?;
        }
        if let Some(result) = return_type {
            return key(facts, result);
        }
        let PatternKind::Name(name) = &parameter.pattern.kind else {
            return Err("generated map inferred result needs a real simple parameter".into());
        };
        return scalar_body(body, name, input, &mut 4096, 0).ok_or_else(|| {
            "generated map result requires its complete original return source".into()
        });
    }
    let callback = crate::sema::record_bound_validation::original_operand_source_key(
        facts,
        source.origin_event,
        1,
    )?;
    let ArgumentKey::Callable {
        parameters, result, ..
    } = callback
    else {
        return Err("generated map callback lost its original callable source".into());
    };
    let [(ParameterMode::Read, parameter)] = parameters.as_slice() else {
        return Err("generated map callback source modes differ".into());
    };
    require(
        parameter == input,
        "generated map callback item source differs",
    )?;
    Ok(*result)
}

fn validate_inner(facts: &SemanticFacts) -> Result<(), String> {
    require(
        facts.generated_sources.len() <= 65_536 && facts.iter_steps.len() <= 65_536,
        "generated source arena exceeds its validation budget",
    )?;
    let creator = |event: &crate::sema::copy_contract::CopyCallEvent| {
        let value = facts.expressions.get(event.callee_expression?)?;
        let [Callable::Builtin(name)] = value.value.callables.as_slice() else {
            return None;
        };
        matches!(
            name.as_str(),
            "Iter::indexed" | "Iter::map" | "Iter::filter" | "Iter::take"
        )
        .then_some(())
    };
    if facts.generated_sources.is_empty()
        && facts.iter_steps.is_empty()
        && !facts
            .copy_call_events
            .iter()
            .any(|event| creator(event).is_some())
    {
        return Ok(());
    }
    // The normal result of the genuine creation event, rather than either
    // mutable generated arena, supplies the reverse coverage obligation.
    for event in facts
        .copy_call_events
        .iter()
        .filter(|event| creator(event).is_some())
    {
        let index = event
            .result_expression
            .ok_or("generated adapter creation lost its actual root observation")?;
        let result = facts
            .expressions
            .get(index)
            .ok_or("generated adapter creation root is absent")?;
        if result.value.ty != Ty::Never {
            require(
                facts
                    .generated_sources
                    .iter()
                    .any(|source| source.origin_event == event.id),
                "normal adapter creation lost every generated source receipt",
            )?;
        }
    }
    require(
        facts.generated_sources.len() == facts.iter_steps.len(),
        "generated iterator source receipt was deleted or duplicated",
    )?;
    let coordinates = crate::sema::record_bound_validation::ordinary_source_coordinates(facts)?;
    let ordinary_lambdas =
        crate::sema::record_bound_validation::ordinary_lambda_coordinates(facts)?;
    let mut closures = BTreeSet::new();
    let mut sites = BTreeSet::new();
    for (index, source) in facts.generated_sources.iter().enumerate() {
        require(
            source.id.0 as usize == index
                && closures.insert(source.closure)
                && sites.insert(source.site),
            "generated source identity, closure or site is duplicated",
        )?;
        let event = facts
            .copy_call_events
            .get(source.origin_event.0 as usize)
            .filter(|event| event.id == source.origin_event)
            .ok_or("generated source lost its true creation event")?;
        let matches: Vec<_> = coordinates
            .iter()
            .filter(|(owner, expr)| {
                Some(*owner) == source.origin_context.owner && expr.span == event.span
            })
            .collect();
        let [(_, origin)] = matches.as_slice() else {
            return Err("generated source creation has no unique genuine adapter Call".into());
        };
        let ExprKind::Call { callee, arguments } = &origin.kind else {
            return Err("generated source creation is not a Call".into());
        };
        let actual_name = match &callee.kind {
            ExprKind::Name(name) => name.clone(),
            ExprKind::Path(path) => path.join("::"),
            _ => {
                return Err("generated source requires its original canonical adapter name".into());
            }
        };
        require(
            actual_name == adapter_name(source.adapter)
                && event.target.is_none()
                && event.owner == source.origin_context.owner
                && event.parent == source.origin_context.invocation,
            "generated source changed its real adapter recipe or creation context",
        )?;
        let callee_index = event
            .callee_expression
            .ok_or("generated source lost its physical callee token")?;
        let callee_value = facts
            .expressions
            .get(callee_index)
            .ok_or("generated source callee token is outside its arena")?;
        require(
            callee_value.span == callee.span
                && callee_value.value.callables == [Callable::Builtin(actual_name.clone())]
                && facts
                    .invocation_expressions
                    .get(callee_index)
                    .is_some_and(|row| {
                        row.expression == callee_index && row.context == source.origin_context
                    }),
            "generated source callee borrowed another occurrence, owner or target",
        )?;
        let count = if source.adapter == iter::AdapterKind::Indexed {
            1
        } else {
            2
        };
        require(
            arguments.len() == count && source.captures.len() == count,
            "generated source capture count differs from its actual adapter operands",
        )?;
        let mut written = BTreeMap::new();
        for argument in arguments {
            let slot = if let Some(label) = &argument.label {
                callee_value
                    .value
                    .signature
                    .as_ref()
                    .and_then(|parameters| {
                        parameters.iter().position(|parameter|
                        matches!(&parameter.pattern.kind, PatternKind::Name(name) if name == label))
                    })
            } else {
                (0..count).find(|slot| !written.contains_key(slot))
            }
            .ok_or("generated source argument has no actual label/position")?;
            require(
                slot < count && written.insert(slot, &argument.value).is_none(),
                "generated source supplies one capture twice",
            )?;
        }
        require(
            written.len() == count && (0..count).all(|slot| written.contains_key(&slot)),
            "generated source arguments do not cover their exact capture slots",
        )?;
        let preparation: Vec<_> = facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id)
            .collect();
        let [preparation] = preparation.as_slice() else {
            return Err("generated source has no unique argument preparation".into());
        };
        require(
            preparation.evaluation_complete
                && preparation.target.is_none()
                && preparation.slots.len() == count
                && preparation.supplied.len() == count,
            "generated source creation operands are incomplete",
        )?;
        let closure = facts
            .closures
            .get(source.closure)
            .ok_or("generated source closure is absent")?;
        let site = facts
            .closure_sites
            .get(source.site.0 as usize)
            .filter(|site| site.id == source.site)
            .ok_or("generated source site is absent")?;
        require(
            closure.site == Some(source.site)
                && Some(site.owner) == source.origin_context.owner
                && closure.creation_invocation == source.origin_context.invocation
                && closure.creation_closure == source.origin_context.closure_invocation
                && closure.creation_default == source.origin_context.default_use
                && closure.writes.is_empty(),
            "generated closure changed its real creation ancestry or readonly recipe",
        )?;
        require(
            !ordinary_lambdas
                .iter()
                .any(|(owner, lambda)| *owner == site.owner && lambda.span == site.span),
            "generated source reused an independent written lambda's lexical identity",
        )?;
        let steps: Vec<_> = facts
            .iter_steps
            .iter()
            .filter(|step| step.closure == source.closure)
            .collect();
        let [step] = steps.as_slice() else {
            return Err("generated source has no unique actual adapter step".into());
        };
        require(
            step.kind == source.adapter
                && step.span == event.span
                && step.identity == format!("ril__iter_step_{}", closure.owner.0),
            "generated source body is attached to another adapter environment",
        )?;
        let ExprKind::Lambda {
            parameters,
            return_type: Some(result),
            body,
            annotations,
        } = &source.syntax.kind
        else {
            return Err("generated source lost its complete lambda schema".into());
        };
        let [parameter] = parameters.as_slice() else {
            return Err("generated source state arity differs".into());
        };
        let state_syntax = parameter
            .ty
            .as_ref()
            .ok_or("generated source has no original state schema")?;
        let TypeKind::Name {
            path,
            arguments: result_arguments,
        } = &result.kind
        else {
            return Err("generated source has no nominal Step result".into());
        };
        require(
            path.join("::") == "Iter::Step"
                && result_arguments.len() == 2
                && annotations.is_empty(),
            "generated source result changed its canonical recipe",
        )?;
        let actual_state = key(facts, state_syntax)?;
        let actual_item = key(facts, &result_arguments[1])?;
        require(
            key(facts, &result_arguments[0])? == actual_state,
            "generated state and result successor source differ",
        )?;
        let input =
            crate::sema::record_bound_validation::original_operand_source_key(facts, event.id, 0)?;
        let (expected_state, expected_item) = if source.adapter == iter::AdapterKind::Indexed {
            let ArgumentKey::Array { element, .. } = input else {
                return Err("generated indexed adapter requires its original array source".into());
            };
            (
                ArgumentKey::Name {
                    name: "int".into(),
                    arguments: vec![],
                },
                *element,
            )
        } else {
            let (state, item) = source_parts(&input)?;
            match source.adapter {
                iter::AdapterKind::Take => (
                    ArgumentKey::Tuple(vec![
                        state,
                        ArgumentKey::Name {
                            name: "int".into(),
                            arguments: vec![],
                        },
                    ]),
                    item,
                ),
                iter::AdapterKind::Filter => (state, item),
                iter::AdapterKind::Map => (state, map_result(facts, source, written[&1], &item)?),
                iter::AdapterKind::Indexed => unreachable!(),
            }
        };
        require(
            actual_state == expected_state && actual_item == expected_item,
            "generated source schema differs from its genuine input/callback source",
        )?;
        let expected = iterator_syntax(
            source.id.0,
            &step.identity,
            state_syntax,
            &result_arguments[1],
            count,
        )
        .ok_or("generated source reconstruction exceeds its budget")?;
        require(
            *source.syntax == expected
                && site.span == source.syntax.span
                && closure.parameters == *parameters
                && closure.body == **body,
            "generated source lambda body/header differs from its canonical recipe",
        )?;
        let capture_ids: BTreeSet<_> = source
            .captures
            .iter()
            .map(|capture| capture.binding)
            .collect();
        require(
            capture_ids == closure.captures,
            "generated closure has a missing or ambient capture",
        )?;
        for (slot, capture) in source.captures.iter().enumerate() {
            require(
                capture.origin_slot as usize == slot
                    && capture.path.is_empty()
                    && closure.lexical.get(&format!("ril__iter_capture_{slot}"))
                        == Some(&capture.binding),
                "generated capture lost its original operand coordinate",
            )?;
            let token = preparation
                .supplied
                .get(&(slot as u32))
                .ok_or("generated capture lost its physical operand token")?;
            let original = facts
                .expressions
                .get(token.expression)
                .ok_or("generated capture operand is absent")?;
            require(
                callee_index < token.expression
                    && original.span == written[&slot].span
                    && token.allocation_epoch <= facts.allocation_history.len()
                    && facts
                        .invocation_expressions
                        .get(token.expression)
                        .is_some_and(|row| {
                            row.expression == token.expression
                                && row.context == source.origin_context
                                && row.argument_of == Some((event.id, slot as u32))
                        }),
                "generated capture operand belongs to another event, context or slot",
            )?;
            let binding = facts
                .bindings
                .get(capture.binding)
                .ok_or("generated capture binding is absent")?;
            require(
                binding.owner == closure.owner
                    && !binding.parameter
                    && binding.name == format!("ril__iter_capture_{slot}")
                    && matches!(binding.mode, BindingMode::Let | BindingMode::View)
                    && binding.value.permission == Permission::Read
                    && binding.cell.is_none()
                    && same_capture_cause(facts, binding.value.cause, original.value.cause)
                    && same_capture_origins(
                        facts,
                        &original.value.origins,
                        &binding.value.origins,
                        token.allocation_epoch,
                    )
                    && binding.value.results == original.value.results
                    && binding.value.source_type_witness == original.value.source_type_witness
                    && binding.value.callables == original.value.callables,
                "generated capture changed its actual operand graph or source identity",
            )?;
        }
        let result_index = event
            .result_expression
            .ok_or("generated source lost its physical creation result")?;
        let result = facts
            .expressions
            .get(result_index)
            .ok_or("generated source creation result is absent")?;
        require(
            result.span == origin.span
                && result.value.ty != Ty::Never
                && result.value.cause == step.cause
                && facts
                    .invocation_expressions
                    .get(result_index)
                    .is_some_and(|row| {
                        row.expression == result_index && row.context == source.origin_context
                    }),
            "generated source receipt is not the actual normal creation result",
        )?;
        let expected_callable = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: source.syntax.span,
            kind: TypeKind::Callable {
                parameters: parameters.clone(),
                result: Some(Box::new(TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: source.syntax.span,
                    kind: TypeKind::Name {
                        path: vec!["Iter".into(), "Step".into()],
                        arguments: result_arguments.clone(),
                    },
                })),
                annotations: vec![],
            },
        };
        let expected_record = ArgumentKey::Record {
            fields: vec![("step".into(), false, key(facts, &expected_callable)?)],
            row: None,
        };
        let output_witness = result
            .value
            .source_type_witness
            .as_ref()
            .ok_or("generated source result lost its complete original record schema")?;
        require(
            output_witness.validate_closed()
                && key(facts, &output_witness.syntax)? == expected_record,
            "generated source result changed its original callable source coordinates",
        )?;
        require(
            result.value.origins.nodes.iter().any(|node| {
                facts
                    .fields
                    .get(&(*node, Slot::Field("step".into())))
                    .is_some_and(|value| {
                        value.callables.contains(&Callable::Closure(source.closure))
                    })
            }),
            "generated source creation result does not retain this actual step closure",
        )?;
    }
    Ok(())
}

pub(crate) fn validate(facts: &SemanticFacts) -> Result<(), Failure> {
    validate_inner(facts).map_err(|message| {
        let span = facts
            .generated_sources
            .first()
            .and_then(|source| facts.copy_call_events.get(source.origin_event.0 as usize))
            .map(|event| event.span)
            .or_else(|| facts.functions.first().map(|function| function.syntax.span))
            .unwrap_or(Span {
                file: FileId(0),
                start: 0,
                end: 0,
            });
        (span, None, message)
    })
}

pub(crate) fn checked_roots(facts: &SemanticFacts) -> Result<Vec<(CallableOwner, &Expr)>, String> {
    validate_inner(facts)?;
    facts
        .generated_sources
        .iter()
        .map(|source| {
            let owner = source
                .origin_context
                .owner
                .ok_or("generated source has no lexical creation owner")?;
            Ok((owner, source.syntax.as_ref()))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn captured_operand_transport_keeps_every_original_cause_and_exact_node() {
        let mut facts = SemanticFacts::default();
        let original = facts
            .explanations
            .add(CauseKind::Source, None, "operand", []);
        let foreign = facts
            .explanations
            .add(CauseKind::Source, None, "other operand", []);
        let joined = facts.explanations.add(
            CauseKind::BranchJoin,
            None,
            "same captured value",
            [original, original],
        );
        let repeated = facts.explanations.add(
            CauseKind::BranchJoin,
            None,
            "later branch",
            [joined, original],
        );
        assert!(same_capture_cause(&facts, repeated, original));
        let mixed = facts.explanations.add(
            CauseKind::BranchJoin,
            None,
            "foreign alternative",
            [joined, foreign],
        );
        assert!(!same_capture_cause(&facts, mixed, original));
        let cycle = CauseId(facts.explanations.causes.len() as u32);
        facts
            .explanations
            .add(CauseKind::BranchJoin, None, "cycle", [cycle]);
        assert!(!same_capture_cause(&facts, cycle, original));
        facts.allocation_history = vec![(NodeId(2), NodeId(3)), (NodeId(3), NodeId(4))];
        assert!(same_capture_origins(
            &facts,
            &Origins::one(NodeId(2)),
            &Origins::one(NodeId(4)),
            0
        ));
        assert!(!same_capture_origins(
            &facts,
            &Origins::one(NodeId(2)),
            &Origins::one(NodeId(3)),
            0
        ));
        assert!(!same_capture_origins(
            &facts,
            &Origins::one(NodeId(2)),
            &Origins::one(NodeId(4)),
            1
        ));
    }

    #[test]
    fn capture_transport_rejects_wide_causes_and_excessive_graph_work() {
        let mut facts = SemanticFacts::default();
        let original = facts
            .explanations
            .add(CauseKind::Source, None, "operand", []);
        let wide = facts.explanations.add(
            CauseKind::BranchJoin,
            None,
            "wide join",
            vec![original; 4097],
        );
        assert!(!same_capture_cause(&facts, wide, original));
        let huge = Origins {
            nodes: (0..4097).map(NodeId).collect(),
            choices: BTreeMap::new(),
        };
        assert!(!same_capture_origins(&facts, &huge, &huge, 0));
        let mut branched = Origins::one(NodeId(2));
        branched
            .choices
            .insert(0, vec![BTreeSet::from([NodeId(2)]); 32]);
        facts.allocation_history = vec![(NodeId(10), NodeId(11)); 128];
        assert!(!same_capture_origins(&facts, &branched, &branched, 0));
        let small = Origins::one(NodeId(2));
        assert!(same_capture_origins(&facts, &small, &small, 0));
        facts
            .allocation_history
            .resize(4097, (NodeId(10), NodeId(11)));
        assert!(!same_capture_origins(&facts, &small, &small, 0));
    }
}
