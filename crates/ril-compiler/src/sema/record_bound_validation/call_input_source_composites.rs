//! Replay each original product operand in the same physical root occurrence.
use super::*;
use ril_syntax::ast::RecordMember;

impl Replay<'_> {
    pub(super) fn original_copy_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<ArgumentKey>> {
        if let ExprKind::Binary {
            operator,
            left,
            right,
        } = &expression.kind
            && matches!(operator.as_str(), "|>" | "!>")
            && matches!(right.kind, ExprKind::Derive { base: None, .. })
        {
            let root =
                self.original_source_root(expression, value, context, visit.observation, work)?;
            let anchor = self
                .facts
                .evaluations
                .get(root)
                .and_then(|record| record.identity)
                .ok_or("copy publication lost its actual evaluation activation")?
                .activation;
            let source = left
                .hir_id
                .ok_or("copy publication lost its original operand")?;
            let operands = self.observations.range(source, context, 0..root, work)?;
            *work = work
                .checked_sub(operands.len())
                .ok_or("copy publication operand lookup exceeds its work bound")?;
            let mut operands = operands.iter().copied().filter(|index| {
                self.facts.evaluations[*index]
                    .identity
                    .and_then(|id| self.facts.activations.get(id.activation.0 as usize))
                    .is_some_and(|activation| activation.parent == Some(anchor))
            });
            let operand = operands
                .next()
                .ok_or("copy publication has no original input root")?;
            require(
                operands.next().is_none(),
                "copy publication borrowed an ambiguous input root",
            )?;
            let key = self.original_source_key_inner(
                left,
                &self.facts.expressions[operand].value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: visit.depth + 1,
                    observation: Some(operand),
                },
            )?;
            return source_reception::copy_view(
                key,
                crate::sema::copy_contract::CopyMode::Immutable,
                work,
            )
            .map(Some)
            .ok_or("copy publication Source exceeds its work bound".into());
        }
        let Some(application) = AstApplication::from_ast(expression) else {
            return Ok(None);
        };
        *work = work
            .checked_sub(self.facts.copy_call_events.len())
            .ok_or_else(|| "copy Source event lookup exceeds its work bound".to_owned())?;
        if !self
            .facts
            .copy_call_events
            .iter()
            .any(|event| event.matches_source(expression) && event.copy_operation.is_some())
        {
            return Ok(None);
        }
        let root =
            self.original_source_root(expression, value, context, visit.observation, work)?;
        let mut matching = self
            .facts
            .copy_call_events
            .iter()
            .filter(|event| event.result_expression == Some(root));
        let event = matching
            .next()
            .ok_or_else(|| "copy Source lost its actual result event".to_owned())?;
        require(
            matching.next().is_none()
                && application.operands.len() == 1
                && event.matches_source(expression)
                && event.owner == context.owner
                && event.parent == context.invocation
                && event.target.is_none(),
            "copy Source borrowed another application or arity",
        )?;
        let callee = event
            .callee_expression
            .and_then(|id| self.facts.expressions.get(id).map(|fact| (id, fact)))
            .ok_or_else(|| "copy Source lost its physical primitive callee".to_owned())?;
        let [crate::sema::model::Callable::Builtin(name)] = callee.1.value.callables.as_slice()
        else {
            return Err("copy Source has no unique actual primitive".into());
        };
        let mode = match name.as_str() {
            "clone" | "Prelude::clone" => crate::sema::copy_contract::CopyMode::Mutable,
            "clone_immut" | "Prelude::clone_immut" => {
                crate::sema::copy_contract::CopyMode::Immutable
            }
            _ => return Err("copy Source borrowed an unrelated primitive".into()),
        };
        require(
            event.copy_operation == Some(mode)
                && callee.1.source_id == application.callee.hir_id
                && callee.1.source_id.is_some()
                && self.observations.row(callee.0, work)?.context == context,
            "copy Source changed its actual primitive identity or context",
        )?;
        crate::sema::checker::actual_prelude_name(self.facts, context, application.callee, name)?;
        *work = work
            .checked_sub(self.facts.call_arguments.len())
            .ok_or_else(|| "copy Source operand lookup exceeds its work bound".to_owned())?;
        let mut preparations = self
            .facts
            .call_arguments
            .iter()
            .filter(|row| row.source_event == event.id);
        let preparation = preparations
            .next()
            .ok_or_else(|| "copy Source lost its actual supplied input".to_owned())?;
        require(
            preparations.next().is_none()
                && preparation.target.is_none()
                && preparation.evaluation_complete
                && preparation.slots == [crate::sema::default_uses::ArgumentSource::Supplied]
                && preparation.supplied.len() == 1,
            "copy Source changed its supplied operand preparation",
        )?;
        let token = preparation
            .supplied
            .get(&0)
            .ok_or_else(|| "copy Source lost its operand token".to_owned())?;
        let original = self
            .facts
            .expressions
            .get(token.expression)
            .ok_or_else(|| "copy Source input is outside its arena".to_owned())?;
        let row = self.observations.row(token.expression, work)?;
        require(
            original.source_id.is_some()
                && original.source_id == application.operands[0].expression.hir_id
                && row.context == context
                && row.argument_of == Some((event.id, 0)),
            "copy Source input borrowed another physical operand",
        )?;
        self.input_operand_interval(event, 0, token.expression, context, sites)?;
        let key = self.original_source_key_inner(
            application.operands[0].expression,
            &original.value,
            context,
            sites,
            work,
            SourceVisit {
                depth: visit.depth + 1,
                observation: Some(token.expression),
            },
        )?;
        source_reception::copy_view(key, mode, work)
            .map(Some)
            .ok_or_else(|| "copy Source transformation exceeds its work bound".to_owned())
    }

    pub(super) fn original_composite_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<ArgumentKey>> {
        let SourceVisit { depth, observation } = visit;
        if let ExprKind::Block(block) = &expression.kind {
            let blocks = self
                .blocks
                .as_ref()
                .ok_or_else(|| "block Source has no original HIR block index".to_owned())?;
            let anchor = blocks
                .source_block_with_budget(block, work)
                .map_err(|error| error.to_string())?
                .ok_or_else(|| "block Source is not a complete original block".to_owned())?;
            require(
                Some(anchor)
                    == expression
                        .hir_id
                        .map(ril_compiler_core::ids::BlockAnchor::ExpressionBody),
                "block Source borrowed another original block owner",
            )?;
            let Some((statement, tail_id)) = blocks
                .tail_with_budget(anchor, work)
                .map_err(|error| error.to_string())?
            else {
                return Ok(None);
            };
            *work = work
                .checked_sub(block.statements.len())
                .ok_or_else(|| "block Source tail lookup exceeds its work bound".to_owned())?;
            let Some(Stmt {
                kind:
                    StmtKind::Expr {
                        expression: tail,
                        terminated: false,
                    },
                ..
            }) = block
                .statements
                .iter()
                .find(|node| node.hir_id == Some(statement))
            else {
                return Err("block Source lost its original HIR tail statement".into());
            };
            require(
                tail.hir_id == Some(tail_id),
                "block Source tail differs from its original HIR child",
            )?;
            // A block may replace its ordinary tail with an effect answer or
            // cleanup outcome. Only the actual unchanged tail Source can be
            // forwarded; a same-span node or current callable tag is not it.
            let root = self.original_source_root(expression, value, context, observation, work)?;
            let source = expression.hir_id.unwrap();
            let lower = self
                .observations
                .previous(source, context, root, work)?
                .map_or(0, |index| index + 1);
            let tail_source = tail
                .hir_id
                .ok_or_else(|| "block Source tail has no genuine HIR identity".to_owned())?;
            let tails = self
                .observations
                .range(tail_source, context, lower..root, work)?;
            let [index] = tails else {
                return Err("block Source tail borrowed another physical occurrence".into());
            };
            let actual = &self.facts.expressions[*index];
            require(
                actual.value.ty != Ty::Never
                    && actual.value.cause == value.cause
                    && actual.value.ty == value.ty
                    && actual.value.source_type_witness == value.source_type_witness
                    && actual.value.callables == value.callables
                    && actual.value.callable_bounds == value.callable_bounds
                    && actual.value.callable_returns == value.callable_returns
                    && actual.value.signature == value.signature,
                "block Source differs from its actual tail's complete public view",
            )?;
            return self
                .original_source_key_inner(
                    tail,
                    &actual.value,
                    context,
                    sites,
                    work,
                    SourceVisit {
                        depth: depth + 1,
                        observation: Some(*index),
                    },
                )
                .map(Some);
        }
        let optional_exit =
            matches!(&expression.kind, ExprKind::Binary { operator, .. } if operator == "??");
        let children: Vec<(Option<&str>, &Expr)> = match &expression.kind {
            ExprKind::Unary { operator, operand } if operator == "^mut" => vec![(None, operand)],
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => vec![(None, left), (None, right)],
            ExprKind::Tuple(items) => items.iter().map(|item| (None, item)).collect(),
            ExprKind::Record {
                ty: None, members, ..
            } => members
                .iter()
                .map(|member| match member {
                    RecordMember::Field(field) => Ok((Some(field.name.as_str()), &field.value)),
                    RecordMember::Spread(_) => {
                        Err("open product Source requires its actual spread transport".to_owned())
                    }
                })
                .collect::<Check<_>>()?,
            _ => return Ok(None),
        };
        let root = self.original_source_root(expression, value, context, observation, work)?;
        let mut lower = self
            .observations
            .previous(expression.hir_id.unwrap(), context, root, work)?
            .map_or(0, |index| index + 1);
        let mut keys = Vec::new();
        for (position, (label, child)) in children.into_iter().enumerate() {
            *work = work
                .checked_sub(1 + label.map_or(0, |label| label.len().div_ceil(32)))
                .ok_or_else(|| "product Source exceeds its reconstruction budget".to_owned())?;
            let source = child
                .hir_id
                .ok_or_else(|| "product operand has no genuine HIR identity".to_owned())?;
            let candidates = self
                .observations
                .range(source, context, lower..root, work)?;
            let [index] = candidates else {
                return Err("product Source operand borrowed another physical occurrence".into());
            };
            let fact = &self.facts.expressions[*index];
            if optional_exit {
                if position == 0 && !matches!(fact.value.ty, Ty::Optional(_)) {
                    return Ok(None);
                }
                if position == 1 {
                    if fact.value.ty == Ty::Never {
                        continue;
                    }
                    return Ok(None);
                }
            }
            if matches!(expression.kind, ExprKind::Unary { .. }) {
                require(
                    value.sources == fact.value.sources
                        && value.source_type_witness == fact.value.source_type_witness
                        && value.callables == fact.value.callables
                        && value.callable_bounds == fact.value.callable_bounds
                        && value.callable_returns == fact.value.callable_returns
                        && value.signature == fact.value.signature
                        && self.facts.explanations.kinds.get(value.cause.0 as usize)
                            == Some(&crate::sema::facts::CauseKind::Retention)
                        && self
                            .facts
                            .explanations
                            .causes
                            .get(value.cause.0 as usize)
                            .is_some_and(|cause| cause.parents == [fact.value.cause]),
                    "sharing marker changed its actual operand's Source view",
                )?;
            }
            lower = *index + 1;
            let key = self.original_source_key_inner(
                child,
                &fact.value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: depth + 1,
                    observation: Some(*index),
                },
            )?;
            require(
                source_reception::complete(&key, work).is_some(),
                "product operand Source is incomplete",
            )?;
            keys.push((label, key));
        }
        if optional_exit {
            let key = keys
                .pop()
                .ok_or_else(|| "optional fallback lost its original payload Source".to_owned())?
                .1;
            let hir = self
                .facts
                .semantic_hir
                .as_deref()
                .ok_or_else(|| "optional fallback has no canonical HIR".to_owned())?;
            let mut limit = crate::sema::source_types::WorkLimit::new(*work);
            let key = crate::sema::source_types::declarations::project_steps(
                &key,
                &[crate::sema::source_types::SourcePath::OptionalPayload],
                hir,
                &mut limit,
            );
            *work = limit.remaining();
            key.map(Some)
                .map_err(|error| format!("optional fallback payload Source: {error}"))
        } else if matches!(expression.kind, ExprKind::Unary { .. }) {
            Ok(keys.pop().map(|(_, key)| key))
        } else if matches!(expression.kind, ExprKind::Tuple(_)) {
            Ok(Some(ArgumentKey::Tuple(
                keys.into_iter().map(|(_, key)| key).collect(),
            )))
        } else {
            let mut fields = BTreeMap::new();
            for (name, key) in keys {
                require(
                    fields.insert(name.unwrap().to_owned(), key).is_none(),
                    "product Source repeats a field",
                )?;
            }
            Ok(Some(ArgumentKey::Record {
                fields: fields
                    .into_iter()
                    .map(|(name, key)| (name, false, key))
                    .collect(),
                row: None,
            }))
        }
    }
}
