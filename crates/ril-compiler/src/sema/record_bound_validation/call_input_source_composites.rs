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
    ) -> Check<Option<Option<ArgumentKey>>> {
        self.original_copy_source_schema(expression, value, context, sites, work, visit)?
            .map(|source| {
                source
                    .map(|(schema, _)| schema.key().map_err(|error| error.to_string()))
                    .transpose()
            })
            .transpose()
    }

    /// Outer None means that this is not a copy source. A recognized copy
    /// keeps an unresolved original view as Some(None), after checking its
    /// physical operands; later output metadata cannot fill that missing view.
    pub(super) fn original_copy_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<Option<OriginalSource>>> {
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
            let key = self.original_source_schema_inner(
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
            return key
                .map(|(schema, environment)| {
                    super::graph_sources::schema_work(work, |budget| {
                        schema.copy_view(crate::sema::copy_contract::CopyMode::Immutable, budget)
                    })
                    .map(|schema| (schema, environment))
                })
                .transpose()
                .map(Some);
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
        self.actual_prelude_name(context, application.callee, name, work)?;
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
        self.input_operand_interval(event, 0, token.expression, context, work)?;
        let key = self.original_source_schema_inner(
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
        key.map(|(schema, environment)| {
            super::graph_sources::schema_work(work, |budget| schema.copy_view(mode, budget))
                .map(|schema| (schema, environment))
        })
        .transpose()
        .map(Some)
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
        self.original_composite_source_schema(expression, value, context, sites, work, visit)?
            .map(|(schema, _)| schema.key().map_err(|error| error.to_string()))
            .transpose()
    }

    pub(super) fn original_composite_source_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
        work: &mut usize,
        visit: SourceVisit,
    ) -> Check<Option<OriginalSource>> {
        let SourceVisit { depth, observation } = visit;
        if let ExprKind::Block(block) = &expression.kind {
            let blocks = self
                .blocks
                .as_ref()
                .ok_or_else(|| "block Source has no original HIR block index".to_owned())?;
            let source = expression
                .hir_id
                .ok_or("block Source lost its original HIR owner")?;
            let anchor = ril_compiler_core::ids::BlockAnchor::ExpressionBody(source);
            require(
                self.facts
                    .semantic_hir
                    .as_deref()
                    .and_then(|hir| hir.expression(source))
                    .is_some_and(|node| matches!(node.kind, crate::hir::nodes::ExprKind::Block(_)))
                    && blocks
                        .matches_source_at_with_budget(anchor, block, work)
                        .map_err(|error| error.to_string())?,
                "block Source is not a complete original block at its actual HIR owner",
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
            let tail_source = tail
                .hir_id
                .ok_or_else(|| "block Source tail has no genuine HIR identity".to_owned())?;
            let index = self.source_child_observation(root, tail_source, context, work)?;
            let actual = &self.facts.expressions[index];
            let expected = crate::sema::evaluated::transport_value_at(
                &actual.value,
                &self.facts.allocation_history,
                actual.allocation_epoch,
                self.facts.expressions[root].allocation_epoch,
                work,
            )
            .map_err(|error| format!("block tail Source transport: {error}"))?;
            let has_handler = expression
                .hir_id
                .and_then(|id| self.facts.semantic_hir.as_deref()?.expression(id))
                .is_some_and(|node| {
                    let crate::hir::nodes::ExprKind::Block(block) = &node.kind else {
                        return false;
                    };
                    block.statements.iter().any(|id| {
                        self.facts
                            .semantic_hir
                            .as_deref()
                            .and_then(|hir| hir.statement(*id))
                            .is_some_and(|statement| {
                                matches!(statement.kind, crate::hir::nodes::StmtKind::Handler(_))
                            })
                    })
                });
            if !crate::sema::evaluated::same_source_public_view(&expected, value, work)
                .map_err(|error| error.to_string())?
                || has_handler
            {
                let exits = crate::sema::source_types::block_exits::Inputs {
                    hir: self
                        .facts
                        .semantic_hir
                        .as_deref()
                        .ok_or("block exit has no original HIR")?,
                    expressions: &self.facts.expressions,
                    evaluations: &self.facts.evaluations,
                    activations: &self.facts.activations,
                    scopes: &self.facts.scopes,
                    explanations: &self.facts.explanations,
                    history: &self.facts.allocation_history,
                    open: None,
                }
                .joined(root, index, work)
                .map_err(|error| format!("block exit Source proof: {error}"))?;
                let mut common: Option<OriginalSource> = None;
                for exit in exits {
                    if let Some(scope) = exit.operation {
                        require(
                            self.frames.operation(scope, work)?.is_some(),
                            "block answer lost its actual operation frame",
                        )?;
                    }
                    source_scan_work(
                        work,
                        2 + sites.expressions.len().checked_ilog2().unwrap_or(0) as usize,
                    )?;
                    let fact = self
                        .facts
                        .expressions
                        .get(exit.observation)
                        .ok_or("block exit lost its physical value")?;
                    let source = fact.source_id.ok_or("block exit lost its HIR expression")?;
                    let syntax = sites
                        .expressions
                        .get(&source)
                        .ok_or("block exit lost its original expression")?;
                    let record = self
                        .facts
                        .evaluations
                        .get(exit.observation)
                        .ok_or("block exit lost its evaluation context")?;
                    let known = self
                        .original_source_schema_inner(
                            syntax,
                            &fact.value,
                            record.context,
                            sites,
                            work,
                            SourceVisit {
                                depth: depth + 1,
                                observation: Some(exit.observation),
                            },
                        )?
                        .ok_or("block exit has no complete original Source")?;
                    if let Some((schema, environment)) = &common {
                        require(
                            super::graph_sources::schema_work(work, |budget| {
                                schema.equivalent_in(&known.0, environment, &known.1, budget)
                            })?,
                            "block exits have different Source coordinates",
                        )?;
                    } else {
                        common = Some(known);
                    }
                }
                return common
                    .map(Some)
                    .ok_or_else(|| "block has no returning Source exit".into());
            }
            return self.original_source_schema_inner(
                tail,
                &actual.value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: depth + 1,
                    observation: Some(index),
                },
            );
        }
        let optional_exit =
            matches!(&expression.kind, ExprKind::Binary { operator, .. } if operator == "??");
        let child_count = match &expression.kind {
            ExprKind::Array(items) | ExprKind::Tuple(items) => items.len(),
            ExprKind::Map(items) => items
                .len()
                .checked_mul(2)
                .ok_or("map Source child count overflow")?,
            ExprKind::Record { members, .. } => members.len(),
            ExprKind::Binary { .. } => 2,
            _ => 1,
        };
        *work = work
            .checked_sub(child_count)
            .ok_or("product Source children exceed their work bound")?;
        let children: Vec<(Option<&str>, &Expr)> = match &expression.kind {
            ExprKind::Unary { operator, operand } if operator == "^mut" => vec![(None, operand)],
            ExprKind::Binary {
                operator,
                left,
                right,
            } if operator == "??" => vec![(None, left), (None, right)],
            ExprKind::Tuple(items) => items.iter().map(|item| (None, item)).collect(),
            ExprKind::Array(items) if !items.is_empty() => {
                items.iter().map(|item| (None, item)).collect()
            }
            ExprKind::Map(items) if !items.is_empty() => items
                .iter()
                .flat_map(|(key, value)| [(None, key), (None, value)])
                .collect(),
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
        let mut previous = None;
        let mut keys = Vec::new();
        for (position, (label, child)) in children.into_iter().enumerate() {
            *work = work
                .checked_sub(1 + label.map_or(0, |label| label.len().div_ceil(32)))
                .ok_or_else(|| "product Source exceeds its reconstruction budget".to_owned())?;
            let source = child
                .hir_id
                .ok_or_else(|| "product operand has no genuine HIR identity".to_owned())?;
            let index = self.source_child_observation(root, source, context, work)?;
            require(
                previous.is_none_or(|previous| previous < index),
                "product Source changed its actual child evaluation order",
            )?;
            previous = Some(index);
            let fact = &self.facts.expressions[index];
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
            let Some(key) = self.original_source_schema_inner(
                child,
                &fact.value,
                context,
                sites,
                work,
                SourceVisit {
                    depth: depth + 1,
                    observation: Some(index),
                },
            )?
            else {
                return Ok(None);
            };
            keys.push((label, key));
        }
        if optional_exit {
            let (schema, environment) = keys
                .pop()
                .ok_or_else(|| "optional fallback lost its original payload Source".to_owned())?
                .1;
            super::graph_sources::schema_work(work, |budget| {
                schema.project_steps(
                    &[crate::sema::source_types::SourcePath::OptionalPayload],
                    budget,
                )
            })
            .map(|schema| Some((schema, environment)))
        } else if matches!(expression.kind, ExprKind::Unary { .. }) {
            Ok(keys.pop().map(|(_, key)| key))
        } else if matches!(expression.kind, ExprKind::Array(_)) {
            let sources: Vec<_> = keys.into_iter().map(|(_, source)| source).collect();
            let environment = self.source_composite_environment(&sources, work)?;
            let element = &sources[0].0;
            for (actual, _) in &sources[1..] {
                require(
                    super::graph_sources::schema_work(work, |budget| {
                        element.equivalent(actual, budget)
                    })?,
                    "array construction children disagree about their original Source graph",
                )?;
            }
            super::graph_sources::schema_work(work, |budget| {
                SourceSchema::array(
                    crate::sema::source_types::SourceLength::Dynamic,
                    element,
                    None,
                    budget,
                )
            })
            .map(|schema| Some((schema, environment)))
        } else if matches!(expression.kind, ExprKind::Map(_)) {
            let sources: Vec<_> = keys.into_iter().map(|(_, source)| source).collect();
            let environment = self.source_composite_environment(&sources, work)?;
            let (key, value) = (&sources[0].0, &sources[1].0);
            for pair in sources[2..].as_chunks::<2>().0 {
                require(
                    super::graph_sources::schema_work(work, |budget| {
                        key.equivalent(&pair[0].0, budget)
                    })? && super::graph_sources::schema_work(work, |budget| {
                        value.equivalent(&pair[1].0, budget)
                    })?,
                    "map construction children disagree about their original Source graphs",
                )?;
            }
            super::graph_sources::schema_work(work, |budget| {
                SourceSchema::map(key, value, None, budget)
            })
            .map(|schema| Some((schema, environment)))
        } else if matches!(expression.kind, ExprKind::Tuple(_)) {
            let sources: Vec<_> = keys.into_iter().map(|(_, source)| source).collect();
            let environment = self.source_composite_environment(&sources, work)?;
            let schemas: Vec<_> = sources.into_iter().map(|(schema, _)| schema).collect();
            super::graph_sources::schema_work(work, |budget| {
                SourceSchema::tuple(&schemas, None, budget)
            })
            .map(|schema| Some((schema, environment)))
        } else {
            let sources: Vec<_> = keys.iter().map(|(_, source)| source.clone()).collect();
            let environment = self.source_composite_environment(&sources, work)?;
            let mut fields = BTreeMap::new();
            for (name, key) in keys {
                require(
                    fields.insert(name.unwrap().to_owned(), key).is_none(),
                    "product Source repeats a field",
                )?;
            }
            let fields: Vec<_> = fields
                .into_iter()
                .map(|(name, (schema, _))| (name, false, schema))
                .collect();
            super::graph_sources::schema_work(work, |budget| {
                SourceSchema::record(&fields, None, None, budget)
            })
            .map(|schema| Some((schema, environment)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collection_sources_require_each_actual_child_even_with_a_closed_root_view() {
        for (case, array) in [
            (
                "tests/regressions/source-transport.ril::generic-literal-collection-source-graphs",
                true,
            ),
            (
                "tests/regressions/source-transport.ril::generic-literal-collection-source-graphs",
                false,
            ),
        ] {
            let source = ril_test::case_source(case);
            let program = crate::Session::new(source.as_bytes().to_vec())
                .verify()
                .unwrap();
            let facts = program.facts();
            let sources = OriginalOperandSources::new(facts).unwrap();
            let empty = facts
                .bindings
                .iter()
                .position(|binding| binding.name == "empty")
                .unwrap();
            let (original, _) = facts
                .source_types
                .binding_schema_if_known(empty, None, &mut WorkLimit::new(4096))
                .unwrap()
                .unwrap();
            let (observation, root, child) = facts.expressions.iter().enumerate().find_map(|(index, fact)| {
                let id = fact.source_id?;
                let syntax = sources.sites.expressions.get(&id)?;
                let child = match &syntax.kind {
                    ExprKind::Array(items) if array && matches!(items.as_slice(), [Expr { kind: ExprKind::Name(name), .. }] if name == "value") => {
                        let parent = facts.evaluations[index].identity?.activation;
                        let child = items[0].hir_id?;
                        let actual = facts.expressions.iter().enumerate().find(|(observation, fact)| {
                            fact.source_id == Some(child) && facts.evaluations[*observation].identity.is_some_and(|identity|
                                facts.activations[identity.activation.0 as usize].parent == Some(parent))
                        })?.1;
                        let selected_empty = actual.value.sources.iter().filter_map(|id| facts.bindings.get(*id))
                            .flat_map(|binding| binding.typing_environment.generic_sources.values())
                            .any(|selected| selected.schema.equivalent(&original, &mut WorkLimit::new(4096)) == Ok(true));
                        if !selected_empty { return None }
                        &items[0]
                    }
                    ExprKind::Map(items) if !array && !items.is_empty() => &items[0].0,
                    _ => return None,
                };
                Some((index, id, child.hir_id.unwrap()))
            }).expect("fixture must retain its nonempty literal and original child");
            let (schema, _) = sources
                .observed(root, observation)
                .unwrap()
                .0
                .expect("known literal children must retain a complete Source graph");
            if array {
                assert!(
                    schema
                        .project_steps(
                            &[crate::sema::source_types::SourcePath::Element],
                            &mut WorkLimit::new(4096)
                        )
                        .unwrap()
                        .equivalent(&original, &mut WorkLimit::new(4096))
                        .unwrap(),
                    "a dynamic literal outer view must preserve the stored child's hidden fixed extent"
                );
            }
            let context = sources
                .replay
                .observations
                .row(observation, &mut 4096)
                .unwrap()
                .context;
            let parent = facts.evaluations[observation].identity.unwrap().activation;
            let children: Vec<_> = sources
                .replay
                .observations
                .range(child, context, 0..observation, &mut 4096)
                .unwrap()
                .iter()
                .copied()
                .filter(|child| {
                    let activation = facts.evaluations[*child].identity.unwrap().activation;
                    facts.activations[activation.0 as usize].parent == Some(parent)
                })
                .collect();
            let [child_observation] = children.as_slice() else {
                panic!("fixture must have one actual literal child")
            };
            let mut changed = facts.clone();
            changed.expressions[*child_observation].source_id = None;
            assert!(
                OriginalOperandSources::new(&changed)
                    .and_then(|sources| sources.observed(root, observation))
                    .is_err(),
                "{case}: a root view cannot replace its missing physical child"
            );
        }
    }

    #[test]
    fn unknown_copy_source_requires_its_primitive_and_physical_supplied_operand() {
        let source = ril_test::case_source("tests/stdlib/random.ril::seed-and-clone");
        let program = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let facts = program.facts();
        let row = facts
            .binding_sources
            .iter()
            .find(|row| facts.bindings[row.binding].name == "independent")
            .unwrap();
        let root = row.initializer.expression;
        assert!(facts.source_types.binding_type(row.binding).is_none());
        let sites =
            crate::sema::record_bound_validation::explicit_named::source_sites_base(facts).unwrap();
        let syntax = sites
            .bindings
            .iter()
            .find(|site| site.binding.pattern.hir_id == Some(row.declaration))
            .map(|site| &site.binding.value)
            .unwrap();
        let replay = Replay::new(facts).unwrap();
        assert_eq!(
            replay
                .original_copy_source_key(
                    syntax,
                    &facts.expressions[root].value,
                    row.context,
                    &sites,
                    &mut 4096,
                    SourceVisit {
                        depth: 0,
                        observation: Some(root),
                    },
                )
                .unwrap(),
            Some(None)
        );
        let event = facts
            .copy_call_events
            .iter()
            .position(|event| event.result_expression == Some(root))
            .unwrap();
        for mutation in 0..3 {
            let mut changed = facts.clone();
            match mutation {
                0 => {
                    changed.copy_call_events[event].copy_operation =
                        Some(crate::sema::copy_contract::CopyMode::Immutable);
                }
                1 => {
                    let id = changed.copy_call_events[event].id;
                    changed
                        .call_arguments
                        .retain(|preparation| preparation.source_event != id);
                }
                _ => changed.copy_call_events[event].callee_expression = Some(root),
            }
            let result = Replay::new(&changed).and_then(|replay| {
                replay.original_observed_source_key_if_known(syntax, root, row.context, &sites)
            });
            assert!(
                result.is_err(),
                "mutation {mutation} hid an invalid copy behind unavailable Source"
            );
        }
    }
}
