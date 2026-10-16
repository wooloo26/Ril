//! Lowering consumes the semantic certificate, never an unverified syntax tree.
use ril_compiler_core::{
    ids::{CallableOwner, DefinitionId, TypeId},
    phase::{NotImplemented, Stage},
    source::Span,
    target::TargetLayout,
};
use ril_ir::core as ir;
use ril_syntax::ast;
mod budget;
mod concurrent;
mod constants;
mod foreign;
mod specialize;

pub fn lower_core(program: &crate::hir::VerifiedProgram) -> Result<ir::Program, NotImplemented> {
    let layout = program
        .facts()
        .target_layout
        .ok_or_else(|| unsupported("verified program has no target layout"))?;
    lower_core_for(program, layout)
}
pub fn lower_core_for(
    program: &crate::hir::VerifiedProgram,
    layout: TargetLayout,
) -> Result<ir::Program, NotImplemented> {
    if !matches!(layout.pointer_bits, 32 | 64) || program.facts().target_layout != Some(layout) {
        return Err(unsupported(
            "Core lowering requires the target layout used by semantic verification",
        ));
    }
    if let Some(site) = crate::syntax_sites::ambiguous(program.syntax()).first() {
        return Err(unsupported(&site.description));
    }
    let specializations = specialize::Plan::new(program)?;
    crate::sema::copy_template_closure::validate(program.facts()).map_err(unsupported)?;
    crate::sema::closure_exclusivity::validate(program.facts()).map_err(unsupported)?;
    let mut provenance = crate::provenance_lower::lower(program.facts())?;
    provenance.static_termination = program
        .static_termination()
        .iter()
        .map(|(name, judgment)| ril_ir::provenance::Termination {
            function: name.clone(),
            may_diverge: judgment.may_diverge,
            unresolved: judgment.unresolved,
            callable_parameters: judgment
                .callable_parameters
                .iter()
                .map(|&index| index as u32)
                .collect(),
        })
        .collect();
    provenance.static_definitions = program
        .static_definitions()
        .iter()
        .map(|function| ril_ir::provenance::StaticDefinition {
            name: function.name.clone(),
            span: function.span,
            family: ril_ir::provenance::StaticFamily::Meta,
            parameters: function
                .parameters
                .iter()
                .map(|parameter| ril_ir::provenance::Parameter {
                    name: if let ast::PatternKind::Name(name) = &parameter.pattern.kind {
                        Some(name.clone())
                    } else {
                        None
                    },
                    mode: match parameter.mode {
                        ast::ParameterMode::Read => ril_ir::provenance::Access::Read,
                        ast::ParameterMode::Mut => ril_ir::provenance::Access::Write,
                        ast::ParameterMode::SharedMut => ril_ir::provenance::Access::Retain,
                    },
                    type_annotation: parameter.ty.as_ref().map(|ty| ty.text.clone()),
                    default: parameter.default.as_ref().map(|value| value.span),
                })
                .collect(),
            generic_names: function
                .generics
                .iter()
                .map(|parameter| parameter.name.clone())
                .collect(),
            result_annotation: function.return_type.as_ref().map(|ty| ty.text.clone()),
        })
        .chain(program.type_functions().iter().map(|function| {
            ril_ir::provenance::StaticDefinition {
                name: function.name.clone(),
                span: function.span,
                family: ril_ir::provenance::StaticFamily::Type,
                parameters: vec![],
                generic_names: function
                    .generics
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect(),
                result_annotation: function.value.as_ref().map(|ty| ty.text.clone()),
            }
        }))
        .collect();
    let generic_types = provenance
        .generic_binders
        .iter()
        .map(|binder| ((binder.definition, binder.index), binder.ty))
        .collect();
    // One source expression can be checked under several call substitutions.
    // A concrete observation from one call cannot specialize every invocation.
    let mut operation_observations =
        std::collections::BTreeMap::<(u32, u32, u32), Option<u64>>::new();
    for fact in &program.facts().expressions {
        let current = if let [crate::sema::model::Callable::Builtin(name)] =
            fact.value.callables.as_slice()
        {
            program
                .facts()
                .operations
                .get(name)
                .map(|operation| operation.identity)
        } else {
            None
        };
        operation_observations
            .entry((fact.span.file.0, fact.span.start, fact.span.end))
            .and_modify(|previous| {
                if *previous != current {
                    *previous = None;
                }
            })
            .or_insert(current);
    }
    let expression_operations = operation_observations
        .into_iter()
        .filter_map(|(span, operation)| operation.map(|operation| (span, operation)))
        .collect();
    let mut builtin_observations =
        std::collections::BTreeMap::<(u32, u32, u32), Option<String>>::new();
    for fact in &program.facts().expressions {
        let current = if let [crate::sema::model::Callable::Builtin(name)] =
            fact.value.callables.as_slice()
            && (name.starts_with("Num::__convert_")
                || name.starts_with("Deque::__new_")
                || name.starts_with("Heap::__new_")
                || name.starts_with("Channel::__bounded_")
                || matches!(name.as_str(), "Concurrent::fork" | "Concurrent::join"))
        {
            Some(name.clone())
        } else {
            None
        };
        builtin_observations
            .entry((fact.span.file.0, fact.span.start, fact.span.end))
            .and_modify(|previous| {
                if *previous != current {
                    *previous = None;
                }
            })
            .or_insert(current);
    }
    let mut lower = Lower {
        specializations: &specializations,
        specialization_context: None,
        default_context: None,
        nonretaining_adapters: Vec::new(),
        callable_owner: Some(CallableOwner::Global),
        external_generic_names: program
            .syntax()
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                ast::StmtKind::Function(function)
                    if function.body.is_none() && !function.generics.is_empty() =>
                {
                    Some(function.name.clone())
                }
                _ => None,
            })
            .collect(),
        facts: program.facts(),
        all_facts: program.facts(),
        call_signatures: vec![],
        layout,
        definitions: program.definitions(),
        next_definition: specializations.next_definition(
            program
                .definitions()
                .iter()
                .map(|definition| definition.id.0)
                .max()
                .map_or(0, |id| id.saturating_add(1)),
        ),
        next_temporary: 0,
        generic_types,
        contextual_types: &program.facts().contextual_types,
        specialized_builtins: builtin_observations
            .into_iter()
            .filter_map(|(span, name)| name.map(|name| (span, name)))
            .collect(),
        operations: program
            .facts()
            .operations
            .iter()
            .map(|(name, operation)| (name.clone(), operation.identity))
            .collect(),
        implicit_unwraps: &program.facts().implicit_unwraps,
        expression_operations,
    };
    let mut functions = Vec::new();
    let mut globals = Vec::new();
    let mut external_functions = Vec::new();
    let mut external_constants = Vec::new();
    for statement in &program.syntax().statements {
        match &statement.kind {
            ast::StmtKind::Function(function)
                if function.body.is_none() && !function.generics.is_empty() =>
            {
                external_functions.extend(foreign::instances(&mut lower, program, function)?)
            }
            ast::StmtKind::Function(function) if function.body.is_none() => {
                external_functions.push(foreign::function(&mut lower, program, function)?)
            }
            ast::StmtKind::Binding(binding)
                if matches!(binding.value.kind, ast::ExprKind::Ambient) =>
            {
                external_constants.push(foreign::constant(&lower, program, binding)?)
            }
            ast::StmtKind::Function(function) => {
                let template = program
                    .facts()
                    .functions
                    .iter()
                    .find(|info| {
                        info.syntax.name == function.name && info.syntax.span == function.span
                    })
                    .is_some_and(|info| specializations.templates.contains(&info.definition));
                if !template {
                    functions.push(lower.function(function)?);
                }
            }
            _ => {
                if let Some(statement) = lower.statement(statement)? {
                    globals.push(statement);
                }
            }
        }
    }
    for (index, instance) in specializations.instances.iter().enumerate() {
        let facts = specializations.facts(program.facts(), index)?;
        let syntax = program
            .facts()
            .functions
            .iter()
            .find(|info| info.definition == instance.record.template)
            .ok_or_else(|| unsupported("specialization template syntax is missing"))?;
        let mut selected = Lower {
            specializations: &specializations,
            specialization_context: Some(index),
            default_context: None,
            nonretaining_adapters: vec![],
            callable_owner: Some(CallableOwner::Global),
            external_generic_names: lower.external_generic_names.clone(),
            facts: &facts,
            all_facts: program.facts(),
            call_signatures: vec![],
            layout,
            definitions: lower.definitions,
            next_definition: lower.next_definition,
            next_temporary: lower.next_temporary,
            generic_types: lower.generic_types.clone(),
            contextual_types: &facts.contextual_types,
            specialized_builtins: specialize::builtins(&facts)?,
            operations: lower.operations.clone(),
            expression_operations: instance.operations.clone(),
            implicit_unwraps: &facts.implicit_unwraps,
        };
        let mut function = selected.function(&syntax.syntax)?;
        function.definition = instance.record.definition;
        function.name.clone_from(&instance.record.name);
        function.generic_parameters.clear();
        lower.next_definition = selected.next_definition;
        lower.next_temporary = selected.next_temporary;
        lower.call_signatures.extend(selected.call_signatures);
        if !selected.nonretaining_adapters.is_empty() {
            return Err(unsupported(
                "specialized builtin adapters require their lexical owner remapping",
            ));
        }
        functions.push(function);
    }
    specializations.publish_closures(program.facts(), &mut provenance)?;
    provenance.specializations = specializations
        .instances
        .iter()
        .map(|instance| instance.record.clone())
        .collect();
    provenance.nonretaining_adapters = lower.nonretaining_adapters;
    Ok(ir::Program {
        constant_graphs: constants::lower(program.facts(), &provenance)?,
        external_functions,
        external_constants,
        call_signatures: lower.call_signatures,
        functions,
        globals: ir::Block {
            statements: globals,
        },
        provenance,
        constructors: program
            .facts()
            .constructors
            .iter()
            .map(|(name, info)| ir::Constructor {
                name: name.clone(),
                tag: info.tag.clone(),
                nominal: info.nominal,
                has_payload: info.has_payload,
                span: info.span,
            })
            .collect(),
        operations: program
            .facts()
            .operations
            .values()
            .map(|operation| ir::Operation {
                identity: operation.identity,
                name: operation.name.clone(),
                span: operation.span,
            })
            .collect(),
    })
}
struct Lower<'a> {
    specializations: &'a specialize::Plan,
    specialization_context: Option<usize>,
    default_context: Option<u32>,
    nonretaining_adapters: Vec<ril_ir::provenance::NonRetainingAdapter>,
    callable_owner: Option<CallableOwner>,
    external_generic_names: std::collections::BTreeSet<String>,
    facts: &'a crate::sema::SemanticFacts,
    all_facts: &'a crate::sema::SemanticFacts,
    call_signatures: Vec<ir::CallSignature>,
    layout: TargetLayout,
    definitions: &'a [crate::hir::Definition],
    next_definition: u32,
    next_temporary: u32,
    generic_types: std::collections::BTreeMap<(DefinitionId, u32), TypeId>,
    contextual_types: &'a std::collections::BTreeMap<(u32, u32, u32), crate::sema::model::Ty>,
    specialized_builtins: std::collections::BTreeMap<(u32, u32, u32), String>,
    operations: std::collections::BTreeMap<String, u64>,
    expression_operations: std::collections::BTreeMap<(u32, u32, u32), u64>,
    implicit_unwraps: &'a std::collections::BTreeMap<(u32, u32, u32), crate::sema::ImplicitUnwrap>,
}
fn unsupported(detail: impl Into<String>) -> NotImplemented {
    NotImplemented::new(Stage::Lowering, detail)
}

impl Lower<'_> {
    fn record_call_signature(&mut self, callee: Span, call: Span) -> Result<(), NotImplemented> {
        let observations: Vec<_> = self
            .facts
            .expressions
            .iter()
            .filter(|fact| fact.span == callee)
            .collect();
        let mut signature: Option<Vec<ir::CallParameter>> = None;
        let mut unresolved = false;
        for fact in observations {
            let Some(parameters) = &fact.value.signature else {
                unresolved = true;
                continue;
            };
            let parameters: Vec<_> = parameters
                .iter()
                .map(|parameter| ir::CallParameter {
                    label: if let ast::PatternKind::Name(name) = &parameter.pattern.kind {
                        Some(name.clone())
                    } else {
                        None
                    },
                    has_default: parameter.default.is_some(),
                })
                .collect();
            if signature
                .as_ref()
                .is_some_and(|previous| previous != &parameters)
            {
                return Err(unsupported(
                    "callable label/default shape differs between verified substitutions",
                ));
            }
            signature = Some(parameters);
        }
        // Missing observations do not establish labels. The backend may still
        // use positional arguments, but cannot infer a dynamic signature.
        if !unresolved && let Some(parameters) = signature {
            self.call_signatures.push(ir::CallSignature {
                span: call,
                parameters,
            });
        }
        Ok(())
    }
    fn function(&mut self, function: &ast::Function) -> Result<ir::Function, NotImplemented> {
        if function.is_meta {
            return Err(unsupported("static function materialization"));
        }
        let definition = if let Some(id) =
            self.facts.functions.iter().position(|info| {
                info.syntax.name == function.name && info.syntax.span == function.span
            }) {
            self.facts.functions[id].definition
        } else if let Some(definition) = self
            .definitions
            .iter()
            .find(|definition| definition.span == function.span)
        {
            definition.id
        } else {
            let id = DefinitionId(self.next_definition);
            self.next_definition += 1;
            id
        };
        if self.specialization_context.is_some_and(|index| {
            self.specializations.instances[index].record.template != definition
        }) {
            return Err(unsupported(
                "effect specialization nested callables require their own lexical owner mapping",
            ));
        }
        let previous_owner = self
            .callable_owner
            .replace(CallableOwner::Function(definition));
        let result = Ok(ir::Function {
            role: ir::FunctionRole::Ordinary,
            definition,
            name: function.name.clone(),
            generic_parameters: function
                .generics
                .iter()
                .enumerate()
                .map(|(index, _)| {
                    self.generic_types
                        .get(&(definition, index as u32))
                        .copied()
                        .ok_or_else(|| unsupported("verified generic binder is missing"))
                })
                .collect::<Result<_, _>>()?,
            parameters: function
                .parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| self.function_parameter(index as u32, parameter))
                .collect::<Result<_, _>>()?,
            body: self.block(
                function
                    .body
                    .as_ref()
                    .ok_or_else(|| unsupported("external native binding"))?,
            )?,
            span: function.span,
        });
        self.callable_owner = previous_owner;
        result
    }
    fn parameter(&mut self, parameter: &ast::Parameter) -> Result<ir::Parameter, NotImplemented> {
        Ok(ir::Parameter {
            pattern: self.pattern(&parameter.pattern)?,
            default: parameter
                .default
                .as_ref()
                .map(|value| self.expression(value))
                .transpose()?,
        })
    }
    fn function_parameter(
        &mut self,
        parameter_index: u32,
        parameter: &ast::Parameter,
    ) -> Result<ir::Parameter, NotImplemented> {
        let (Some(index), Some(value)) = (self.specialization_context, parameter.default.as_ref())
        else {
            return self.parameter(parameter);
        };
        let pattern = self.pattern(&parameter.pattern)?;
        let Some(facts) =
            self.specializations
                .default_facts(self.all_facts, index, parameter_index)?
        else {
            return Ok(ir::Parameter {
                pattern,
                default: None,
            });
        };
        let mut nested = Lower {
            specializations: self.specializations,
            specialization_context: Some(index),
            default_context: Some(parameter_index),
            nonretaining_adapters: vec![],
            callable_owner: self.callable_owner,
            external_generic_names: self.external_generic_names.clone(),
            facts: &facts,
            all_facts: self.all_facts,
            call_signatures: vec![],
            layout: self.layout,
            definitions: self.definitions,
            next_definition: self.next_definition,
            next_temporary: self.next_temporary,
            generic_types: self.generic_types.clone(),
            contextual_types: &facts.contextual_types,
            specialized_builtins: specialize::builtins(&facts)?,
            operations: self.operations.clone(),
            expression_operations: self
                .specializations
                .default_operations(index, parameter_index),
            implicit_unwraps: &facts.implicit_unwraps,
        };
        let default = nested.expression(value)?;
        self.next_definition = nested.next_definition;
        self.next_temporary = nested.next_temporary;
        self.call_signatures.extend(nested.call_signatures);
        if !nested.nonretaining_adapters.is_empty() {
            return Err(unsupported(
                "specialized default builtin adapters require their owner mapping",
            ));
        }
        Ok(ir::Parameter {
            pattern,
            default: Some(default),
        })
    }
    fn block(&mut self, block: &ast::Block) -> Result<ir::Block, NotImplemented> {
        let mut statements = Vec::new();
        for statement in block.where_items.iter().chain(&block.statements) {
            if let ast::StmtKind::Binding(binding) = &statement.kind
                && let ast::PatternKind::Record {
                    fields,
                    rest_binding: Some(rest),
                    ..
                } = &binding.pattern.kind
            {
                if self.specialization_context.is_some() {
                    return Err(unsupported(
                        "effect specialization record-rest bindings require invocation-owned shape witnesses",
                    ));
                }
                if binding.fallback.is_some() || binding.is_meta {
                    return Err(unsupported("guarded or static record-rest lowering"));
                }
                let mut keys = None;
                for observed in self.facts.bindings.iter().filter(|observed| {
                    observed.span == binding.pattern.span && observed.name == *rest
                }) {
                    let crate::sema::model::Ty::Record(shape) = &observed.value.ty else {
                        return Err(unsupported("record-rest binding has no exact closed shape"));
                    };
                    let current: Vec<_> = shape.keys().cloned().collect();
                    if keys.as_ref().is_some_and(|previous| *previous != current) {
                        return Err(unsupported(
                            "record-rest binding requires distinct field specializations",
                        ));
                    }
                    keys = Some(current);
                }
                let keys =
                    keys.ok_or_else(|| unsupported("verified record-rest binding is missing"))?;
                let temporary = format!("\0ril.record_rest.{}", self.next_temporary);
                self.next_temporary += 1;
                statements.push(ir::Statement::Bind {
                    pattern: ir::Pattern::Name(temporary.clone()),
                    value: self.expression(&binding.value)?,
                    scoped: false,
                });
                let reference = ir::Expr {
                    kind: ir::ExprKind::Name(temporary),
                    span: binding.value.span,
                };
                let scoped = matches!(
                    binding.mode,
                    ast::BindingMode::Scoped | ast::BindingMode::ScopedMut
                );
                statements.push(ir::Statement::Bind {
                    pattern: ir::Pattern::Record(
                        fields
                            .iter()
                            .map(|field| Ok((field.name.clone(), self.pattern(&field.pattern)?)))
                            .collect::<Result<_, NotImplemented>>()?,
                    ),
                    value: reference.clone(),
                    scoped,
                });
                let rest_fields: Vec<_> = keys
                    .into_iter()
                    .map(|field| {
                        let value = ir::Expr {
                            kind: ir::ExprKind::Field {
                                base: Box::new(reference.clone()),
                                field: field.clone(),
                                safe: false,
                            },
                            span: binding.pattern.span,
                        };
                        (field, value)
                    })
                    .collect();
                statements.push(ir::Statement::Bind {
                    pattern: ir::Pattern::Name(rest.clone()),
                    value: ir::Expr {
                        kind: ir::ExprKind::Record {
                            members: rest_fields
                                .iter()
                                .map(|(field, value)| {
                                    ir::RecordMember::Field(field.clone(), value.clone())
                                })
                                .collect(),
                            fields: rest_fields,
                            spread: None,
                        },
                        span: binding.pattern.span,
                    },
                    scoped,
                });
                continue;
            }
            if let ast::StmtKind::Binding(binding) = &statement.kind
                && let Some(fallback) = &binding.fallback
            {
                let temporary = format!("\0ril.guard.{}", self.next_temporary);
                self.next_temporary += 1;
                let pattern = self.pattern(&binding.pattern)?;
                let value = self.expression(&binding.value)?;
                statements.push(ir::Statement::Bind {
                    pattern: ir::Pattern::Name(temporary.clone()),
                    value,
                    scoped: false,
                });
                let reference = ir::Expr {
                    kind: ir::ExprKind::Name(temporary),
                    span: binding.value.span,
                };
                statements.push(ir::Statement::Expr {
                    expression: ir::Expr {
                        kind: ir::ExprKind::If {
                            condition: Box::new(ir::Expr {
                                kind: ir::ExprKind::Is {
                                    value: Box::new(reference.clone()),
                                    pattern: binding_test(&pattern),
                                },
                                span: binding.pattern.span,
                            }),
                            then_branch: Box::new(ir::Expr {
                                kind: ir::ExprKind::Literal(ir::Literal::Unit),
                                span: statement.span,
                            }),
                            else_branch: Some(Box::new(self.expression(fallback)?)),
                        },
                        span: statement.span,
                    },
                    terminated: true,
                });
                statements.push(ir::Statement::Bind {
                    pattern,
                    value: reference,
                    scoped: matches!(
                        binding.mode,
                        ast::BindingMode::Scoped | ast::BindingMode::ScopedMut
                    ),
                });
                continue;
            }
            if let Some(statement) = self.statement(statement)? {
                statements.push(statement);
            }
        }
        Ok(ir::Block { statements })
    }
    fn statement(
        &mut self,
        statement: &ast::Stmt,
    ) -> Result<Option<ir::Statement>, NotImplemented> {
        Ok(Some(match &statement.kind {
            ast::StmtKind::Binding(binding) => {
                if binding.is_meta {
                    return Err(unsupported("static constant materialization"));
                }
                if binding.fallback.is_some() {
                    return Err(unsupported("guarded binding lowering"));
                }
                ir::Statement::Bind {
                    pattern: self.pattern(&binding.pattern)?,
                    value: self.expression(&binding.value)?,
                    scoped: matches!(
                        binding.mode,
                        ast::BindingMode::Scoped | ast::BindingMode::ScopedMut
                    ),
                }
            }
            ast::StmtKind::Assignment {
                target,
                operator,
                value,
            } => ir::Statement::Assign {
                target: self.expression(target)?,
                operator: operator.clone(),
                value: self.expression(value)?,
            },
            ast::StmtKind::Expr {
                expression,
                terminated,
            } => ir::Statement::Expr {
                expression: self.expression(expression)?,
                terminated: *terminated,
            },
            ast::StmtKind::Function(function) => ir::Statement::Function(self.function(function)?),
            ast::StmtKind::Handler(arms) => ir::Statement::Handle {
                definition: self
                    .facts
                    .handlers
                    .iter()
                    .find_map(|handler| {
                        (self.callable_owner.is_some()
                            && handler.callable_owner == self.callable_owner
                            && handler.span == statement.span)
                            .then_some(handler.site)
                            .flatten()
                    })
                    .ok_or_else(|| {
                        unsupported("handler definition requires a verified lexical callable owner")
                    })?
                    .0 as u64,
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(ir::HandlerArm {
                            operation: self
                                .expression_operations
                                .get(&(
                                    arm.operation.span.file.0,
                                    arm.operation.span.start,
                                    arm.operation.span.end,
                                ))
                                .copied()
                                .or_else(|| {
                                    expression_name(&arm.operation)
                                        .and_then(|name| self.operations.get(&name).copied())
                                })
                                .ok_or_else(|| {
                                    unsupported("verified effect operation identity is missing")
                                })?,
                            parameters: arm
                                .parameters
                                .iter()
                                .map(|parameter| self.parameter(parameter))
                                .collect::<Result<_, _>>()?,
                            body: self.expression(&arm.body)?,
                        })
                    })
                    .collect::<Result<_, NotImplemented>>()?,
            },
            ast::StmtKind::Type(_) | ast::StmtKind::Effect(_) | ast::StmtKind::Use(_) => {
                return Ok(None);
            }
            _ => return Err(unsupported("parameterized handler application lowering")),
        }))
    }
    fn pattern(&mut self, pattern: &ast::Pattern) -> Result<ir::Pattern, NotImplemented> {
        Ok(match &pattern.kind {
            ast::PatternKind::Name(name) => ir::Pattern::Name(name.clone()),
            ast::PatternKind::Wildcard => ir::Pattern::Wildcard,
            ast::PatternKind::Literal(literal) => {
                ir::Pattern::Literal(self.literal(literal, pattern.span)?)
            }
            ast::PatternKind::Value(expression) => {
                ir::Pattern::Value(Box::new(self.expression(expression)?))
            }
            ast::PatternKind::Tuple(items) => ir::Pattern::Tuple(
                items
                    .iter()
                    .map(|item| self.pattern(item))
                    .collect::<Result<_, _>>()?,
            ),
            ast::PatternKind::Record {
                rest_binding: Some(_),
                ..
            } => {
                return Err(unsupported(
                    "record-rest lowering requires a standalone closed binding",
                ));
            }
            ast::PatternKind::Record { fields, .. } => ir::Pattern::Record(
                fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), self.pattern(&field.pattern)?)))
                    .collect::<Result<_, NotImplemented>>()?,
            ),
            ast::PatternKind::Constructor {
                path, arguments, ..
            } => ir::Pattern::Constructor {
                tag: path.join("::"),
                arguments: arguments
                    .iter()
                    .map(|argument| self.pattern(argument))
                    .collect::<Result<_, _>>()?,
            },
            ast::PatternKind::Alternative(patterns) => ir::Pattern::Alternative(
                patterns
                    .iter()
                    .map(|pattern| self.pattern(pattern))
                    .collect::<Result<_, _>>()?,
            ),
            ast::PatternKind::Mode { pattern, .. } => self.pattern(pattern)?,
            _ => return Err(unsupported("static or computed pattern lowering")),
        })
    }
    fn runtime_static_key(&self, name: &str, span: Span) -> Result<Option<String>, NotImplemented> {
        let observations: Vec<_> = self
            .facts
            .expressions
            .iter()
            .filter(|fact| fact.span == span)
            .collect();
        let identity = observations.iter().find_map(|fact| {
            if let crate::sema::model::Ty::StaticKey(identity) = &fact.value.ty {
                Some(identity)
            } else {
                None
            }
        });
        let Some(identity) = identity else {
            return Ok(None);
        };
        if !self
            .facts
            .generic_binders
            .values()
            .any(|binder| binder.identity == *identity && binder.name == name)
        {
            return Ok(None);
        }
        if observations.iter().any(|fact| !matches!(&fact.value.ty,crate::sema::model::Ty::StaticKey(other) if other==identity)) {
            return Err(unsupported("static-key value has inconsistent lexical binder evidence"));
        }
        let enclosing: Vec<_> = self
            .facts
            .static_key_parameters
            .iter()
            .filter(|parameter| {
                parameter.binder == *identity
                    && parameter.owner.file == span.file
                    && parameter.owner.start <= span.start
                    && span.end <= parameter.owner.end
            })
            .collect();
        let Some(width) = enclosing
            .iter()
            .map(|parameter| parameter.owner.end - parameter.owner.start)
            .min()
        else {
            return Err(unsupported(
                "static-key value has no certified runtime parameter carrier",
            ));
        };
        let carriers: std::collections::BTreeSet<_> = enclosing
            .into_iter()
            .filter(|parameter| parameter.owner.end - parameter.owner.start == width)
            .map(|parameter| {
                (
                    parameter.owner.start,
                    parameter.owner.end,
                    parameter.parameter,
                    parameter.name.clone(),
                )
            })
            .collect();
        if carriers.len() != 1 {
            return Err(unsupported(
                "static-key runtime carrier is not unique in its lexical owner",
            ));
        }
        Ok(carriers.into_iter().next().map(|(_, _, _, name)| name))
    }
    fn expression(&mut self, expression: &ast::Expr) -> Result<ir::Expr, NotImplemented> {
        if let Some(bound) = self.concurrent_receiver(expression)? {
            return Ok(bound);
        }
        if let Some(proof) = self
            .facts
            .variant_projections
            .get(&(
                expression.span.file.0,
                expression.span.start,
                expression.span.end,
            ))
            .cloned()
        {
            let ast::ExprKind::Field {
                base,
                field,
                safe: false,
            } = &expression.kind
            else {
                return Err(unsupported(
                    "tag projection certificate has no matching field expression",
                ));
            };
            let payload = ir::Expr {
                span: expression.span,
                kind: ir::ExprKind::Call {
                    callback_entry: false,
                    callee: Box::new(ir::Expr {
                        kind: ir::ExprKind::Name("__unwrap_tag".into()),
                        span: expression.span,
                    }),
                    arguments: vec![
                        ir::Argument {
                            label: None,
                            value: self.expression(base)?,
                        },
                        ir::Argument {
                            label: None,
                            value: ir::Expr {
                                kind: ir::ExprKind::Literal(ir::Literal::String(proof.tag)),
                                span: expression.span,
                            },
                        },
                    ],
                },
            };
            return Ok(if proof.direct {
                payload
            } else {
                ir::Expr {
                    span: expression.span,
                    kind: ir::ExprKind::Field {
                        base: Box::new(payload),
                        field: field.clone(),
                        safe: false,
                    },
                }
            });
        }
        let kind = match &expression.kind {
            ast::ExprKind::Interpolated(parts) => {
                let mut values = Vec::new();
                for part in parts {
                    values.push(match part {
                        ast::StringPart::Text(text) => ir::Expr {
                            kind: ir::ExprKind::Literal(ir::Literal::String(text.clone())),
                            span: expression.span,
                        },
                        ast::StringPart::Interpolation {
                            expression,
                            format,
                            span,
                        } => {
                            let mut arguments = vec![ir::Argument {
                                label: None,
                                value: self.expression(expression)?,
                            }];
                            if let Some(format) = format {
                                arguments.push(ir::Argument {
                                    label: None,
                                    value: ir::Expr {
                                        kind: ir::ExprKind::Literal(ir::Literal::String(
                                            format.clone(),
                                        )),
                                        span: *span,
                                    },
                                });
                            }
                            ir::Expr {
                                kind: ir::ExprKind::Call {
                                    callback_entry: false,
                                    callee: Box::new(ir::Expr {
                                        kind: ir::ExprKind::Name(
                                            if format.is_some() {
                                                "__format_spec"
                                            } else {
                                                "__format"
                                            }
                                            .into(),
                                        ),
                                        span: *span,
                                    }),
                                    arguments,
                                },
                                span: *span,
                            }
                        }
                    });
                }
                let mut values = values.into_iter();
                let mut value = values.next().unwrap_or(ir::Expr {
                    kind: ir::ExprKind::Literal(ir::Literal::String(String::new())),
                    span: expression.span,
                });
                for next in values {
                    value = ir::Expr {
                        kind: ir::ExprKind::Binary {
                            operator: "+".into(),
                            left: Box::new(value),
                            right: Box::new(next),
                        },
                        span: expression.span,
                    };
                }
                return Ok(value);
            }
            ast::ExprKind::Literal(ast::Literal::String(text)) => {
                return self.string_expression(text, expression.span);
            }
            ast::ExprKind::Literal(literal) => {
                ir::ExprKind::Literal(self.literal(literal, expression.span)?)
            }
            ast::ExprKind::Name(name) if self.facts.constant_pool.references.contains_key(name) => {
                ir::ExprKind::ConstRef(self.facts.constant_pool.references[name])
            }
            ast::ExprKind::Name(name) if self.specializations.is_template_name(name) => {
                return Err(unsupported(
                    "generic effect callable extraction requires a closed callable-instance certificate",
                ));
            }
            ast::ExprKind::Path(path)
                if self.specializations.is_template_name(&path.join("::")) =>
            {
                return Err(unsupported(
                    "generic effect callable extraction requires a closed callable-instance certificate",
                ));
            }
            ast::ExprKind::Name(name) if self.external_generic_names.contains(name) => {
                return Err(unsupported(
                    "foreign generic callable requires a concrete checked static instance",
                ));
            }
            ast::ExprKind::Path(path) if self.external_generic_names.contains(&path.join("::")) => {
                return Err(unsupported(
                    "foreign generic callable requires a concrete checked static instance",
                ));
            }
            ast::ExprKind::Name(name) => ir::ExprKind::Name(
                self.runtime_static_key(name, expression.span)?
                    .unwrap_or_else(|| name.clone()),
            ),
            ast::ExprKind::Path(path) => ir::ExprKind::Name(path.join("::")),
            ast::ExprKind::Generic { base, .. } => {
                let site = (
                    expression.span.file.0,
                    expression.span.start,
                    expression.span.end,
                );
                let instances: std::collections::BTreeSet<_> = self
                    .facts
                    .external_instances
                    .iter()
                    .filter(|instance| instance.sites.contains(&site))
                    .map(|instance| instance.syntax.name.clone())
                    .collect();
                if instances.len() > 1 {
                    return Err(unsupported(
                        "generic foreign callable has different static instances at one unspecialized source site",
                    ));
                }
                if let Some(name) = instances.into_iter().next() {
                    ir::ExprKind::Name(name)
                } else if let Some(name) = self.specialized_builtins.get(&(
                    expression.span.file.0,
                    expression.span.start,
                    expression.span.end,
                )) {
                    ir::ExprKind::Name(name.clone())
                } else {
                    return self.expression(base);
                }
            }
            ast::ExprKind::Tuple(values) => ir::ExprKind::Tuple(
                values
                    .iter()
                    .map(|value| self.expression(value))
                    .collect::<Result<_, _>>()?,
            ),
            ast::ExprKind::Array(values) => ir::ExprKind::Array(
                values
                    .iter()
                    .map(|value| self.expression(value))
                    .collect::<Result<_, _>>()?,
            ),
            ast::ExprKind::Map(entries) => ir::ExprKind::Map(
                entries
                    .iter()
                    .map(|(key, value)| Ok((self.expression(key)?, self.expression(value)?)))
                    .collect::<Result<_, NotImplemented>>()?,
            ),
            ast::ExprKind::Range {
                start,
                end,
                inclusive,
            } => ir::ExprKind::Range {
                lower: start
                    .as_ref()
                    .map(|value| self.expression(value).map(Box::new))
                    .transpose()?,
                upper: end
                    .as_ref()
                    .map(|value| self.expression(value).map(Box::new))
                    .transpose()?,
                inclusive: *inclusive,
            },
            ast::ExprKind::Record {
                fields,
                spread,
                members,
                ..
            } => ir::ExprKind::Record {
                fields: fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), self.expression(&field.value)?)))
                    .collect::<Result<_, NotImplemented>>()?,
                spread: spread
                    .as_ref()
                    .map(|value| self.expression(value).map(Box::new))
                    .transpose()?,
                members: members
                    .iter()
                    .map(|member| match member {
                        ast::RecordMember::Field(field) => Ok(ir::RecordMember::Field(
                            field.name.clone(),
                            self.expression(&field.value)?,
                        )),
                        ast::RecordMember::Spread(value) => {
                            Ok(ir::RecordMember::Spread(self.expression(value)?))
                        }
                    })
                    .collect::<Result<_, NotImplemented>>()?,
            },
            ast::ExprKind::Unary { operator, operand } => {
                if operator == "?" {
                    let tag = self.propagation_tag(operand.span)?;
                    let temporary = format!("\0ril.propagate.{}", self.next_temporary);
                    self.next_temporary += 1;
                    let value = self.expression(operand)?;
                    let reference = ir::Expr {
                        kind: ir::ExprKind::Name(temporary.clone()),
                        span: operand.span,
                    };
                    return Ok(ir::Expr {
                        kind: ir::ExprKind::Block(ir::Block {
                            statements: vec![
                                ir::Statement::Bind {
                                    pattern: ir::Pattern::Name(temporary),
                                    value,
                                    scoped: false,
                                },
                                ir::Statement::Expr {
                                    expression: ir::Expr {
                                        kind: ir::ExprKind::If {
                                            condition: Box::new(ir::Expr {
                                                kind: ir::ExprKind::Is {
                                                    value: Box::new(reference.clone()),
                                                    pattern: ir::Pattern::Constructor {
                                                        tag: tag.into(),
                                                        arguments: vec![],
                                                    },
                                                },
                                                span: expression.span,
                                            }),
                                            then_branch: Box::new(ir::Expr {
                                                kind: ir::ExprKind::Call {
                                                    callback_entry: false,
                                                    callee: Box::new(ir::Expr {
                                                        kind: ir::ExprKind::Name(
                                                            "__variant_payload".into(),
                                                        ),
                                                        span: expression.span,
                                                    }),
                                                    arguments: vec![ir::Argument {
                                                        label: None,
                                                        value: reference.clone(),
                                                    }],
                                                },
                                                span: expression.span,
                                            }),
                                            else_branch: Some(Box::new(ir::Expr {
                                                kind: ir::ExprKind::Control {
                                                    operation: ir::ControlOperation::Return,
                                                    value: Some(Box::new(reference)),
                                                },
                                                span: expression.span,
                                            })),
                                        },
                                        span: expression.span,
                                    },
                                    terminated: false,
                                },
                            ],
                        }),
                        span: expression.span,
                    });
                }
                if operator == "^mut" {
                    return self.expression(operand);
                }
                if operator == "-"
                    && matches!(
                        operand.kind,
                        ast::ExprKind::Literal(ast::Literal::Integer(_) | ast::Literal::Float(_))
                    )
                    && let Some(literal) =
                        self.selected_numeric_literal(operand.span, Some(expression.span))?
                {
                    return Ok(ir::Expr {
                        kind: ir::ExprKind::Literal(literal),
                        span: expression.span,
                    });
                }
                if operator == "-"
                    && let ast::ExprKind::Literal(ast::Literal::Integer(text)) = &operand.kind
                    && !text.ends_with("bigint")
                {
                    let literal =
                        match self.literal(&ast::Literal::Integer(text.clone()), operand.span)? {
                            ir::Literal::Integer {
                                value,
                                bits,
                                signed,
                            } => ir::Literal::Integer {
                                value: value.checked_neg().ok_or_else(|| {
                                    unsupported("integer literal exceeds supported width")
                                })?,
                                bits,
                                signed,
                            },
                            ir::Literal::BigInteger(value) => {
                                ir::Literal::BigInteger(format!("-{value}"))
                            }
                            _ => return Err(unsupported("invalid verified numeric literal")),
                        };
                    return Ok(ir::Expr {
                        kind: ir::ExprKind::Literal(literal),
                        span: expression.span,
                    });
                }
                ir::ExprKind::Unary {
                    operator: operator.clone(),
                    operand: Box::new(self.expression(operand)?),
                }
            }
            ast::ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "|>"
                    && let ast::ExprKind::Derive { base: None, recipe } = &right.kind
                {
                    return Ok(ir::Expr {
                        kind: ir::ExprKind::Derive {
                            base: Box::new(self.expression(left)?),
                            recipe: Box::new(self.expression(recipe)?),
                        },
                        span: expression.span,
                    });
                }
                if matches!(operator.as_str(), "|>" | "!>") {
                    let temporary = format!("\0ril.pipeline.{}", self.next_temporary);
                    self.next_temporary += 1;
                    let input = self.expression(left)?;
                    let (callee, written) =
                        if let ast::ExprKind::Call { callee, arguments } = &right.kind {
                            (callee.as_ref(), arguments.as_slice())
                        } else {
                            (right.as_ref(), &[][..])
                        };
                    self.record_call_signature(callee.span, expression.span)?;
                    let mut arguments = vec![ir::Argument {
                        label: None,
                        value: ir::Expr {
                            kind: ir::ExprKind::Name(temporary.clone()),
                            span: left.span,
                        },
                    }];
                    for argument in written {
                        arguments.push(ir::Argument {
                            label: argument.label.clone(),
                            value: self.expression(&argument.value)?,
                        });
                    }
                    return Ok(ir::Expr {
                        span: expression.span,
                        kind: ir::ExprKind::Block(ir::Block {
                            statements: vec![
                                ir::Statement::Bind {
                                    pattern: ir::Pattern::Name(temporary),
                                    value: input,
                                    scoped: false,
                                },
                                ir::Statement::Expr {
                                    expression: ir::Expr {
                                        kind: ir::ExprKind::Call {
                                            callback_entry: false,
                                            callee: Box::new(self.expression(callee)?),
                                            arguments,
                                        },
                                        span: expression.span,
                                    },
                                    terminated: false,
                                },
                            ],
                        }),
                    });
                }
                ir::ExprKind::Binary {
                    operator: operator.clone(),
                    left: Box::new(self.expression(left)?),
                    right: Box::new(self.expression(right)?),
                }
            }
            ast::ExprKind::Call { callee, arguments } => {
                if let Some(budget) = self.budget_call(callee, arguments, expression.span)? {
                    budget
                } else {
                    self.record_call_signature(callee.span, expression.span)?;
                    let arguments = arguments
                        .iter()
                        .map(|argument| {
                            Ok(ir::Argument {
                                label: argument.label.clone(),
                                value: self.expression(&argument.value)?,
                            })
                        })
                        .collect::<Result<_, NotImplemented>>()?;
                    if let Some(&operation) = self.expression_operations.get(&(
                        callee.span.file.0,
                        callee.span.start,
                        callee.span.end,
                    )) {
                        if !matches!(
                            callee.kind,
                            ast::ExprKind::Name(_)
                                | ast::ExprKind::Path(_)
                                | ast::ExprKind::Generic { .. }
                        ) && !matches!(&callee.kind, ast::ExprKind::Field { base, safe: false, .. } if matches!(base.kind, ast::ExprKind::Generic { .. }))
                        {
                            return Err(unsupported("computed effect operation callee evaluation"));
                        }
                        ir::ExprKind::Perform {
                            operation,
                            arguments,
                        }
                    } else {
                        let selected = self.specializations.call_target(
                            self.facts,
                            self.callable_owner,
                            self.specialization_context,
                            self.default_context,
                            expression.span,
                        )?;
                        let callee = if let Some((definition, name)) = selected {
                            let mut base = callee.as_ref();
                            while let ast::ExprKind::Generic { base: inner, .. } = &base.kind {
                                base = inner;
                            }
                            let actual = expression_name(base);
                            let declared = self
                                .facts
                                .functions
                                .iter()
                                .find(|info| info.definition == definition)
                                .map(|info| info.syntax.name.as_str());
                            if actual.as_deref() != declared {
                                return Err(unsupported(
                                    "generic effect call requires its exact direct declaration reference",
                                ));
                            }
                            ir::Expr {
                                span: callee.span,
                                kind: ir::ExprKind::Name(name),
                            }
                        } else {
                            self.expression(callee)?
                        };
                        ir::ExprKind::Call {
                            callback_entry: false,
                            callee: Box::new(callee),
                            arguments,
                        }
                    }
                }
            }
            ast::ExprKind::Field {
                base,
                field,
                safe: true,
            } => ir::ExprKind::Call {
                callback_entry: false,
                callee: Box::new(ir::Expr {
                    kind: ir::ExprKind::Name("__safe_field".into()),
                    span: expression.span,
                }),
                arguments: vec![
                    ir::Argument {
                        label: None,
                        value: self.expression(base)?,
                    },
                    ir::Argument {
                        label: None,
                        value: ir::Expr {
                            kind: ir::ExprKind::Literal(ir::Literal::String(field.clone())),
                            span: expression.span,
                        },
                    },
                ],
            },
            ast::ExprKind::Field { base, field, safe } => ir::ExprKind::Field {
                base: Box::new(self.expression(base)?),
                field: field.clone(),
                safe: *safe,
            },
            ast::ExprKind::ComputedField { base, key } => {
                let field = match &key.kind {
                    ast::ExprKind::Literal(ast::Literal::String(text)) => {
                        decode_text(&text[1..text.len() - 1])?
                    }
                    ast::ExprKind::Literal(ast::Literal::RawString(text)) => {
                        text[1..text.len() - 1].to_owned()
                    }
                    ast::ExprKind::Literal(ast::Literal::Integer(text)) => {
                        let ir::Literal::Integer { value, .. } = self.integer(text)? else {
                            return Err(unsupported("tuple coordinate must be a verified integer"));
                        };
                        value.to_string()
                    }
                    ast::ExprKind::Interpolated(parts)
                        if parts
                            .iter()
                            .all(|part| matches!(part, ast::StringPart::Text(_))) =>
                    {
                        parts
                            .iter()
                            .filter_map(|part| {
                                if let ast::StringPart::Text(text) = part {
                                    Some(text.as_str())
                                } else {
                                    None
                                }
                            })
                            .collect()
                    }
                    _ => {
                        return Ok(ir::Expr {
                            span: expression.span,
                            kind: ir::ExprKind::Call {
                                callback_entry: false,
                                callee: Box::new(ir::Expr {
                                    kind: ir::ExprKind::Name("__computed_field".into()),
                                    span: expression.span,
                                }),
                                arguments: vec![
                                    ir::Argument {
                                        label: None,
                                        value: self.expression(base)?,
                                    },
                                    ir::Argument {
                                        label: None,
                                        value: self.expression(key)?,
                                    },
                                ],
                            },
                        });
                    }
                };
                ir::ExprKind::Field {
                    base: Box::new(self.expression(base)?),
                    field,
                    safe: false,
                }
            }
            ast::ExprKind::Index { base, index, safe } => ir::ExprKind::Index {
                base: Box::new(self.expression(base)?),
                index: Box::new(self.expression(index)?),
                safe: *safe,
            },
            ast::ExprKind::Lambda {
                parameters, body, ..
            } => {
                let owner = self
                    .facts
                    .closure_sites
                    .iter()
                    .find(|site| {
                        Some(site.owner) == self.callable_owner && site.span == expression.span
                    })
                    .map(|site| CallableOwner::Lambda(site.id));
                let (parameters, body) = if let Some(index) = self.specialization_context {
                    let Some(CallableOwner::Lambda(site)) = owner else {
                        return Err(unsupported(
                            "specialized closure has no source lexical identity",
                        ));
                    };
                    if parameters
                        .iter()
                        .any(|parameter| parameter.default.is_some())
                    {
                        return Err(unsupported(
                            "specialized closure defaults require their evaluation identity",
                        ));
                    }
                    let facts = self
                        .specializations
                        .closure_facts(self.all_facts, index, site)?;
                    let mut nested = Lower {
                        specializations: self.specializations,
                        specialization_context: Some(index),
                        default_context: None,
                        nonretaining_adapters: vec![],
                        callable_owner: owner,
                        external_generic_names: self.external_generic_names.clone(),
                        facts: &facts,
                        all_facts: self.all_facts,
                        call_signatures: vec![],
                        layout: self.layout,
                        definitions: self.definitions,
                        next_definition: self.next_definition,
                        next_temporary: self.next_temporary,
                        generic_types: self.generic_types.clone(),
                        contextual_types: &facts.contextual_types,
                        specialized_builtins: specialize::builtins(&facts)?,
                        operations: self.operations.clone(),
                        expression_operations: self
                            .specializations
                            .closure_operations(index, site)?,
                        implicit_unwraps: &facts.implicit_unwraps,
                    };
                    let parameters = parameters
                        .iter()
                        .map(|parameter| nested.parameter(parameter))
                        .collect::<Result<_, _>>()?;
                    let body = Box::new(nested.expression(body)?);
                    self.next_definition = nested.next_definition;
                    self.next_temporary = nested.next_temporary;
                    self.call_signatures.extend(nested.call_signatures);
                    if !nested.nonretaining_adapters.is_empty() {
                        return Err(unsupported(
                            "specialized closure builtin adapters require their owner mapping",
                        ));
                    }
                    (parameters, body)
                } else {
                    let previous_owner = std::mem::replace(&mut self.callable_owner, owner);
                    let parameters = parameters
                        .iter()
                        .map(|parameter| self.parameter(parameter))
                        .collect::<Result<_, _>>()?;
                    let body = Box::new(self.expression(body)?);
                    self.callable_owner = previous_owner;
                    (parameters, body)
                };
                ir::ExprKind::Lambda { parameters, body }
            }
            ast::ExprKind::Block(block) => ir::ExprKind::Block(self.block(block)?),
            ast::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => ir::ExprKind::If {
                condition: Box::new(self.expression(condition)?),
                then_branch: Box::new(self.expression(then_branch)?),
                else_branch: else_branch
                    .as_ref()
                    .map(|branch| self.expression(branch).map(Box::new))
                    .transpose()?,
            },
            ast::ExprKind::Match {
                value,
                arms,
                type_match,
            } => {
                if *type_match {
                    return Err(unsupported("static type match lowering"));
                }
                ir::ExprKind::Match {
                    value: Box::new(self.expression(value)?),
                    arms: arms
                        .iter()
                        .map(|arm| {
                            Ok(ir::MatchArm {
                                pattern: self.pattern(&arm.pattern)?,
                                guard: arm
                                    .guard
                                    .as_ref()
                                    .map(|guard| self.expression(guard))
                                    .transpose()?,
                                body: self.expression(&arm.body)?,
                            })
                        })
                        .collect::<Result<_, NotImplemented>>()?,
                }
            }
            ast::ExprKind::Is { value, pattern } => ir::ExprKind::Is {
                value: Box::new(self.expression(value)?),
                pattern: self.pattern(pattern)?,
            },
            ast::ExprKind::Loop(block) => ir::ExprKind::Loop {
                body: self.block(block)?,
                charge: Some(ir::ChargeEvent::LoopIteration),
            },
            ast::ExprKind::While { condition, body } => ir::ExprKind::While {
                charge: Some(ir::ChargeEvent::LoopIteration),
                condition: Box::new(self.expression(condition)?),
                body: self.block(body)?,
            },
            ast::ExprKind::For {
                iterable,
                pattern,
                body,
            } => ir::ExprKind::For {
                charge: Some(ir::ChargeEvent::LoopIteration),
                iterable: Box::new(self.expression(iterable)?),
                pattern: self.pattern(pattern)?,
                body: self.block(body)?,
            },
            ast::ExprKind::Control { operation, value } => ir::ExprKind::Control {
                operation: match operation {
                    ast::ControlOperation::Return => ir::ControlOperation::Return,
                    ast::ControlOperation::Last => ir::ControlOperation::Last,
                    ast::ControlOperation::Next => ir::ControlOperation::Next,
                    ast::ControlOperation::Resume => ir::ControlOperation::Resume,
                },
                value: value
                    .as_ref()
                    .map(|value| self.expression(value).map(Box::new))
                    .transpose()?,
            },
            ast::ExprKind::Derive {
                base: Some(base),
                recipe,
            } => ir::ExprKind::Derive {
                base: Box::new(self.expression(base)?),
                recipe: Box::new(self.expression(recipe)?),
            },
            _ => {
                return Err(unsupported(format!(
                    "expression lowering at {}:{}",
                    expression.span.file.0, expression.span.start
                )));
            }
        };
        let mut lowered = ir::Expr {
            kind,
            span: expression.span,
        };
        if let Some(proof) = self.implicit_unwraps.get(&(
            expression.span.file.0,
            expression.span.start,
            expression.span.end,
        )) {
            if proof.tags.len() != proof.depth as usize {
                return Err(unsupported(
                    "implicit projection certificate has an incomplete tag sequence",
                ));
            }
            for tag in &proof.tags {
                lowered = ir::Expr {
                    kind: ir::ExprKind::Call {
                        callback_entry: false,
                        callee: Box::new(ir::Expr {
                            kind: ir::ExprKind::Name("__unwrap_tag".into()),
                            span: expression.span,
                        }),
                        arguments: vec![
                            ir::Argument {
                                label: None,
                                value: lowered,
                            },
                            ir::Argument {
                                label: None,
                                value: ir::Expr {
                                    kind: ir::ExprKind::Literal(ir::Literal::String(tag.clone())),
                                    span: expression.span,
                                },
                            },
                        ],
                    },
                    span: expression.span,
                };
            }
        }
        Ok(lowered)
    }
    fn literal(&self, literal: &ast::Literal, span: Span) -> Result<ir::Literal, NotImplemented> {
        if matches!(literal, ast::Literal::Integer(_) | ast::Literal::Float(_))
            && let Some(selected) = self.selected_numeric_literal(span, None)?
        {
            return Ok(selected);
        }
        let context = self
            .contextual_types
            .get(&(span.file.0, span.start, span.end));
        Ok(match literal {
            ast::Literal::Unit => ir::Literal::Unit,
            ast::Literal::Bool(value) => ir::Literal::Bool(*value),
            ast::Literal::Integer(text) => {
                if let Some(digits) = text.strip_suffix("bigint") {
                    ir::Literal::BigInteger(digits.replace('_', ""))
                } else if !["int", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8"]
                    .iter()
                    .any(|suffix| text.ends_with(suffix))
                    && let Some(crate::sema::model::Ty::Int(name)) = context
                {
                    if name == "bigint" {
                        ir::Literal::BigInteger(text.replace('_', ""))
                    } else {
                        self.integer(&format!("{text}{name}"))?
                    }
                } else {
                    self.integer(text)?
                }
            }
            ast::Literal::Float(text) => {
                match crate::static_eval::committed_float::decode(text) {
                    Ok(Some(committed)) => {
                        return Ok(ir::Literal::Float {
                            value: committed.value(),
                            bits: committed.width,
                        });
                    }
                    Err(()) => {
                        return Err(unsupported(
                            "invalid committed floating-point literal witness",
                        ));
                    }
                    Ok(None) => {}
                }
                let (text, bits) = if let Some(value) = text.strip_suffix("f32") {
                    (value, 32)
                } else {
                    let bits = if !text.ends_with("f64")
                        && matches!(context, Some(crate::sema::model::Ty::Float(name)) if name == "f32")
                    {
                        32
                    } else {
                        64
                    };
                    (text.strip_suffix("f64").unwrap_or(text), bits)
                };
                ir::Literal::Float {
                    value: if bits == 32 {
                        f64::from(
                            text.replace('_', "")
                                .parse::<f32>()
                                .map_err(|_| unsupported("invalid floating literal"))?,
                        )
                    } else {
                        text.replace('_', "")
                            .parse::<f64>()
                            .map_err(|_| unsupported("invalid floating literal"))?
                    },
                    bits,
                }
            }
            ast::Literal::String(text) => {
                ir::Literal::String(decode_text(&text[1..text.len() - 1])?)
            }
            ast::Literal::RawString(text) => ir::Literal::String(text[1..text.len() - 1].into()),
            ast::Literal::Bytes(text) => {
                ir::Literal::Bytes(decode_bytes(&text[2..text.len() - 1])?)
            }
        })
    }
    fn selected_numeric_literal(
        &self,
        span: Span,
        immediate_minus: Option<Span>,
    ) -> Result<Option<ir::Literal>, NotImplemented> {
        let mut selected = None;
        for fact in &self.facts.numeric_selections {
            if fact.span != span || fact.context.owner != self.callable_owner {
                continue;
            }
            let usage = self
                .all_facts
                .numeric_uses
                .get(fact.literal.0 as usize)
                .filter(|usage| {
                    usage.id == fact.literal && usage.context == fact.context && usage.span == span
                })
                .ok_or_else(|| {
                    unsupported("numeric selection has no matching actual literal use")
                })?;
            if usage.immediate_minus != immediate_minus {
                return Err(unsupported(
                    "numeric literal sign must be consumed at its proved unary boundary",
                ));
            }
            if selected.as_ref().is_some_and(
                |previous: &&crate::sema::numeric_selection::NumericSelection| {
                    previous.ty != fact.ty || previous.encoded != fact.encoded
                },
            ) {
                return Err(unsupported(
                    "one emitted numeric literal has incompatible actual selections",
                ));
            }
            selected = Some(fact);
        }
        if selected.is_none()
            && self
                .all_facts
                .numeric_uses
                .iter()
                .any(|usage| usage.span == span && usage.context.owner == self.callable_owner)
        {
            return Err(unsupported(
                "numeric literal lacks a selection in its actual invocation view",
            ));
        }
        Ok(selected.map(|selection| match &selection.encoded {
            crate::numeric_literals::EncodedNumber::Integer {
                value,
                bits,
                signed,
                ..
            } => ir::Literal::Integer {
                value: *value,
                bits: *bits,
                signed: *signed,
            },
            crate::numeric_literals::EncodedNumber::BigInteger(value) => {
                ir::Literal::BigInteger(value.to_string())
            }
            crate::numeric_literals::EncodedNumber::Float(value) => ir::Literal::Float {
                value: value.as_f64(),
                bits: match value.format() {
                    crate::numeric_literals::FloatFormat::F32 => 32,
                    crate::numeric_literals::FloatFormat::F64 => 64,
                },
            },
        }))
    }
    fn propagation_tag(&self, span: Span) -> Result<&'static str, NotImplemented> {
        fn family(ty: &crate::sema::model::Ty) -> Option<&'static str> {
            match ty {
                crate::sema::model::Ty::Optional(_) => Some("Prelude::Some"),
                crate::sema::model::Ty::Result(..) => Some("Prelude::Ok"),
                crate::sema::model::Ty::Immutable(inner) => family(inner),
                _ => None,
            }
        }
        let mut proven = None;
        for fact in self.facts.expressions_at(span) {
            let tag = family(&fact.value.ty)
                .ok_or_else(|| unsupported("propagation receiver family is not materialized"))?;
            if proven.is_some_and(|previous| previous != tag) {
                return Err(unsupported(
                    "propagation receiver needs distinct family specializations",
                ));
            }
            proven = Some(tag);
        }
        proven.ok_or_else(|| unsupported("verified propagation receiver is missing"))
    }
    fn integer(&self, text: &str) -> Result<ir::Literal, NotImplemented> {
        let mut digits = text;
        let (mut bits, mut signed) = (self.layout.pointer_bits, true);
        for suffix in [
            "bigint", "int", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
        ] {
            if let Some(value) = text.strip_suffix(suffix) {
                digits = value;
                if suffix == "bigint" {
                    return Err(unsupported("bigint native literal"));
                }
                if suffix != "int" {
                    signed = suffix.starts_with('i');
                    bits = suffix[1..].parse().unwrap();
                }
                break;
            }
        }
        let digits = digits.replace('_', "");
        let (radix, digits) = if let Some(digits) = digits
            .strip_prefix("0x")
            .or_else(|| digits.strip_prefix("0X"))
        {
            (16, digits)
        } else if let Some(digits) = digits
            .strip_prefix("0o")
            .or_else(|| digits.strip_prefix("0O"))
        {
            (8, digits)
        } else if let Some(digits) = digits
            .strip_prefix("0b")
            .or_else(|| digits.strip_prefix("0B"))
        {
            (2, digits)
        } else {
            (10, digits.as_str())
        };
        let value = i128::from_str_radix(digits, radix)
            .map_err(|_| unsupported("integer literal exceeds supported width"))?;
        Ok(ir::Literal::Integer {
            value,
            bits,
            signed,
        })
    }
    fn string_expression(&mut self, text: &str, span: Span) -> Result<ir::Expr, NotImplemented> {
        // The parser owns interpolation expressions. A literal's Unicode escape
        // braces must never be reparsed as an interpolation delimiter.
        Ok(ir::Expr {
            span,
            kind: ir::ExprKind::Literal(ir::Literal::String(decode_text(
                &text[1..text.len() - 1],
            )?)),
        })
    }
}
fn binding_test(pattern: &ir::Pattern) -> ir::Pattern {
    match pattern {
        ir::Pattern::Name(_) => ir::Pattern::Wildcard,
        ir::Pattern::Tuple(items) => ir::Pattern::Tuple(items.iter().map(binding_test).collect()),
        ir::Pattern::Record(fields) => ir::Pattern::Record(
            fields
                .iter()
                .map(|(name, value)| (name.clone(), binding_test(value)))
                .collect(),
        ),
        ir::Pattern::Constructor { tag, arguments } => ir::Pattern::Constructor {
            tag: tag.clone(),
            arguments: arguments.iter().map(binding_test).collect(),
        },
        ir::Pattern::Alternative(items) => {
            ir::Pattern::Alternative(items.iter().map(binding_test).collect())
        }
        other => other.clone(),
    }
}

fn expression_name(expression: &ast::Expr) -> Option<String> {
    match &expression.kind {
        ast::ExprKind::Name(name) => Some(name.clone()),
        ast::ExprKind::Path(path) => Some(path.join("::")),
        _ => None,
    }
}
pub(crate) fn decode_text(text: &str) -> Result<String, NotImplemented> {
    let mut chars = text.chars().peekable();
    let mut result = String::new();
    while let Some(c) = chars.next() {
        if c != '\\' {
            if matches!(c, '{' | '}') && chars.peek() == Some(&c) {
                chars.next();
            }
            result.push(c);
            continue;
        }
        result.push(match chars.next() {
            Some('n') => '\n',
            Some('r') => '\r',
            Some('t') => '\t',
            Some('0') => '\0',
            Some('\\') => '\\',
            Some('"') => '"',
            Some('u') => {
                if chars.next() != Some('{') {
                    return Err(unsupported("invalid unicode escape"));
                }
                let mut digits = String::new();
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                    digits.push(c);
                }
                char::from_u32(
                    u32::from_str_radix(&digits, 16)
                        .map_err(|_| unsupported("invalid unicode scalar"))?,
                )
                .ok_or_else(|| unsupported("invalid unicode scalar"))?
            }
            _ => return Err(unsupported("invalid text escape")),
        });
    }
    Ok(result)
}
pub(crate) fn decode_bytes(text: &str) -> Result<Vec<u8>, NotImplemented> {
    let mut chars = text.chars();
    let mut result = Vec::new();
    while let Some(c) = chars.next() {
        if c != '\\' {
            result.push(u8::try_from(c as u32).map_err(|_| unsupported("invalid byte literal"))?);
            continue;
        }
        result.push(match chars.next() {
            Some('n') => b'\n',
            Some('r') => b'\r',
            Some('t') => b'\t',
            Some('0') => 0,
            Some('\\') => b'\\',
            Some('"') => b'"',
            Some('x') => {
                let digits = chars.by_ref().take(2).collect::<String>();
                u8::from_str_radix(&digits, 16).map_err(|_| unsupported("invalid byte escape"))?
            }
            _ => return Err(unsupported("invalid byte escape")),
        });
    }
    Ok(result)
}
