//! Give every lexical binding a separate native continuation-environment slot.
use super::*;
type Env = BTreeMap<String, String>;
pub(super) fn function(source: &core::Function) -> Result<core::Function, NotImplemented> {
    let mut rename = Rename {
        next: 0,
        prefix: source.name.clone(),
    };
    let mut env = Env::new();
    let mut function = source.clone();
    for parameter in &mut function.parameters {
        if let Some(default) = &mut parameter.default {
            *default = rename.expr(default, &env)?;
        }
        parameter.pattern = rename.binding(&parameter.pattern, &mut env);
    }
    function.body = rename.block_scope(
        &source.body,
        &env,
        source.name == ril_ir::native::GLOBAL_INITIALIZER,
    )?;
    Ok(function)
}
struct Rename {
    next: u32,
    prefix: String,
}
impl Rename {
    fn binding(&mut self, pattern: &Pattern, env: &mut Env) -> Pattern {
        self.binding_mode(pattern, env, false)
    }
    fn slot(&mut self, name: &str, preserve: bool) -> String {
        if preserve {
            return name.into();
        }
        let slot = format!("\0ril.cps.slot.{}.{}", self.prefix, self.next);
        self.next += 1;
        slot
    }
    fn binding_mode(&mut self, pattern: &Pattern, env: &mut Env, preserve: bool) -> Pattern {
        match pattern {
            Pattern::Name(name) => {
                let slot = self.slot(name, preserve);
                env.insert(name.clone(), slot.clone());
                Pattern::Name(slot)
            }
            Pattern::Rest(Some(name)) => {
                let slot = self.slot(name, preserve);
                env.insert(name.clone(), slot.clone());
                Pattern::Rest(Some(slot))
            }
            Pattern::Array(items) => Pattern::Array(
                items
                    .iter()
                    .map(|pattern| self.binding_mode(pattern, env, preserve))
                    .collect(),
            ),
            Pattern::RecordRest { fields, rest } => {
                let fields = fields
                    .iter()
                    .map(|(name, pattern)| {
                        (name.clone(), self.binding_mode(pattern, env, preserve))
                    })
                    .collect();
                let slot = self.slot(rest, preserve);
                env.insert(rest.clone(), slot.clone());
                Pattern::RecordRest { fields, rest: slot }
            }
            Pattern::Tuple(items) => Pattern::Tuple(
                items
                    .iter()
                    .map(|pattern| self.binding_mode(pattern, env, preserve))
                    .collect(),
            ),
            Pattern::Record(fields) => Pattern::Record(
                fields
                    .iter()
                    .map(|(name, pattern)| {
                        (name.clone(), self.binding_mode(pattern, env, preserve))
                    })
                    .collect(),
            ),
            Pattern::Constructor { tag, arguments } => Pattern::Constructor {
                tag: tag.clone(),
                arguments: arguments
                    .iter()
                    .map(|pattern| self.binding_mode(pattern, env, preserve))
                    .collect(),
            },
            // Binding alternatives must name the same slots. The source checker
            // certifies their binder sets; this pass keeps those identities.
            Pattern::Alternative(items) => {
                let mut names = BTreeSet::new();
                for item in items {
                    pattern_names(item, &mut names);
                }
                for name in names {
                    let slot = self.slot(&name, preserve);
                    env.insert(name, slot);
                }
                Pattern::Alternative(
                    items
                        .iter()
                        .map(|pattern| Self::bound_pattern(pattern, env))
                        .collect(),
                )
            }
            other => other.clone(),
        }
    }
    fn bound_pattern(pattern: &Pattern, env: &Env) -> Pattern {
        match pattern {
            Pattern::Name(name) => Pattern::Name(env.get(name).unwrap_or(name).clone()),
            Pattern::Rest(Some(name)) => Pattern::Rest(Some(env.get(name).unwrap_or(name).clone())),
            Pattern::Array(items) => Pattern::Array(
                items
                    .iter()
                    .map(|pattern| Self::bound_pattern(pattern, env))
                    .collect(),
            ),
            Pattern::RecordRest { fields, rest } => Pattern::RecordRest {
                fields: fields
                    .iter()
                    .map(|(name, pattern)| (name.clone(), Self::bound_pattern(pattern, env)))
                    .collect(),
                rest: env.get(rest).unwrap_or(rest).clone(),
            },
            Pattern::Tuple(items) => Pattern::Tuple(
                items
                    .iter()
                    .map(|pattern| Self::bound_pattern(pattern, env))
                    .collect(),
            ),
            Pattern::Record(fields) => Pattern::Record(
                fields
                    .iter()
                    .map(|(name, pattern)| (name.clone(), Self::bound_pattern(pattern, env)))
                    .collect(),
            ),
            Pattern::Constructor { tag, arguments } => Pattern::Constructor {
                tag: tag.clone(),
                arguments: arguments
                    .iter()
                    .map(|pattern| Self::bound_pattern(pattern, env))
                    .collect(),
            },
            Pattern::Alternative(items) => Pattern::Alternative(
                items
                    .iter()
                    .map(|pattern| Self::bound_pattern(pattern, env))
                    .collect(),
            ),
            other => other.clone(),
        }
    }
    fn test_pattern(&mut self, pattern: &Pattern, env: &Env) -> Result<Pattern, NotImplemented> {
        Ok(match pattern {
            Pattern::Value(value) => Pattern::Value(Box::new(self.expr(value, env)?)),
            Pattern::Name(name) => Pattern::Name(env.get(name).unwrap_or(name).clone()),
            Pattern::Rest(binding) => Pattern::Rest(
                binding
                    .as_ref()
                    .map(|name| env.get(name).unwrap_or(name).clone()),
            ),
            Pattern::Array(items) => Pattern::Array(
                items
                    .iter()
                    .map(|item| self.test_pattern(item, env))
                    .collect::<Result<_, _>>()?,
            ),
            Pattern::RecordRest { fields, rest } => Pattern::RecordRest {
                fields: fields
                    .iter()
                    .map(|(name, pattern)| Ok((name.clone(), self.test_pattern(pattern, env)?)))
                    .collect::<Result<_, NotImplemented>>()?,
                rest: env.get(rest).unwrap_or(rest).clone(),
            },
            Pattern::Tuple(items) => Pattern::Tuple(
                items
                    .iter()
                    .map(|item| self.test_pattern(item, env))
                    .collect::<Result<_, _>>()?,
            ),
            Pattern::Record(fields) => Pattern::Record(
                fields
                    .iter()
                    .map(|(name, pattern)| Ok((name.clone(), self.test_pattern(pattern, env)?)))
                    .collect::<Result<_, NotImplemented>>()?,
            ),
            Pattern::Constructor { tag, arguments } => Pattern::Constructor {
                tag: tag.clone(),
                arguments: arguments
                    .iter()
                    .map(|item| self.test_pattern(item, env))
                    .collect::<Result<_, _>>()?,
            },
            Pattern::Alternative(items) => Pattern::Alternative(
                items
                    .iter()
                    .map(|item| self.test_pattern(item, env))
                    .collect::<Result<_, _>>()?,
            ),
            other => other.clone(),
        })
    }
    fn block(&mut self, block: &core::Block, outer: &Env) -> Result<core::Block, NotImplemented> {
        self.block_scope(block, outer, false)
    }
    fn block_scope(
        &mut self,
        block: &core::Block,
        outer: &Env,
        preserve: bool,
    ) -> Result<core::Block, NotImplemented> {
        let mut env = outer.clone();
        let mut statements = vec![];
        let hoisted = block
            .statements
            .iter()
            .any(|statement| matches!(statement, Statement::Function(_)));
        if hoisted {
            for statement in &block.statements {
                match statement {
                    Statement::Bind { pattern, .. } => {
                        self.binding_mode(pattern, &mut env, preserve);
                    }
                    Statement::Function(function) => {
                        self.binding_mode(
                            &Pattern::Name(function.name.clone()),
                            &mut env,
                            preserve,
                        );
                    }
                    _ => {}
                }
            }
        }
        for statement in &block.statements {
            statements.push(match statement {
                Statement::Bind {
                    pattern,
                    value,
                    scoped,
                } => {
                    let value = self.expr(value, &env)?;
                    let pattern = if hoisted {
                        Self::bound_pattern(pattern, &env)
                    } else {
                        self.binding_mode(pattern, &mut env, preserve)
                    };
                    Statement::Bind {
                        pattern,
                        value,
                        scoped: *scoped,
                    }
                }
                Statement::Assign {
                    target,
                    operator,
                    value,
                } => Statement::Assign {
                    target: self.expr(target, &env)?,
                    operator: operator.clone(),
                    value: self.expr(value, &env)?,
                },
                Statement::Expr {
                    expression,
                    terminated,
                } => Statement::Expr {
                    expression: self.expr(expression, &env)?,
                    terminated: *terminated,
                },
                Statement::Handle { definition, arms } => {
                    let mut renamed = vec![];
                    for arm in arms {
                        let mut own = env.clone();
                        let mut parameters = arm.parameters.clone();
                        for parameter in &mut parameters {
                            parameter.pattern = self.binding(&parameter.pattern, &mut own);
                        }
                        renamed.push(core::HandlerArm {
                            operation: arm.operation,
                            parameters,
                            body: self.expr(&arm.body, &own)?,
                        });
                    }
                    Statement::Handle {
                        definition: *definition,
                        arms: renamed,
                    }
                }
                Statement::Function(function) => {
                    let mut child = function.clone();
                    child.name = env[&function.name].clone();
                    let mut own = env.clone();
                    for parameter in &mut child.parameters {
                        if let Some(default) = &mut parameter.default {
                            *default = self.expr(default, &own)?;
                        }
                        parameter.pattern = self.binding(&parameter.pattern, &mut own);
                    }
                    child.body = self.block(&function.body, &own)?;
                    Statement::Function(child)
                }
            });
        }
        Ok(core::Block { statements })
    }
    fn expr(&mut self, expr: &Expr, env: &Env) -> Result<Expr, NotImplemented> {
        let kind = match &expr.kind {
            ExprKind::ConstRef(reference) => ExprKind::ConstRef(*reference),
            ExprKind::Budget {
                limit,
                action,
                exhaustion_operation,
                coverage,
            } => ExprKind::Budget {
                limit: Box::new(self.expr(limit, env)?),
                action: Box::new(self.expr(action, env)?),
                exhaustion_operation: *exhaustion_operation,
                coverage: *coverage,
            },
            ExprKind::Charge(event) => ExprKind::Charge(*event),
            ExprKind::Name(name) => ExprKind::Name(env.get(name).unwrap_or(name).clone()),
            ExprKind::Literal(value) => ExprKind::Literal(value.clone()),
            ExprKind::Tuple(items) => ExprKind::Tuple(self.items(items, env)?),
            ExprKind::Array(items) => ExprKind::Array(self.items(items, env)?),
            ExprKind::Map(items) => ExprKind::Map(
                items
                    .iter()
                    .map(|(key, value)| Ok((self.expr(key, env)?, self.expr(value, env)?)))
                    .collect::<Result<_, NotImplemented>>()?,
            ),
            ExprKind::Range {
                lower,
                upper,
                inclusive,
            } => ExprKind::Range {
                lower: lower
                    .as_ref()
                    .map(|value| self.expr(value, env).map(Box::new))
                    .transpose()?,
                upper: upper
                    .as_ref()
                    .map(|value| self.expr(value, env).map(Box::new))
                    .transpose()?,
                inclusive: *inclusive,
            },
            ExprKind::Record { members } => ExprKind::Record {
                members: members
                    .iter()
                    .map(|member| {
                        Ok(match member {
                            core::RecordMember::Field(key, value) => {
                                core::RecordMember::Field(key.clone(), self.expr(value, env)?)
                            }
                            core::RecordMember::Spread(value) => {
                                core::RecordMember::Spread(self.expr(value, env)?)
                            }
                        })
                    })
                    .collect::<Result<_, NotImplemented>>()?,
            },
            ExprKind::Unary { operator, operand } => ExprKind::Unary {
                operator: operator.clone(),
                operand: Box::new(self.expr(operand, env)?),
            },
            ExprKind::Binary {
                operator,
                left,
                right,
            } => ExprKind::Binary {
                operator: operator.clone(),
                left: Box::new(self.expr(left, env)?),
                right: Box::new(self.expr(right, env)?),
            },
            ExprKind::Call {
                callee,
                arguments,
                callback_entry,
            } => ExprKind::Call {
                callback_entry: *callback_entry,
                callee: Box::new(self.expr(callee, env)?),
                arguments: self.arguments(arguments, env)?,
            },
            ExprKind::Perform {
                operation,
                arguments,
            } => ExprKind::Perform {
                operation: *operation,
                arguments: self.arguments(arguments, env)?,
            },
            ExprKind::Field { base, field, safe } => ExprKind::Field {
                base: Box::new(self.expr(base, env)?),
                field: field.clone(),
                safe: *safe,
            },
            ExprKind::Index { base, index, safe } => ExprKind::Index {
                base: Box::new(self.expr(base, env)?),
                index: Box::new(self.expr(index, env)?),
                safe: *safe,
            },
            ExprKind::Block(block) => ExprKind::Block(self.block(block, env)?),
            ExprKind::Lambda { parameters, body } => {
                let mut own = env.clone();
                let mut parameters = parameters.clone();
                for parameter in &mut parameters {
                    if let Some(default) = &mut parameter.default {
                        *default = self.expr(default, &own)?;
                    }
                    parameter.pattern = self.binding(&parameter.pattern, &mut own);
                }
                ExprKind::Lambda {
                    parameters,
                    body: Box::new(self.expr(body, &own)?),
                }
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => ExprKind::If {
                condition: Box::new(self.expr(condition, env)?),
                then_branch: Box::new(self.expr(then_branch, env)?),
                else_branch: else_branch
                    .as_ref()
                    .map(|value| self.expr(value, env).map(Box::new))
                    .transpose()?,
            },
            ExprKind::Is { value, pattern } => ExprKind::Is {
                value: Box::new(self.expr(value, env)?),
                pattern: self.test_pattern(pattern, env)?,
            },
            ExprKind::Match { value, arms } => {
                let value = Box::new(self.expr(value, env)?);
                let mut renamed = vec![];
                for arm in arms {
                    let mut own = env.clone();
                    let pattern = self.binding(&arm.pattern, &mut own);
                    renamed.push(core::MatchArm {
                        pattern,
                        guard: arm
                            .guard
                            .as_ref()
                            .map(|guard| self.expr(guard, &own))
                            .transpose()?,
                        body: self.expr(&arm.body, &own)?,
                    });
                }
                ExprKind::Match {
                    value,
                    arms: renamed,
                }
            }
            ExprKind::While {
                condition,
                body,
                charge,
            } => ExprKind::While {
                charge: *charge,
                condition: Box::new(self.expr(condition, env)?),
                body: self.block(body, env)?,
            },
            ExprKind::Loop { body, charge } => ExprKind::Loop {
                body: self.block(body, env)?,
                charge: *charge,
            },
            ExprKind::For {
                iterable,
                pattern,
                body,
                charge,
            } => {
                let iterable = Box::new(self.expr(iterable, env)?);
                let mut own = env.clone();
                let pattern = self.binding(pattern, &mut own);
                ExprKind::For {
                    charge: *charge,
                    iterable,
                    pattern,
                    body: self.block(body, &own)?,
                }
            }
            ExprKind::Control { operation, value } => ExprKind::Control {
                operation: *operation,
                value: value
                    .as_ref()
                    .map(|value| self.expr(value, env).map(Box::new))
                    .transpose()?,
            },
            ExprKind::Derive { base, recipe } => ExprKind::Derive {
                base: Box::new(self.expr(base, env)?),
                recipe: Box::new(self.expr(recipe, env)?),
            },
        };
        Ok(expression(kind, expr.span))
    }
    fn items(&mut self, items: &[Expr], env: &Env) -> Result<Vec<Expr>, NotImplemented> {
        items.iter().map(|value| self.expr(value, env)).collect()
    }
    fn arguments(
        &mut self,
        args: &[core::Argument],
        env: &Env,
    ) -> Result<Vec<core::Argument>, NotImplemented> {
        args.iter()
            .map(|argument| {
                Ok(core::Argument {
                    label: argument.label.clone(),
                    value: self.expr(&argument.value, env)?,
                })
            })
            .collect()
    }
}
