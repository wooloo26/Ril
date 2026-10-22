//! The only AST-to-HIR allocation boundary. Every recursive syntax category
//! has an exhaustive match, and every occurrence receives an arena ID.
use super::*;

struct Lower<'a> {
    hir: &'a mut HirProgram,
    left: HirLimits,
    origin: NodeOrigin,
}
impl Lower<'_> {
    fn enter(&mut self, depth: usize) -> Result<(), LowerError> {
        if depth >= self.left.depth {
            return Err(LowerError::Budget("depth"));
        }
        self.left.nodes = self
            .left
            .nodes
            .checked_sub(1)
            .ok_or(LowerError::Budget("node"))?;
        Ok(())
    }
    fn text(&mut self, value: &str) -> Result<String, LowerError> {
        self.left.text_items = self
            .left
            .text_items
            .checked_sub(1)
            .ok_or(LowerError::Budget("text item"))?;
        let cost = value
            .len()
            .checked_add(1)
            .ok_or(LowerError::Budget("text"))?;
        self.left.text_bytes = self
            .left
            .text_bytes
            .checked_sub(cost)
            .ok_or(LowerError::Budget("text"))?;
        Ok(value.to_owned())
    }
    fn optional_text(&mut self, value: Option<&str>) -> Result<Option<String>, LowerError> {
        value.map(|value| self.text(value)).transpose()
    }
    fn path(&mut self, path: &[String]) -> Result<Vec<String>, LowerError> {
        path.iter().map(|part| self.text(part)).collect()
    }
    fn info(&self, span: Span, owner: LexicalOwner) -> NodeInfo {
        NodeInfo {
            span,
            owner,
            origin: self.origin,
            analyzed_type: None,
        }
    }
    fn literal(&mut self, value: &ast::Literal) -> Result<ast::Literal, LowerError> {
        Ok(match value {
            ast::Literal::Integer(value) => ast::Literal::Integer(self.text(value)?),
            ast::Literal::Float(value) => ast::Literal::Float(self.text(value)?),
            ast::Literal::String(value) => ast::Literal::String(self.text(value)?),
            ast::Literal::RawString(value) => ast::Literal::RawString(self.text(value)?),
            ast::Literal::Bytes(value) => ast::Literal::Bytes(self.text(value)?),
            ast::Literal::Bool(value) => ast::Literal::Bool(*value),
            ast::Literal::Unit => ast::Literal::Unit,
        })
    }
    fn annotations(&mut self, values: &[ast::Annotation]) -> Result<Vec<Annotation>, LowerError> {
        values
            .iter()
            .map(|value| {
                Ok(Annotation {
                    kind: value.kind,
                    text: self.text(&value.text)?,
                    span: value.span,
                })
            })
            .collect()
    }
    fn parameters(
        &mut self,
        values: &[ast::Parameter],
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<Vec<Parameter>, LowerError> {
        values
            .iter()
            .map(|p| {
                Ok(Parameter {
                    pattern: self.pattern(&p.pattern, owner, depth)?,
                    mode: p.mode,
                    ty: p
                        .ty
                        .as_ref()
                        .map(|ty| self.ty(ty, owner, depth))
                        .transpose()?,
                    default: p
                        .default
                        .as_ref()
                        .map(|value| self.expr(value, owner, depth))
                        .transpose()?,
                    span: p.span,
                })
            })
            .collect()
    }
    fn generics(
        &mut self,
        values: &[ast::GenericParameter],
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<Vec<GenericParamId>, LowerError> {
        values
            .iter()
            .map(|parameter| {
                self.enter(depth)?;
                let id = GenericParamId(
                    u32::try_from(self.hir.generics.len())
                        .map_err(|_| LowerError::IdentitySpace)?,
                );
                self.hir.generics.push(GenericParam {
                    info: self.info(parameter.span, owner),
                    name: String::new(),
                    bound: None,
                    default: None,
                });
                let name = self.text(&parameter.name)?;
                let bound = parameter
                    .bound
                    .as_ref()
                    .map(|ty| self.ty(ty, owner, depth + 1))
                    .transpose()?;
                let default = parameter
                    .default
                    .as_ref()
                    .map(|ty| self.ty(ty, owner, depth + 1))
                    .transpose()?;
                self.hir.generics[id.0 as usize] = GenericParam {
                    info: self.info(parameter.span, owner),
                    name,
                    bound,
                    default,
                };
                Ok(id)
            })
            .collect()
    }
    fn block(
        &mut self,
        block: &ast::Block,
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<Block, LowerError> {
        Ok(Block {
            statements: block
                .statements
                .iter()
                .map(|stmt| self.stmt(stmt, owner, depth))
                .collect::<Result<_, _>>()?,
            where_items: block
                .where_items
                .iter()
                .map(|stmt| self.stmt(stmt, owner, depth))
                .collect::<Result<_, _>>()?,
            span: block.span,
        })
    }
    fn reserve_stmt(
        &mut self,
        span: Span,
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<StmtId, LowerError> {
        self.enter(depth)?;
        let id = StmtId(
            u32::try_from(self.hir.statements.len()).map_err(|_| LowerError::IdentitySpace)?,
        );
        self.hir.statements.push(Stmt {
            info: self.info(span, owner),
            kind: StmtKind::Expr {
                expression: ExprId(u32::MAX),
                terminated: true,
            },
        });
        Ok(id)
    }
    fn function(
        &mut self,
        function: &ast::Function,
        id: StmtId,
        depth: usize,
    ) -> Result<Function, LowerError> {
        let owner = LexicalOwner::Declaration(id);
        Ok(Function {
            visibility: function.visibility,
            is_meta: function.is_meta,
            is_halt: function.is_halt,
            name: self.text(&function.name)?,
            generics: self.generics(&function.generics, owner, depth)?,
            parameters: self.parameters(&function.parameters, owner, depth)?,
            return_type: function
                .return_type
                .as_ref()
                .map(|ty| self.ty(ty, owner, depth))
                .transpose()?,
            annotations: self.annotations(&function.annotations)?,
            signature_where: function
                .signature_where
                .iter()
                .map(|stmt| self.stmt(stmt, owner, depth))
                .collect::<Result<_, _>>()?,
            body: function
                .body
                .as_ref()
                .map(|body| self.block(body, owner, depth))
                .transpose()?,
        })
    }
    fn stmt(
        &mut self,
        stmt: &ast::Stmt,
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<StmtId, LowerError> {
        let id = self.reserve_stmt(stmt.span, owner, depth)?;
        let d = depth + 1;
        let kind = match &stmt.kind {
            ast::StmtKind::Binding(b) => StmtKind::Binding {
                visibility: b.visibility,
                is_meta: b.is_meta,
                mode: b.mode,
                pattern: self.pattern(&b.pattern, owner, d)?,
                ty: b.ty.as_ref().map(|ty| self.ty(ty, owner, d)).transpose()?,
                value: self.expr(&b.value, owner, d)?,
                fallback: b
                    .fallback
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
            },
            ast::StmtKind::Function(function) => {
                StmtKind::Function(self.function(function, id, d)?)
            }
            ast::StmtKind::Type(ty) => {
                let own = LexicalOwner::Declaration(id);
                let mut variants = Vec::new();
                for (index, v) in ty.variants.iter().enumerate() {
                    let variant = LexicalOwner::Variant {
                        declaration: id,
                        index: u32::try_from(index).map_err(|_| LowerError::IdentitySpace)?,
                    };
                    variants.push(Variant {
                        name: self.text(&v.name)?,
                        generics: self.generics(&v.generics, variant, d)?,
                        payload: v
                            .payload
                            .as_ref()
                            .map(|ty| self.ty(ty, variant, d))
                            .transpose()?,
                        result: v
                            .result
                            .as_ref()
                            .map(|ty| self.ty(ty, variant, d))
                            .transpose()?,
                        annotations: self.annotations(&v.annotations)?,
                        span: v.span,
                    });
                }
                StmtKind::Type {
                    visibility: ty.visibility,
                    is_halt: ty.is_halt,
                    name: self.text(&ty.name)?,
                    generics: self.generics(&ty.generics, own, d)?,
                    value: ty
                        .value
                        .as_ref()
                        .map(|ty| self.ty(ty, own, d))
                        .transpose()?,
                    variants,
                    opaque: ty.opaque,
                    nominal: ty.nominal,
                }
            }
            ast::StmtKind::Effect(effect) => {
                let own = LexicalOwner::Declaration(id);
                let generics = self.generics(&effect.generics, own, d)?;
                let mut operations = Vec::new();
                for function in &effect.operations {
                    let operation = self.reserve_stmt(function.span, own, d)?;
                    let function = self.function(function, operation, d + 1)?;
                    self.hir.statements[operation.0 as usize].kind = StmtKind::Function(function);
                    operations.push(operation);
                }
                StmtKind::Effect {
                    visibility: effect.visibility,
                    name: self.text(&effect.name)?,
                    generics,
                    operations,
                    members: effect
                        .members
                        .iter()
                        .map(|ty| self.ty(ty, own, d))
                        .collect::<Result<_, _>>()?,
                }
            }
            ast::StmtKind::Use(import) => StmtKind::Use {
                visibility: import.visibility,
                path: self.path(&import.path)?,
                alias: self.optional_text(import.alias.as_deref())?,
                members: import
                    .members
                    .iter()
                    .map(|member| {
                        Ok(ImportMember {
                            name: self.text(&member.name)?,
                            alias: self.optional_text(member.alias.as_deref())?,
                            span: member.span,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
                glob: import.glob,
            },
            ast::StmtKind::Handler(arms) => {
                let mut lowered = Vec::new();
                for (index, arm) in arms.iter().enumerate() {
                    let own = LexicalOwner::HandlerArm {
                        statement: id,
                        index: u32::try_from(index).map_err(|_| LowerError::IdentitySpace)?,
                    };
                    lowered.push(HandlerArm {
                        operation: self.expr(&arm.operation, owner, d)?,
                        parameters: self.parameters(&arm.parameters, own, d)?,
                        body: self.expr(&arm.body, own, d)?,
                        span: arm.span,
                    });
                }
                StmtKind::Handler(lowered)
            }
            ast::StmtKind::HandlerApplication(value) => {
                StmtKind::HandlerApplication(self.expr(value, owner, d)?)
            }
            ast::StmtKind::Assignment {
                target,
                operator,
                value,
            } => StmtKind::Assignment {
                target: self.expr(target, owner, d)?,
                operator: self.text(operator)?,
                value: self.expr(value, owner, d)?,
            },
            ast::StmtKind::Expr {
                expression,
                terminated,
            } => StmtKind::Expr {
                expression: self.expr(expression, owner, d)?,
                terminated: *terminated,
            },
        };
        self.hir.statements[id.0 as usize].kind = kind;
        Ok(id)
    }
    fn expr(
        &mut self,
        expr: &ast::Expr,
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<ExprId, LowerError> {
        self.enter(depth)?;
        let id = ExprId(
            u32::try_from(self.hir.expressions.len()).map_err(|_| LowerError::IdentitySpace)?,
        );
        self.hir.expressions.push(Expr {
            info: self.info(expr.span, owner),
            kind: ExprKind::Error,
        });
        let d = depth + 1;
        let kind = match &expr.kind {
            ast::ExprKind::Literal(value) => ExprKind::Literal(self.literal(value)?),
            ast::ExprKind::Interpolated(parts) => ExprKind::Interpolated(
                parts
                    .iter()
                    .map(|part| {
                        Ok(match part {
                            ast::StringPart::Text(text) => StringPart::Text(self.text(text)?),
                            ast::StringPart::Interpolation {
                                expression,
                                format,
                                span,
                            } => StringPart::Interpolation {
                                expression: self.expr(expression, owner, d)?,
                                format: self.optional_text(format.as_deref())?,
                                span: *span,
                            },
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
            ),
            ast::ExprKind::Name(name) => ExprKind::Name(self.text(name)?),
            ast::ExprKind::Path(path) => ExprKind::Path(self.path(path)?),
            ast::ExprKind::Generic { base, arguments } => ExprKind::Generic {
                base: self.expr(base, owner, d)?,
                arguments: arguments
                    .iter()
                    .map(|ty| self.ty(ty, owner, d))
                    .collect::<Result<_, _>>()?,
            },
            ast::ExprKind::Tuple(items) => ExprKind::Tuple(
                items
                    .iter()
                    .map(|item| self.expr(item, owner, d))
                    .collect::<Result<_, _>>()?,
            ),
            ast::ExprKind::Array(items) => ExprKind::Array(
                items
                    .iter()
                    .map(|item| self.expr(item, owner, d))
                    .collect::<Result<_, _>>()?,
            ),
            ast::ExprKind::Map(items) => ExprKind::Map(
                items
                    .iter()
                    .map(|(key, value)| {
                        Ok((self.expr(key, owner, d)?, self.expr(value, owner, d)?))
                    })
                    .collect::<Result<_, LowerError>>()?,
            ),
            ast::ExprKind::Record {
                ty,
                fields,
                spread,
                members,
            } => {
                let mut lowered = Vec::new();
                if members.is_empty() {
                    for field in fields {
                        lowered.push(RecordMember::Field {
                            name: self.text(&field.name)?,
                            value: self.expr(&field.value, owner, d)?,
                            span: field.span,
                        });
                    }
                    if let Some(value) = spread {
                        lowered.push(RecordMember::Spread(self.expr(value, owner, d)?));
                    }
                } else {
                    for member in members {
                        lowered.push(match member {
                            ast::RecordMember::Field(field) => RecordMember::Field {
                                name: self.text(&field.name)?,
                                value: self.expr(&field.value, owner, d)?,
                                span: field.span,
                            },
                            ast::RecordMember::Spread(value) => {
                                RecordMember::Spread(self.expr(value, owner, d)?)
                            }
                        });
                    }
                }
                ExprKind::Record {
                    ty: ty.as_ref().map(|ty| self.ty(ty, owner, d)).transpose()?,
                    members: lowered,
                }
            }
            ast::ExprKind::Unary { operator, operand } => ExprKind::Unary {
                operator: self.text(operator)?,
                operand: self.expr(operand, owner, d)?,
            },
            ast::ExprKind::Binary {
                operator,
                left,
                right,
            } => ExprKind::Binary {
                operator: self.text(operator)?,
                left: self.expr(left, owner, d)?,
                right: self.expr(right, owner, d)?,
            },
            ast::ExprKind::Call { callee, arguments } => ExprKind::Call {
                callee: self.expr(callee, owner, d)?,
                arguments: arguments
                    .iter()
                    .map(|arg| {
                        Ok(Argument {
                            label: self.optional_text(arg.label.as_deref())?,
                            mode: arg.mode,
                            value: self.expr(&arg.value, owner, d)?,
                            span: arg.span,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
            },
            ast::ExprKind::Field { base, field, safe } => ExprKind::Field {
                base: self.expr(base, owner, d)?,
                field: self.text(field)?,
                safe: *safe,
            },
            ast::ExprKind::ComputedField { base, key } => ExprKind::ComputedField {
                base: self.expr(base, owner, d)?,
                key: self.expr(key, owner, d)?,
            },
            ast::ExprKind::Index { base, index, safe } => ExprKind::Index {
                base: self.expr(base, owner, d)?,
                index: self.expr(index, owner, d)?,
                safe: *safe,
            },
            ast::ExprKind::Lambda {
                parameters,
                return_type,
                annotations,
                body,
            } => {
                let own = LexicalOwner::Lambda(id);
                ExprKind::Lambda {
                    parameters: self.parameters(parameters, own, d)?,
                    return_type: return_type
                        .as_ref()
                        .map(|ty| self.ty(ty, own, d))
                        .transpose()?,
                    annotations: self.annotations(annotations)?,
                    body: self.expr(body, own, d)?,
                }
            }
            ast::ExprKind::Accessor(segments) => ExprKind::Accessor(
                segments
                    .iter()
                    .map(|part| {
                        Ok(AccessorSegment {
                            field: self.text(&part.field)?,
                            safe: part.safe,
                            span: part.span,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
            ),
            ast::ExprKind::Block(block) => ExprKind::Block(self.block(block, owner, d)?),
            ast::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => ExprKind::If {
                condition: self.expr(condition, owner, d)?,
                then_branch: self.expr(then_branch, owner, d)?,
                else_branch: else_branch
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
            },
            ast::ExprKind::Match {
                value,
                arms,
                type_match,
            } => ExprKind::Match {
                value: self.expr(value, owner, d)?,
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(MatchArm {
                            pattern: self.pattern(&arm.pattern, owner, d)?,
                            guard: arm
                                .guard
                                .as_ref()
                                .map(|guard| self.expr(guard, owner, d))
                                .transpose()?,
                            body: self.expr(&arm.body, owner, d)?,
                            span: arm.span,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
                type_match: *type_match,
            },
            ast::ExprKind::Is { value, pattern } => ExprKind::Is {
                value: self.expr(value, owner, d)?,
                pattern: self.pattern(pattern, owner, d)?,
            },
            ast::ExprKind::Loop(block) => ExprKind::Loop(self.block(block, owner, d)?),
            ast::ExprKind::While { condition, body } => ExprKind::While {
                condition: self.expr(condition, owner, d)?,
                body: self.block(body, owner, d)?,
            },
            ast::ExprKind::For {
                iterable,
                pattern,
                body,
            } => ExprKind::For {
                iterable: self.expr(iterable, owner, d)?,
                pattern: self.pattern(pattern, owner, d)?,
                body: self.block(body, owner, d)?,
            },
            ast::ExprKind::Control { operation, value } => ExprKind::Control {
                operation: *operation,
                value: value
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
            },
            ast::ExprKind::TypeValue(ty) => ExprKind::TypeValue(self.ty(ty, owner, d)?),
            ast::ExprKind::KeyOf(ty) => ExprKind::KeyOf(self.ty(ty, owner, d)?),
            ast::ExprKind::Derive { base, recipe } => ExprKind::Derive {
                base: base
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
                recipe: self.expr(recipe, owner, d)?,
            },
            ast::ExprKind::Range {
                start,
                end,
                inclusive,
            } => ExprKind::Range {
                start: start
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
                end: end
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
                inclusive: *inclusive,
            },
            ast::ExprKind::Ambient => ExprKind::Ambient,
            ast::ExprKind::Error => ExprKind::Error,
        };
        self.hir.expressions[id.0 as usize].kind = kind;
        Ok(id)
    }
    fn ty(
        &mut self,
        ty: &ast::TypeExpr,
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<TypeExprId, LowerError> {
        self.enter(depth)?;
        let id =
            TypeExprId(u32::try_from(self.hir.types.len()).map_err(|_| LowerError::IdentitySpace)?);
        self.hir.types.push(TypeExpr {
            info: self.info(ty.span, owner),
            kind: TypeKind::Error,
        });
        let d = depth + 1;
        let kind = match &ty.kind {
            ast::TypeKind::Name { path, arguments } => TypeKind::Name {
                path: self.path(path)?,
                arguments: arguments
                    .iter()
                    .map(|arg| self.ty(arg, owner, d))
                    .collect::<Result<_, _>>()?,
            },
            ast::TypeKind::Optional(inner) => TypeKind::Optional(self.ty(inner, owner, d)?),
            ast::TypeKind::Array { length, element } => TypeKind::Array {
                length: length
                    .as_ref()
                    .map(|value| self.expr(value, owner, d))
                    .transpose()?,
                element: self.ty(element, owner, d)?,
            },
            ast::TypeKind::Map { key, value } => TypeKind::Map {
                key: self.ty(key, owner, d)?,
                value: self.ty(value, owner, d)?,
            },
            ast::TypeKind::Tuple(items) => TypeKind::Tuple(
                items
                    .iter()
                    .map(|item| self.ty(item, owner, d))
                    .collect::<Result<_, _>>()?,
            ),
            ast::TypeKind::Record { fields, row } => TypeKind::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(TypeField {
                            name: self.text(&field.name)?,
                            mutable: field.mutable,
                            ty: self.ty(&field.ty, owner, d)?,
                            span: field.span,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
                row: row.as_ref().map(|ty| self.ty(ty, owner, d)).transpose()?,
            },
            ast::TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                let own = LexicalOwner::CallableType(id);
                TypeKind::Callable {
                    parameters: self.parameters(parameters, own, d)?,
                    result: result.as_ref().map(|ty| self.ty(ty, own, d)).transpose()?,
                    annotations: self.annotations(annotations)?,
                }
            }
            ast::TypeKind::TypeFunction { parameters, body } => {
                let own = LexicalOwner::TypeFunction(id);
                TypeKind::TypeFunction {
                    parameters: self.generics(parameters, own, d)?,
                    body: self.expr(body, own, d)?,
                }
            }
            ast::TypeKind::Projection { base, field } => TypeKind::Projection {
                base: self.ty(base, owner, d)?,
                field: self.text(field)?,
            },
            ast::TypeKind::ComputedProjection { base, key } => TypeKind::ComputedProjection {
                base: self.ty(base, owner, d)?,
                key: self.expr(key, owner, d)?,
            },
            ast::TypeKind::KeyOf(inner) => TypeKind::KeyOf(self.ty(inner, owner, d)?),
            ast::TypeKind::Computation(value) => TypeKind::Computation(self.expr(value, owner, d)?),
            ast::TypeKind::Mapped {
                binder,
                keys,
                value,
                tuple,
            } => TypeKind::Mapped {
                binder: self.text(binder)?,
                keys: self.expr(keys, owner, d)?,
                value: self.ty(value, owner, d)?,
                tuple: *tuple,
            },
            ast::TypeKind::Rest(inner) => TypeKind::Rest(self.ty(inner, owner, d)?),
            ast::TypeKind::KindArrow { parameter, result } => TypeKind::KindArrow {
                parameter: self.ty(parameter, owner, d)?,
                result: self.ty(result, owner, d)?,
            },
            ast::TypeKind::Error => TypeKind::Error,
        };
        self.hir.types[id.0 as usize].kind = kind;
        Ok(id)
    }
    fn pattern(
        &mut self,
        pattern: &ast::Pattern,
        owner: LexicalOwner,
        depth: usize,
    ) -> Result<PatternId, LowerError> {
        self.enter(depth)?;
        let id = PatternId(
            u32::try_from(self.hir.patterns.len()).map_err(|_| LowerError::IdentitySpace)?,
        );
        self.hir.patterns.push(Pattern {
            info: self.info(pattern.span, owner),
            kind: PatternKind::Error,
        });
        let d = depth + 1;
        let kind = match &pattern.kind {
            ast::PatternKind::Name(name) => PatternKind::Name(self.text(name)?),
            ast::PatternKind::Wildcard => PatternKind::Wildcard,
            ast::PatternKind::Literal(value) => PatternKind::Literal(self.literal(value)?),
            ast::PatternKind::Tuple(items) => PatternKind::Tuple(
                items
                    .iter()
                    .map(|item| self.pattern(item, owner, d))
                    .collect::<Result<_, _>>()?,
            ),
            ast::PatternKind::Record {
                ty,
                fields,
                rest,
                rest_binding,
            } => PatternKind::Record {
                ty: ty.as_ref().map(|ty| self.ty(ty, owner, d)).transpose()?,
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(PatternField {
                            name: self.text(&field.name)?,
                            pattern: self.pattern(&field.pattern, owner, d)?,
                            span: field.span,
                        })
                    })
                    .collect::<Result<_, LowerError>>()?,
                rest: *rest,
                rest_binding: self.optional_text(rest_binding.as_deref())?,
            },
            ast::PatternKind::Constructor {
                path,
                arguments,
                parenthesized,
            } => PatternKind::Constructor {
                path: self.path(path)?,
                arguments: arguments
                    .iter()
                    .map(|item| self.pattern(item, owner, d))
                    .collect::<Result<_, _>>()?,
                parenthesized: *parenthesized,
            },
            ast::PatternKind::Alternative(items) => PatternKind::Alternative(
                items
                    .iter()
                    .map(|item| self.pattern(item, owner, d))
                    .collect::<Result<_, _>>()?,
            ),
            ast::PatternKind::Mode { mode, pattern } => PatternKind::Mode {
                mode: *mode,
                pattern: self.pattern(pattern, owner, d)?,
            },
            ast::PatternKind::Type { ty, binder } => PatternKind::Type {
                ty: self.ty(ty, owner, d)?,
                binder: self.optional_text(binder.as_deref())?,
            },
            ast::PatternKind::Value(value) => PatternKind::Value(self.expr(value, owner, d)?),
            ast::PatternKind::Error => PatternKind::Error,
        };
        self.hir.patterns[id.0 as usize].kind = kind;
        Ok(id)
    }
}

pub(super) fn program(source: &ast::Program, limits: HirLimits) -> Result<HirProgram, LowerError> {
    let mut hir = HirProgram::default();
    let mut lower = Lower {
        hir: &mut hir,
        left: limits,
        origin: NodeOrigin::Source,
    };
    for statement in &source.statements {
        let id = lower.stmt(statement, LexicalOwner::Module, 0)?;
        lower.hir.roots.push(id);
    }
    Ok(hir)
}

fn owner_exists(hir: &HirProgram, owner: LexicalOwner) -> bool {
    match owner {
        LexicalOwner::Module => true,
        LexicalOwner::Declaration(id) => hir.statement(id).is_some_and(|stmt| matches!(stmt.kind, StmtKind::Function(_) | StmtKind::Type { .. } | StmtKind::Effect { .. })),
        LexicalOwner::Lambda(id) => hir.expression(id).is_some_and(|expr| matches!(expr.kind, ExprKind::Lambda { .. })),
        LexicalOwner::TypeFunction(id) => hir.type_expression(id).is_some_and(|ty| matches!(ty.kind, TypeKind::TypeFunction { .. })),
        LexicalOwner::CallableType(id) => hir.type_expression(id).is_some_and(|ty| matches!(ty.kind, TypeKind::Callable { .. })),
        LexicalOwner::Variant { declaration, index } => hir.statement(declaration).is_some_and(|stmt| matches!(&stmt.kind, StmtKind::Type { variants, .. } if (index as usize) < variants.len())),
        LexicalOwner::HandlerArm { statement, index } => hir.statement(statement).is_some_and(|stmt| matches!(&stmt.kind, StmtKind::Handler(arms) if (index as usize) < arms.len())),
    }
}

pub(super) fn generated(
    hir: &mut HirProgram,
    source: &ast::Expr,
    anchor: NodeId,
    kind: GeneratedKind,
    owner: LexicalOwner,
    limits: HirLimits,
) -> Result<ExprId, LowerError> {
    match generated_node(
        hir,
        GeneratedInput::Expression(source),
        anchor,
        kind,
        owner,
        limits,
    )? {
        NodeId::Expr(id) => Ok(id),
        _ => unreachable!("generated expression has its expression identity"),
    }
}

pub(super) fn generated_statement(
    hir: &mut HirProgram,
    source: &ast::Stmt,
    anchor: NodeId,
    kind: GeneratedKind,
    owner: LexicalOwner,
    limits: HirLimits,
) -> Result<StmtId, LowerError> {
    match generated_node(
        hir,
        GeneratedInput::Statement(source),
        anchor,
        kind,
        owner,
        limits,
    )? {
        NodeId::Stmt(id) => Ok(id),
        _ => unreachable!("generated statement has its statement identity"),
    }
}

enum GeneratedInput<'a> {
    Expression(&'a ast::Expr),
    Statement(&'a ast::Stmt),
}

fn generated_node(
    hir: &mut HirProgram,
    source: GeneratedInput<'_>,
    anchor: NodeId,
    kind: GeneratedKind,
    owner: LexicalOwner,
    limits: HirLimits,
) -> Result<NodeId, LowerError> {
    if hir.info(anchor).is_none() || !owner_exists(hir, owner) {
        return Err(LowerError::MissingAnchor);
    }
    let generation =
        u32::try_from(hir.generated_roots.len()).map_err(|_| LowerError::IdentitySpace)?;
    let before = (
        hir.expressions.len(),
        hir.statements.len(),
        hir.patterns.len(),
        hir.generics.len(),
        hir.types.len(),
    );
    let mut lower = Lower {
        hir,
        left: limits,
        origin: NodeOrigin::Generated {
            generation,
            anchor,
            kind,
        },
    };
    let result = match source {
        GeneratedInput::Expression(source) => lower.expr(source, owner, 0).map(NodeId::Expr),
        GeneratedInput::Statement(source) => lower.stmt(source, owner, 0).map(NodeId::Stmt),
    };
    match result {
        Ok(id) => {
            hir.generated_roots.push(id);
            Ok(id)
        }
        Err(error) => {
            hir.expressions.truncate(before.0);
            hir.statements.truncate(before.1);
            hir.patterns.truncate(before.2);
            hir.generics.truncate(before.3);
            hir.types.truncate(before.4);
            Err(error)
        }
    }
}
