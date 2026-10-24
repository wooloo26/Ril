//! A controlled identity bridge, not a span index. The first pass validates the
//! finite structural pairing without mutation. Only the identical second pass
//! writes IDs; existing IDs have no role in either pass.
use super::*;

struct Identify<'a> {
    hir: &'a HirProgram,
    left: HirLimits,
    write: bool,
    validate_ids: bool,
}
impl Identify<'_> {
    fn enter(&mut self, depth: usize) -> Result<(), LowerError> {
        if depth >= self.left.depth {
            return Err(LowerError::Budget("identity depth"));
        }
        self.left.nodes = self
            .left
            .nodes
            .checked_sub(1)
            .ok_or(LowerError::Budget("identity node"))?;
        Ok(())
    }
    fn equal(&self, condition: bool) -> Result<(), LowerError> {
        if condition {
            Ok(())
        } else {
            Err(LowerError::Correspondence)
        }
    }
    fn text(&mut self, actual: &str, expected: &str) -> Result<(), LowerError> {
        self.left.text_items = self
            .left
            .text_items
            .checked_sub(1)
            .ok_or(LowerError::Budget("identity text item"))?;
        self.left.text_bytes = actual
            .len()
            .checked_add(1)
            .and_then(|cost| self.left.text_bytes.checked_sub(cost))
            .ok_or(LowerError::Budget("identity text"))?;
        self.equal(actual == expected)
    }
    fn optional_text(
        &mut self,
        actual: Option<&str>,
        expected: Option<&str>,
    ) -> Result<(), LowerError> {
        match (actual, expected) {
            (Some(a), Some(b)) => self.text(a, b),
            (None, None) => Ok(()),
            _ => Err(LowerError::Correspondence),
        }
    }
    fn path(&mut self, actual: &[String], expected: &[String]) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter().zip(expected) {
            self.text(a, b)?;
        }
        Ok(())
    }
    fn literal(
        &mut self,
        actual: &ast::Literal,
        expected: &ast::Literal,
    ) -> Result<(), LowerError> {
        match (actual, expected) {
            (ast::Literal::Integer(a), ast::Literal::Integer(b))
            | (ast::Literal::Float(a), ast::Literal::Float(b))
            | (ast::Literal::String(a), ast::Literal::String(b))
            | (ast::Literal::RawString(a), ast::Literal::RawString(b))
            | (ast::Literal::Bytes(a), ast::Literal::Bytes(b)) => self.text(a, b),
            (ast::Literal::Bool(a), ast::Literal::Bool(b)) => self.equal(a == b),
            (ast::Literal::Unit, ast::Literal::Unit) => Ok(()),
            _ => Err(LowerError::Correspondence),
        }
    }
    fn annotations(
        &mut self,
        actual: &[ast::Annotation],
        expected: &[Annotation],
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter().zip(expected) {
            self.equal(a.kind == b.kind)?;
            self.text(&a.text, &b.text)?;
        }
        Ok(())
    }
    fn opt_expr(
        &mut self,
        actual: Option<&mut ast::Expr>,
        expected: Option<ExprId>,
        d: usize,
    ) -> Result<(), LowerError> {
        match (actual, expected) {
            (Some(a), Some(b)) => self.expr(a, b, d),
            (None, None) => Ok(()),
            _ => Err(LowerError::Correspondence),
        }
    }
    fn opt_type(
        &mut self,
        actual: Option<&mut ast::TypeExpr>,
        expected: Option<TypeExprId>,
        d: usize,
    ) -> Result<(), LowerError> {
        match (actual, expected) {
            (Some(a), Some(b)) => self.ty(a, b, d),
            (None, None) => Ok(()),
            _ => Err(LowerError::Correspondence),
        }
    }
    fn statements(
        &mut self,
        actual: &mut [ast::Stmt],
        expected: &[StmtId],
        d: usize,
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter_mut().zip(expected) {
            self.stmt(a, *b, d)?;
        }
        Ok(())
    }
    fn exprs(
        &mut self,
        actual: &mut [ast::Expr],
        expected: &[ExprId],
        d: usize,
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter_mut().zip(expected) {
            self.expr(a, *b, d)?;
        }
        Ok(())
    }
    fn types(
        &mut self,
        actual: &mut [ast::TypeExpr],
        expected: &[TypeExprId],
        d: usize,
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter_mut().zip(expected) {
            self.ty(a, *b, d)?;
        }
        Ok(())
    }
    fn patterns(
        &mut self,
        actual: &mut [ast::Pattern],
        expected: &[PatternId],
        d: usize,
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter_mut().zip(expected) {
            self.pattern(a, *b, d)?;
        }
        Ok(())
    }
    fn parameters(
        &mut self,
        actual: &mut [ast::Parameter],
        expected: &[Parameter],
        d: usize,
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (a, b) in actual.iter_mut().zip(expected) {
            self.equal(a.mode == b.mode)?;
            self.pattern(&mut a.pattern, b.pattern, d)?;
            self.opt_type(a.ty.as_mut(), b.ty, d)?;
            self.opt_expr(a.default.as_mut(), b.default, d)?;
        }
        Ok(())
    }
    fn generics(
        &mut self,
        actual: &mut [ast::GenericParameter],
        expected: &[GenericParamId],
        depth: usize,
    ) -> Result<(), LowerError> {
        self.equal(actual.len() == expected.len())?;
        for (parameter, id) in actual.iter_mut().zip(expected) {
            self.enter(depth)?;
            let hir = self.hir;
            let expected = hir.generic(*id).ok_or(LowerError::Correspondence)?;
            self.text(&parameter.name, &expected.name)?;
            self.opt_type(parameter.bound.as_mut(), expected.bound, depth + 1)?;
            self.opt_type(parameter.default.as_mut(), expected.default, depth + 1)?;
            if self.validate_ids {
                self.equal(parameter.hir_id == Some(*id))?;
            }
            if self.write {
                parameter.hir_id = Some(*id);
            }
        }
        Ok(())
    }
    fn block(
        &mut self,
        actual: &mut ast::Block,
        expected: &Block,
        d: usize,
    ) -> Result<(), LowerError> {
        self.statements(&mut actual.statements, &expected.statements, d)?;
        self.statements(&mut actual.where_items, &expected.where_items, d)
    }
    fn function(
        &mut self,
        actual: &mut ast::Function,
        expected: &Function,
        d: usize,
    ) -> Result<(), LowerError> {
        self.equal(
            actual.visibility == expected.visibility
                && actual.is_meta == expected.is_meta
                && actual.is_halt == expected.is_halt,
        )?;
        self.text(&actual.name, &expected.name)?;
        self.generics(&mut actual.generics, &expected.generics, d)?;
        self.parameters(&mut actual.parameters, &expected.parameters, d)?;
        self.opt_type(actual.return_type.as_mut(), expected.return_type, d)?;
        self.annotations(&actual.annotations, &expected.annotations)?;
        self.statements(&mut actual.signature_where, &expected.signature_where, d)?;
        match (&mut actual.body, &expected.body) {
            (Some(a), Some(b)) => self.block(a, b, d),
            (None, None) => Ok(()),
            _ => Err(LowerError::Correspondence),
        }
    }
    fn stmt(&mut self, actual: &mut ast::Stmt, id: StmtId, depth: usize) -> Result<(), LowerError> {
        self.enter(depth)?;
        let hir = self.hir;
        let expected = hir.statement(id).ok_or(LowerError::Correspondence)?;
        let d = depth + 1;
        match (&mut actual.kind, &expected.kind) {
            (
                ast::StmtKind::Binding(a),
                StmtKind::Binding {
                    visibility,
                    is_meta,
                    mode,
                    pattern,
                    ty,
                    value,
                    fallback,
                },
            ) => {
                self.equal(
                    a.visibility == *visibility && a.is_meta == *is_meta && a.mode == *mode,
                )?;
                self.pattern(&mut a.pattern, *pattern, d)?;
                self.opt_type(a.ty.as_mut(), *ty, d)?;
                self.expr(&mut a.value, *value, d)?;
                self.opt_expr(a.fallback.as_mut(), *fallback, d)?;
            }
            (ast::StmtKind::Function(a), StmtKind::Function(b)) => self.function(a, b, d)?,
            (
                ast::StmtKind::Type(a),
                StmtKind::Type {
                    visibility,
                    is_halt,
                    name,
                    generics,
                    value,
                    variants,
                    opaque,
                    nominal,
                },
            ) => {
                self.equal(
                    a.visibility == *visibility
                        && a.is_halt == *is_halt
                        && a.opaque == *opaque
                        && a.nominal == *nominal,
                )?;
                self.text(&a.name, name)?;
                self.generics(&mut a.generics, generics, d)?;
                self.opt_type(a.value.as_mut(), *value, d)?;
                self.equal(a.variants.len() == variants.len())?;
                for (a, b) in a.variants.iter_mut().zip(variants) {
                    self.text(&a.name, &b.name)?;
                    self.generics(&mut a.generics, &b.generics, d)?;
                    self.opt_type(a.payload.as_mut(), b.payload, d)?;
                    self.opt_type(a.result.as_mut(), b.result, d)?;
                    self.annotations(&a.annotations, &b.annotations)?;
                }
            }
            (
                ast::StmtKind::Effect(a),
                StmtKind::Effect {
                    visibility,
                    name,
                    generics,
                    operations,
                    members,
                },
            ) => {
                self.equal(a.visibility == *visibility)?;
                self.text(&a.name, name)?;
                self.generics(&mut a.generics, generics, d)?;
                self.equal(a.operations.len() == operations.len())?;
                for (a, id) in a.operations.iter_mut().zip(operations) {
                    self.enter(d)?;
                    let StmtKind::Function(b) =
                        &hir.statement(*id).ok_or(LowerError::Correspondence)?.kind
                    else {
                        return Err(LowerError::Correspondence);
                    };
                    self.function(a, b, d + 1)?;
                }
                self.types(&mut a.members, members, d)?;
            }
            (
                ast::StmtKind::Use(a),
                StmtKind::Use {
                    visibility,
                    path,
                    alias,
                    members,
                    glob,
                },
            ) => {
                self.equal(
                    a.visibility == *visibility
                        && a.glob == *glob
                        && a.members.len() == members.len(),
                )?;
                self.path(&a.path, path)?;
                self.optional_text(a.alias.as_deref(), alias.as_deref())?;
                for (a, b) in a.members.iter().zip(members) {
                    self.text(&a.name, &b.name)?;
                    self.optional_text(a.alias.as_deref(), b.alias.as_deref())?;
                }
            }
            (ast::StmtKind::Handler(a), StmtKind::Handler(b)) => {
                self.equal(a.len() == b.len())?;
                for (a, b) in a.iter_mut().zip(b) {
                    self.expr(&mut a.operation, b.operation, d)?;
                    self.parameters(&mut a.parameters, &b.parameters, d)?;
                    self.expr(&mut a.body, b.body, d)?;
                }
            }
            (ast::StmtKind::HandlerApplication(a), StmtKind::HandlerApplication(b)) => {
                self.expr(a, *b, d)?
            }
            (
                ast::StmtKind::Assignment {
                    target,
                    operator,
                    value,
                },
                StmtKind::Assignment {
                    target: b,
                    operator: op,
                    value: v,
                },
            ) => {
                self.text(operator, op)?;
                self.expr(target, *b, d)?;
                self.expr(value, *v, d)?;
            }
            (
                ast::StmtKind::Expr {
                    expression,
                    terminated,
                },
                StmtKind::Expr {
                    expression: b,
                    terminated: done,
                },
            ) => {
                self.equal(terminated == done)?;
                self.expr(expression, *b, d)?;
            }
            _ => return Err(LowerError::Correspondence),
        }
        if self.validate_ids {
            self.equal(actual.hir_id == Some(id))?;
        }
        if self.write {
            actual.hir_id = Some(id);
        }
        Ok(())
    }
    fn field(
        &mut self,
        actual: &mut ast::RecordField,
        expected: &RecordMember,
        d: usize,
    ) -> Result<(), LowerError> {
        let RecordMember::Field { name, value, .. } = expected else {
            return Err(LowerError::Correspondence);
        };
        self.text(&actual.name, name)?;
        self.expr(&mut actual.value, *value, d)
    }
    fn expr(&mut self, actual: &mut ast::Expr, id: ExprId, depth: usize) -> Result<(), LowerError> {
        self.enter(depth)?;
        let hir = self.hir;
        let expected = hir.expression(id).ok_or(LowerError::Correspondence)?;
        let d = depth + 1;
        match (&mut actual.kind, &expected.kind) {
            (ast::ExprKind::Literal(a), ExprKind::Literal(b)) => self.literal(a, b)?,
            (ast::ExprKind::Name(a), ExprKind::Name(b)) => self.text(a, b)?,
            (ast::ExprKind::Path(a), ExprKind::Path(b)) => self.path(a, b)?,
            (ast::ExprKind::Interpolated(a), ExprKind::Interpolated(b)) => {
                self.equal(a.len() == b.len())?;
                for (a, b) in a.iter_mut().zip(b) {
                    match (a, b) {
                        (ast::StringPart::Text(a), StringPart::Text(b)) => self.text(a, b)?,
                        (
                            ast::StringPart::Interpolation {
                                expression, format, ..
                            },
                            StringPart::Interpolation {
                                expression: b,
                                format: f,
                                ..
                            },
                        ) => {
                            self.opt_expr(Some(expression), Some(*b), d)?;
                            self.optional_text(format.as_deref(), f.as_deref())?;
                        }
                        _ => return Err(LowerError::Correspondence),
                    }
                }
            }
            (
                ast::ExprKind::Generic { base, arguments },
                ExprKind::Generic {
                    base: b,
                    arguments: args,
                },
            ) => {
                self.expr(base, *b, d)?;
                self.types(arguments, args, d)?;
            }
            (ast::ExprKind::Tuple(a), ExprKind::Tuple(b))
            | (ast::ExprKind::Array(a), ExprKind::Array(b)) => self.exprs(a, b, d)?,
            (ast::ExprKind::Map(a), ExprKind::Map(b)) => {
                self.equal(a.len() == b.len())?;
                for ((a, v), (b, w)) in a.iter_mut().zip(b) {
                    self.expr(a, *b, d)?;
                    self.expr(v, *w, d)?;
                }
            }
            (
                ast::ExprKind::Record { ty, members },
                ExprKind::Record {
                    ty: b,
                    members: expected,
                },
            ) => {
                self.opt_type(ty.as_mut(), *b, d)?;
                self.equal(members.len() == expected.len())?;
                for (a, b) in members.iter_mut().zip(expected) {
                    match (a, b) {
                        (ast::RecordMember::Field(a), b @ RecordMember::Field { .. }) => {
                            self.field(a, b, d)?
                        }
                        (ast::RecordMember::Spread(a), RecordMember::Spread(b)) => {
                            self.expr(a, *b, d)?
                        }
                        _ => return Err(LowerError::Correspondence),
                    }
                }
            }
            (
                ast::ExprKind::Unary { operator, operand },
                ExprKind::Unary {
                    operator: op,
                    operand: b,
                },
            ) => {
                self.text(operator, op)?;
                self.expr(operand, *b, d)?;
            }
            (
                ast::ExprKind::Binary {
                    operator,
                    left,
                    right,
                },
                ExprKind::Binary {
                    operator: op,
                    left: a,
                    right: b,
                },
            ) => {
                self.text(operator, op)?;
                self.expr(left, *a, d)?;
                self.expr(right, *b, d)?;
            }
            (
                ast::ExprKind::Call { callee, arguments },
                ExprKind::Call {
                    callee: b,
                    arguments: args,
                },
            ) => {
                self.expr(callee, *b, d)?;
                self.equal(arguments.len() == args.len())?;
                for (a, b) in arguments.iter_mut().zip(args) {
                    self.equal(a.mode == b.mode)?;
                    self.optional_text(a.label.as_deref(), b.label.as_deref())?;
                    self.expr(&mut a.value, b.value, d)?;
                }
            }
            (
                ast::ExprKind::Field { base, field, safe },
                ExprKind::Field {
                    base: b,
                    field: f,
                    safe: s,
                },
            ) => {
                self.equal(safe == s)?;
                self.text(field, f)?;
                self.expr(base, *b, d)?;
            }
            (
                ast::ExprKind::ComputedField { base, key },
                ExprKind::ComputedField { base: b, key: k },
            ) => {
                self.expr(base, *b, d)?;
                self.expr(key, *k, d)?;
            }
            (
                ast::ExprKind::Index { base, index, safe },
                ExprKind::Index {
                    base: b,
                    index: i,
                    safe: s,
                },
            ) => {
                self.equal(safe == s)?;
                self.expr(base, *b, d)?;
                self.expr(index, *i, d)?;
            }
            (
                ast::ExprKind::Lambda {
                    parameters,
                    return_type,
                    annotations,
                    body,
                },
                ExprKind::Lambda {
                    parameters: p,
                    return_type: t,
                    annotations: a,
                    body: b,
                },
            ) => {
                self.parameters(parameters, p, d)?;
                self.opt_type(return_type.as_mut(), *t, d)?;
                self.annotations(annotations, a)?;
                self.expr(body, *b, d)?;
            }
            (ast::ExprKind::Accessor(a), ExprKind::Accessor(b)) => {
                self.equal(a.len() == b.len())?;
                for (a, b) in a.iter().zip(b) {
                    self.equal(a.safe == b.safe)?;
                    self.text(&a.field, &b.field)?;
                }
            }
            (ast::ExprKind::Block(a), ExprKind::Block(b))
            | (ast::ExprKind::Loop(a), ExprKind::Loop(b)) => self.block(a, b, d)?,
            (
                ast::ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                },
                ExprKind::If {
                    condition: c,
                    then_branch: t,
                    else_branch: e,
                },
            ) => {
                self.expr(condition, *c, d)?;
                self.expr(then_branch, *t, d)?;
                self.opt_expr(else_branch.as_deref_mut(), *e, d)?;
            }
            (
                ast::ExprKind::IfLet {
                    pattern,
                    value,
                    then_branch,
                    else_branch,
                },
                ExprKind::IfLet {
                    pattern: p,
                    value: v,
                    then_branch: t,
                    else_branch: e,
                },
            ) => {
                self.expr(value, *v, d)?;
                self.pattern(pattern, *p, d)?;
                self.expr(then_branch, *t, d)?;
                self.opt_expr(else_branch.as_deref_mut(), *e, d)?;
            }
            (
                ast::ExprKind::Match {
                    value,
                    arms,
                    type_match,
                },
                ExprKind::Match {
                    value: v,
                    arms: a,
                    type_match: t,
                },
            ) => {
                self.equal(type_match == t && arms.len() == a.len())?;
                self.expr(value, *v, d)?;
                for (a, b) in arms.iter_mut().zip(a) {
                    self.pattern(&mut a.pattern, b.pattern, d)?;
                    self.opt_expr(a.guard.as_mut(), b.guard, d)?;
                    self.expr(&mut a.body, b.body, d)?;
                }
            }
            (
                ast::ExprKind::Is { value, pattern },
                ExprKind::Is {
                    value: v,
                    pattern: p,
                },
            ) => {
                self.expr(value, *v, d)?;
                self.pattern(pattern, *p, d)?;
            }
            (
                ast::ExprKind::While { condition, body },
                ExprKind::While {
                    condition: c,
                    body: b,
                },
            ) => {
                self.expr(condition, *c, d)?;
                self.block(body, b, d)?;
            }
            (
                ast::ExprKind::WhileLet {
                    pattern,
                    value,
                    body,
                },
                ExprKind::WhileLet {
                    pattern: p,
                    value: v,
                    body: b,
                },
            ) => {
                self.expr(value, *v, d)?;
                self.pattern(pattern, *p, d)?;
                self.block(body, b, d)?;
            }
            (
                ast::ExprKind::For {
                    iterable,
                    pattern,
                    body,
                },
                ExprKind::For {
                    iterable: i,
                    pattern: p,
                    body: b,
                },
            ) => {
                self.expr(iterable, *i, d)?;
                self.pattern(pattern, *p, d)?;
                self.block(body, b, d)?;
            }
            (
                ast::ExprKind::Control { operation, value },
                ExprKind::Control {
                    operation: o,
                    value: v,
                },
            ) => {
                self.equal(operation == o)?;
                self.opt_expr(value.as_deref_mut(), *v, d)?;
            }
            (ast::ExprKind::TypeValue(a), ExprKind::TypeValue(b))
            | (ast::ExprKind::KeyOf(a), ExprKind::KeyOf(b)) => self.ty(a, *b, d)?,
            (ast::ExprKind::Derive { base, recipe }, ExprKind::Derive { base: b, recipe: r }) => {
                self.opt_expr(base.as_deref_mut(), *b, d)?;
                self.expr(recipe, *r, d)?;
            }
            (
                ast::ExprKind::Range {
                    start,
                    end,
                    inclusive,
                },
                ExprKind::Range {
                    start: a,
                    end: b,
                    inclusive: i,
                },
            ) => {
                self.equal(inclusive == i)?;
                self.opt_expr(start.as_deref_mut(), *a, d)?;
                self.opt_expr(end.as_deref_mut(), *b, d)?;
            }
            (ast::ExprKind::Ambient, ExprKind::Ambient)
            | (ast::ExprKind::Error, ExprKind::Error) => {}
            _ => return Err(LowerError::Correspondence),
        }
        if self.validate_ids {
            self.equal(actual.hir_id == Some(id))?;
        }
        if self.write {
            actual.hir_id = Some(id);
        }
        Ok(())
    }
    fn ty(
        &mut self,
        actual: &mut ast::TypeExpr,
        id: TypeExprId,
        depth: usize,
    ) -> Result<(), LowerError> {
        self.enter(depth)?;
        let hir = self.hir;
        let expected = hir.type_expression(id).ok_or(LowerError::Correspondence)?;
        let d = depth + 1;
        match (&mut actual.kind, &expected.kind) {
            (
                ast::TypeKind::Name { path, arguments },
                TypeKind::Name {
                    path: p,
                    arguments: a,
                },
            ) => {
                self.path(path, p)?;
                self.types(arguments, a, d)?;
            }
            (ast::TypeKind::Optional(a), TypeKind::Optional(b))
            | (ast::TypeKind::KeyOf(a), TypeKind::KeyOf(b))
            | (ast::TypeKind::Rest(a), TypeKind::Rest(b)) => self.ty(a, *b, d)?,
            (
                ast::TypeKind::Array { length, element },
                TypeKind::Array {
                    length: l,
                    element: e,
                },
            ) => {
                self.opt_expr(length.as_deref_mut(), *l, d)?;
                self.ty(element, *e, d)?;
            }
            (ast::TypeKind::Map { key, value }, TypeKind::Map { key: k, value: v }) => {
                self.ty(key, *k, d)?;
                self.ty(value, *v, d)?;
            }
            (ast::TypeKind::Tuple(a), TypeKind::Tuple(b)) => self.types(a, b, d)?,
            (ast::TypeKind::Record { fields, row }, TypeKind::Record { fields: f, row: r }) => {
                self.equal(fields.len() == f.len())?;
                for (a, b) in fields.iter_mut().zip(f) {
                    self.text(&a.name, &b.name)?;
                    self.equal(a.mutable == b.mutable)?;
                    self.ty(&mut a.ty, b.ty, d)?;
                }
                self.opt_type(row.as_deref_mut(), *r, d)?;
            }
            (
                ast::TypeKind::Callable {
                    parameters,
                    result,
                    annotations,
                },
                TypeKind::Callable {
                    parameters: p,
                    result: r,
                    annotations: a,
                },
            ) => {
                self.parameters(parameters, p, d)?;
                self.opt_type(result.as_deref_mut(), *r, d)?;
                self.annotations(annotations, a)?;
            }
            (
                ast::TypeKind::TypeFunction { parameters, body },
                TypeKind::TypeFunction {
                    parameters: p,
                    body: b,
                },
            ) => {
                self.generics(parameters, p, d)?;
                self.expr(body, *b, d)?;
            }
            (
                ast::TypeKind::Projection { base, field },
                TypeKind::Projection { base: b, field: f },
            ) => {
                self.ty(base, *b, d)?;
                self.text(field, f)?;
            }
            (
                ast::TypeKind::ComputedProjection { base, key },
                TypeKind::ComputedProjection { base: b, key: k },
            ) => {
                self.ty(base, *b, d)?;
                self.expr(key, *k, d)?;
            }
            (ast::TypeKind::Computation(a), TypeKind::Computation(b)) => self.expr(a, *b, d)?,
            (
                ast::TypeKind::Mapped {
                    binder,
                    keys,
                    value,
                    tuple,
                },
                TypeKind::Mapped {
                    binder: b,
                    keys: k,
                    value: v,
                    tuple: t,
                },
            ) => {
                self.equal(tuple == t)?;
                self.text(binder, b)?;
                self.expr(keys, *k, d)?;
                self.ty(value, *v, d)?;
            }
            (
                ast::TypeKind::KindArrow { parameter, result },
                TypeKind::KindArrow {
                    parameter: p,
                    result: r,
                },
            ) => {
                self.ty(parameter, *p, d)?;
                self.ty(result, *r, d)?;
            }
            (ast::TypeKind::Error, TypeKind::Error) => {}
            _ => return Err(LowerError::Correspondence),
        }
        if self.validate_ids {
            self.equal(actual.hir_id == Some(id))?;
        }
        if self.write {
            actual.hir_id = Some(id);
        }
        Ok(())
    }
    fn pattern(
        &mut self,
        actual: &mut ast::Pattern,
        id: PatternId,
        depth: usize,
    ) -> Result<(), LowerError> {
        self.enter(depth)?;
        let hir = self.hir;
        let expected = hir.pattern(id).ok_or(LowerError::Correspondence)?;
        let d = depth + 1;
        match (&mut actual.kind, &expected.kind) {
            (ast::PatternKind::Name(a), PatternKind::Name(b)) => self.text(a, b)?,
            (ast::PatternKind::Wildcard, PatternKind::Wildcard)
            | (ast::PatternKind::Error, PatternKind::Error) => {}
            (ast::PatternKind::Literal(a), PatternKind::Literal(b)) => self.literal(a, b)?,
            (ast::PatternKind::Tuple(a), PatternKind::Tuple(b))
            | (ast::PatternKind::Array(a), PatternKind::Array(b))
            | (ast::PatternKind::Alternative(a), PatternKind::Alternative(b)) => {
                self.patterns(a, b, d)?
            }
            (ast::PatternKind::Rest(a), PatternKind::Rest(b)) => {
                self.optional_text(a.as_deref(), b.as_deref())?
            }
            (
                ast::PatternKind::Record {
                    ty,
                    fields,
                    rest,
                    rest_binding,
                },
                PatternKind::Record {
                    ty: t,
                    fields: f,
                    rest: r,
                    rest_binding: b,
                },
            ) => {
                self.equal(rest == r && fields.len() == f.len())?;
                self.opt_type(ty.as_mut(), *t, d)?;
                self.optional_text(rest_binding.as_deref(), b.as_deref())?;
                for (a, b) in fields.iter_mut().zip(f) {
                    self.text(&a.name, &b.name)?;
                    self.pattern(&mut a.pattern, b.pattern, d)?;
                }
            }
            (
                ast::PatternKind::Constructor {
                    path,
                    arguments,
                    parenthesized,
                },
                PatternKind::Constructor {
                    path: p,
                    arguments: a,
                    parenthesized: b,
                },
            ) => {
                self.equal(parenthesized == b)?;
                self.path(path, p)?;
                self.patterns(arguments, a, d)?;
            }
            (
                ast::PatternKind::Mode { mode, pattern },
                PatternKind::Mode {
                    mode: m,
                    pattern: p,
                },
            ) => {
                self.equal(mode == m)?;
                self.pattern(pattern, *p, d)?;
            }
            (ast::PatternKind::Type { ty, binder }, PatternKind::Type { ty: t, binder: b }) => {
                self.ty(ty, *t, d)?;
                self.optional_text(binder.as_deref(), b.as_deref())?;
            }
            (ast::PatternKind::Value(a), PatternKind::Value(b)) => self.expr(a, *b, d)?,
            _ => return Err(LowerError::Correspondence),
        }
        if self.validate_ids {
            self.equal(actual.hir_id == Some(id))?;
        }
        if self.write {
            actual.hir_id = Some(id);
        }
        Ok(())
    }
}

pub(super) fn program(
    hir: &HirProgram,
    source: &mut ast::Program,
    limits: HirLimits,
) -> Result<(), LowerError> {
    Identify {
        hir,
        left: limits,
        write: false,
        validate_ids: false,
    }
    .statements(&mut source.statements, &hir.roots, 0)?;
    // The only intervening mutation is ID assignment, which the pairing never
    // reads. This second pass therefore has the exact same admitted work.
    Identify {
        hir,
        left: limits,
        write: true,
        validate_ids: false,
    }
    .statements(&mut source.statements, &hir.roots, 0)
}
pub(super) fn expression(
    hir: &HirProgram,
    source: &mut ast::Expr,
    id: ExprId,
    limits: HirLimits,
) -> Result<(), LowerError> {
    Identify {
        hir,
        left: limits,
        write: false,
        validate_ids: false,
    }
    .expr(source, id, 0)?;
    Identify {
        hir,
        left: limits,
        write: true,
        validate_ids: false,
    }
    .expr(source, id, 0)
}

pub(super) fn statement(
    hir: &HirProgram,
    source: &mut ast::Stmt,
    id: StmtId,
    limits: HirLimits,
) -> Result<(), LowerError> {
    Identify {
        hir,
        left: limits,
        write: false,
        validate_ids: false,
    }
    .stmt(source, id, 0)?;
    Identify {
        hir,
        left: limits,
        write: true,
        validate_ids: false,
    }
    .stmt(source, id, 0)
}

pub(super) fn validate_type_syntax(
    hir: &HirProgram,
    source: &mut ast::TypeExpr,
    id: TypeExprId,
    limits: HirLimits,
) -> Result<(), LowerError> {
    Identify {
        hir,
        left: limits,
        write: false,
        validate_ids: true,
    }
    .ty(source, id, 0)
}

pub(super) fn validate_catalog_declaration(
    hir: &HirProgram,
    source: &mut ast::Stmt,
    id: StmtId,
    limits: HirLimits,
) -> Result<(), LowerError> {
    Identify {
        hir,
        left: limits,
        write: false,
        validate_ids: false,
    }
    .stmt(source, id, 0)
}

pub(super) fn validate_statement_syntax(
    hir: &HirProgram,
    source: &mut ast::Stmt,
    id: StmtId,
    limits: HirLimits,
) -> Result<(), LowerError> {
    Identify {
        hir,
        left: limits,
        write: false,
        validate_ids: true,
    }
    .stmt(source, id, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_compiler_core::source::FileId;

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 1,
            end: 2,
        }
    }
    fn name(value: &str) -> ast::Expr {
        ast::Expr {
            kind: ast::ExprKind::Name(value.into()),
            span: span(),
            hir_id: None,
        }
    }
    fn program(value: ast::Expr) -> ast::Program {
        ast::Program {
            statements: vec![ast::Stmt {
                kind: ast::StmtKind::Expr {
                    expression: value,
                    terminated: false,
                },
                span: span(),
                hir_id: None,
            }],
        }
    }
    fn record(value: ast::Expr) -> ast::Expr {
        ast::Expr {
            kind: ast::ExprKind::Record {
                ty: None,
                members: vec![ast::RecordMember::Field(ast::RecordField {
                    name: "item".into(),
                    value,
                    span: span(),
                })],
            },
            span: span(),
            hir_id: None,
        }
    }

    #[test]
    fn identified_ast_clones_keep_ids_without_changing_structure_or_debug_keys() {
        let mut parsed = ril_syntax::parse(ril_test::case_source(
            "tests/regressions/semantic-hir.ril::lexical-owners",
        ));
        assert!(parsed.is_ok());
        let original = parsed.program.clone();
        let debug = format!("{:?}", parsed.program);
        parsed.program.statements[0].hir_id = Some(StmtId(u32::MAX));
        let ast::StmtKind::Type(declaration) = &mut parsed.program.statements[0].kind else {
            panic!()
        };
        declaration.generics[0].hir_id = Some(GenericParamId(u32::MAX));
        declaration.value.as_mut().unwrap().hir_id = Some(TypeExprId(u32::MAX));
        let ast::StmtKind::Function(function) = &mut parsed.program.statements[1].kind else {
            panic!()
        };
        function.parameters[0].pattern.hir_id = Some(PatternId(u32::MAX));
        let hir = HirProgram::lower_identified(&mut parsed.program, InputOrigin::Source).unwrap();
        assert_eq!(parsed.program, original);
        assert_eq!(format!("{:?}", parsed.program), debug);
        assert_eq!(parsed.program.statements[0].hir_id, Some(hir.roots()[0]));
        let ast::StmtKind::Type(declaration) = &parsed.program.statements[0].kind else {
            panic!()
        };
        assert_ne!(
            declaration.generics[0].hir_id,
            Some(GenericParamId(u32::MAX))
        );
        assert!(
            hir.generic(declaration.generics[0].hir_id.unwrap())
                .is_some()
        );
        assert!(
            hir.type_expression(declaration.value.as_ref().unwrap().hir_id.unwrap())
                .is_some()
        );
        let ast::StmtKind::Function(function) = &parsed.program.statements[1].kind else {
            panic!()
        };
        assert!(
            hir.pattern(function.parameters[0].pattern.hir_id.unwrap())
                .is_some()
        );
        let original_body = function.body.as_ref().unwrap();
        let cloned_body = original_body.clone();
        assert_eq!(
            cloned_body.statements[0].hir_id,
            original_body.statements[0].hir_id
        );
        let ast::StmtKind::Expr { expression, .. } = &original_body.statements[0].kind else {
            panic!()
        };
        let ast::StmtKind::Expr {
            expression: cloned, ..
        } = &cloned_body.statements[0].kind
        else {
            panic!()
        };
        assert!(expression.hir_id.is_some());
        assert_eq!(cloned.hir_id, expression.hir_id);
    }

    #[test]
    fn equal_span_occurrences_replace_untrusted_ids_with_distinct_structural_ids() {
        let mut child = name("same");
        child.hir_id = Some(ExprId(u32::MAX));
        let mut source = program(ast::Expr {
            kind: ast::ExprKind::Tuple(vec![child.clone(), child]),
            span: span(),
            hir_id: Some(ExprId(u32::MAX)),
        });
        let ignored = HirProgram::lower(&source).unwrap();
        assert!(ignored.expression(ExprId(u32::MAX)).is_none());
        let hir = HirProgram::lower_identified(
            &mut source,
            InputOrigin::Transformed(GeneratedKind::StaticMaterialization),
        )
        .unwrap();
        let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
            panic!()
        };
        let ast::ExprKind::Tuple(items) = &expression.kind else {
            panic!()
        };
        assert_ne!(items[0].hir_id, items[1].hir_id);
        for child in items {
            assert!(matches!(
                hir.expression(child.hir_id.unwrap()).unwrap().info.origin,
                NodeOrigin::Transformed { .. }
            ));
        }
    }

    #[test]
    fn ordered_record_members_keep_one_identity_and_preflight_every_node() {
        let value = name("same");
        let mut source = program(record(value));
        source.statements[0].hir_id = Some(StmtId(99));
        // Statement, record and field expression each have one semantic node.
        // Insufficient admission writes no occurrence IDs.
        let limits = HirLimits {
            nodes: 2,
            ..Default::default()
        };
        assert!(
            HirProgram::lower_identified_with_limits(&mut source, InputOrigin::Source, limits)
                .is_err()
        );
        assert_eq!(source.statements[0].hir_id, Some(StmtId(99)));
        let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
            panic!()
        };
        assert_eq!(expression.hir_id, None);
        let hir = HirProgram::lower_identified(&mut source, InputOrigin::Source).unwrap();
        let ast::StmtKind::Expr { expression, .. } = &source.statements[0].kind else {
            panic!()
        };
        let ast::ExprKind::Record { members, .. } = &expression.kind else {
            panic!()
        };
        let ast::RecordMember::Field(member) = &members[0] else {
            panic!()
        };
        assert_ne!(expression.hir_id, member.value.hir_id);
        assert!(hir.expression(member.value.hir_id.unwrap()).is_some());
    }

    #[test]
    fn generated_identification_budget_failure_preserves_ids_and_arena() {
        let mut source = program(name("original"));
        let mut hir = HirProgram::lower_identified(&mut source, InputOrigin::Source).unwrap();
        let anchor = NodeId::Stmt(source.statements[0].hir_id.unwrap());
        let before = hir.node_count();
        let mut generated = record(name("actual"));
        assert!(matches!(
            hir.mint_generated_identified_expr(
                &mut generated,
                anchor,
                GeneratedKind::Desugaring,
                LexicalOwner::Module,
                HirLimits {
                    nodes: 1,
                    ..Default::default()
                }
            ),
            Err(LowerError::Budget(_))
        ));
        assert_eq!(hir.node_count(), before);
        assert!(hir.generated_roots().is_empty());
        assert_eq!(generated.hir_id, None);
        let ast::ExprKind::Record { members, .. } = &mut generated.kind else {
            panic!()
        };
        let ast::RecordMember::Field(member) = &members[0] else {
            panic!()
        };
        assert_eq!(member.value.hir_id, None);
        let id = hir
            .mint_generated_identified_expr(
                &mut generated,
                anchor,
                GeneratedKind::Desugaring,
                LexicalOwner::Module,
                HirLimits::default(),
            )
            .unwrap();
        assert_eq!(generated.hir_id, Some(id));
        assert_eq!(hir.generated_roots(), &[NodeId::Expr(id)]);
        assert!(
            matches!(hir.expression(id).unwrap().info.origin, NodeOrigin::Generated { generation: 0, anchor: actual, .. } if actual == anchor)
        );
    }

    #[test]
    fn generated_statement_identification_rolls_back_every_arena_before_publishing_ids() {
        let mut source = program(name("original"));
        let mut hir = HirProgram::lower_identified(&mut source, InputOrigin::Source).unwrap();
        let anchor = NodeId::Stmt(source.statements[0].hir_id.unwrap());
        let before = hir.node_count();
        let mut generated = ast::Stmt {
            hir_id: Some(StmtId(99)),
            span: span(),
            kind: ast::StmtKind::Expr {
                expression: record(name("actual")),
                terminated: false,
            },
        };
        assert!(matches!(
            hir.mint_generated_identified_statement(
                &mut generated,
                anchor,
                GeneratedKind::StaticSpecialization,
                LexicalOwner::Module,
                HirLimits {
                    text_bytes: 0,
                    ..Default::default()
                },
            ),
            Err(LowerError::Budget(_))
        ));
        assert_eq!(hir.node_count(), before);
        assert!(hir.generated_roots().is_empty());
        assert_eq!(generated.hir_id, Some(StmtId(99)));
        let ast::StmtKind::Expr { expression, .. } = &mut generated.kind else {
            unreachable!()
        };
        assert_eq!(expression.hir_id, None);
        let ast::ExprKind::Record { members, .. } = &mut expression.kind else {
            unreachable!()
        };
        let ast::RecordMember::Field(member) = &members[0] else {
            unreachable!()
        };
        assert_eq!(member.value.hir_id, None);
        let limited = HirLimits {
            nodes: 1,
            ..HirLimits::default()
        };
        assert!(matches!(
            hir.mint_generated_identified_statement(
                &mut generated,
                anchor,
                GeneratedKind::StaticSpecialization,
                LexicalOwner::Module,
                limited,
            ),
            Err(LowerError::Budget(_))
        ));
        assert_eq!(hir.node_count(), before);
        assert!(hir.generated_roots().is_empty());
        assert_eq!(generated.hir_id, Some(StmtId(99)));
        let id = hir
            .mint_generated_identified_statement(
                &mut generated,
                anchor,
                GeneratedKind::StaticSpecialization,
                LexicalOwner::Module,
                HirLimits::default(),
            )
            .unwrap();
        assert_eq!(generated.hir_id, Some(id));
        assert_ne!(id, StmtId(99));
        assert_eq!(hir.generated_roots(), &[NodeId::Stmt(id)]);
        assert!(matches!(hir.statement(id).unwrap().info.origin,
            NodeOrigin::Generated { generation: 0, anchor: actual,
                kind: GeneratedKind::StaticSpecialization } if actual == anchor));
        hir.validate_statement_syntax(&mut generated, id, HirLimits::default())
            .unwrap();
    }

    #[test]
    fn generated_patterns_share_transactional_roots_and_generations_with_expressions() {
        let mut source = program(name("original"));
        let mut hir = HirProgram::lower_identified(&mut source, InputOrigin::Source).unwrap();
        let anchor = NodeId::Stmt(source.statements[0].hir_id.unwrap());
        let before = hir.node_count();
        let empty = HirLimits {
            nodes: 0,
            ..HirLimits::default()
        };
        assert!(
            hir.mint_generated_name_pattern(anchor, GeneratedKind::ResourceLease, "lease", empty)
                .is_err()
        );
        assert_eq!(hir.node_count(), before);
        assert!(hir.generated_roots().is_empty());
        assert!(
            hir.mint_generated_name_pattern(
                NodeId::Expr(ExprId(u32::MAX)),
                GeneratedKind::ResourceLease,
                "lease",
                HirLimits::default()
            )
            .is_err()
        );
        assert_eq!(hir.node_count(), before);
        let pattern = hir
            .mint_generated_name_pattern(
                anchor,
                GeneratedKind::ResourceLease,
                "lease",
                HirLimits::default(),
            )
            .unwrap();
        let expression = hir
            .mint_generated_expr(
                &name("value"),
                anchor,
                GeneratedKind::Desugaring,
                LexicalOwner::Module,
                HirLimits::default(),
            )
            .unwrap();
        assert_eq!(
            hir.generated_roots(),
            &[NodeId::Pattern(pattern), NodeId::Expr(expression)]
        );
        assert!(matches!(
            hir.pattern(pattern).unwrap().info.origin,
            NodeOrigin::Generated { generation: 0, .. }
        ));
        assert!(matches!(
            hir.expression(expression).unwrap().info.origin,
            NodeOrigin::Generated { generation: 1, .. }
        ));
        let mut seen = false;
        hir.walk(4096, |id, _| seen |= id == NodeId::Pattern(pattern))
            .unwrap();
        assert!(seen);
    }
}
