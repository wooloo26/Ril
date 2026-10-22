//! Borrow original declaration syntax by identity for one header query. This
//! walk neither resolves names nor clones or retains another source tree.
use crate::sema::source_types::{SourceTypesError, WorkLimit};
use ril_compiler_core::ids::StmtId;
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

enum Node<'a> {
    Statement(&'a Stmt),
    Function(&'a Function),
    Block(&'a Block),
    Parameter(&'a Parameter),
    Generic(&'a GenericParameter),
    Type(&'a TypeExpr),
    Expression(&'a Expr),
    Pattern(&'a Pattern),
    Variant(&'a Variant),
    Handler(&'a HandlerArm),
    Match(&'a MatchArm),
    StringPart(&'a StringPart),
    RecordMember(&'a RecordMember),
    RecordField(&'a RecordField),
    Argument(&'a Argument),
    PatternField(&'a PatternField),
    Pair(&'a Expr, &'a Expr),
}

struct Walk<'a, 'w> {
    pending: Vec<(Node<'a>, usize)>,
    declarations: BTreeMap<StmtId, &'a Stmt>,
    statements: BTreeSet<StmtId>,
    work: &'w mut WorkLimit,
}

fn lookup_cost(len: usize) -> usize {
    len.checked_ilog2().unwrap_or(0) as usize + 1
}

pub(super) fn declarations<'a>(
    program: &'a Program,
    work: &mut WorkLimit,
) -> Result<BTreeMap<StmtId, &'a Stmt>, SourceTypesError> {
    work.charge(1)?;
    let mut walk = Walk {
        pending: Vec::new(),
        declarations: BTreeMap::new(),
        statements: BTreeSet::new(),
        work,
    };
    walk.slice(&program.statements, 0, Node::Statement)?;
    while let Some((node, depth)) = walk.pending.pop() {
        walk.work.charge(1)?;
        walk.visit(node, depth)?;
    }
    Ok(walk.declarations)
}

impl<'a> Walk<'a, '_> {
    fn push(&mut self, node: Node<'a>, depth: usize) -> Result<(), SourceTypesError> {
        self.work.charge(1)?;
        if depth > 128 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        self.pending.push((node, depth));
        Ok(())
    }

    fn slice<T: 'a>(
        &mut self,
        values: &'a [T],
        depth: usize,
        node: impl Fn(&'a T) -> Node<'a>,
    ) -> Result<(), SourceTypesError> {
        self.work.charge(values.len())?;
        for value in values {
            self.push(node(value), depth)?;
        }
        Ok(())
    }

    fn optional<T: 'a>(
        &mut self,
        value: Option<&'a T>,
        depth: usize,
        node: impl FnOnce(&'a T) -> Node<'a>,
    ) -> Result<(), SourceTypesError> {
        if let Some(value) = value {
            self.push(node(value), depth)?;
        }
        Ok(())
    }

    fn visit(&mut self, node: Node<'a>, depth: usize) -> Result<(), SourceTypesError> {
        let child = depth + 1;
        match node {
            Node::Statement(statement) => {
                let id = statement.hir_id.ok_or(SourceTypesError::MissingNode)?;
                self.work.charge(lookup_cost(self.statements.len()))?;
                if !self.statements.insert(id) {
                    return Err(SourceTypesError::AlreadyDefined);
                }
                match &statement.kind {
                    StmtKind::Type(declaration) => {
                        self.work.charge(lookup_cost(self.declarations.len()))?;
                        self.declarations.insert(id, statement);
                        self.slice(&declaration.generics, child, Node::Generic)?;
                        self.optional(declaration.value.as_ref(), child, Node::Type)?;
                        self.slice(&declaration.variants, child, Node::Variant)?;
                    }
                    StmtKind::Function(function) => self.push(Node::Function(function), child)?,
                    StmtKind::Binding(binding) => {
                        self.push(Node::Pattern(&binding.pattern), child)?;
                        self.optional(binding.ty.as_ref(), child, Node::Type)?;
                        self.push(Node::Expression(&binding.value), child)?;
                        self.optional(binding.fallback.as_ref(), child, Node::Expression)?;
                    }
                    StmtKind::Effect(effect) => {
                        self.slice(&effect.generics, child, Node::Generic)?;
                        self.slice(&effect.operations, child, Node::Function)?;
                        self.slice(&effect.members, child, Node::Type)?;
                    }
                    StmtKind::Handler(arms) => self.slice(arms, child, Node::Handler)?,
                    StmtKind::Expr { expression, .. }
                    | StmtKind::HandlerApplication(expression) => {
                        self.push(Node::Expression(expression), child)?;
                    }
                    StmtKind::Assignment { target, value, .. } => {
                        self.push(Node::Expression(target), child)?;
                        self.push(Node::Expression(value), child)?;
                    }
                    StmtKind::Use(_) => {}
                }
            }
            Node::Function(function) => {
                self.slice(&function.generics, child, Node::Generic)?;
                self.slice(&function.parameters, child, Node::Parameter)?;
                self.slice(&function.signature_where, child, Node::Statement)?;
                self.optional(function.return_type.as_ref(), child, Node::Type)?;
                self.optional(function.body.as_ref(), child, Node::Block)?;
            }
            Node::Block(block) => {
                self.slice(&block.where_items, child, Node::Statement)?;
                self.slice(&block.statements, child, Node::Statement)?;
            }
            Node::Parameter(parameter) => {
                self.push(Node::Pattern(&parameter.pattern), child)?;
                self.optional(parameter.ty.as_ref(), child, Node::Type)?;
                self.optional(parameter.default.as_ref(), child, Node::Expression)?;
            }
            Node::Generic(generic) => {
                self.optional(generic.bound.as_ref(), child, Node::Type)?;
                self.optional(generic.default.as_ref(), child, Node::Type)?;
            }
            Node::Type(ty) => match &ty.kind {
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    self.slice(arguments, child, Node::Type)?;
                }
                TypeKind::Optional(ty) | TypeKind::Rest(ty) | TypeKind::KeyOf(ty) => {
                    self.push(Node::Type(ty), child)?;
                }
                TypeKind::Array { length, element } => {
                    self.optional(length.as_deref(), child, Node::Expression)?;
                    self.push(Node::Type(element), child)?;
                }
                TypeKind::Map { key, value }
                | TypeKind::KindArrow {
                    parameter: key,
                    result: value,
                } => {
                    self.push(Node::Type(key), child)?;
                    self.push(Node::Type(value), child)?;
                }
                TypeKind::Record { fields, row } => {
                    self.slice(fields, child, |field| Node::Type(&field.ty))?;
                    self.optional(row.as_deref(), child, Node::Type)?;
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    self.slice(parameters, child, Node::Parameter)?;
                    self.optional(result.as_deref(), child, Node::Type)?;
                }
                TypeKind::TypeFunction { parameters, body } => {
                    self.slice(parameters, child, Node::Generic)?;
                    self.push(Node::Expression(body), child)?;
                }
                TypeKind::Projection { base, .. } => self.push(Node::Type(base), child)?,
                TypeKind::ComputedProjection { base, key } => {
                    self.push(Node::Type(base), child)?;
                    self.push(Node::Expression(key), child)?;
                }
                TypeKind::Computation(expression) => {
                    self.push(Node::Expression(expression), child)?;
                }
                TypeKind::Mapped { keys, value, .. } => {
                    self.push(Node::Expression(keys), child)?;
                    self.push(Node::Type(value), child)?;
                }
                TypeKind::Error => {}
            },
            Node::Expression(expression) => match &expression.kind {
                ExprKind::Literal(_)
                | ExprKind::Name(_)
                | ExprKind::Path(_)
                | ExprKind::Accessor(_)
                | ExprKind::Ambient
                | ExprKind::Error => {}
                ExprKind::Interpolated(parts) => self.slice(parts, child, Node::StringPart)?,
                ExprKind::Generic { base, arguments } => {
                    self.push(Node::Expression(base), child)?;
                    self.slice(arguments, child, Node::Type)?;
                }
                ExprKind::Tuple(values) | ExprKind::Array(values) => {
                    self.slice(values, child, Node::Expression)?;
                }
                ExprKind::Map(entries) => {
                    self.slice(entries, child, |entry| Node::Pair(&entry.0, &entry.1))?;
                }
                ExprKind::Record {
                    ty,
                    fields,
                    spread,
                    members,
                } => {
                    self.optional(ty.as_ref(), child, Node::Type)?;
                    // These compatibility fields mirror members after source
                    // identification; their IDs are not another occurrence.
                    if members.is_empty() {
                        self.slice(fields, child, Node::RecordField)?;
                        self.optional(spread.as_deref(), child, Node::Expression)?;
                    } else {
                        self.slice(members, child, Node::RecordMember)?;
                    }
                }
                ExprKind::Unary { operand, .. } | ExprKind::Field { base: operand, .. } => {
                    self.push(Node::Expression(operand), child)?;
                }
                ExprKind::Binary { left, right, .. }
                | ExprKind::ComputedField {
                    base: left,
                    key: right,
                }
                | ExprKind::Index {
                    base: left,
                    index: right,
                    ..
                } => {
                    self.push(Node::Expression(left), child)?;
                    self.push(Node::Expression(right), child)?;
                }
                ExprKind::Call { callee, arguments } => {
                    self.push(Node::Expression(callee), child)?;
                    self.slice(arguments, child, Node::Argument)?;
                }
                ExprKind::Lambda {
                    parameters,
                    return_type,
                    body,
                    ..
                } => {
                    self.slice(parameters, child, Node::Parameter)?;
                    self.optional(return_type.as_ref(), child, Node::Type)?;
                    self.push(Node::Expression(body), child)?;
                }
                ExprKind::Block(block) | ExprKind::Loop(block) => {
                    self.push(Node::Block(block), child)?
                }
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    self.push(Node::Expression(condition), child)?;
                    self.push(Node::Expression(then_branch), child)?;
                    self.optional(else_branch.as_deref(), child, Node::Expression)?;
                }
                ExprKind::Match { value, arms, .. } => {
                    self.push(Node::Expression(value), child)?;
                    self.slice(arms, child, Node::Match)?;
                }
                ExprKind::Is { value, pattern } => {
                    self.push(Node::Expression(value), child)?;
                    self.push(Node::Pattern(pattern), child)?;
                }
                ExprKind::While { condition, body } => {
                    self.push(Node::Expression(condition), child)?;
                    self.push(Node::Block(body), child)?;
                }
                ExprKind::For {
                    iterable,
                    pattern,
                    body,
                } => {
                    self.push(Node::Expression(iterable), child)?;
                    self.push(Node::Pattern(pattern), child)?;
                    self.push(Node::Block(body), child)?;
                }
                ExprKind::Control { value, .. } => {
                    self.optional(value.as_deref(), child, Node::Expression)?
                }
                ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) => {
                    self.push(Node::Type(ty), child)?
                }
                ExprKind::Derive { base, recipe } => {
                    self.optional(base.as_deref(), child, Node::Expression)?;
                    self.push(Node::Expression(recipe), child)?;
                }
                ExprKind::Range { start, end, .. } => {
                    self.optional(start.as_deref(), child, Node::Expression)?;
                    self.optional(end.as_deref(), child, Node::Expression)?;
                }
            },
            Node::Pattern(pattern) => match &pattern.kind {
                PatternKind::Name(_)
                | PatternKind::Wildcard
                | PatternKind::Literal(_)
                | PatternKind::Error => {}
                PatternKind::Tuple(items)
                | PatternKind::Alternative(items)
                | PatternKind::Constructor {
                    arguments: items, ..
                } => self.slice(items, child, Node::Pattern)?,
                PatternKind::Record { ty, fields, .. } => {
                    self.optional(ty.as_ref(), child, Node::Type)?;
                    self.slice(fields, child, Node::PatternField)?;
                }
                PatternKind::Mode { pattern, .. } => self.push(Node::Pattern(pattern), child)?,
                PatternKind::Type { ty, .. } => self.push(Node::Type(ty), child)?,
                PatternKind::Value(expression) => self.push(Node::Expression(expression), child)?,
            },
            Node::Variant(variant) => {
                self.slice(&variant.generics, child, Node::Generic)?;
                self.optional(variant.payload.as_ref(), child, Node::Type)?;
                self.optional(variant.result.as_ref(), child, Node::Type)?;
            }
            Node::Handler(arm) => {
                self.push(Node::Expression(&arm.operation), child)?;
                self.slice(&arm.parameters, child, Node::Parameter)?;
                self.push(Node::Expression(&arm.body), child)?;
            }
            Node::Match(arm) => {
                self.push(Node::Pattern(&arm.pattern), child)?;
                self.optional(arm.guard.as_ref(), child, Node::Expression)?;
                self.push(Node::Expression(&arm.body), child)?;
            }
            Node::StringPart(part) => match part {
                StringPart::Text(_) => {}
                StringPart::Interpolation { expression, .. } => {
                    self.push(Node::Expression(expression), child)?
                }
            },
            Node::RecordMember(member) => match member {
                RecordMember::Field(field) => self.push(Node::RecordField(field), child)?,
                RecordMember::Spread(expression) => {
                    self.push(Node::Expression(expression), child)?
                }
            },
            Node::RecordField(field) => self.push(Node::Expression(&field.value), child)?,
            Node::Argument(argument) => self.push(Node::Expression(&argument.value), child)?,
            Node::PatternField(field) => self.push(Node::Pattern(&field.pattern), child)?,
            Node::Pair(key, value) => {
                self.push(Node::Expression(key), child)?;
                self.push(Node::Expression(value), child)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{HirProgram, nodes::InputOrigin};
    use ril_compiler_core::source::{FileId, Span};

    fn fixture() -> Program {
        let mut program = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::shadowed-alias-pattern-safe",
        ))
        .program;
        HirProgram::lower_identified(&mut program, InputOrigin::Source).unwrap();
        program
    }

    fn span() -> Span {
        Span {
            file: FileId(0),
            start: 0,
            end: 0,
        }
    }

    fn declaration(id: u32) -> Stmt {
        Stmt {
            kind: StmtKind::Type(TypeDeclaration {
                visibility: Visibility::Private,
                is_halt: false,
                name: format!("Type{id}"),
                generics: vec![],
                value: None,
                variants: vec![],
                opaque: false,
                nominal: false,
                span: span(),
            }),
            span: span(),
            hir_id: Some(StmtId(id)),
        }
    }

    fn expression(id: u32) -> Expr {
        Expr {
            kind: ExprKind::Block(Block {
                statements: vec![declaration(id)],
                where_items: vec![],
                span: span(),
            }),
            span: span(),
            hir_id: None,
        }
    }

    fn computation(id: u32) -> TypeExpr {
        TypeExpr {
            kind: TypeKind::Computation(Box::new(expression(id))),
            text: String::new(),
            span: span(),
            hir_id: None,
        }
    }

    #[test]
    fn original_statement_ids_keep_both_same_named_aliases() {
        let program = fixture();
        let values = declarations(&program, &mut WorkLimit::new(65_536)).unwrap();
        assert_eq!(values.len(), 2);
        for (id, statement) in values {
            assert_eq!(statement.hir_id, Some(id));
            assert!(matches!(&statement.kind, StmtKind::Type(value) if value.name == "Narrow"));
        }
    }

    #[test]
    fn query_reaches_headers_defaults_computations_patterns_and_record_primary_members() {
        let program = fixture();
        let StmtKind::Function(mut function) = program.statements[1].kind.clone() else {
            unreachable!()
        };
        function.generics = vec![GenericParameter {
            name: "T".into(),
            bound: Some(computation(6)),
            default: Some(computation(7)),
            span: span(),
            hir_id: None,
        }];
        function.parameters = vec![Parameter {
            pattern: Pattern {
                kind: PatternKind::Value(Box::new(expression(3))),
                span: span(),
                hir_id: None,
            },
            mode: ParameterMode::Read,
            ty: Some(computation(4)),
            default: Some(expression(5)),
            span: span(),
        }];
        function.return_type = Some(TypeExpr {
            kind: TypeKind::Callable {
                parameters: vec![Parameter {
                    pattern: Pattern {
                        kind: PatternKind::Wildcard,
                        span: span(),
                        hir_id: None,
                    },
                    mode: ParameterMode::Read,
                    ty: None,
                    default: Some(expression(8)),
                    span: span(),
                }],
                result: Some(Box::new(computation(9))),
                annotations: vec![],
            },
            text: String::new(),
            span: span(),
            hir_id: None,
        });
        let mut first = declaration(1);
        let StmtKind::Type(value) = &mut first.kind else {
            unreachable!()
        };
        value.value = Some(computation(19));
        function.signature_where = vec![first];
        let field = RecordField {
            name: "field".into(),
            value: expression(11),
            span: span(),
        };
        function.body = Some(Block {
            where_items: vec![declaration(2)],
            statements: vec![
                Stmt {
                    kind: StmtKind::Expr {
                        expression: Expr {
                            kind: ExprKind::Record {
                                ty: None,
                                fields: vec![field.clone()],
                                spread: None,
                                members: vec![RecordMember::Field(field)],
                            },
                            span: span(),
                            hir_id: None,
                        },
                        terminated: false,
                    },
                    span: span(),
                    hir_id: Some(StmtId(10)),
                },
                Stmt {
                    kind: StmtKind::Handler(vec![HandlerArm {
                        operation: expression(15),
                        parameters: vec![Parameter {
                            pattern: Pattern {
                                kind: PatternKind::Wildcard,
                                span: span(),
                                hir_id: None,
                            },
                            mode: ParameterMode::Read,
                            ty: None,
                            default: Some(expression(14)),
                            span: span(),
                        }],
                        body: expression(13),
                        span: span(),
                    }]),
                    span: span(),
                    hir_id: Some(StmtId(12)),
                },
            ],
            span: span(),
        });
        let mut operation = function.clone();
        operation.generics.clear();
        operation.signature_where.clear();
        operation.return_type = None;
        operation.body = None;
        operation.parameters = vec![Parameter {
            pattern: Pattern {
                kind: PatternKind::Wildcard,
                span: span(),
                hir_id: None,
            },
            mode: ParameterMode::Read,
            ty: None,
            default: Some(expression(17)),
            span: span(),
        }];
        let program = Program {
            statements: vec![
                Stmt {
                    kind: StmtKind::Function(function),
                    span: span(),
                    hir_id: Some(StmtId(0)),
                },
                Stmt {
                    kind: StmtKind::Effect(EffectDeclaration {
                        visibility: Visibility::Private,
                        name: "Effects".into(),
                        generics: vec![],
                        operations: vec![operation],
                        members: vec![computation(18)],
                        span: span(),
                    }),
                    span: span(),
                    hir_id: Some(StmtId(16)),
                },
            ],
        };
        let values = declarations(&program, &mut WorkLimit::new(65_536)).unwrap();
        let expected: BTreeSet<_> = (1..=9)
            .chain([11, 13, 14, 15, 17, 18, 19])
            .map(StmtId)
            .collect();
        assert_eq!(values.keys().copied().collect::<BTreeSet<_>>(), expected);
    }

    #[test]
    fn query_cannot_publish_missing_duplicate_or_unpaid_statement_identities() {
        let program = fixture();
        let mut work = WorkLimit::new(65_536);
        declarations(&program, &mut work).unwrap();
        let cost = 65_536 - work.remaining();
        assert!(declarations(&program, &mut WorkLimit::new(cost)).is_ok());
        assert!(matches!(
            declarations(&program, &mut WorkLimit::new(cost - 1)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            declarations(&program, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut missing = program.clone();
        missing.statements[0].hir_id = None;
        assert!(matches!(
            declarations(&missing, &mut WorkLimit::new(65_536)),
            Err(SourceTypesError::MissingNode)
        ));
        let mut duplicate = program.clone();
        duplicate.statements.push(duplicate.statements[0].clone());
        assert!(matches!(
            declarations(&duplicate, &mut WorkLimit::new(65_536)),
            Err(SourceTypesError::AlreadyDefined)
        ));
        let wide = Program {
            statements: vec![declaration(0); 256],
        };
        assert!(matches!(
            declarations(&wide, &mut WorkLimit::new(1)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        let mut deep = expression(1);
        for _ in 0..256 {
            deep = Expr {
                kind: ExprKind::Unary {
                    operator: "-".into(),
                    operand: Box::new(deep),
                },
                span: span(),
                hir_id: None,
            };
        }
        let deep = Program {
            statements: vec![Stmt {
                kind: StmtKind::Expr {
                    expression: deep,
                    terminated: false,
                },
                span: span(),
                hir_id: Some(StmtId(0)),
            }],
        };
        assert!(matches!(
            declarations(&deep, &mut WorkLimit::new(65_536)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }
}
