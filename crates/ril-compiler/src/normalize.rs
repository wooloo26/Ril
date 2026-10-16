//! Owned syntax normalization shared by verification and lowering.
//!
//! The lossless CST remains source-shaped. Here a handler application becomes
//! its specified ordinary call, before lexical names or callable scopes resolve.
use ril_syntax::ast::*;

pub(crate) fn program(program: &mut Program) {
    statements(&mut program.statements);
}

fn statements(statements: &mut [Stmt]) {
    for item in statements {
        statement(item);
    }
}

fn statement(statement: &mut Stmt) {
    match &mut statement.kind {
        StmtKind::Binding(binding) => {
            pattern(&mut binding.pattern);
            optional_type(&mut binding.ty);
            expression(&mut binding.value);
            optional_expression(&mut binding.fallback);
        }
        StmtKind::Function(value) => function(value),
        StmtKind::Type(declaration) => {
            generics(&mut declaration.generics);
            optional_type(&mut declaration.value);
            for variant in &mut declaration.variants {
                generics(&mut variant.generics);
                optional_type(&mut variant.payload);
                optional_type(&mut variant.result);
            }
        }
        StmtKind::Effect(declaration) => {
            generics(&mut declaration.generics);
            for operation in &mut declaration.operations {
                function(operation);
            }
            for member in &mut declaration.members {
                ty(member);
            }
        }
        StmtKind::Use(_) => {}
        StmtKind::Handler(arms) => {
            for arm in arms {
                expression(&mut arm.operation);
                parameters(&mut arm.parameters);
                expression(&mut arm.body);
            }
        }
        StmtKind::HandlerApplication(value) => expression(value),
        StmtKind::Assignment { target, value, .. } => {
            expression(target);
            expression(value);
        }
        StmtKind::Expr {
            expression: value, ..
        } => expression(value),
    }
}

fn function(function: &mut Function) {
    generics(&mut function.generics);
    parameters(&mut function.parameters);
    optional_type(&mut function.return_type);
    statements(&mut function.signature_where);
    if let Some(body) = &mut function.body {
        normalize_block(body);
    }
}

fn generics(generics: &mut [GenericParameter]) {
    for generic in generics {
        optional_type(&mut generic.bound);
        optional_type(&mut generic.default);
    }
}

fn parameters(parameters: &mut [Parameter]) {
    for parameter in parameters {
        pattern(&mut parameter.pattern);
        optional_type(&mut parameter.ty);
        optional_expression(&mut parameter.default);
    }
}

fn normalize_block(block: &mut Block) {
    // Hoisted declarations remain owned by the original declaration region.
    statements(&mut block.where_items);
    // Fold from the end so consecutive applications are normalized in linear
    // work, without recursively revisiting each synthetic remainder.
    let source = std::mem::take(&mut block.statements);
    let mut remaining = Vec::new();
    for mut item in source.into_iter().rev() {
        let StmtKind::HandlerApplication(mut header) = item.kind else {
            statement(&mut item);
            remaining.push(item);
            continue;
        };
        expression(&mut header);
        remaining.reverse();
        let remainder_span = ril_compiler_core::source::Span {
            file: block.span.file,
            start: remaining
                .first()
                .map_or(header.span.end, |item| item.span.start),
            end: block.span.end,
        };
        let remainder = Block {
            statements: std::mem::take(&mut remaining),
            where_items: vec![],
            span: remainder_span,
        };
        let final_argument = Argument {
            label: None,
            mode: ParameterMode::Read,
            value: Expr {
                hir_id: None,
                kind: ExprKind::Lambda {
                    parameters: vec![],
                    return_type: None,
                    annotations: vec![],
                    body: Box::new(Expr {
                        hir_id: None,
                        kind: ExprKind::Block(remainder),
                        span: remainder_span,
                    }),
                },
                span: remainder_span,
            },
            span: remainder_span,
        };
        // Retain the exact written header span. Budget proofs and downstream
        // Core use this call identity despite its synthetic final argument.
        if let ExprKind::Call { arguments, .. } = &mut header.kind {
            arguments.push(final_argument);
        } else {
            let span = header.span;
            header = Expr {
                hir_id: None,
                kind: ExprKind::Call {
                    callee: Box::new(header),
                    arguments: vec![final_argument],
                },
                span,
            };
        }
        item.kind = StmtKind::Expr {
            expression: header,
            terminated: false,
        };
        remaining.push(item);
    }
    remaining.reverse();
    block.statements = remaining;
}
fn optional_expression(value: &mut Option<Expr>) {
    if let Some(value) = value {
        expression(value);
    }
}

fn expression(value: &mut Expr) {
    match &mut value.kind {
        ExprKind::Literal(_)
        | ExprKind::Name(_)
        | ExprKind::Path(_)
        | ExprKind::Accessor(_)
        | ExprKind::Ambient
        | ExprKind::Error => {}
        ExprKind::Interpolated(parts) => {
            for part in parts {
                if let StringPart::Interpolation {
                    expression: value, ..
                } = part
                {
                    expression(value);
                }
            }
        }
        ExprKind::Generic { base, arguments } => {
            expression(base);
            for argument in arguments {
                ty(argument);
            }
        }
        ExprKind::Tuple(values) | ExprKind::Array(values) => {
            for value in values {
                expression(value);
            }
        }
        ExprKind::Map(entries) => {
            for (key, value) in entries {
                expression(key);
                expression(value);
            }
        }
        ExprKind::Record {
            ty: record_type,
            fields,
            spread,
            members,
        } => {
            optional_type(record_type);
            for field in fields {
                expression(&mut field.value);
            }
            if let Some(spread) = spread {
                expression(spread);
            }
            // The AST retains both its ordered members and convenient field
            // projection; normalize both without changing either's identity.
            for member in members {
                match member {
                    RecordMember::Field(field) => expression(&mut field.value),
                    RecordMember::Spread(value) => expression(value),
                }
            }
        }
        ExprKind::Unary { operand, .. } => expression(operand),
        ExprKind::Binary { left, right, .. } => {
            expression(left);
            expression(right);
        }
        ExprKind::Call { callee, arguments } => {
            expression(callee);
            for argument in arguments {
                expression(&mut argument.value);
            }
        }
        ExprKind::Field { base, .. } => expression(base),
        ExprKind::ComputedField { base, key } => {
            expression(base);
            expression(key);
        }
        ExprKind::Index { base, index, .. } => {
            expression(base);
            expression(index);
        }
        ExprKind::Lambda {
            parameters: params,
            return_type,
            body,
            ..
        } => {
            parameters(params);
            optional_type(return_type);
            expression(body);
        }
        ExprKind::Block(value) | ExprKind::Loop(value) => normalize_block(value),
        ExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            expression(condition);
            expression(then_branch);
            if let Some(value) = else_branch {
                expression(value);
            }
        }
        ExprKind::Match { value, arms, .. } => {
            expression(value);
            for arm in arms {
                pattern(&mut arm.pattern);
                optional_expression(&mut arm.guard);
                expression(&mut arm.body);
            }
        }
        ExprKind::Is {
            value,
            pattern: tested,
        } => {
            expression(value);
            pattern(tested);
        }
        ExprKind::While { condition, body } => {
            expression(condition);
            normalize_block(body);
        }
        ExprKind::For {
            iterable,
            pattern: binder,
            body,
        } => {
            expression(iterable);
            pattern(binder);
            normalize_block(body);
        }
        ExprKind::Control { value, .. } => {
            if let Some(value) = value {
                expression(value);
            }
        }
        ExprKind::TypeValue(value) | ExprKind::KeyOf(value) => ty(value),
        ExprKind::Derive { base, recipe } => {
            if let Some(base) = base {
                expression(base);
            }
            expression(recipe);
        }
        ExprKind::Range { start, end, .. } => {
            if let Some(start) = start {
                expression(start);
            }
            if let Some(end) = end {
                expression(end);
            }
        }
    }
}

fn optional_type(value: &mut Option<TypeExpr>) {
    if let Some(value) = value {
        ty(value);
    }
}

fn ty(value: &mut TypeExpr) {
    match &mut value.kind {
        TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
            for argument in arguments {
                ty(argument);
            }
        }
        TypeKind::Optional(value) | TypeKind::Rest(value) | TypeKind::KeyOf(value) => ty(value),
        TypeKind::Array { length, element } => {
            if let Some(length) = length {
                expression(length);
            }
            ty(element);
        }
        TypeKind::Map { key, value } => {
            ty(key);
            ty(value);
        }
        TypeKind::Record { fields, row } => {
            for field in fields {
                ty(&mut field.ty);
            }
            if let Some(row) = row {
                ty(row);
            }
        }
        TypeKind::Callable {
            parameters: params,
            result,
            ..
        } => {
            parameters(params);
            if let Some(result) = result {
                ty(result);
            }
        }
        TypeKind::TypeFunction { parameters, body } => {
            generics(parameters);
            expression(body);
        }
        TypeKind::Projection { base, .. } => ty(base),
        TypeKind::ComputedProjection { base, key } => {
            ty(base);
            expression(key);
        }
        TypeKind::Computation(value) => expression(value),
        TypeKind::Mapped { keys, value, .. } => {
            expression(keys);
            ty(value);
        }
        TypeKind::KindArrow { parameter, result } => {
            ty(parameter);
            ty(result);
        }
        TypeKind::Error => {}
    }
}

fn pattern(value: &mut Pattern) {
    match &mut value.kind {
        PatternKind::Tuple(values) | PatternKind::Alternative(values) => {
            for value in values {
                pattern(value);
            }
        }
        PatternKind::Record {
            ty: record_type,
            fields,
            ..
        } => {
            optional_type(record_type);
            for field in fields {
                pattern(&mut field.pattern);
            }
        }
        PatternKind::Constructor { arguments, .. } => {
            for argument in arguments {
                pattern(argument);
            }
        }
        PatternKind::Mode { pattern: value, .. } => pattern(value),
        PatternKind::Type { ty: value, .. } => ty(value),
        PatternKind::Value(value) => expression(value),
        PatternKind::Name(_)
        | PatternKind::Wildcard
        | PatternKind::Literal(_)
        | PatternKind::Error => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn body(program: &Program) -> &Block {
        let StmtKind::Function(function) = &program.statements[0].kind else {
            panic!("expected function")
        };
        function.body.as_ref().unwrap()
    }

    fn call(expression: &Expr) -> (&Expr, &[Argument]) {
        let ExprKind::Call { callee, arguments } = &expression.kind else {
            panic!("expected call")
        };
        (callee, arguments)
    }

    fn final_expression(block: &Block) -> &Expr {
        let StmtKind::Expr {
            expression,
            terminated: false,
        } = &block.statements.last().unwrap().kind
        else {
            panic!("expected final computation")
        };
        expression
    }

    fn remainder(argument: &Argument) -> &Block {
        assert_eq!(argument.mode, ParameterMode::Read);
        assert!(argument.label.is_none());
        let ExprKind::Lambda {
            parameters,
            return_type,
            annotations,
            body,
        } = &argument.value.kind
        else {
            panic!("expected anonymous callable")
        };
        assert!(parameters.is_empty());
        assert!(return_type.is_none());
        assert!(annotations.is_empty());
        let ExprKind::Block(block) = &body.kind else {
            panic!("expected remainder block")
        };
        block
    }

    #[test]
    fn applications_keep_written_calls_and_nest_remainders_without_moving_where_items() {
        let source = "fn example(){\nlet value=1\nwith first(left(), right: right())\nlet value=2\nwith second()\nreturn value\nwhere\nfn helper()->int{3}\n}";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        assert_eq!(parsed.syntax().to_string(), source);
        let raw = body(&parsed.program);
        let StmtKind::HandlerApplication(first) = &raw.statements[1].kind else {
            panic!()
        };
        let first_span = first.span;
        let (_, written_arguments) = call(first);
        let written_arguments = written_arguments.to_vec();
        let where_items = raw.where_items.clone();
        let mut normalized = parsed.program.clone();
        program(&mut normalized);
        let outer = body(&normalized);
        assert_eq!(outer.statements.len(), 2);
        assert_eq!(outer.where_items, where_items);
        let first = final_expression(outer);
        assert_eq!(first.span, first_span);
        let (_, arguments) = call(first);
        assert_eq!(&arguments[..2], written_arguments);
        let first_remainder = remainder(&arguments[2]);
        assert!(first_remainder.where_items.is_empty());
        assert_eq!(first_remainder.statements.len(), 2);
        let second = final_expression(first_remainder);
        let (_, arguments) = call(second);
        let second_remainder = remainder(&arguments[0]);
        assert!(second_remainder.where_items.is_empty());
        assert!(matches!(
            &final_expression(second_remainder).kind,
            ExprKind::Control {
                operation: ControlOperation::Return,
                ..
            }
        ));
        let once = normalized.clone();
        program(&mut normalized);
        assert_eq!(normalized, once);
    }

    #[test]
    fn defaults_and_nested_type_computations_use_the_same_owned_normalization() {
        let source = "fn example(value:int={with first();1}){let other={with second();2};other}";
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let StmtKind::Function(raw_function) = &parsed.program.statements[0].kind else {
            panic!()
        };
        let raw_default = raw_function.parameters[0].default.as_ref().unwrap().clone();
        let mut normalized = parsed.program;
        program(&mut normalized);
        let StmtKind::Function(function) = &normalized.statements[0].kind else {
            panic!()
        };
        let ExprKind::Block(default) = &function.parameters[0].default.as_ref().unwrap().kind
        else {
            panic!()
        };
        let (_, arguments) = call(final_expression(default));
        assert_eq!(remainder(&arguments[0]).statements.len(), 1);
        let StmtKind::Binding(binding) = &function.body.as_ref().unwrap().statements[0].kind else {
            panic!()
        };
        let ExprKind::Block(nested) = &binding.value.kind else {
            panic!()
        };
        let (_, arguments) = call(final_expression(nested));
        assert_eq!(remainder(&arguments[0]).statements.len(), 1);

        let mut computation = TypeExpr {
            hir_id: None,
            text: "computed".into(),
            kind: TypeKind::Computation(Box::new(raw_default)),
            span: default.span,
        };
        let original_span = computation.span;
        ty(&mut computation);
        assert_eq!(computation.span, original_span);
        let TypeKind::Computation(value) = &computation.kind else {
            panic!()
        };
        let ExprKind::Block(block) = &value.kind else {
            panic!()
        };
        assert_eq!(block, default);
    }

    #[test]
    fn top_level_application_does_not_capture_public_declarations() {
        let parsed = ril_syntax::parse("with first()\npub fn main(){}");
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut normalized = parsed.program;
        program(&mut normalized);
        assert!(matches!(
            normalized.statements[0].kind,
            StmtKind::HandlerApplication(_)
        ));
        assert!(matches!(
            normalized.statements[1].kind,
            StmtKind::Function(_)
        ));
    }
}
