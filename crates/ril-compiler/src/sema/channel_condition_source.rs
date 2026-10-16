//! Source-only theorem, independent of recorded types/constants.
//! The caller supplies the actual frozen Program and a physical-ID-validated
//! lexical owner path. This reader does not prove execution or snapshot identity.
use ril_compiler_core::source::Span;
use ril_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

type Check<T> = Result<T, &'static str>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct FormalRoot {
    pub callable: Span,
    pub parameter: usize,
    pub parameter_span: Span,
    pub binder: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum SourceStep {
    Capture { lambda: Span, name: String },
    Alias { binding: Span },
    OptionPayload { pattern: Span },
    Field { expression: Span, field: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ResultSource {
    pub root: FormalRoot,
    pub steps: Vec<SourceStep>,
    pub subject: Span,
    pub condition: Span,
    pub first_head: Span,
    pub first_success: bool,
    pub controls: Vec<SourceControl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum SourceControl {
    Some {
        root: FormalRoot,
        steps: Vec<SourceStep>,
        pattern: Span,
    },
    Assertion {
        owner: Span,
        call: Span,
        callee: Span,
        condition: Span,
    },
    UnprovedPrefix,
}

pub(super) struct LambdaHeader<'a> {
    pub span: Span,
    pub parameters: &'a [Parameter],
    pub body: &'a Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Shape {
    Other,
    Result,
    Optional(Box<Shape>),
    Tuple(Vec<Shape>),
    Record(BTreeMap<String, Shape>),
}

#[derive(Debug, Clone)]
struct SourceValue {
    shape: Shape,
    root: FormalRoot,
    steps: Vec<SourceStep>,
}

impl SourceValue {
    fn charge_copy(&self, work: &mut usize, depth: usize) -> Check<()> {
        fn charge_shape(shape: &Shape, work: &mut usize, depth: usize) -> Check<()> {
            charge(work, depth)?;
            match shape {
                Shape::Optional(inner) => charge_shape(inner, work, depth + 1)?,
                Shape::Tuple(items) => {
                    for item in items {
                        charge_shape(item, work, depth + 1)?;
                    }
                }
                Shape::Record(fields) => {
                    for field in fields.values() {
                        charge_shape(field, work, depth + 1)?;
                    }
                }
                _ => {}
            }
            Ok(())
        }
        charge(work, depth)?;
        charge_many(work, self.steps.len())?;
        charge_shape(&self.shape, work, depth + 1)
    }

    fn copy(&self, work: &mut usize, depth: usize) -> Check<Self> {
        self.charge_copy(work, depth)?;
        Ok(self.clone())
    }
}

// None is a real lexical shadow, never a fallback to an outer binding.
#[derive(Clone, Default)]
struct Lexical {
    values: BTreeMap<String, Option<SourceValue>>,
    type_shadows: BTreeSet<String>,
    constructor_shadows: BTreeSet<String>,
    unresolved_glob: bool,
}

impl Lexical {
    fn fork(&self, work: &mut usize, depth: usize) -> Check<Self> {
        charge(work, depth)?;
        charge_many(
            work,
            self.type_shadows.len() + self.constructor_shadows.len(),
        )?;
        for source in self.values.values() {
            charge(work, depth)?;
            if let Some(source) = source {
                source.charge_copy(work, depth + 1)?;
            }
        }
        Ok(self.clone())
    }

    fn declarations(
        &mut self,
        statements: &[Stmt],
        bindings: bool,
        work: &mut usize,
        depth: usize,
    ) -> Check<()> {
        for statement in statements {
            charge(work, depth)?;
            match &statement.kind {
                StmtKind::Type(declaration) => {
                    self.type_shadows.insert(declaration.name.clone());
                    for variant in &declaration.variants {
                        charge(work, depth)?;
                        self.constructor_shadows.insert(variant.name.clone());
                        self.constructor_shadows
                            .insert(format!("{}::{}", declaration.name, variant.name));
                    }
                }
                StmtKind::Function(function) => {
                    self.constructor_shadows.insert(function.name.clone());
                    self.type_shadows.insert(function.name.clone());
                }
                StmtKind::Effect(effect) => {
                    self.type_shadows.insert(effect.name.clone());
                }
                StmtKind::Use(import) => {
                    self.unresolved_glob |= import.glob;
                    if import.members.is_empty()
                        && let Some(name) = import.alias.as_ref().or_else(|| import.path.last())
                    {
                        self.type_shadows.insert(name.clone());
                        self.constructor_shadows.insert(name.clone());
                    }
                    for member in &import.members {
                        charge(work, depth)?;
                        let name = member.alias.as_ref().unwrap_or(&member.name);
                        self.type_shadows.insert(name.clone());
                        self.constructor_shadows.insert(name.clone());
                    }
                }
                StmtKind::Binding(binding) if bindings => {
                    self.bind(&binding.pattern, None, work, depth + 1)?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn standard_type(&self, path: &[String], name: &str) -> bool {
        if self.unresolved_glob
            || self.type_shadows.contains(&path.join("::"))
            || self.values.contains_key(&path.join("::"))
        {
            return false;
        }
        path == [name.to_owned()]
            || (path == ["Prelude".to_owned(), name.to_owned()]
                && !self.type_shadows.contains("Prelude")
                && !self.values.contains_key("Prelude"))
    }

    fn standard_constructor(&self, path: &[String], name: &str) -> bool {
        if self.unresolved_glob || self.constructor_shadows.contains(&path.join("::")) {
            return false;
        }
        if path == [name.to_owned()] {
            !self.values.contains_key(name)
        } else {
            path == ["Prelude".to_owned(), name.to_owned()]
                && !self.type_shadows.contains("Prelude")
                && !self.values.contains_key("Prelude")
        }
    }

    fn shape(&self, syntax: &TypeExpr, work: &mut usize, depth: usize) -> Check<Shape> {
        charge(work, depth)?;
        Ok(match &syntax.kind {
            TypeKind::Name { path, arguments }
                if self.standard_type(path, "Result") && arguments.len() == 2 =>
            {
                Shape::Result
            }
            // Payload types do not affect the exhaustive outer tag theorem.
            // They supply no inner inspection, alias, or access permission.
            TypeKind::Name { path, arguments }
                if self.standard_type(path, "Option") && arguments.len() == 1 =>
            {
                Shape::Optional(Box::new(self.shape(&arguments[0], work, depth + 1)?))
            }
            TypeKind::Optional(inner) => {
                Shape::Optional(Box::new(self.shape(inner, work, depth + 1)?))
            }
            TypeKind::Tuple(items) => Shape::Tuple(
                items
                    .iter()
                    .map(|item| self.shape(item, work, depth + 1))
                    .collect::<Check<_>>()?,
            ),
            TypeKind::Record { fields, row: None } => {
                let mut result = BTreeMap::new();
                for field in fields {
                    if result
                        .insert(field.name.clone(), self.shape(&field.ty, work, depth + 1)?)
                        .is_some()
                    {
                        return Err("condition Source record has duplicate members");
                    }
                }
                Shape::Record(result)
            }
            // Aliases, computed types and rows need a separate actual Source
            // expansion, never a string, annotation or final Value shortcut.
            _ => Shape::Other,
        })
    }

    fn expression_source(
        &self,
        expression: &Expr,
        work: &mut usize,
        depth: usize,
    ) -> Check<Option<SourceValue>> {
        charge(work, depth)?;
        Ok(match &expression.kind {
            ExprKind::Name(name) => self
                .values
                .get(name)
                .and_then(Option::as_ref)
                .map(|source| source.copy(work, depth + 1))
                .transpose()?,
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let Some(mut source) = self.expression_source(base, work, depth + 1)? else {
                    return Ok(None);
                };
                // Projected shape copying is extra work after the base copy.
                source.charge_copy(work, depth + 1)?;
                source.shape = match &source.shape {
                    Shape::Record(fields) => match fields.get(field) {
                        Some(shape) => shape.clone(),
                        None => return Ok(None),
                    },
                    Shape::Tuple(items) => {
                        match field.parse::<usize>().ok().and_then(|i| items.get(i)) {
                            Some(shape) => shape.clone(),
                            None => return Ok(None),
                        }
                    }
                    _ => return Ok(None),
                };
                source.steps.push(SourceStep::Field {
                    expression: expression.span,
                    field: field.clone(),
                });
                Some(source)
            }
            // Initial scope excludes calls, annotations, implicit unwrap and
            // clone. A historical subject snapshot alone cannot replace Source.
            _ => None,
        })
    }

    fn bind(
        &mut self,
        pattern: &Pattern,
        source: Option<SourceValue>,
        work: &mut usize,
        depth: usize,
    ) -> Check<()> {
        charge(work, depth)?;
        match &pattern.kind {
            PatternKind::Name(name) => {
                self.values.insert(name.clone(), source);
            }
            PatternKind::Mode { mode, pattern } => self.bind(
                pattern,
                if matches!(mode, BindingMode::Let | BindingMode::View) {
                    source
                } else {
                    None
                },
                work,
                depth + 1,
            )?,
            PatternKind::Constructor {
                path,
                arguments,
                parenthesized: true,
            } if self.standard_constructor(path, "Some") && arguments.len() == 1 => {
                let payload = source.and_then(|mut source| {
                    let Shape::Optional(inner) = source.shape else {
                        return None;
                    };
                    source.shape = *inner;
                    source.steps.push(SourceStep::OptionPayload {
                        pattern: pattern.span,
                    });
                    Some(source)
                });
                self.bind(&arguments[0], payload, work, depth + 1)?;
            }
            PatternKind::Tuple(items) => {
                for (index, pattern) in items.iter().enumerate() {
                    let child = if let Some(source) = source.as_ref()
                        && let Shape::Tuple(items) = &source.shape
                        && let Some(shape) = items.get(index)
                    {
                        let mut child = source.copy(work, depth + 1)?;
                        source.charge_copy(work, depth + 1)?;
                        child.shape = shape.clone();
                        child.steps.push(SourceStep::Field {
                            expression: pattern.span,
                            field: index.to_string(),
                        });
                        Some(child)
                    } else {
                        None
                    };
                    self.bind(pattern, child, work, depth + 1)?;
                }
            }
            PatternKind::Wildcard | PatternKind::Literal(_) => {}
            PatternKind::Constructor { arguments, .. } | PatternKind::Alternative(arguments) => {
                for pattern in arguments {
                    self.bind(pattern, None, work, depth + 1)?;
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    self.bind(&field.pattern, None, work, depth + 1)?;
                }
                if let Some(name) = rest_binding {
                    self.values.insert(name.clone(), None);
                }
            }
            PatternKind::Type {
                binder: Some(name), ..
            } => {
                self.values.insert(name.clone(), None);
            }
            _ => {}
        }
        Ok(())
    }

    fn formals(
        &mut self,
        parameters: &[Parameter],
        callable: Span,
        work: &mut usize,
        depth: usize,
    ) -> Check<()> {
        for (index, parameter) in parameters.iter().enumerate() {
            charge(work, depth)?;
            let source = if parameter.mode == ParameterMode::Read
                && matches!(
                    parameter.pattern.kind,
                    PatternKind::Name(_) | PatternKind::Wildcard
                ) {
                parameter
                    .ty
                    .as_ref()
                    .map(|syntax| self.shape(syntax, work, depth + 1))
                    .transpose()?
                    .map(|shape| SourceValue {
                        shape,
                        root: FormalRoot {
                            callable,
                            parameter: index,
                            parameter_span: parameter.span,
                            binder: parameter.pattern.span,
                        },
                        steps: vec![],
                    })
            } else {
                None
            };
            self.bind(&parameter.pattern, source, work, depth + 1)?;
        }
        Ok(())
    }
}

fn charge(work: &mut usize, depth: usize) -> Check<()> {
    if depth > 128 {
        return Err("condition Source reconstruction exceeds its depth bound");
    }
    *work = work
        .checked_sub(1)
        .ok_or("condition Source reconstruction exceeds its work bound")?;
    Ok(())
}

fn charge_many(work: &mut usize, amount: usize) -> Check<()> {
    *work = work
        .checked_sub(amount)
        .ok_or("condition Source reconstruction exceeds its work bound")?;
    Ok(())
}

fn exhaustive_wildcard_result(pattern: &Pattern, lexical: &Lexical) -> bool {
    let PatternKind::Alternative(alternatives) = &pattern.kind else {
        return false;
    };
    if alternatives.len() != 2 {
        return false;
    }
    let (mut ok, mut error) = (false, false);
    for alternative in alternatives {
        let PatternKind::Constructor {
            path,
            arguments,
            parenthesized: true,
        } = &alternative.kind
        else {
            return false;
        };
        if !matches!(
            arguments.as_slice(),
            [Pattern {
                kind: PatternKind::Wildcard,
                ..
            }]
        ) {
            return false;
        }
        if lexical.standard_constructor(path, "Ok") {
            ok = true;
        } else if lexical.standard_constructor(path, "Err") {
            error = true;
        } else {
            return false;
        }
    }
    ok && error
}

struct Reader<'a, 'w> {
    root_owner: Span,
    condition: Span,
    lambda_path: &'a [Span],
    work: &'w mut usize,
    hits: usize,
    proof: Option<ResultSource>,
    controls: Vec<SourceControl>,
    lambda_headers: Option<&'a [LambdaHeader<'a>]>,
}

impl Reader<'_, '_> {
    fn child(
        &mut self,
        expression: &Expr,
        lexical: &Lexical,
        lambda_depth: usize,
        depth: usize,
    ) -> Check<()> {
        let lexical = lexical.fork(self.work, depth)?;
        self.expression(expression, lexical, lambda_depth, depth)
    }

    fn block(
        &mut self,
        block: &Block,
        mut lexical: Lexical,
        lambda_depth: usize,
        depth: usize,
    ) -> Check<()> {
        charge(self.work, depth)?;
        lexical.declarations(&block.where_items, true, self.work, depth + 1)?;
        lexical.declarations(&block.statements, false, self.work, depth + 1)?;
        let initial_controls = self.controls.len();
        for statement in &block.statements {
            charge(self.work, depth + 1)?;
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    self.child(&binding.value, &lexical, lambda_depth, depth + 1)?;
                    let source = if matches!(binding.mode, BindingMode::Let | BindingMode::View)
                        && binding.fallback.is_none()
                        && matches!(binding.pattern.kind, PatternKind::Name(_))
                    {
                        let mut source =
                            lexical.expression_source(&binding.value, self.work, depth + 1)?;
                        if let Some(source) = &mut source {
                            source.steps.push(SourceStep::Alias {
                                binding: statement.span,
                            });
                        }
                        source
                    } else {
                        None
                    };
                    lexical.bind(&binding.pattern, source, self.work, depth + 1)?;
                    if !matches!(binding.value.kind, ExprKind::Literal(_) | ExprKind::Name(_))
                        || binding.fallback.is_some()
                    {
                        self.controls.push(SourceControl::UnprovedPrefix);
                    }
                }
                StmtKind::Expr { expression, .. } => {
                    self.child(expression, &lexical, lambda_depth, depth + 1)?;
                    if let ExprKind::Call { callee, arguments } = &expression.kind {
                        let path = match &callee.kind {
                            ExprKind::Name(name) => vec![name.clone()],
                            ExprKind::Path(path) => path.clone(),
                            _ => vec![],
                        };
                        if lexical.standard_constructor(&path, "assert") && arguments.len() == 1 {
                            if matches!(arguments[0].value.kind, ExprKind::Is { .. }) {
                                self.controls.push(SourceControl::Assertion {
                                    owner: lambda_depth
                                        .checked_sub(1)
                                        .map_or(self.root_owner, |index| self.lambda_path[index]),
                                    call: expression.span,
                                    callee: callee.span,
                                    condition: arguments[0].value.span,
                                });
                            } else {
                                self.controls.push(SourceControl::UnprovedPrefix);
                            }
                        } else {
                            self.controls.push(SourceControl::UnprovedPrefix);
                        }
                    } else if !matches!(expression.kind, ExprKind::Literal(_) | ExprKind::Name(_)) {
                        self.controls.push(SourceControl::UnprovedPrefix);
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    self.child(value, &lexical, lambda_depth, depth + 1)?;
                    if let ExprKind::Name(name) = &target.kind {
                        lexical.values.insert(name.clone(), None);
                    }
                    self.controls.push(SourceControl::UnprovedPrefix);
                }
                // Nested named callables own another header and actual context.
                _ => {}
            }
        }
        self.controls.truncate(initial_controls);
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &Expr,
        lexical: Lexical,
        lambda_depth: usize,
        depth: usize,
    ) -> Check<()> {
        charge(self.work, depth)?;
        if expression.span == self.condition && lambda_depth == self.lambda_path.len() {
            self.hits += 1;
            if let ExprKind::Is { value, pattern } = &expression.kind
                && exhaustive_wildcard_result(pattern, &lexical)
                && let Some(source) = lexical.expression_source(value, self.work, depth + 1)?
                && source.shape == Shape::Result
            {
                for control in &self.controls {
                    charge(self.work, depth)?;
                    if let SourceControl::Some { steps, .. } = control {
                        charge_many(self.work, steps.len())?;
                    }
                }
                self.proof = Some(ResultSource {
                    root: source.root,
                    steps: source.steps,
                    subject: value.span,
                    condition: expression.span,
                    first_head: match &pattern.kind {
                        PatternKind::Alternative(items) => items[0].span,
                        _ => unreachable!(),
                    },
                    first_success: match &pattern.kind {
                        PatternKind::Alternative(items) => match &items[0].kind {
                            PatternKind::Constructor { path, .. } => {
                                lexical.standard_constructor(path, "Ok")
                            }
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    },
                    controls: self.controls.clone(),
                });
            }
        }
        match &expression.kind {
            ExprKind::Lambda {
                parameters, body, ..
            } => {
                if self.lambda_path.get(lambda_depth) != Some(&expression.span) {
                    return Ok(());
                }
                if let Some(headers) = self.lambda_headers
                    && headers.get(lambda_depth).is_none_or(|header| {
                        header.span != expression.span
                            || header.parameters != parameters
                            || header.body != &**body
                    })
                {
                    return Err(
                        "condition Source lambda header/body differs from its actual object",
                    );
                }
                let mut captured = lexical;
                for (name, source) in &mut captured.values {
                    if let Some(source) = source {
                        source.steps.push(SourceStep::Capture {
                            lambda: expression.span,
                            name: name.clone(),
                        });
                    }
                }
                captured.formals(parameters, expression.span, self.work, depth + 1)?;
                self.expression(body, captured, lambda_depth + 1, depth + 1)?;
            }
            ExprKind::Block(block) => self.block(block, lexical, lambda_depth, depth + 1)?,
            ExprKind::Match {
                value,
                arms,
                type_match: false,
            } => {
                self.child(value, &lexical, lambda_depth, depth + 1)?;
                let source = lexical.expression_source(value, self.work, depth + 1)?;
                // Later arms also owe preceding-pattern failure, which this
                // initial theorem does not reconstruct (including previews).
                for arm in arms.iter().take(1) {
                    if arm.guard.is_some() {
                        continue;
                    }
                    // Initial conditional admission is exactly canonical Some
                    // projection. Its actual presence guard is checked later.
                    let PatternKind::Constructor {
                        path,
                        arguments,
                        parenthesized: true,
                    } = &arm.pattern.kind
                    else {
                        continue;
                    };
                    if !lexical.standard_constructor(path, "Some")
                        || arguments.len() != 1
                        || !matches!(
                            arguments[0].kind,
                            PatternKind::Name(_) | PatternKind::Wildcard
                        )
                    {
                        continue;
                    }
                    let Some(control) = source
                        .as_ref()
                        .filter(|source| matches!(source.shape, Shape::Optional(_)))
                    else {
                        continue;
                    };
                    charge_many(self.work, control.steps.len() + 1)?;
                    self.controls.push(SourceControl::Some {
                        root: control.root.clone(),
                        steps: control.steps.clone(),
                        pattern: arm.pattern.span,
                    });
                    let mut arm_lexical = lexical.fork(self.work, depth + 1)?;
                    let arm_source = source
                        .as_ref()
                        .map(|source| source.copy(self.work, depth + 1))
                        .transpose()?;
                    arm_lexical.bind(&arm.pattern, arm_source, self.work, depth + 1)?;
                    self.expression(&arm.body, arm_lexical, lambda_depth, depth + 1)?;
                    self.controls.pop();
                }
            }
            ExprKind::Call { callee, arguments } => {
                let initial_controls = self.controls.len();
                if !matches!(callee.kind, ExprKind::Name(_) | ExprKind::Path(_)) {
                    self.controls.push(SourceControl::UnprovedPrefix);
                }
                for argument in arguments {
                    self.child(&argument.value, &lexical, lambda_depth, depth + 1)?;
                    if !matches!(
                        argument.value.kind,
                        ExprKind::Literal(_) | ExprKind::Name(_) | ExprKind::Path(_)
                    ) {
                        self.controls.push(SourceControl::UnprovedPrefix);
                    }
                }
                self.controls.truncate(initial_controls);
            }
            ExprKind::Is { value, .. }
            | ExprKind::Unary { operand: value, .. }
            | ExprKind::Field { base: value, .. } => {
                self.expression(value, lexical, lambda_depth, depth + 1)?
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                let initial_controls = self.controls.len();
                for item in items {
                    self.child(item, &lexical, lambda_depth, depth + 1)?;
                    if !matches!(
                        item.kind,
                        ExprKind::Literal(_) | ExprKind::Name(_) | ExprKind::Path(_)
                    ) {
                        self.controls.push(SourceControl::UnprovedPrefix);
                    }
                }
                self.controls.truncate(initial_controls);
            }
            // Loops/defaults/effects/handlers remain unproved. Syntax existence
            // is never a minimum-entry or normal-completion witness.
            _ => {}
        }
        Ok(())
    }
}

/// This returns only a lexical type/projection theorem. At use, separately
/// prove actual-ID owner/context, normal completion, minimum entry, historical
/// snapshot/source identity and source-path consistency. No debt is paid here.
fn reconstruct(
    program: &Program,
    header: &Function,
    lambda_path: &[Span],
    condition: Span,
    work: &mut usize,
    lambda_headers: Option<&[LambdaHeader<'_>]>,
) -> Check<Option<ResultSource>> {
    let mut root = None;
    for statement in &program.statements {
        charge(work, 0)?;
        if let StmtKind::Function(function) = &statement.kind
            && function.span == header.span
        {
            if root.is_some() || function != header {
                return Err("condition Source function header/body is ambiguous or inconsistent");
            }
            root = Some(function);
        }
    }
    let Some(function) = root else {
        return Ok(None);
    };
    let Some(body) = &function.body else {
        return Ok(None);
    };
    let mut lexical = Lexical::default();
    lexical.declarations(&program.statements, true, work, 0)?;
    lexical.declarations(&function.signature_where, true, work, 0)?;
    for parameter in &function.generics {
        lexical.type_shadows.insert(parameter.name.clone());
    }
    lexical.formals(&function.parameters, function.span, work, 0)?;
    let mut reader = Reader {
        root_owner: function.span,
        condition,
        lambda_path,
        work,
        hits: 0,
        proof: None,
        controls: vec![],
        lambda_headers,
    };
    reader.block(body, lexical, 0, 0)?;
    match reader.hits {
        0 => Ok(None),
        1 => Ok(reader.proof),
        _ => Err("condition Source occurrence is ambiguous in its actual lexical owner"),
    }
}

pub(super) fn observed_result_source(
    program: &Program,
    header: &Function,
    lambdas: &[LambdaHeader<'_>],
    condition: Span,
    work: &mut usize,
) -> Check<Option<ResultSource>> {
    charge_many(work, lambdas.len())?;
    let path = lambdas.iter().map(|header| header.span).collect::<Vec<_>>();
    reconstruct(program, header, &path, condition, work, Some(lambdas))
}

/// Only the canonical resolved scope path is initially admitted. Computed
/// callees and local aliases need their own normal-return and name proof.
pub(super) fn canonical_scope_callee(
    program: &Program,
    header: &Function,
    callee: &Expr,
    work: &mut usize,
) -> Check<bool> {
    charge(work, 0)?;
    let canonical = match &callee.kind {
        ExprKind::Path(path) => path == &["Concurrent".to_owned(), "scope".to_owned()],
        ExprKind::Name(name) => name == "Concurrent::scope",
        _ => false,
    };
    if !canonical {
        return Ok(false);
    }
    let mut lexical = Lexical::default();
    lexical.declarations(&program.statements, true, work, 0)?;
    lexical.declarations(&header.signature_where, true, work, 0)?;
    if let Some(body) = &header.body {
        lexical.declarations(&body.where_items, true, work, 0)?;
        lexical.declarations(&body.statements, false, work, 0)?;
    }
    Ok(!lexical.unresolved_glob
        && !lexical.type_shadows.contains("Concurrent")
        && !lexical.values.contains_key("Concurrent")
        && !lexical.values.contains_key("Concurrent::scope")
        && !lexical.constructor_shadows.contains("Concurrent::scope")
        && !header
            .generics
            .iter()
            .any(|parameter| parameter.name == "Concurrent"))
}

#[cfg(test)]
fn result_source(
    program: &Program,
    header: &Function,
    lambda_path: &[Span],
    condition: Span,
    work: &mut usize,
) -> Check<Option<ResultSource>> {
    reconstruct(program, header, lambda_path, condition, work, None)
}

#[cfg(test)]
#[path = "channel_condition_source_tests.rs"]
mod tests;
