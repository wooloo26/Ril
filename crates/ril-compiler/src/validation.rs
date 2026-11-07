//! Source roles are checked before module resolution can introduce internal names.
use crate::{ast::*, lexer::diagnostic, library::PrimitiveSource};
use crate::{
    diagnostic::Diagnostic,
    source::{Span, UnitKind},
};
use std::collections::BTreeSet;

pub(crate) fn validate(
    program: &Program,
    unit_kind: Option<UnitKind>,
    primitive_source: Option<&PrimitiveSource>,
) -> Vec<Diagnostic> {
    let mut validator = Validator {
        diagnostics: vec![],
        unit_kind,
        primitive_source,
    };
    validator.statements(&program.statements, true, false);
    validator.diagnostics
}
pub(crate) fn validate_module_stem(stem: &str, span: Span) -> Vec<Diagnostic> {
    let mut validator = Validator {
        diagnostics: vec![],
        unit_kind: None,
        primitive_source: None,
    };
    validator.module_segment(stem, span);
    validator.derived_module_name(stem, span);
    validator.diagnostics
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AnnotationPlace {
    Definition,
    Meta,
    Operation,
    CallableType,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TypePatternPosition {
    Type,
    Argument,
    Member,
}

struct Validator<'a> {
    diagnostics: Vec<Diagnostic>,
    unit_kind: Option<UnitKind>,
    primitive_source: Option<&'a PrimitiveSource>,
}
impl Validator<'_> {
    fn spelling(&mut self, name: &str, span: Span) {
        if !crate::lexer::valid_identifier(name) {
            self.error("E0102", span, "malformed identifier spelling");
        }
    }
    fn annotations(&mut self, annotations: &[Annotation], place: AnnotationPlace) {
        let mut effects_seen = false;
        let mut state_seen = false;
        let mut open_effect_end = None;
        let mut open_state = false;
        let mut leading_open_state = false;
        let mut empty_state = false;

        for annotation in annotations {
            match &annotation.kind {
                AnnotationKind::Effects(row) => {
                    if effects_seen || state_seen {
                        self.error(
                            "E0120",
                            annotation.span,
                            "one effect row may precede the state clauses",
                        );
                    }
                    effects_seen = true;
                    match row {
                        EffectRow::Open => {
                            open_effect_end = Some(annotation.span.end);
                            if place != AnnotationPlace::CallableType {
                                self.error(
                                    "E0547",
                                    annotation.span,
                                    "open effect rows belong to callable types",
                                );
                            }
                        }
                        EffectRow::Closed(effects) => {
                            if place == AnnotationPlace::Meta {
                                self.error(
                                    "E0813",
                                    annotation.span,
                                    "meta functions cannot declare effects",
                                );
                            } else if place == AnnotationPlace::Operation {
                                self.error(
                                    "E0120",
                                    annotation.span,
                                    "effect operations cannot declare an effect row",
                                );
                            }
                            for effect in effects {
                                self.ty(effect);
                            }
                        }
                    }
                }
                AnnotationKind::State(clause) => {
                    let combined = !state_seen && open_effect_end == Some(annotation.span.start);
                    state_seen = true;
                    match clause {
                        StateClause::Open => {
                            if place != AnnotationPlace::CallableType || open_state || empty_state {
                                self.error("E0547", annotation.span, "invalid open state row");
                            }
                            open_state = true;
                            leading_open_state = combined;
                        }
                        _ => {
                            if place == AnnotationPlace::Meta {
                                self.error(
                                    "E0813",
                                    annotation.span,
                                    "meta functions cannot declare state",
                                );
                            } else if open_state && !leading_open_state {
                                self.error(
                                    "E0547",
                                    annotation.span,
                                    "a standalone open state marker follows the state clauses",
                                );
                            }
                            match clause {
                                StateClause::Empty => {
                                    if open_state {
                                        self.error(
                                            "E0547",
                                            annotation.span,
                                            "an open state row cannot require an empty state row",
                                        );
                                    }
                                    empty_state = true;
                                }
                                StateClause::Environment
                                    if place != AnnotationPlace::CallableType
                                        && place != AnnotationPlace::Meta =>
                                {
                                    self.error(
                                        "E0534",
                                        annotation.span,
                                        "a definition requires concrete captured sources",
                                    );
                                }
                                StateClause::Sources {
                                    owner: StateOwner::Named { name, span },
                                    ..
                                } => {
                                    self.snake(name, *span);
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
    }
    fn error(&mut self, code: &str, span: Span, message: &str) {
        self.diagnostics.push(diagnostic(
            span.file,
            span.start as usize,
            span.end as usize,
            code,
            message,
        ));
    }
    fn snake(&mut self, name: &str, span: Span) {
        self.spelling(name, span);
        if name == "_" {
            return;
        }
        let name = name.strip_prefix('_').unwrap_or(name);
        if !name.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
            || !name
                .bytes()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == b'_')
        {
            self.error("E0101", span, "this declaration requires snake_case");
        }
    }
    fn pascal(&mut self, name: &str, span: Span) {
        self.spelling(name, span);
        if !name.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
            || !name.bytes().all(|c| c.is_ascii_alphanumeric())
        {
            self.error("E0101", span, "this declaration requires PascalCase");
        } else if name
            .as_bytes()
            .windows(2)
            .any(|pair| pair[0].is_ascii_uppercase() && pair[1].is_ascii_uppercase())
        {
            self.error("E0102", span, "PascalCase acronyms must be title-cased");
        }
    }
    fn constant(&mut self, name: &str, span: Span) {
        self.spelling(name, span);
        if name != "_"
            && (!name.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
                || !name
                    .bytes()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == b'_'))
        {
            self.error(
                "E0101",
                span,
                "immutable module and meta bindings require SCREAMING_SNAKE_CASE",
            );
        }
    }
    fn module_segment(&mut self, name: &str, span: Span) -> bool {
        self.snake(name, span);
        let malformed = name.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
            && name
                .split('_')
                .any(|word| !word.as_bytes().first().is_some_and(u8::is_ascii_lowercase));
        if malformed {
            self.error(
                "E0102",
                span,
                "every module path word must start with a lowercase letter",
            );
        }
        !malformed
    }

    fn derived_module_name(&mut self, stem: &str, span: Span) {
        let module = crate::hir::module_name(stem);
        self.pascal(&module, span);
        if matches!(module.as_str(), "Super" | "Type") {
            self.error("E0203", span, "module file name maps to a protected name");
        }
    }

    fn statements(&mut self, statements: &[Stmt], top: bool, where_scope: bool) {
        let mut declared = BTreeSet::new();
        for statement in statements {
            // A pattern introduces one lexical declaration per spelling.
            // Repeated binders within one pattern branch are checked by the
            // pattern verifier as E0347; alternatives may share names.
            let names: BTreeSet<_> = declaration_names(statement).into_iter().collect();
            for name in names {
                if !declared.insert(name) {
                    self.error(
                        "E0203",
                        statement.span,
                        "duplicate declaration in one lexical scope",
                    );
                }
            }
            if where_scope
                && !matches!(
                    statement.kind,
                    StmtKind::Function(_) | StmtKind::Type(_) | StmtKind::Effect(_)
                )
            {
                self.error(
                    "E0702",
                    statement.span,
                    "where clauses contain only hoisted functions, types and effects",
                );
            }
            if !top
                && !where_scope
                && matches!(
                    statement.kind,
                    StmtKind::Function(_)
                        | StmtKind::Type(_)
                        | StmtKind::Effect(_)
                        | StmtKind::Sub(_)
                )
            {
                self.error(
                    "E0703",
                    statement.span,
                    "declarations inside an executable block belong in its where clause",
                );
            }
            match &statement.kind {
                StmtKind::Binding(binding) => {
                    let names = self.binding_pattern(
                        &binding.pattern,
                        (top && binding.mode == BindingMode::Let) || binding.is_meta,
                        false,
                    );
                    let discard = binding.fallback.is_none()
                        && matches!(binding.pattern.kind, PatternKind::Wildcard);
                    if !binding.mode.is_reassignable() && names.is_empty() && !discard {
                        self.error(
                            "E0309",
                            binding.pattern.span,
                            "a let pattern must bind a variable",
                        );
                    }
                    if let Some(ty) = &binding.ty {
                        self.ty(ty);
                    }
                    if let Some(initializer) = &binding.initializer {
                        self.expr(initializer);
                    }
                    if let Some(fallback) = &binding.fallback {
                        self.expr(fallback);
                    }
                }
                StmtKind::Function(function) => self.function(function, false),
                StmtKind::Type(declaration) => {
                    self.pascal(&declaration.name, declaration.span);
                    for generic in &declaration.generics {
                        self.generic(generic);
                    }
                    self.signature_where(&declaration.signature_where);
                    if let Some(value) = &declaration.value {
                        self.ty(value);
                    }
                    for variant in &declaration.variants {
                        self.pascal(&variant.name, variant.span);
                        for generic in &variant.generics {
                            self.generic(generic);
                        }
                        if let Some(payload) = &variant.payload {
                            self.ty(payload);
                        }
                        if let Some(result) = &variant.result {
                            self.ty(result);
                        }
                    }
                }
                StmtKind::Effect(declaration) => {
                    self.pascal(&declaration.name, declaration.span);
                    for generic in &declaration.generics {
                        self.generic(generic);
                    }
                    for operation in &declaration.operations {
                        self.function(operation, true);
                    }
                    for member in &declaration.members {
                        self.ty(member);
                    }
                }
                StmtKind::Sub(sub) => {
                    self.pascal(&sub.name, statement.span);
                    self.statements(&sub.items, true, false);
                }
                StmtKind::Use(import) => {
                    let file_path = import.path.len() > 1
                        || import.path.first().is_some_and(|part| {
                            part.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
                        })
                        || !import.glob && import.members.is_empty();
                    if file_path {
                        for component in &import.path {
                            if !self.module_segment(component, import.span) {
                                break;
                            }
                        }
                        if let Some(stem) = import.path.last() {
                            self.derived_module_name(stem, import.span);
                        }
                    } else if let Some(module) = import.path.first() {
                        self.pascal(module, import.span);
                    }
                    for component in &import.namespaces {
                        self.pascal(component, import.span);
                    }
                    if let Some(alias) = &import.alias {
                        self.pascal(alias, import.span);
                    }
                    for member in &import.members {
                        if let Some(alias) = &member.alias {
                            self.spelling(alias, member.span);
                        }
                    }
                }
                StmtKind::Expr { expression, .. } | StmtKind::HandlerApplication(expression) => {
                    self.expr(expression)
                }
                StmtKind::Handler(arms) => {
                    for arm in arms {
                        self.expr(&arm.operation);
                        for parameter in &arm.parameters {
                            self.operation_parameter_mode(parameter);
                            self.parameter(parameter);
                        }
                        self.expr(&arm.body);
                    }
                }
            }
            // An application supplies the remaining computation as an ordinary
            // nullary callable. Its declarations belong to that callable's
            // execution scope, and can shadow the containing block's bindings.
            if !top && !where_scope && matches!(statement.kind, StmtKind::HandlerApplication(_)) {
                declared.clear();
            }
        }
    }
    fn function(&mut self, function: &Function, operation: bool) {
        self.snake(&function.name, function.span);
        let primitive = !operation
            && self
                .primitive_source
                .is_some_and(|source| source.primitive(&function.name).is_some());
        let foreign = !operation && self.unit_kind == Some(UnitKind::External);
        if foreign && (function.body.is_some() || function.is_meta || function.is_halt) {
            self.error(
                "E0901",
                function.span,
                "foreign functions require an ordinary bodyless declaration",
            );
            return;
        }
        if !foreign && !operation && !primitive && function.body.is_none() {
            self.error(
                "E0902",
                function.span,
                "function body required in a .ril file",
            );
            return;
        }
        if let ReturnMode::Infer(span) = function.return_mode {
            if function.is_meta || foreign || operation {
                self.error(
                    "E0412",
                    span,
                    "infer requires an ordinary Ril function definition or callable type",
                );
            } else {
                self.infer_inputs(span, &function.parameters);
            }
        }
        if function.is_meta && function.return_type.is_none() {
            self.error(
                "E0124",
                function.span,
                "meta fn requires an explicit return type",
            );
        }
        let place = if operation {
            AnnotationPlace::Operation
        } else if function.is_meta {
            AnnotationPlace::Meta
        } else {
            AnnotationPlace::Definition
        };
        self.annotations(&function.annotations, place);
        for generic in &function.generics {
            self.generic(generic);
        }
        for parameter in &function.parameters {
            if operation {
                self.operation_parameter_mode(parameter);
            } else if foreign && parameter.mode == ParameterMode::New {
                self.error(
                    "E0908",
                    parameter.span,
                    "foreign functions cannot receive construction inputs",
                );
            } else if function.is_meta && parameter.mode == ParameterMode::New {
                self.error(
                    "E0411",
                    parameter.span,
                    "static functions cannot receive construction inputs",
                );
            } else if parameter.mode == ParameterMode::Via && (function.is_meta || foreign) {
                self.error(
                    "E0412",
                    parameter.span,
                    "via requires an ordinary Ril callable definition",
                );
            }
            self.parameter(parameter);
        }
        if let Some(result) = &function.return_type {
            self.ty(result);
        }
        self.signature_where(&function.signature_where);
        if let Some(body) = &function.body {
            self.block(body);
        }
    }

    fn infer_inputs(&mut self, span: Span, parameters: &[Parameter]) {
        if !inputs_use_via(parameters) {
            self.error("E0412", span, "infer requires via in the callable's inputs");
        }
    }

    fn signature_where(&mut self, items: &[Stmt]) {
        for item in items {
            if !matches!(item.kind, StmtKind::Type(_)) {
                self.error(
                    "E0704",
                    item.span,
                    "signature where admits only type declarations",
                );
            }
        }
        self.statements(items, true, false);
    }
    fn parameter(&mut self, parameter: &Parameter) {
        self.binding_pattern(&parameter.pattern, false, false);
        if let Some(ty) = &parameter.ty {
            self.ty(ty);
        }
        if let Some(default) = &parameter.default {
            if matches!(
                parameter.mode,
                ParameterMode::Mut
                    | ParameterMode::SharedMut
                    | ParameterMode::New
                    | ParameterMode::Via
            ) {
                self.error(
                    "E0404",
                    default.span,
                    "this parameter mode does not admit a default",
                );
            }
            self.expr(default);
        }
    }

    fn operation_parameter_mode(&mut self, parameter: &Parameter) {
        match parameter.mode {
            ParameterMode::New => self.error(
                "E0411",
                parameter.span,
                "effect operations and handler arms cannot receive construction authority",
            ),
            ParameterMode::Via => self.error(
                "E0412",
                parameter.span,
                "effect operations and handler arms require a concrete parameter mode",
            ),
            _ => {}
        }
    }
    fn generic(&mut self, generic: &GenericParameter) {
        if generic.name.chars().next().is_some_and(char::is_uppercase) {
            self.pascal(&generic.name, generic.span);
        } else {
            self.snake(&generic.name, generic.span);
        }
        if let Some(bound) = &generic.bound {
            self.ty(bound);
        }
        for guard in &generic.guards {
            self.ty(guard);
        }
        if let Some(default) = &generic.default {
            self.ty(default);
        }
    }
    fn block(&mut self, block: &Block) {
        self.statements(&block.statements, false, false);
        self.statements(&block.where_items, false, true);
    }
    fn binding_pattern(
        &mut self,
        pattern: &Pattern,
        constant: bool,
        nested: bool,
    ) -> BTreeSet<String> {
        if matches!(&pattern.kind, PatternKind::Literal(Literal::Integer(text) | Literal::Float(text)) if text.contains('\0'))
        {
            self.error(
                "E0111",
                pattern.span,
                "private numeric witnesses are not source syntax",
            );
        }
        match &pattern.kind {
            PatternKind::Name(name) | PatternKind::Rest(Some(name)) => {
                self.binding_name(name, pattern.span, constant, nested);
                if name == "_" {
                    BTreeSet::new()
                } else {
                    BTreeSet::from([name.clone()])
                }
            }
            PatternKind::Tuple(items) | PatternKind::Array(items) => {
                self.binding_group(items, constant)
            }
            PatternKind::Alternative(items) => {
                let Some((first, alternatives)) = items.split_first() else {
                    return BTreeSet::new();
                };
                let names = self.binding_pattern(first, constant, nested);
                for alternative in alternatives {
                    let other_names = self.binding_pattern(alternative, constant, nested);
                    if names != other_names {
                        self.error(
                            "E0346",
                            alternative.span,
                            "every alternative must bind the same names",
                        );
                    }
                }
                names
            }
            PatternKind::Record {
                ty,
                fields,
                rest_binding,
                ..
            } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                let mut labels = BTreeSet::new();
                for field in fields {
                    self.spelling(&field.name, field.span);
                    if !labels.insert(&field.name) {
                        self.error("E0210", field.span, "duplicate field in a record pattern");
                    }
                }
                let mut names =
                    self.binding_group(fields.iter().map(|field| &field.pattern), constant);
                if let Some(name) = rest_binding {
                    self.binding_name(name, pattern.span, constant, true);
                    self.merge_binding_names(&mut names, [name.clone()], pattern.span);
                }
                names
            }
            PatternKind::Constructor {
                path, arguments, ..
            } => {
                if arguments.is_empty() && path.len() == 1 && path[0].contains('_') {
                    self.error(
                        "E0103",
                        pattern.span,
                        "pattern binding casing collides with a constructor",
                    );
                }
                self.binding_group(arguments, constant)
            }
            PatternKind::Mode { pattern, .. } => self.binding_pattern(pattern, constant, nested),
            PatternKind::Type(ty) => {
                self.ty(ty);
                self.type_pattern(ty, TypePatternPosition::Type);
                let mut bound = vec![];
                pattern.binding_names(&mut bound);
                let mut names = BTreeSet::new();
                self.merge_binding_names(&mut names, bound, pattern.span);
                names
            }
            _ => BTreeSet::new(),
        }
    }

    fn binding_name(&mut self, name: &str, span: Span, constant: bool, nested: bool) {
        if constant {
            self.constant(name, span);
        } else if nested && name.as_bytes().first().is_some_and(u8::is_ascii_uppercase) {
            self.error(
                "E0103",
                span,
                "pattern bindings cannot use uppercase identifiers",
            );
        } else {
            self.snake(name, span);
        }
    }

    fn binding_group<'p>(
        &mut self,
        patterns: impl IntoIterator<Item = &'p Pattern>,
        constant: bool,
    ) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        for pattern in patterns {
            let bound = self.binding_pattern(pattern, constant, true);
            self.merge_binding_names(&mut names, bound, pattern.span);
        }
        names
    }

    fn merge_binding_names(
        &mut self,
        names: &mut BTreeSet<String>,
        bound: impl IntoIterator<Item = String>,
        span: Span,
    ) {
        for name in bound {
            if !names.insert(name.clone()) {
                self.error(
                    "E0347",
                    span,
                    &format!("pattern binds '{name}' more than once"),
                );
            }
        }
    }

    fn type_pattern(&mut self, ty: &TypeExpr, position: TypePatternPosition) {
        use TypePatternPosition::{Argument, Member, Type};
        match &ty.kind {
            TypeKind::Name { arguments, .. } => {
                for argument in arguments {
                    self.type_pattern(argument, Argument);
                }
            }
            TypeKind::TypeBinder(_) | TypeKind::Error => {}
            TypeKind::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    if matches!(item.kind, TypeKind::PatternRest(_)) && index + 1 == items.len() {
                        continue;
                    }
                    self.type_pattern(item, Member);
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    self.type_pattern(&field.ty, Member);
                }
                if let Some(row) = row
                    && !matches!(row.kind, TypeKind::PatternRest(_))
                {
                    self.type_pattern(row, Type);
                }
            }
            TypeKind::Map { key, value, .. } => {
                self.type_pattern(key, Type);
                self.type_pattern(value, Type);
            }
            TypeKind::ArrayPattern { element, .. } => self.type_pattern(element, Type),
            TypeKind::PatternMode { ty, .. } | TypeKind::Member { ty, .. }
                if position == Member =>
            {
                self.type_pattern(ty, Type);
            }
            TypeKind::Computation(value) if position == Argument && literal_pattern(value) => {}
            _ => self.error(
                "E0120",
                ty.span,
                "expected a type pattern; literals belong to const arguments and rests must be final",
            ),
        }
    }

    fn ty(&mut self, ty: &TypeExpr) {
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                for part in path {
                    self.spelling(part.strip_prefix("let ").unwrap_or(part), ty.span);
                }
                if path.iter().any(|part| part.contains('\0')) {
                    self.error(
                        "E0101",
                        ty.span,
                        "source type paths cannot name compiler-internal identities",
                    );
                }
                for argument in arguments {
                    self.ty(argument);
                }
            }
            TypeKind::Optional(inner) | TypeKind::KeyOf(inner) | TypeKind::Rest(inner) => {
                self.ty(inner)
            }
            TypeKind::Array { access, element } => {
                self.storage_mode(access.as_ref());
                self.ty(element);
            }
            TypeKind::ArrayPattern { length, element } => {
                if let Some(length) = length {
                    self.expr(length);
                }
                self.ty(element);
            }
            TypeKind::Map { key, access, value } => {
                self.ty(key);
                self.storage_mode(access.as_ref());
                self.ty(value);
            }
            TypeKind::Tuple(items) | TypeKind::Alternatives(items) => {
                for item in items {
                    self.ty(item);
                }
            }
            TypeKind::VariantPayload(fields) => {
                for field in fields {
                    if let Some(label) = &field.label {
                        self.snake(label, field.ty.span);
                    }
                    self.ty(&field.ty);
                }
            }
            TypeKind::Record { fields, row } => {
                let mut names = BTreeSet::new();
                for field in fields {
                    self.snake(&field.name, field.span);
                    if !names.insert(&field.name) {
                        self.error("E0210", field.span, "duplicate record field");
                    }
                    self.ty(&field.ty);
                }
                if let Some(row) = row {
                    if let TypeKind::Name { path, .. } = &row.kind
                        && path.len() == 1
                        && path[0] != "never"
                    {
                        self.pascal(&path[0], row.span);
                    }
                    self.ty(row);
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
                return_mode,
            } => {
                if let ReturnMode::Infer(span) = return_mode {
                    self.infer_inputs(*span, parameters);
                }
                self.annotations(annotations, AnnotationPlace::CallableType);
                for parameter in parameters {
                    self.parameter(parameter);
                }
                if let Some(result) = result {
                    self.ty(result);
                }
            }
            TypeKind::TypeFunction { parameters, body } => {
                for generic in parameters {
                    self.generic(generic);
                }
                self.expr(body);
            }
            TypeKind::Projection { base, .. } => self.ty(base),
            TypeKind::ComputedProjection { base, key } => {
                self.ty(base);
                self.expr(key);
            }
            TypeKind::Computation(value) => self.expr(value),
            TypeKind::Mapped {
                mode,
                binder,
                keys,
                value,
                ..
            } => {
                self.pascal(binder, ty.span);
                if let Some(ModeExpression::Static(mode)) = mode {
                    self.expr(mode);
                }
                self.expr(keys);
                self.ty(value);
            }
            TypeKind::KindArrow { parameter, result } => {
                self.ty(parameter);
                self.ty(result);
            }
            TypeKind::Member { ty, .. } => self.ty(ty),
            TypeKind::TypeBinder(name) | TypeKind::PatternRest(Some(name)) if name != "_" => {
                self.pascal(name, ty.span)
            }
            TypeKind::PatternMode { binder, ty: inner } => {
                self.pascal(binder, ty.span);
                self.ty(inner);
            }
            TypeKind::TypeBinder(_)
            | TypeKind::PatternRest(_)
            | TypeKind::ModeLiteral(_)
            | TypeKind::QualifiedMemberMode
            | TypeKind::OpenRow
            | TypeKind::Error => {}
        }
    }
    fn storage_mode(&mut self, mode: Option<&StorageMode>) {
        if let Some(StorageMode {
            kind: StorageModeKind::Parameter(name),
            span,
        }) = mode
        {
            self.pascal(name, *span);
        }
    }

    fn expr(&mut self, expr: &Expr) {
        if matches!(&expr.kind,ExprKind::Literal(Literal::Integer(text)|Literal::Float(text))if text.contains('\0'))
        {
            self.error(
                "E0111",
                expr.span,
                "private numeric witnesses are not source syntax",
            );
        }
        match &expr.kind {
            ExprKind::Name(name) if name.contains('\0') => self.error(
                "E0101",
                expr.span,
                "source names cannot contain compiler-reserved characters",
            ),
            ExprKind::Path(path) if path.iter().any(|part| part.contains('\0')) => self.error(
                "E0101",
                expr.span,
                "source paths cannot contain compiler-reserved characters",
            ),
            ExprKind::Name(name) if name == "_" => self.error(
                "E0322",
                expr.span,
                "wildcard cannot be evaluated as a value",
            ),
            ExprKind::Name(name) => self.spelling(name, expr.span),
            ExprKind::Path(path) => {
                for part in path {
                    self.spelling(part, expr.span);
                }
            }
            ExprKind::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation { expression, .. } = part {
                        self.expr(expression);
                    }
                }
            }
            ExprKind::Generic { base, arguments } => {
                self.expr(base);
                for argument in arguments {
                    self.ty(argument);
                }
            }
            ExprKind::Tuple(items) | ExprKind::Array(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            ExprKind::Map(pairs) => {
                for (key, value) in pairs {
                    self.expr(key);
                    self.expr(value);
                }
            }
            ExprKind::Record { ty, members, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                let mut names = BTreeSet::new();

                for member in members {
                    match member {
                        RecordMember::Field(field) => {
                            if !names.insert(&field.name) {
                                self.error("E0210", field.span, "duplicate explicit record field");
                            }
                            self.expr(&field.value);
                        }
                        RecordMember::Spread(value) => self.expr(value),
                    }
                }
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Observe { operand, .. }
            | ExprKind::TupleMember { value: operand, .. } => self.expr(operand),
            ExprKind::Binary { left, right, .. }
            | ExprKind::Assignment {
                target: left,
                value: right,
                ..
            } => {
                self.expr(left);
                self.expr(right);
            }
            ExprKind::Call { callee, arguments } => {
                self.expr(callee);
                for argument in arguments {
                    self.expr(&argument.value);
                }
            }
            ExprKind::Field { base, .. } | ExprKind::EffectOperation { effect: base, .. } => {
                self.expr(base)
            }
            ExprKind::ComputedField { base, key } => {
                self.expr(base);
                self.expr(key);
            }
            ExprKind::Index { base, index, .. } => {
                self.expr(base);
                self.expr(index);
            }
            ExprKind::Lambda {
                parameters,
                return_type,
                body,
                annotations,
                ..
            } => {
                self.annotations(annotations, AnnotationPlace::Definition);
                for parameter in parameters {
                    self.parameter(parameter);
                }
                if let Some(result) = return_type {
                    self.ty(result);
                }
                self.expr(body);
            }
            ExprKind::Block(block) | ExprKind::Loop(block) => self.block(block),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition);
                self.expr(then_branch);
                if let Some(branch) = else_branch {
                    self.expr(branch);
                }
            }
            ExprKind::IfLet {
                pattern,
                value,
                then_branch,
                else_branch,
            } => {
                self.binding_pattern(pattern, false, true);
                self.expr(value);
                self.expr(then_branch);
                if let Some(branch) = else_branch {
                    self.expr(branch);
                }
            }
            ExprKind::Match { value, arms, .. } => {
                self.expr(value);
                for arm in arms {
                    self.binding_pattern(&arm.pattern, false, true);
                    if let Some(guard) = &arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&arm.body);
                }
            }
            ExprKind::Is { value, test } => {
                self.expr(value);
                self.value_test(test);
            }
            ExprKind::While { condition, body } => {
                self.expr(condition);
                self.block(body);
            }
            ExprKind::WhileLet {
                pattern,
                value,
                body,
            } => {
                self.binding_pattern(pattern, false, true);
                self.expr(value);
                self.block(body);
            }
            ExprKind::For {
                iterable,
                pattern,
                body,
            } => {
                self.expr(iterable);
                self.binding_pattern(pattern, false, true);
                self.block(body);
            }
            ExprKind::Control {
                value: Some(value), ..
            } => self.expr(value),
            ExprKind::TypeValue(ty) | ExprKind::KeyOf(ty) | ExprKind::ModeOf(ty) => self.ty(ty),
            ExprKind::Range { start, end, .. } => {
                if let Some(start) = start {
                    self.expr(start);
                }
                if let Some(end) = end {
                    self.expr(end);
                }
            }
            _ => {}
        }
    }

    fn value_test(&mut self, test: &ValueTest) {
        match &test.kind {
            ValueTestKind::Value(value) => self.expr(value),
            ValueTestKind::Range { start, end, .. } => {
                self.expr(start);
                self.expr(end);
            }
            ValueTestKind::Constructor { arguments, .. } => {
                if let Some(arguments) = arguments {
                    for argument in arguments {
                        self.value_test(argument);
                    }
                }
            }
            ValueTestKind::Tuple(tests) | ValueTestKind::Alternative(tests) => {
                for test in tests {
                    self.value_test(test);
                }
            }
            ValueTestKind::Record { ty, fields } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                let mut labels = BTreeSet::new();
                for field in fields {
                    self.spelling(&field.name, field.span);
                    if !labels.insert(&field.name) {
                        self.error("E0210", field.span, "duplicate field in a record test");
                    }
                    self.value_test(&field.test);
                }
            }
            ValueTestKind::Wildcard | ValueTestKind::Error => {}
        }
    }
}

fn literal_pattern(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Literal(_) => true,
        ExprKind::Unary { operator, operand } if operator == "-" => {
            matches!(
                operand.kind,
                ExprKind::Literal(Literal::Integer(_) | Literal::Float(_))
            )
        }
        _ => false,
    }
}

fn inputs_use_via(parameters: &[Parameter]) -> bool {
    parameters.iter().any(|parameter| {
        parameter.mode == ParameterMode::Via || parameter.ty.as_ref().is_some_and(type_uses_via)
    })
}

fn type_uses_via(ty: &TypeExpr) -> bool {
    match &ty.kind {
        TypeKind::Name { arguments, .. }
        | TypeKind::Tuple(arguments)
        | TypeKind::Alternatives(arguments) => arguments.iter().any(type_uses_via),
        TypeKind::Optional(inner) => type_uses_via(inner),
        TypeKind::Array { access, element } => {
            access
                .as_ref()
                .is_some_and(|mode| mode.kind == StorageModeKind::Via)
                || type_uses_via(element)
        }
        TypeKind::Map { key, access, value } => {
            access
                .as_ref()
                .is_some_and(|mode| mode.kind == StorageModeKind::Via)
                || type_uses_via(key)
                || type_uses_via(value)
        }
        TypeKind::Record { fields, .. } => fields.iter().any(|field| {
            field
                .mode
                .as_ref()
                .is_some_and(|mode| mode.access == MemberAccess::Via)
                || type_uses_via(&field.ty)
        }),
        TypeKind::Member { mode, ty } => mode.access == MemberAccess::Via || type_uses_via(ty),
        // A callback contributes its input mode pattern, independent of its result.
        TypeKind::Callable { parameters, .. } => inputs_use_via(parameters),
        _ => false,
    }
}

fn declaration_names(statement: &Stmt) -> Vec<String> {
    let mut names = vec![];
    if let Some(name) = statement.item_name() {
        names.push(name.to_owned());
    } else if let StmtKind::Binding(binding) = &statement.kind {
        binding.pattern.binding_names(&mut names);
    }
    names
}
