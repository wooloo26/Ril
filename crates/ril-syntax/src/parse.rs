//! Recovering recursive-descent declarations and Pratt expressions.
use crate::{
    RilLanguage, SyntaxKind, SyntaxNode,
    ast::*,
    lexer::{Token, diagnostic, lex},
};
use ril_compiler_core::{
    diagnostic::Diagnostic,
    source::{FileId, Span},
};
use rowan::{GreenNode, GreenNodeBuilder, Language};
use std::collections::BTreeSet;
thread_local! {static PARSE_WORKER:std::cell::Cell<bool>=const {std::cell::Cell::new(false)};}
fn on_parser_stack<T: Send>(work: impl FnOnce() -> T + Send, fallback: impl FnOnce() -> T) -> T {
    if PARSE_WORKER.with(std::cell::Cell::get) {
        return work();
    }
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("ril-syntax".into())
            .stack_size(16 * 1024 * 1024)
            .spawn_scoped(scope, move || {
                PARSE_WORKER.with(|worker| worker.set(true));
                work()
            });
        match worker {
            Ok(worker) => worker.join().unwrap_or_else(|_| fallback()),
            Err(_) => fallback(),
        }
    })
}

#[derive(Debug, Clone)]
pub struct Parse {
    pub green: GreenNode,
    pub program: Program,
    pub diagnostics: Vec<Diagnostic>,
    /// No unsupported construct is silently accepted.
    pub incomplete: bool,
}
impl Parse {
    pub fn is_ok(&self) -> bool {
        self.diagnostics.is_empty() && !self.incomplete
    }
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }
}

pub fn parse(text: &str) -> Parse {
    parse_file(text, FileId(0))
}
#[derive(Debug, Clone)]
pub struct ExpressionParse {
    pub expression: Expr,
    pub diagnostics: Vec<Diagnostic>,
    pub incomplete: bool,
}
pub fn parse_expression(text: &str, file: FileId) -> ExpressionParse {
    parse_expression_at(text, file, 0)
}
pub fn parse_expression_at(text: &str, file: FileId, offset: usize) -> ExpressionParse {
    on_parser_stack(
        || parse_expression_inner(text, file, offset),
        || ExpressionParse {
            expression: Expr {
                hir_id: None,
                kind: ExprKind::Error,
                span: Span {
                    file,
                    start: offset as u32,
                    end: offset.saturating_add(text.len()).min(u32::MAX as usize) as u32,
                },
            },
            diagnostics: vec![],
            incomplete: true,
        },
    )
}
fn parse_expression_inner(text: &str, file: FileId, offset: usize) -> ExpressionParse {
    let mut parser = Parser::new(text, file, offset);
    parser.start(SyntaxKind::Root);
    let expression = parser.expression(0, true);
    if !parser.eof() {
        parser.error("E0120", "unexpected token after expression");
    }
    while !parser.eof() {
        parser.bump();
    }
    parser.trivia();
    parser.finish();
    ExpressionParse {
        expression,
        diagnostics: parser.diagnostics,
        incomplete: parser.incomplete,
    }
}
pub fn parse_file(text: &str, file: FileId) -> Parse {
    on_parser_stack(
        || parse_file_inner(text, file),
        || {
            let mut builder = GreenNodeBuilder::new();
            builder.start_node(RilLanguage::kind_to_raw(SyntaxKind::Root));
            builder.token(RilLanguage::kind_to_raw(SyntaxKind::Invalid), text);
            builder.finish_node();
            Parse {
                green: builder.finish(),
                program: Program::default(),
                diagnostics: vec![],
                incomplete: true,
            }
        },
    )
}
fn parse_file_inner(text: &str, file: FileId) -> Parse {
    let mut parser = Parser::new(text, file, 0);
    parser.start(SyntaxKind::Root);
    let mut statements = vec![];
    parser.separators();
    while !parser.eof() {
        let before = parser.pos;
        statements.push(parser.statement());
        if parser.pos == before {
            parser.error("E0120", "parser could not identify this statement");
            parser.bump();
        }
        parser.statement_separator();
    }
    parser.trivia();
    parser.finish();
    let program = Program { statements };
    if !parser.budget_exhausted {
        parser
            .diagnostics
            .extend(crate::validation::validate(&program));
    }
    Parse {
        green: parser.builder.finish(),
        program,
        diagnostics: parser.diagnostics,
        incomplete: parser.incomplete,
    }
}

struct Parser<'a> {
    text: &'a str,
    file: FileId,
    base: usize,
    tokens: Vec<Token>,
    pos: usize,
    last_end: usize,
    builder: GreenNodeBuilder<'static>,
    diagnostics: Vec<Diagnostic>,
    incomplete: bool,
    depth: usize,
    budget_exhausted: bool,
    grouped_values: BTreeSet<(u32, u32)>,
}

impl<'a> Parser<'a> {
    fn exhaust_nesting(&mut self) {
        self.incomplete = true;
        self.budget_exhausted = true;
        while !self.eof() {
            self.bump();
        }
    }
    fn new(text: &'a str, file: FileId, base: usize) -> Self {
        let lexed = lex(text, file, base);
        Self {
            text,
            file,
            base,
            tokens: lexed.tokens,
            pos: 0,
            last_end: 0,
            builder: GreenNodeBuilder::new(),
            diagnostics: lexed.diagnostics,
            incomplete: lexed.incomplete,
            depth: 0,
            budget_exhausted: lexed.incomplete,
            grouped_values: BTreeSet::new(),
        }
    }
    fn span(&self, start: usize) -> Span {
        Span {
            file: self.file,
            start: (self.base + start) as u32,
            end: (self.base + self.last_end.max(start)) as u32,
        }
    }
    fn start(&mut self, kind: SyntaxKind) {
        self.builder.start_node(RilLanguage::kind_to_raw(kind));
    }
    fn finish(&mut self) {
        self.builder.finish_node();
    }
    fn significant(&self) -> usize {
        let mut i = self.pos;
        while self.tokens.get(i).is_some_and(|t| {
            matches!(
                t.kind,
                SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
            )
        }) {
            i += 1;
        }
        i
    }
    fn current(&self) -> &str {
        self.tokens
            .get(self.significant())
            .map(|t| &self.text[t.start..t.end])
            .unwrap_or("")
    }
    fn kind(&self) -> Option<SyntaxKind> {
        self.tokens.get(self.significant()).map(|t| t.kind)
    }
    fn look(&self, n: usize) -> &str {
        let mut i = self.significant();
        let mut seen = 0;
        while i < self.tokens.len() {
            if !matches!(
                self.tokens[i].kind,
                SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
            ) {
                if seen == n {
                    return &self.text[self.tokens[i].start..self.tokens[i].end];
                }
                seen += 1;
            }
            i += 1;
        }
        ""
    }
    fn offset(&self) -> usize {
        self.tokens
            .get(self.significant())
            .map_or(self.text.len(), |t| t.start)
    }
    fn newline(&self) -> bool {
        self.tokens[self.pos..self.significant()]
            .iter()
            .any(|t| self.text[t.start..t.end].contains(['\n', '\r']))
    }
    fn at(&self, text: &str) -> bool {
        self.current() == text
    }
    fn eof(&self) -> bool {
        self.significant() >= self.tokens.len()
    }
    fn trivia(&mut self) {
        let end = self.significant();
        while self.pos < end {
            self.raw_bump();
        }
    }
    fn raw_bump(&mut self) {
        if let Some(t) = self.tokens.get(self.pos) {
            self.builder
                .token(RilLanguage::kind_to_raw(t.kind), &self.text[t.start..t.end]);
            self.last_end = t.end;
            self.pos += 1;
        }
    }
    fn bump(&mut self) -> String {
        self.trivia();
        let value = self.current().to_owned();
        self.raw_bump();
        value
    }
    fn eat(&mut self, text: &str) -> bool {
        if self.at(text) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn at_type_close(&self) -> bool {
        matches!(self.current(), ">" | ">>" | ">=" | ">>=")
    }
    fn expect_type_close(&mut self) {
        if self.at(">>") || self.at(">=") || self.at(">>=") {
            let i = self.significant();
            let token = self.tokens[i];
            self.tokens[i].end = token.start + 1;
            self.tokens.insert(
                i + 1,
                Token {
                    kind: SyntaxKind::Punctuation,
                    start: token.start + 1,
                    end: token.end,
                },
            );
            // Splitting a close from >= can expose the first half of ==.
            // Keep the remaining adjacent operator tokenized as written.
            if let Some(next) = self.tokens.get(i + 2).copied()
                && &self.text[self.tokens[i + 1].start..self.tokens[i + 1].end] == "="
                && self.tokens[i + 1].end == next.start
                && &self.text[next.start..next.end] == "="
            {
                self.tokens[i + 1].end = next.end;
                self.tokens.remove(i + 2);
            }
        }
        self.expect(">");
    }
    fn error(&mut self, code: &str, message: &str) {
        if self.budget_exhausted {
            return;
        }
        let start = self.offset();
        let end = self.tokens.get(self.significant()).map_or(start, |t| t.end);
        self.diagnostics.push(diagnostic(
            self.file,
            self.base + start,
            self.base + end,
            code,
            message,
        ));
    }
    fn expect(&mut self, text: &str) {
        if !self.eat(text) {
            let code = if self.eof() {
                if matches!(text, ")" | "]" | "}") {
                    "E0122"
                } else {
                    "E0121"
                }
            } else if matches!(self.current(), ")" | "]" | "}") && matches!(text, ")" | "]" | "}") {
                "E0123"
            } else {
                "E0124"
            };
            self.error(code, &format!("expected '{text}'"));
            if code == "E0123" {
                self.bump();
            }
        }
    }
    fn name(&mut self) -> String {
        match self.kind() {
            Some(SyntaxKind::Identifier) => self.bump(),
            Some(SyntaxKind::Keyword) => {
                self.error("E0113", "reserved keyword used as an identifier");
                self.bump()
            }
            _ => {
                self.error(
                    if self.eof() { "E0121" } else { "E0120" },
                    "expected identifier",
                );
                if self.eof() {
                    String::new()
                } else {
                    self.bump()
                }
            }
        }
    }
    fn separators(&mut self) {
        self.trivia();
        while self.eat(";") {
            self.trivia();
        }
    }
    fn statement_separator(&mut self) {
        if self.eof() || self.at("}") || self.at("where") {
            return;
        }
        if self.eat(";") {
            self.separators();
        } else if self.newline() {
            self.trivia();
        } else {
            self.error("E0124", "statements require a newline or semicolon");
        }
    }
    fn list_separator(&mut self, closing: &str) -> bool {
        if self.eat(",") {
            true
        } else if self.at(closing) || self.eof() || matches!(self.current(), ")" | "]" | "}") {
            false
        } else {
            self.error("E0124", "list elements require commas");
            true
        }
    }

    fn statement(&mut self) -> Stmt {
        self.start(SyntaxKind::Statement);
        let start = self.offset();
        let visibility = if self.eat("pub") {
            Visibility::Public
        } else {
            Visibility::Private
        };
        let is_meta = self.eat("meta");
        let is_halt = self.eat("halt");
        let opaque = self.eat("opaque");
        let kind = match self.current() {
            "fn" => StmtKind::Function(self.function(visibility, is_meta, is_halt)),
            "type" if self.look(1) != "<" => {
                StmtKind::Type(self.type_declaration(visibility, is_halt, opaque))
            }
            "eff" => StmtKind::Effect(self.effect(visibility)),
            "use" => StmtKind::Use(self.use_declaration(visibility)),
            "let" | "var" => StmtKind::Binding(self.binding(visibility, is_meta)),
            "with" => self.handler(),
            _ => {
                if visibility == Visibility::Public || is_meta || is_halt || opaque {
                    self.error("E0120", "declaration modifier has no matching declaration");
                }
                let expression = self.expression(0, false);
                if assignment_operator(self.current()) {
                    let operator = self.bump();
                    let value = self.expression(0, false);
                    if assignment_operator(self.current()) {
                        self.error("E0701", "chained assignment is prohibited");
                    }
                    StmtKind::Assignment {
                        target: expression,
                        operator,
                        value,
                    }
                } else {
                    let terminated = self.at(";");
                    StmtKind::Expr {
                        expression,
                        terminated,
                    }
                }
            }
        };
        let span = self.span(start);
        self.finish();
        Stmt {
            hir_id: None,
            kind,
            span,
        }
    }

    fn binding(&mut self, visibility: Visibility, is_meta: bool) -> Binding {
        let variable = self.eat("var");
        if !variable {
            self.expect("let");
        }
        let mode = if variable {
            let mutable = self.eat("mut");
            if self.eat("scoped") {
                self.error(
                    "E0532",
                    "scoped resources cannot use a reassignable binding",
                );
                if self.eat("mut") || mutable {
                    BindingMode::VarMut
                } else {
                    BindingMode::Var
                }
            } else if mutable {
                BindingMode::VarMut
            } else {
                BindingMode::Var
            }
        } else if self.eat("view") {
            BindingMode::View
        } else if self.eat("scoped") {
            if self.eat("mut") {
                BindingMode::ScopedMut
            } else {
                BindingMode::Scoped
            }
        } else if self.eat("mut") {
            BindingMode::LetMut
        } else {
            BindingMode::Let
        };
        self.rejected_annotations(
            "E0613",
            "passive bindings cannot carry effect or capability annotations",
        );
        let plain_name = self.kind() == Some(SyntaxKind::Identifier)
            && !matches!(self.look(1), "(" | "::" | ".");
        let mut pattern = if self.kind() == Some(SyntaxKind::Keyword)
            && self.look(1) == "="
            && !matches!(self.current(), "true" | "false")
        {
            // This spelling is a local identifier, not a control expression
            // whose operand may consume the binding's initializer.
            let start = self.offset();
            let name = self.name();
            Pattern {
                hir_id: None,
                kind: PatternKind::Name(name),
                span: self.span(start),
            }
        } else {
            self.pattern(true)
        };
        if plain_name
            && let PatternKind::Constructor {
                path, arguments, ..
            } = &pattern.kind
            && path.len() == 1
            && arguments.is_empty()
        {
            pattern.kind = PatternKind::Name(path[0].clone());
        }
        let ty = if self.eat(":") {
            Some(self.type_expr())
        } else {
            None
        };
        self.rejected_annotations(
            "E0613",
            "a binding type cannot carry an invocation annotation",
        );
        let value = if self.eat("=") {
            self.expression(0, false)
        } else if ty.is_some() && (self.eof() || self.newline() || self.at(";")) {
            Expr {
                hir_id: None,
                kind: ExprKind::Ambient,
                span: self.span(self.offset()),
            }
        } else {
            self.expect("=");
            self.expression(0, false)
        };
        self.rejected_annotations(
            "E0613",
            "completed passive values have no effect annotation",
        );
        let fallback = if self.eat("else") {
            Some(self.expression(0, false))
        } else {
            None
        };
        Binding {
            visibility,
            is_meta,
            mode,
            pattern,
            ty,
            value,
            fallback,
        }
    }

    fn function(&mut self, visibility: Visibility, is_meta: bool, is_halt: bool) -> Function {
        self.start(SyntaxKind::Declaration);
        let start = self.offset();
        self.expect("fn");
        let name = self.name();
        let generics = self.generics();
        self.expect("(");
        let parameters = self.parameters(")", true);
        self.expect(")");
        let return_type = if self.eat("->") {
            Some(self.type_expr())
        } else {
            None
        };
        let annotations = self.annotations();
        let mut signature_where = vec![];
        if self.eat("where") {
            self.trivia();
            while matches!(
                self.current(),
                "type" | "halt" | "fn" | "eff" | "opaque" | "pub" | "meta"
            ) {
                let before = self.pos;
                signature_where.push(self.statement());
                if self.pos == before {
                    break;
                }
                if self.at("{") {
                    break;
                }
                self.statement_separator();
            }
        }
        let body = if self.at("{") {
            Some(self.block())
        } else {
            None
        };
        let span = self.span(start);
        self.finish();
        Function {
            visibility,
            is_meta,
            is_halt,
            name,
            generics,
            parameters,
            return_type,
            annotations,
            signature_where,
            body,
            span,
        }
    }

    fn generics(&mut self) -> Vec<GenericParameter> {
        let mut result = vec![];
        if !self.eat("<") {
            return result;
        }
        while !self.at_type_close() && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            let name = self.name();
            let bound = if self.eat(":") {
                if self.at("@") || self.at("&") {
                    let span = self.span(self.offset());
                    self.rejected_annotations(
                        "E0334",
                        "generic parameters cannot constrain effects or capabilities",
                    );
                    Some(TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        kind: TypeKind::Error,
                        span,
                    })
                } else {
                    Some(self.type_expr())
                }
            } else {
                None
            };
            let default = if self.eat("=") {
                Some(self.type_expr())
            } else {
                None
            };
            result.push(GenericParameter {
                hir_id: None,
                name,
                bound,
                default,
                span: self.span(start),
            });
            if self.pos == before || self.at_type_close() || !self.list_separator(">") {
                break;
            }
        }
        self.expect_type_close();
        result
    }

    fn parameters(&mut self, closing: &str, typed: bool) -> Vec<Parameter> {
        let mut parameters = vec![];
        while !self.at(closing) && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            let mode = self.parameter_mode();
            let (pattern, ty) = if typed && self.look(1) != ":" && self.type_only_parameter() {
                let ty = self.type_expr();
                (
                    Pattern {
                        hir_id: None,
                        kind: PatternKind::Wildcard,
                        span: ty.span,
                    },
                    Some(ty),
                )
            } else {
                let pattern = self.pattern(false);
                let ty = if self.eat(":") {
                    Some(self.type_expr())
                } else {
                    None
                };
                (pattern, ty)
            };
            let default = if self.eat("=") {
                Some(self.expression(0, true))
            } else {
                None
            };
            parameters.push(Parameter {
                pattern,
                mode,
                ty,
                default,
                span: self.span(start),
            });
            if self.pos == before || !self.list_separator(closing) {
                break;
            }
        }
        parameters
    }
    fn type_only_parameter(&self) -> bool {
        matches!(self.current(), "[" | "{" | "?" | "fn" | "(")
            || self
                .current()
                .chars()
                .next()
                .is_some_and(char::is_uppercase)
            || matches!(
                self.current(),
                "int"
                    | "bigint"
                    | "str"
                    | "bytes"
                    | "bool"
                    | "f32"
                    | "f64"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "u8"
                    | "u16"
                    | "u32"
                    | "u64"
                    | "never"
            )
    }
    fn parameter_mode(&mut self) -> ParameterMode {
        if self.eat("^mut") {
            ParameterMode::SharedMut
        } else if self.eat("mut") {
            ParameterMode::Mut
        } else {
            ParameterMode::Read
        }
    }

    fn annotations(&mut self) -> Vec<Annotation> {
        let mut result = vec![];
        while self.at("@") || self.at("&") {
            let start = self.offset();
            let kind = if self.eat("@") {
                AnnotationKind::Effect
            } else {
                self.bump();
                AnnotationKind::Capability
            };
            if self.eat("{") {
                let mut depth = 1;
                while depth > 0 && !self.eof() {
                    match self.current() {
                        "{" => depth += 1,
                        "}" => depth -= 1,
                        _ => {}
                    }
                    self.bump();
                }
                if depth > 0 {
                    self.error("E0122", "unclosed annotation group");
                }
            } else {
                if self.eat("^mut") || self.eat("mut") {
                } else if !self.eof() {
                    self.bump();
                }
                while self.at("::") || self.at("+") || self.at("<") {
                    if self.eat("<") {
                        let mut depth = 1;
                        while depth > 0 && !self.eof() {
                            if self.at("<") {
                                depth += 1;
                            } else if self.at(">") {
                                depth -= 1;
                            }
                            self.bump();
                        }
                        if depth > 0 {
                            self.error("E0122", "unclosed effect generic arguments");
                        }
                    } else {
                        self.bump();
                        self.name();
                    }
                }
            }
            result.push(Annotation {
                kind,
                text: self.text[start..self.last_end].to_owned(),
                span: self.span(start),
            });
        }
        result
    }
    fn rejected_annotations(&mut self, code: &str, message: &str) {
        for annotation in self.annotations() {
            self.diagnostics.push(diagnostic(
                annotation.span.file,
                annotation.span.start as usize,
                annotation.span.end as usize,
                code,
                message,
            ));
        }
    }

    fn type_declaration(
        &mut self,
        visibility: Visibility,
        is_halt: bool,
        opaque: bool,
    ) -> TypeDeclaration {
        self.start(SyntaxKind::Declaration);
        let start = self.offset();
        self.expect("type");
        let name = self.name();
        let generics = self.generics();
        let mut variants = vec![];
        let alias = self.eat("=");
        let nominal = !alias && !self.at("{");
        let value = if alias || self.at("(") {
            Some(self.type_expr())
        } else if self.eat("{") {
            while !self.at("}") && !self.eof() {
                let before = self.pos;
                let start = self.offset();
                let name = self.name();
                let generics = self.generics();
                let payload = if self.at("(") || self.at("{") {
                    Some(self.type_expr())
                } else {
                    None
                };
                let result = if self.eat("->") {
                    Some(self.type_expr())
                } else {
                    None
                };
                let annotations = self.annotations();
                for annotation in &annotations {
                    self.diagnostics.push(diagnostic(
                        annotation.span.file,
                        annotation.span.start as usize,
                        annotation.span.end as usize,
                        "E0332",
                        "a variant tag or payload cannot carry an invocation suffix",
                    ));
                }
                variants.push(Variant {
                    name,
                    generics,
                    payload,
                    result,
                    annotations,
                    span: self.span(start),
                });
                if self.pos == before || !self.list_separator("}") {
                    break;
                }
            }
            self.expect("}");
            None
        } else {
            None
        };
        let span = self.span(start);
        self.finish();
        TypeDeclaration {
            visibility,
            is_halt,
            name,
            generics,
            value,
            variants,
            opaque,
            nominal,
            span,
        }
    }

    fn effect(&mut self, visibility: Visibility) -> EffectDeclaration {
        let start = self.offset();
        self.expect("eff");
        let name = self.name();
        let generics = self.generics();
        self.expect("{");
        let mut operations = vec![];
        let mut members = vec![];
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.look(1) == "(" {
                let name = self.name();
                self.expect("(");
                let parameters = self.parameters(")", true);
                self.expect(")");
                let return_type = if self.eat("->") {
                    Some(self.type_expr())
                } else {
                    None
                };
                let annotations = self.annotations();
                operations.push(Function {
                    visibility: Visibility::Public,
                    is_meta: false,
                    is_halt: false,
                    name,
                    generics: vec![],
                    parameters,
                    return_type,
                    annotations,
                    signature_where: vec![],
                    body: None,
                    span: self.span(start),
                });
            } else {
                members.push(self.type_expr());
            }
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        EffectDeclaration {
            visibility,
            name,
            generics,
            operations,
            members,
            span: self.span(start),
        }
    }

    fn use_declaration(&mut self, visibility: Visibility) -> UseDeclaration {
        let start = self.offset();
        self.expect("use");
        let mut path = vec![self.name()];
        while self.eat("/") {
            path.push(self.name());
        }
        let mut members = vec![];
        let mut glob = false;
        let mut alias = None;
        if self.eat("::") {
            if self.eat("*") {
                glob = true;
            } else if !self.at("{") {
                let start = self.offset();
                let name = self.name();
                let member_alias = if self.eat("as") {
                    Some(self.name())
                } else {
                    None
                };
                members.push(ImportMember {
                    name,
                    alias: member_alias,
                    span: self.span(start),
                });
            } else {
                self.expect("{");
                while !self.at("}") && !self.eof() {
                    let start = self.offset();
                    let name = self.name();
                    let alias = if self.eat("as") {
                        Some(self.name())
                    } else {
                        None
                    };
                    members.push(ImportMember {
                        name,
                        alias,
                        span: self.span(start),
                    });
                    if !self.list_separator("}") {
                        break;
                    }
                }
                self.expect("}");
            }
        }
        if self.eat("as") {
            alias = Some(self.name());
        }
        UseDeclaration {
            visibility,
            path,
            alias,
            members,
            glob,
            span: self.span(start),
        }
    }

    fn handler(&mut self) -> StmtKind {
        self.expect("with");
        let grouped = self.eat("{");
        let mut arms = vec![];
        loop {
            let before = self.pos;
            let start = self.offset();
            let operation = self.expression(100, true);
            if !grouped && !self.at("->") {
                return StmtKind::HandlerApplication(operation);
            }
            // Postfix parsing leaves a Call for the operation-arm parameter list.
            let (operation, parameters) =
                if let ExprKind::Call { callee, arguments } = operation.kind {
                    let parameters = arguments
                        .into_iter()
                        .map(|argument| Parameter {
                            pattern: expr_pattern(argument.value),
                            mode: argument.mode,
                            ty: None,
                            default: None,
                            span: argument.span,
                        })
                        .collect();
                    (*callee, parameters)
                } else {
                    (operation, vec![])
                };
            self.expect("->");
            let body = self.expression(0, false);
            arms.push(HandlerArm {
                operation,
                parameters,
                body,
                span: self.span(start),
            });
            if !grouped || self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        if grouped {
            self.expect("}");
        }
        StmtKind::Handler(arms)
    }

    fn block(&mut self) -> Block {
        self.start(SyntaxKind::Block);
        let start = self.offset();
        self.expect("{");
        let mut statements = vec![];
        let mut where_items = vec![];
        self.separators();
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            if self.eat("where") {
                self.separators();
                while !self.at("}") && !self.eof() {
                    let before = self.pos;
                    where_items.push(self.statement());
                    if self.pos == before {
                        self.bump();
                    }
                    self.statement_separator();
                }
                break;
            }
            statements.push(self.statement());
            if self.pos == before {
                self.bump();
            }
            self.statement_separator();
        }
        self.expect("}");
        let span = self.span(start);
        self.finish();
        Block {
            statements,
            where_items,
            span,
        }
    }

    fn type_expr(&mut self) -> TypeExpr {
        self.depth += 1;
        let result = if self.depth > 128 {
            self.start(SyntaxKind::TypeExpression);
            let start = self.offset();
            self.exhaust_nesting();
            self.finish();
            TypeExpr {
                hir_id: None,
                kind: TypeKind::Error,
                text: String::new(),
                span: self.span(start),
            }
        } else {
            self.type_expr_inner()
        };
        self.depth -= 1;
        result
    }
    fn type_expr_inner(&mut self) -> TypeExpr {
        self.start(SyntaxKind::TypeExpression);
        let start = self.offset();
        if self.at("?[") {
            let i = self.significant();
            let token = self.tokens[i];
            self.tokens[i].end = token.start + 1;
            self.tokens.insert(
                i + 1,
                Token {
                    kind: SyntaxKind::Punctuation,
                    start: token.start + 1,
                    end: token.end,
                },
            );
        }
        let mut kind = if self.eat("typeof") {
            let operand = self.expression(14, true);
            TypeKind::Computation(Box::new(Expr {
                hir_id: None,
                span: self.span(start),
                kind: ExprKind::Unary {
                    operator: "typeof".into(),
                    operand: Box::new(operand),
                },
            }))
        } else if self.eat("?") {
            TypeKind::Optional(Box::new(self.type_expr()))
        } else if self.eat("keyof") {
            TypeKind::KeyOf(Box::new(self.type_expr()))
        } else if self.eat("..") {
            TypeKind::Rest(Box::new(self.type_expr()))
        } else if self.at("@") || self.at("&") {
            let code = if self.at("@") { "E0330" } else { "E0331" };
            self.rejected_annotations(code, "effects and capabilities are not data types");
            TypeKind::Error
        } else if self.at("[") && self.static_array_ahead() {
            TypeKind::Computation(Box::new(self.expression(11, true)))
        } else if self.eat("[") {
            if self.eat("]") {
                TypeKind::Array {
                    length: None,
                    element: Box::new(self.type_expr()),
                }
            } else if self.type_map_ahead() {
                let key = self.type_expr();
                self.expect(":");
                let value = self.type_expr();
                self.expect("]");
                TypeKind::Map {
                    key: Box::new(key),
                    value: Box::new(value),
                }
            } else {
                let length = self.expression(0, true);
                self.expect("]");
                TypeKind::Array {
                    length: Some(Box::new(length)),
                    element: Box::new(self.type_expr()),
                }
            }
        } else if self.at("(") && self.look(1) == "[" && self.look(3) == "in" {
            self.bump();
            let kind = self.mapped_type(true);
            self.expect(")");
            kind
        } else if self.eat("(") {
            let mut items = vec![];
            while !self.at(")") && !self.eof() {
                let before = self.pos;
                items.push(self.type_expr());
                self.rejected_annotations(
                    "E0333",
                    "a tuple constituent must put invocation annotations on a callable arrow",
                );
                if self.pos == before || !self.list_separator(")") {
                    break;
                }
            }
            self.expect(")");
            if items.len() == 1 {
                items.remove(0).kind
            } else {
                TypeKind::Tuple(items)
            }
        } else if self.at("{") && self.look(1) == "[" {
            self.bump();
            let kind = self.mapped_type(false);
            self.expect("}");
            kind
        } else if self.eat("{") {
            let mut fields = vec![];
            let mut row = None;
            while !self.at("}") && !self.eof() {
                let before = self.pos;
                let field_start = self.offset();
                if self.eat("..") {
                    row = Some(Box::new(self.type_expr()));
                } else {
                    let mutable = self.at("mut") && self.look(1) != ":" && self.eat("mut");
                    let name = self.name();
                    self.expect(":");
                    let ty = self.type_expr();
                    self.rejected_annotations(
                        "E0333",
                        "a record constituent must put invocation annotations on a callable arrow",
                    );
                    fields.push(TypeField {
                        name,
                        mutable,
                        ty,
                        span: self.span(field_start),
                    });
                }
                if self.pos == before || !self.list_separator("}") {
                    break;
                }
            }
            self.expect("}");
            TypeKind::Record { fields, row }
        } else if self.eat("fn") {
            self.expect("(");
            let parameters = self.parameters(")", true);
            self.expect(")");
            let result = if self.eat("->") {
                Some(Box::new(self.type_expr()))
            } else {
                None
            };
            let annotations = self.annotations();
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            }
        } else if self.at("\\") {
            self.bump();
            let mut parameters = vec![];
            while !self.at("->") && !self.eof() {
                let start = self.offset();
                let name = self.name();
                let bound = if self.eat(":") {
                    Some(self.type_expr())
                } else {
                    None
                };
                let default = if self.eat("=") {
                    Some(self.type_expr())
                } else {
                    None
                };
                parameters.push(GenericParameter {
                    hir_id: None,
                    name,
                    bound,
                    default,
                    span: self.span(start),
                });
                if !self.list_separator("->") {
                    break;
                }
            }
            self.expect("->");
            let kind = TypeKind::TypeFunction {
                parameters,
                body: Box::new(self.expression(0, false)),
            };
            self.rejected_annotations(
                "E0335",
                "type functions cannot carry effects or capabilities",
            );
            kind
        } else if matches!(
            self.kind(),
            Some(
                SyntaxKind::Integer
                    | SyntaxKind::Float
                    | SyntaxKind::String
                    | SyntaxKind::RawString
                    | SyntaxKind::Bytes
            )
        ) || matches!(self.current(), "true" | "false" | "-" | ".")
            || (self.kind() == Some(SyntaxKind::Identifier) && self.static_call_ahead())
        {
            TypeKind::Computation(Box::new(self.expression(11, true)))
        } else if self.at("let") {
            // Type-pattern binders remain syntax, distinct from ordinary names.
            self.bump();
            let name = self.name();
            TypeKind::Name {
                path: vec![format!("let {name}")],
                arguments: vec![],
            }
        } else if self.kind() == Some(SyntaxKind::Identifier) || self.at("never") || self.at("type")
        {
            let mut path = vec![self.bump()];
            while self.eat("::") {
                path.push(self.name());
            }
            let arguments = self.type_arguments();
            TypeKind::Name { path, arguments }
        } else {
            self.error(
                if self.eof() { "E0121" } else { "E0120" },
                "expected type expression",
            );
            if !self.eof() && !matches!(self.current(), ")" | "]" | "}" | "," | "=" | "->") {
                self.bump();
            }
            TypeKind::Error
        };
        if self.at("<")
            && let TypeKind::Name { arguments, .. } = &mut kind
        {
            *arguments = self.type_arguments();
        }
        let mut projections = 0;
        while self.eat(".") {
            projections += 1;
            if projections + self.depth > 128 {
                self.exhaust_nesting();
                let result = TypeExpr {
                    hir_id: None,
                    kind: TypeKind::Error,
                    text: String::new(),
                    span: self.span(start),
                };
                self.finish();
                return result;
            }
            let base = TypeExpr {
                hir_id: None,
                text: self.text[start..self.last_end].to_owned(),
                kind,
                span: self.span(start),
            };
            kind = if self.eat("(") {
                let key = Box::new(self.expression(0, true));
                self.expect(")");
                TypeKind::ComputedProjection {
                    base: Box::new(base),
                    key,
                }
            } else {
                let field = if self.kind() == Some(SyntaxKind::Integer) {
                    self.bump()
                } else {
                    self.name()
                };
                TypeKind::Projection {
                    base: Box::new(base),
                    field,
                }
            };
        }
        if self.at("->")
            && self.look(1) == "Type"
            && matches!(&kind,TypeKind::Name{path,..} if path==&["Type".to_owned()])
        {
            let parameter = TypeExpr {
                hir_id: None,
                text: self.text[start..self.last_end].to_owned(),
                kind,
                span: self.span(start),
            };
            self.bump();
            let result = self.type_expr();
            kind = TypeKind::KindArrow {
                parameter: Box::new(parameter),
                result: Box::new(result),
            };
        }
        let result = TypeExpr {
            hir_id: None,
            text: self.text[start..self.last_end.max(start)].to_owned(),
            kind,
            span: self.span(start),
        };
        self.finish();
        result
    }
    fn mapped_type(&mut self, tuple: bool) -> TypeKind {
        self.expect("[");
        let binder = self.name();
        self.expect("in");
        let keys = Box::new(self.expression(0, true));
        self.expect("]");
        self.expect(":");
        let value = Box::new(self.type_expr());
        TypeKind::Mapped {
            binder,
            keys,
            value,
            tuple,
        }
    }

    fn type_map_ahead(&self) -> bool {
        let mut depth = 0;
        for t in &self.tokens[self.significant()..] {
            let text = &self.text[t.start..t.end];
            match text {
                "[" | "(" | "{" => depth += 1,
                "]" if depth == 0 => return false,
                "]" | ")" | "}" => depth -= 1,
                ":" if depth == 0 => return true,
                _ => {}
            }
        }
        false
    }
    fn static_array_ahead(&self) -> bool {
        let first = self.look(1);
        if first == ":" {
            return true;
        }
        let value_key = first.starts_with('"')
            || first.starts_with('`')
            || first.starts_with("b\"")
            || first == "."
            || first == "[";
        let mut depth = 0usize;
        for (offset, t) in self.tokens[self.significant() + 1..].iter().enumerate() {
            let text = &self.text[t.start..t.end];
            match text {
                "[" | "(" | "{" => depth += 1,
                "]" if depth == 0 => {
                    let next =
                        self.tokens[self.significant() + 2 + offset..]
                            .iter()
                            .find(|token| {
                                !matches!(
                                    token.kind,
                                    SyntaxKind::Whitespace
                                        | SyntaxKind::Comment
                                        | SyntaxKind::Newline
                                )
                            });
                    return next.is_none_or(|token| {
                        matches!(
                            &self.text[token.start..token.end],
                            ">" | ">>" | "," | ")" | "}" | ";" | "="
                        )
                    });
                }
                "]" | ")" | "}" => depth = depth.saturating_sub(1),
                ":" if depth == 0 && !value_key => return false,
                "," if depth == 0 => return true,
                _ => {}
            }
        }
        false
    }
    fn static_call_ahead(&self) -> bool {
        let mut offset = 1;
        while self.look(offset) == "::" {
            offset += 2;
        }
        self.look(offset) == "("
    }
    fn type_arguments(&mut self) -> Vec<TypeExpr> {
        let mut args = vec![];
        if self.eat("<") {
            while !self.at_type_close() && !self.eof() {
                let before = self.pos;
                args.push(self.type_expr());
                if self.pos == before || self.at_type_close() || !self.list_separator(">") {
                    break;
                }
            }
            self.expect_type_close();
        }
        args
    }

    fn expression(&mut self, min: u8, multiline: bool) -> Expr {
        self.start(SyntaxKind::Expression);
        let start = self.offset();
        self.depth += 1;
        if self.depth > 128 {
            let kind = ExprKind::Error;
            self.exhaust_nesting();
            self.depth -= 1;
            self.finish();
            return Expr {
                hir_id: None,
                kind,
                span: self.span(start),
            };
        }
        let mut left = self.prefix(multiline);
        let mut extensions = 0;
        loop {
            if self.eof() {
                break;
            }
            extensions += 1;
            if extensions + self.depth > 128 {
                self.exhaust_nesting();
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Error,
                    span: self.span(start),
                };
                break;
            }
            if matches!(left.kind, ExprKind::TypeValue(_))
                && self.at("&")
                && matches!(self.look(1), "mut" | "^mut" | "capture" | "closure" | "{")
            {
                break;
            }
            if !multiline && self.newline() && !matches!(self.current(), "|>" | "!>" | "??") {
                break;
            }
            if self.at("(") {
                self.bump();
                let arguments = self.arguments();
                self.expect(")");
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Call {
                        callee: Box::new(left),
                        arguments,
                    },
                    span: self.span(start),
                };
                continue;
            }
            if self.at("[") || self.at("?[") {
                let safe = self.eat("?[");
                if !safe {
                    self.bump();
                }
                let index = self.expression(0, true);
                self.expect("]");
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Index {
                        base: Box::new(left),
                        index: Box::new(index),
                        safe,
                    },
                    span: self.span(start),
                };
                continue;
            }
            if self.at(".") || self.at("?.") {
                let safe = self.eat("?.");
                if !safe {
                    self.bump();
                }
                if self.at("{") && !safe {
                    let ty = expr_type(&left);
                    left = self.record(Some(ty), start);
                    continue;
                }
                if self.eat("(") {
                    let key = self.expression(0, true);
                    self.expect(")");
                    left = Expr {
                        hir_id: None,
                        kind: ExprKind::ComputedField {
                            base: Box::new(left),
                            key: Box::new(key),
                        },
                        span: self.span(start),
                    };
                } else {
                    let field = if self.kind() == Some(SyntaxKind::Integer) {
                        self.bump()
                    } else {
                        self.name()
                    };
                    left = Expr {
                        hir_id: None,
                        kind: ExprKind::Field {
                            base: Box::new(left),
                            field,
                            safe,
                        },
                        span: self.span(start),
                    };
                }
                continue;
            }
            if self.eat("::") {
                let name = self.name();
                left = match left.kind {
                    ExprKind::Name(first) => Expr {
                        hir_id: None,
                        kind: ExprKind::Path(vec![first, name]),
                        span: self.span(start),
                    },
                    ExprKind::Path(mut path) => {
                        path.push(name);
                        Expr {
                            hir_id: None,
                            kind: ExprKind::Path(path),
                            span: self.span(start),
                        }
                    }
                    _ => Expr {
                        hir_id: None,
                        kind: ExprKind::Field {
                            base: Box::new(left),
                            field: name,
                            safe: false,
                        },
                        span: self.span(start),
                    },
                };
                continue;
            }
            if self.at("<") && self.generic_call_ahead() {
                let arguments = self.type_arguments();
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Generic {
                        base: Box::new(left),
                        arguments,
                    },
                    span: self.span(start),
                };
                continue;
            }
            if self.eat("?") {
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Unary {
                        operator: "?".into(),
                        operand: Box::new(left),
                    },
                    span: self.span(start),
                };
                continue;
            }
            if self.at("\\") {
                let body = self.expression(0, multiline);
                let span = body.span;
                left = match left.kind {
                    ExprKind::Call {
                        callee,
                        mut arguments,
                    } => {
                        arguments.push(Argument {
                            label: None,
                            mode: ParameterMode::Read,
                            value: body,
                            span,
                        });
                        Expr {
                            hir_id: None,
                            kind: ExprKind::Call { callee, arguments },
                            span: self.span(start),
                        }
                    }
                    _ => Expr {
                        hir_id: None,
                        kind: ExprKind::Call {
                            callee: Box::new(left),
                            arguments: vec![Argument {
                                label: None,
                                mode: ParameterMode::Read,
                                value: body,
                                span,
                            }],
                        },
                        span: self.span(start),
                    },
                };
                continue;
            }
            let Some((binding, right_binding)) = precedence(self.current()) else {
                break;
            };
            if binding < min {
                break;
            }
            let operator = self.bump();
            if operator == "is" {
                let value = self.expression(6, multiline);
                if has_test_binding_mode(&value, &self.grouped_values) {
                    self.error(
                        "E0120",
                        "is tests do not introduce mutable pattern bindings",
                    );
                }
                let pattern = expr_test_pattern(value, &self.grouped_values);
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Is {
                        value: Box::new(left),
                        pattern,
                    },
                    span: self.span(start),
                };
                continue;
            }
            if matches!(operator.as_str(), ".." | "..=") {
                let end =
                    if matches!(self.current(), "]" | ")" | "," | "}" | ";" | "as") || self.eof() {
                        None
                    } else {
                        Some(Box::new(self.expression(right_binding, multiline)))
                    };
                left = Expr {
                    hir_id: None,
                    kind: ExprKind::Range {
                        start: Some(Box::new(left)),
                        end,
                        inclusive: operator == "..=",
                    },
                    span: self.span(start),
                };
                continue;
            }
            let right = self.expression(right_binding, multiline);
            left = Expr {
                hir_id: None,
                kind: ExprKind::Binary {
                    operator,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span: self.span(start),
            };
        }
        self.depth -= 1;
        self.finish();
        left
    }

    fn prefix(&mut self, multiline: bool) -> Expr {
        let start = self.offset();
        let kind = match self.current() {
            "true" => {
                self.bump();
                ExprKind::Literal(Literal::Bool(true))
            }
            "false" => {
                self.bump();
                ExprKind::Literal(Literal::Bool(false))
            }
            "-" | "!" | "~" | "typeof" | "^mut" => {
                let operator = self.bump();
                if operator == "typeof" {
                    self.error(
                        "E0319",
                        "typeof in expression position requires type<...> quotation",
                    );
                }
                let operand = Box::new(self.expression(14, multiline));
                ExprKind::Unary { operator, operand }
            }
            ".." | "..=" => {
                let inclusive = self.bump() == "..=";
                let end = if matches!(self.current(), "]" | ")" | "," | "}") || self.eof() {
                    None
                } else {
                    Some(Box::new(self.expression(7, multiline)))
                };
                ExprKind::Range {
                    start: None,
                    end,
                    inclusive,
                }
            }
            "(" => {
                self.bump();
                if self.eat(")") {
                    ExprKind::Literal(Literal::Unit)
                } else {
                    let first = self.expression(0, true);
                    if self.eat(",") {
                        let mut items = vec![first];
                        while !self.at(")") && !self.eof() {
                            let before = self.pos;
                            items.push(self.expression(0, true));
                            if self.pos == before || !self.list_separator(")") {
                                break;
                            }
                        }
                        self.expect(")");
                        ExprKind::Tuple(items)
                    } else {
                        self.expect(")");
                        self.grouped_values
                            .insert((first.span.start, first.span.end));
                        return first;
                    }
                }
            }
            "[" => return self.collection(),
            "." if self.look(1) == "{" => {
                self.bump();
                return self.record(None, start);
            }
            "{" => ExprKind::Block(self.block()),
            "\\" => return self.lambda(),
            "if" => {
                self.bump();
                let condition = Box::new(self.expression(0, true));
                let then_branch = Box::new(self.expression(0, false));
                let else_branch = if self.eat("else") {
                    Some(Box::new(self.expression(0, false)))
                } else {
                    None
                };
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                }
            }
            "match" => return self.match_expr(),
            "loop" => {
                self.bump();
                ExprKind::Loop(self.block())
            }
            "while" => {
                self.bump();
                let condition = Box::new(self.expression(0, true));
                let body = self.block();
                ExprKind::While { condition, body }
            }
            "for" => {
                self.bump();
                let iterable = Box::new(self.expression(0, true));
                self.expect("as");
                let pattern = self.pattern(false);
                let body = self.block();
                ExprKind::For {
                    iterable,
                    pattern,
                    body,
                }
            }
            "return" | "last" | "next" | "resume" => {
                let operation = match self.bump().as_str() {
                    "return" => ControlOperation::Return,
                    "last" => ControlOperation::Last,
                    "next" => ControlOperation::Next,
                    _ => ControlOperation::Resume,
                };
                let value = if !self.eof()
                    && !self.newline()
                    && !matches!(self.current(), ";" | "}" | "," | ")" | "]")
                {
                    Some(Box::new(self.expression(0, multiline)))
                } else {
                    None
                };
                ExprKind::Control { operation, value }
            }
            "type" if self.look(1) == "<" => {
                self.bump();
                self.bump();
                let ty = self.type_expr();
                self.expect_type_close();
                ExprKind::TypeValue(ty)
            }
            "keyof" => {
                self.bump();
                ExprKind::KeyOf(self.type_expr())
            }
            "derive" => {
                self.bump();
                let recipe = Box::new(self.expression(0, multiline));
                ExprKind::Derive { base: None, recipe }
            }
            _ => match self.kind() {
                Some(SyntaxKind::Integer) => ExprKind::Literal(Literal::Integer(self.bump())),
                Some(SyntaxKind::Float) => ExprKind::Literal(Literal::Float(self.bump())),
                Some(SyntaxKind::String) => {
                    let text = self.bump();
                    self.string_kind(&text, start)
                }
                Some(SyntaxKind::RawString) => ExprKind::Literal(Literal::RawString(self.bump())),
                Some(SyntaxKind::Bytes) => ExprKind::Literal(Literal::Bytes(self.bump())),
                Some(SyntaxKind::Identifier) => ExprKind::Name(self.bump()),
                _ => {
                    self.error(
                        if self.eof() { "E0121" } else { "E0120" },
                        "expected expression",
                    );
                    if !self.eof()
                        && !matches!(self.current(), "}" | ")" | "]" | "," | ";" | "where")
                    {
                        self.bump();
                    }
                    ExprKind::Error
                }
            },
        };
        Expr {
            hir_id: None,
            kind,
            span: self.span(start),
        }
    }

    fn string_kind(&mut self, text: &str, start: usize) -> ExprKind {
        if self.budget_exhausted {
            return ExprKind::Error;
        }
        let regions = crate::lexer::string_regions(text);
        if regions.is_empty() {
            return ExprKind::Literal(Literal::String(text.into()));
        }
        let mut parts = vec![];
        let mut previous = 1;
        for region in regions {
            if previous < region.start
                && let Some(decoded) = decode_string_text(&text[previous..region.start])
            {
                parts.push(StringPart::Text(decoded));
            }
            let parsed = parse_expression_at(
                &text[region.start + 1..region.expression_end],
                self.file,
                self.base + start + region.start + 1,
            );
            self.diagnostics.extend(parsed.diagnostics);
            self.incomplete |= parsed.incomplete;
            parts.push(StringPart::Interpolation {
                expression: Box::new(parsed.expression),
                format: region
                    .format
                    .map(|colon| text[colon + 1..region.end].to_owned()),
                span: Span {
                    file: self.file,
                    start: (self.base + start + region.start) as u32,
                    end: (self.base + start + region.end + 1) as u32,
                },
            });
            previous = region.end + 1;
        }
        if previous < text.len().saturating_sub(1)
            && let Some(decoded) = decode_string_text(&text[previous..text.len() - 1])
        {
            parts.push(StringPart::Text(decoded));
        }
        ExprKind::Interpolated(parts)
    }

    fn generic_call_ahead(&self) -> bool {
        let mut i = self.significant();
        let mut depth = 0usize;
        let mut delimiters = 0usize;
        while let Some(t) = self.tokens.get(i) {
            let text = &self.text[t.start..t.end];
            if text == "<" {
                depth += 1;
            } else if text == ">" || text == ">>" {
                depth = depth.saturating_sub(if text == ">>" { 2 } else { 1 });
                if depth == 0 {
                    let mut next = i + 1;
                    let mut newline = false;
                    while self.tokens.get(next).is_some_and(|t| {
                        matches!(
                            t.kind,
                            SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
                        )
                    }) {
                        if let Some(token) = self.tokens.get(next) {
                            newline |= self.text[token.start..token.end].contains(['\n', '\r']);
                        }
                        next += 1;
                    }
                    if newline {
                        return true;
                    }
                    return self.tokens.get(next).is_none_or(|t| {
                        matches!(
                            &self.text[t.start..t.end],
                            "(" | "::" | "." | "{" | "}" | ")" | "]" | "," | ";" | "@" | "&"
                        )
                    });
                }
            } else if matches!(text, "(" | "[" | "{") {
                delimiters += 1;
            } else if delimiters > 0 && matches!(text, ")" | "]" | "}") {
                delimiters -= 1;
            } else if depth == 1
                && delimiters == 0
                && matches!(text, ";" | "=" | "->" | "}" | "&&" | "||")
            {
                return false;
            }
            i += 1;
        }
        false
    }

    fn arguments(&mut self) -> Vec<Argument> {
        let mut args = vec![];
        while !self.at(")") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            let mode = self.parameter_mode();
            let label = if self.kind() == Some(SyntaxKind::Identifier) && self.look(1) == ":" {
                let name = self.name();
                self.bump();
                Some(name)
            } else {
                None
            };
            let value = self.expression(0, true);
            args.push(Argument {
                label,
                mode,
                value,
                span: self.span(start),
            });
            if self.pos == before || !self.list_separator(")") {
                break;
            }
        }
        args
    }

    fn collection(&mut self) -> Expr {
        let start = self.offset();
        self.expect("[");
        if self.eat("]") {
            return Expr {
                hir_id: None,
                kind: ExprKind::Array(vec![]),
                span: self.span(start),
            };
        }
        if self.eat(":") {
            self.expect("]");
            return Expr {
                hir_id: None,
                kind: ExprKind::Map(vec![]),
                span: self.span(start),
            };
        }
        let first = self.expression(0, true);
        let kind = if self.eat(":") {
            let mut pairs = vec![(first, self.expression(0, true))];
            while self.eat(",") && !self.at("]") && !self.eof() {
                let key = self.expression(0, true);
                self.expect(":");
                let value = self.expression(0, true);
                pairs.push((key, value));
            }
            ExprKind::Map(pairs)
        } else {
            let mut items = vec![first];
            while self.list_separator("]") {
                if self.at("]") || self.eof() {
                    break;
                }
                let before = self.pos;
                items.push(self.expression(0, true));
                if self.pos == before {
                    break;
                }
            }
            ExprKind::Array(items)
        };
        self.expect("]");
        Expr {
            hir_id: None,
            kind,
            span: self.span(start),
        }
    }

    fn record(&mut self, ty: Option<TypeExpr>, start: usize) -> Expr {
        self.expect("{");
        let mut fields = vec![];
        let mut spread = None;
        let mut members = vec![];
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.eat("..") {
                let value = self.expression(0, true);
                members.push(RecordMember::Spread(value.clone()));
                spread = Some(Box::new(value));
            } else {
                let name = self.name();
                let value = if self.eat(":") {
                    self.expression(0, true)
                } else {
                    Expr {
                        hir_id: None,
                        kind: ExprKind::Name(name.clone()),
                        span: self.span(start),
                    }
                };
                let field = RecordField {
                    name,
                    value,
                    span: self.span(start),
                };
                members.push(RecordMember::Field(field.clone()));
                fields.push(field);
            }
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        Expr {
            hir_id: None,
            kind: ExprKind::Record {
                ty,
                fields,
                spread,
                members,
            },
            span: self.span(start),
        }
    }

    fn lambda(&mut self) -> Expr {
        let start = self.offset();
        self.expect("\\");
        if self.at(".") || self.at("?.") {
            let mut path = vec![];
            while self.at(".") || self.at("?.") {
                if path.len() >= 128 {
                    self.exhaust_nesting();
                    break;
                }
                let segment_start = self.offset();
                let safe = self.eat("?.");
                if !safe {
                    self.bump();
                }
                let field = if self.kind() == Some(SyntaxKind::Integer) {
                    self.bump()
                } else {
                    self.name()
                };
                path.push(AccessorSegment {
                    field,
                    safe,
                    span: self.span(segment_start),
                });
            }
            return Expr {
                hir_id: None,
                kind: ExprKind::Accessor(path),
                span: self.span(start),
            };
        }
        let parameters = self.parameters("->", false);
        self.expect("->");
        let annotations = self.annotations();
        let body = Box::new(self.expression(0, false));
        Expr {
            hir_id: None,
            kind: ExprKind::Lambda {
                parameters,
                return_type: None,
                annotations,
                body,
            },
            span: self.span(start),
        }
    }

    fn match_expr(&mut self) -> Expr {
        let start = self.offset();
        self.expect("match");
        let type_match = self.at("type");
        let value = Box::new(self.expression(0, true));
        self.expect("{");
        let mut arms = vec![];
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            let pattern = self.pattern(true);
            let guard = if self.eat("if") {
                Some(self.expression(0, true))
            } else {
                None
            };
            self.expect("->");
            let body = self.expression(0, false);
            arms.push(MatchArm {
                pattern,
                guard,
                body,
                span: self.span(start),
            });
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        Expr {
            hir_id: None,
            kind: ExprKind::Match {
                value,
                arms,
                type_match,
            },
            span: self.span(start),
        }
    }

    fn pattern(&mut self, alternatives: bool) -> Pattern {
        self.start(SyntaxKind::Pattern);
        let start = self.offset();
        let mut pattern = self.pattern_atom();
        if !matches!(self.current(), "|" | ".." | "..=")
            && let Some((_, right_binding)) = precedence(self.current())
        {
            self.error(
                "E0349",
                "match and binding patterns cannot evaluate a computed expression",
            );
            let operator = self.bump();
            let right = self.expression(right_binding, true);
            let left = pattern_value(&pattern);
            pattern = Pattern {
                hir_id: None,
                kind: PatternKind::Value(Box::new(Expr {
                    hir_id: None,
                    kind: ExprKind::Binary {
                        operator,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    span: self.span(start),
                })),
                span: self.span(start),
            };
        }
        if matches!(self.current(), ".." | "..=") {
            let inclusive = self.bump() == "..=";
            let end = self.expression(7, true);
            let begin = pattern_value(&pattern);
            pattern = Pattern {
                hir_id: None,
                kind: PatternKind::Value(Box::new(Expr {
                    hir_id: None,
                    kind: ExprKind::Range {
                        start: Some(Box::new(begin)),
                        end: Some(Box::new(end)),
                        inclusive,
                    },
                    span: self.span(start),
                })),
                span: self.span(start),
            };
        }
        if alternatives && self.eat("|") {
            let mut choices = vec![pattern];
            loop {
                choices.push(self.pattern_atom());
                if !self.eat("|") {
                    break;
                }
            }
            pattern = Pattern {
                hir_id: None,
                kind: PatternKind::Alternative(choices),
                span: self.span(start),
            };
        }
        self.finish();
        pattern
    }

    fn pattern_atom(&mut self) -> Pattern {
        self.depth += 1;
        let result = if self.depth > 128 {
            self.start(SyntaxKind::Pattern);
            let start = self.offset();
            self.exhaust_nesting();
            self.finish();
            Pattern {
                hir_id: None,
                kind: PatternKind::Wildcard,
                span: self.span(start),
            }
        } else {
            self.pattern_atom_inner()
        };
        self.depth -= 1;
        result
    }
    fn pattern_atom_inner(&mut self) -> Pattern {
        let start = self.offset();
        let kind = match self.current() {
            "_" => {
                self.bump();
                PatternKind::Wildcard
            }
            "let" | "var" | "mut" | "^mut" => {
                let mode = match self.bump().as_str() {
                    "let" => {
                        if self.eat("mut") {
                            BindingMode::LetMut
                        } else {
                            BindingMode::Let
                        }
                    }
                    "var" => {
                        if self.eat("mut") {
                            BindingMode::VarMut
                        } else {
                            BindingMode::Var
                        }
                    }
                    _ => BindingMode::LetMut,
                };
                PatternKind::Mode {
                    mode,
                    pattern: Box::new(self.pattern_atom()),
                }
            }
            "type" if self.look(1) == "<" => {
                self.bump();
                self.bump();
                let ty = self.type_expr();
                self.expect_type_close();
                PatternKind::Type { ty, binder: None }
            }
            "(" => {
                self.bump();
                let mut parts = vec![];
                while !self.at(")") && !self.eof() {
                    let before = self.pos;
                    parts.push(self.pattern(true));
                    if self.pos == before || !self.list_separator(")") {
                        break;
                    }
                }
                self.expect(")");
                PatternKind::Tuple(parts)
            }
            "." if self.look(1) == "{" => {
                self.bump();
                return self.record_pattern(None, start);
            }
            "{" => return self.record_pattern(None, start),
            "true" | "false" => PatternKind::Literal(Literal::Bool(self.bump() == "true")),
            _ => match self.kind() {
                Some(SyntaxKind::Integer) => PatternKind::Literal(Literal::Integer(self.bump())),
                Some(SyntaxKind::Float) => PatternKind::Literal(Literal::Float(self.bump())),
                Some(SyntaxKind::String) => PatternKind::Literal(Literal::String(self.bump())),
                Some(SyntaxKind::RawString) => {
                    PatternKind::Literal(Literal::RawString(self.bump()))
                }
                Some(SyntaxKind::Bytes) => PatternKind::Literal(Literal::Bytes(self.bump())),
                Some(SyntaxKind::Identifier) => {
                    let mut path = vec![self.name()];
                    while self.eat("::") {
                        path.push(self.name());
                    }
                    if self.eat("(") {
                        let mut arguments = vec![];
                        while !self.at(")") && !self.eof() {
                            let before = self.pos;
                            arguments.push(self.pattern(true));
                            if self.pos == before || !self.list_separator(")") {
                                break;
                            }
                        }
                        self.expect(")");
                        PatternKind::Constructor {
                            path,
                            arguments,
                            parenthesized: true,
                        }
                    } else if self.at(".") && self.look(1) == "{" {
                        self.bump();
                        let ty = TypeExpr {
                            hir_id: None,
                            text: path.join("::"),
                            kind: TypeKind::Name {
                                path,
                                arguments: vec![],
                            },
                            span: self.span(start),
                        };
                        return self.record_pattern(Some(ty), start);
                    } else if path.len() > 1
                        || path[0].chars().next().is_some_and(char::is_uppercase)
                    {
                        PatternKind::Constructor {
                            path,
                            arguments: vec![],
                            parenthesized: false,
                        }
                    } else {
                        PatternKind::Name(path.remove(0))
                    }
                }
                _ => {
                    let value = self.expression(10, true);
                    PatternKind::Value(Box::new(value))
                }
            },
        };
        Pattern {
            hir_id: None,
            kind,
            span: self.span(start),
        }
    }
    fn record_pattern(&mut self, ty: Option<TypeExpr>, start: usize) -> Pattern {
        self.expect("{");
        let mut fields = vec![];
        let mut rest = false;
        let mut rest_binding = None;
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.eat("..") {
                if rest {
                    self.error("E0347", "a record pattern permits at most one rest");
                }
                rest = true;
                if self.kind() == Some(SyntaxKind::Identifier) {
                    rest_binding = Some(self.name());
                }
            } else {
                let mode = if self.eat("mut") {
                    Some(BindingMode::LetMut)
                } else if self.eat("var") {
                    Some(BindingMode::Var)
                } else {
                    None
                };
                let name = self.name();
                let mut pattern = if self.eat(":") {
                    self.pattern(true)
                } else {
                    Pattern {
                        hir_id: None,
                        kind: PatternKind::Name(name.clone()),
                        span: self.span(start),
                    }
                };
                if let Some(mode) = mode {
                    pattern = Pattern {
                        hir_id: None,
                        kind: PatternKind::Mode {
                            mode,
                            pattern: Box::new(pattern),
                        },
                        span: self.span(start),
                    };
                }
                fields.push(PatternField {
                    name,
                    pattern,
                    span: self.span(start),
                });
            }
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        Pattern {
            hir_id: None,
            kind: PatternKind::Record {
                ty,
                fields,
                rest,
                rest_binding,
            },
            span: self.span(start),
        }
    }
}

fn assignment_operator(operator: &str) -> bool {
    matches!(
        operator,
        "=" | "+="
            | "-="
            | "*="
            | "/="
            | "%="
            | "+%="
            | "-%="
            | "*%="
            | "&="
            | "|="
            | "^="
            | "<<="
            | ">>="
    )
}
fn precedence(operator: &str) -> Option<(u8, u8)> {
    Some(match operator {
        "|>" | "!>" => (1, 2),
        "??" => (2, 2),
        "||" => (3, 4),
        "&&" => (4, 5),
        "==" | "!=" | "<" | "<=" | ">" | ">=" | "is" | "in" => (5, 6),
        ".." | "..=" => (6, 7),
        "|" => (7, 8),
        "^" => (8, 9),
        "&" => (9, 10),
        "<<" | ">>" => (10, 11),
        "+" | "-" | "+%" | "-%" => (11, 12),
        "*" | "/" | "%" | "/?" | "%?" | "*%" => (12, 13),
        _ => return None,
    })
}
fn expr_type(expr: &Expr) -> TypeExpr {
    let (path, arguments) = match &expr.kind {
        ExprKind::Name(name) => (vec![name.clone()], vec![]),
        ExprKind::Path(path) => (path.clone(), vec![]),
        ExprKind::Generic { base, arguments } => {
            let base = expr_type(base);
            if let TypeKind::Name { path, .. } = base.kind {
                (path, arguments.clone())
            } else {
                (vec![], arguments.clone())
            }
        }
        _ => (vec![], vec![]),
    };
    TypeExpr {
        hir_id: None,
        text: path.join("::"),
        kind: TypeKind::Name { path, arguments },
        span: expr.span,
    }
}
fn expr_pattern(expr: Expr) -> Pattern {
    let span = expr.span;
    let kind = match expr.kind {
        ExprKind::Name(name) if name == "_" => PatternKind::Wildcard,
        ExprKind::Name(name) => PatternKind::Name(name),
        ExprKind::Literal(literal) => PatternKind::Literal(literal),
        ExprKind::Tuple(parts) => PatternKind::Tuple(parts.into_iter().map(expr_pattern).collect()),
        ExprKind::Path(path)
            if path
                .last()
                .is_some_and(|name| name.chars().next().is_some_and(char::is_uppercase)) =>
        {
            PatternKind::Constructor {
                path,
                arguments: vec![],
                parenthesized: false,
            }
        }
        _ => PatternKind::Value(Box::new(expr)),
    };
    Pattern {
        hir_id: None,
        kind,
        span,
    }
}
fn expr_test_pattern(expr: Expr, groups: &BTreeSet<(u32, u32)>) -> Pattern {
    let span = expr.span;
    if groups.contains(&(span.start, span.end)) {
        return Pattern {
            hir_id: None,
            kind: PatternKind::Value(Box::new(expr)),
            span,
        };
    }
    let kind = match expr.kind {
        ExprKind::Binary {
            operator,
            left,
            right,
        } if operator == "|" => {
            let left = expr_test_pattern(*left, groups);
            let right = expr_test_pattern(*right, groups);
            let mut alternatives = if let PatternKind::Alternative(alternatives) = left.kind {
                alternatives
            } else {
                vec![left]
            };
            if let PatternKind::Alternative(parts) = right.kind {
                alternatives.extend(parts);
            } else {
                alternatives.push(right);
            }
            PatternKind::Alternative(alternatives)
        }
        ExprKind::Name(name) if name == "_" => PatternKind::Wildcard,
        ExprKind::Name(name) if name.chars().next().is_some_and(char::is_uppercase) => {
            PatternKind::Constructor {
                path: vec![name],
                arguments: vec![],
                parenthesized: false,
            }
        }
        ExprKind::Path(path)
            if path
                .last()
                .is_some_and(|name| name.chars().next().is_some_and(char::is_uppercase)) =>
        {
            PatternKind::Constructor {
                path,
                arguments: vec![],
                parenthesized: false,
            }
        }
        ExprKind::Literal(literal) => PatternKind::Literal(literal),
        ExprKind::Tuple(parts) => PatternKind::Tuple(
            parts
                .into_iter()
                .map(|part| expr_test_pattern(part, groups))
                .collect(),
        ),
        ExprKind::Call { callee, arguments }
            if matches!(&callee.kind,ExprKind::Name(name) if name.chars().next().is_some_and(char::is_uppercase))
                || matches!(&callee.kind, ExprKind::Path(path) if path.last().is_some_and(|name| name.chars().next().is_some_and(char::is_uppercase))) =>
        {
            let path = match callee.kind {
                ExprKind::Name(name) => vec![name],
                ExprKind::Path(path) => path,
                _ => unreachable!(),
            };
            PatternKind::Constructor {
                path,
                parenthesized: true,
                arguments: arguments
                    .into_iter()
                    .map(|arg| expr_test_pattern(arg.value, groups))
                    .collect(),
            }
        }
        ExprKind::Record { ty, fields, .. } => PatternKind::Record {
            ty,
            fields: fields
                .into_iter()
                .map(|field| PatternField {
                    name: field.name,
                    pattern: expr_test_pattern(field.value, groups),
                    span: field.span,
                })
                .collect(),
            rest: false,
            rest_binding: None,
        },
        _ => PatternKind::Value(Box::new(expr)),
    };
    Pattern {
        hir_id: None,
        kind,
        span,
    }
}
fn pattern_value(pattern: &Pattern) -> Expr {
    Expr {
        hir_id: None,
        kind: match &pattern.kind {
            PatternKind::Literal(literal) => ExprKind::Literal(literal.clone()),
            PatternKind::Name(name) => ExprKind::Name(name.clone()),
            PatternKind::Value(value) => return *value.clone(),
            _ => ExprKind::Error,
        },
        span: pattern.span,
    }
}
fn has_test_binding_mode(expr: &Expr, groups: &BTreeSet<(u32, u32)>) -> bool {
    if groups.contains(&(expr.span.start, expr.span.end)) {
        return false;
    }
    match &expr.kind {
        ExprKind::Binary {
            operator,
            left,
            right,
        } if operator == "|" => {
            has_test_binding_mode(left, groups) || has_test_binding_mode(right, groups)
        }
        ExprKind::Call { callee, arguments }
            if matches!(&callee.kind, ExprKind::Name(name) if name.chars().next().is_some_and(char::is_uppercase))
                || matches!(&callee.kind, ExprKind::Path(path) if path.last().is_some_and(|name| name.chars().next().is_some_and(char::is_uppercase))) =>
        {
            arguments.iter().any(|arg| {
                arg.mode != ParameterMode::Read || has_test_binding_mode(&arg.value, groups)
            })
        }
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            items.iter().any(|item| has_test_binding_mode(item, groups))
        }
        ExprKind::Record { fields, .. } => fields
            .iter()
            .any(|field| has_test_binding_mode(&field.value, groups)),
        _ => false,
    }
}

fn decode_string_text(text: &str) -> Option<String> {
    let mut output = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' => output.push(match chars.next()? {
                'n' => '\n',
                'r' => '\r',
                't' => '\t',
                '0' => '\0',
                '\\' => '\\',
                '"' => '"',
                'u' => {
                    if chars.next()? != '{' {
                        return None;
                    }
                    let mut digits = String::new();
                    for c in chars.by_ref() {
                        if c == '}' {
                            break;
                        }
                        digits.push(c);
                    }
                    char::from_u32(u32::from_str_radix(&digits, 16).ok()?)?
                }
                _ => return None,
            }),
            '{' | '}' => {
                if chars.peek() == Some(&c) {
                    chars.next();
                }
                output.push(c);
            }
            _ => output.push(c),
        }
    }
    Some(output)
}
