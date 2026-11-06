//! Recovering recursive-descent declarations and Pratt expressions.
use crate::{
    RilLanguage, SyntaxKind, SyntaxNode,
    ast::*,
    hir::{DeclarationHead, HeadKind},
    lexer::{StringRegion, Token, diagnostic, lex},
};
use crate::{
    diagnostic::Diagnostic,
    source::{FileId, Span},
    text::FormatSpec,
};
use rowan::{GreenNode, GreenNodeBuilder, Language};
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum ParameterSyntax {
    Named,
    Types,
}

type HeadLookup<'a> = dyn Fn(&[String], u32, HeadKind) -> Option<DeclarationHead> + Sync + 'a;

const ASSIGNMENT_PRECEDENCE: u8 = 0;
const COMPARISON_PRECEDENCE: u8 = 5;
const RANGE_PRECEDENCE: u8 = 6;
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

pub(crate) fn parse_with_heads(text: &str, file: FileId, lookup: &HeadLookup<'_>) -> Parse {
    on_parser_stack(
        || parse_file_inner(text, file, Some(lookup)),
        || exhausted_parse(text),
    )
}

pub(crate) fn parse_skeleton(text: &str, file: FileId) -> Program {
    on_parser_stack(
        || parse_file_inner(text, file, None).program,
        Program::default,
    )
}

fn exhausted_parse(text: &str) -> Parse {
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
}

fn parse_file_inner(text: &str, file: FileId, lookup: Option<&HeadLookup<'_>>) -> Parse {
    let mut parser = Parser::new(text, file, 0, lookup);
    parser.start(SyntaxKind::Root);
    let mut statements = vec![];
    parser.separators();
    while !parser.eof() {
        let before = parser.pos;
        statements.push(parser.statement(true));
        if parser.pos == before {
            parser.error("E0120", "parser could not identify this statement");
            parser.recovery(true);
        }
        parser.statement_separator();
    }
    parser.trivia();
    parser.finish();
    Parse {
        green: parser.builder.finish(),
        program: Program { statements },
        diagnostics: parser.diagnostics,
        incomplete: parser.incomplete,
    }
}

struct Parser<'a> {
    text: &'a str,
    file: FileId,
    base: usize,
    tokens: Vec<Token>,
    interpolations: Rc<BTreeMap<usize, Vec<StringRegion>>>,
    limit: usize,
    pos: usize,
    last_end: usize,
    builder: GreenNodeBuilder<'static>,
    diagnostics: Vec<Diagnostic>,
    incomplete: bool,
    depth: usize,
    budget_exhausted: bool,
    grouped_values: BTreeSet<(u32, u32)>,
    lookup: Option<&'a HeadLookup<'a>>,
    delimiters: Vec<&'static str>,
    angles: Vec<usize>,
    type_pattern_depth: usize,
    probing_test_group: bool,
}

impl<'a> Parser<'a> {
    fn exhaust_nesting(&mut self) {
        self.incomplete = true;
        self.budget_exhausted = true;
        while !self.eof() {
            self.bump();
        }
    }
    fn new(text: &'a str, file: FileId, base: usize, lookup: Option<&'a HeadLookup<'a>>) -> Self {
        let lexed = lex(text, file, base);
        let mut parser = Self::with_tokens(
            text,
            file,
            base,
            lookup,
            lexed.tokens,
            Rc::new(lexed.interpolations),
        );
        parser.diagnostics = lexed.diagnostics;
        parser.incomplete = lexed.incomplete;
        parser.budget_exhausted = lexed.incomplete;
        parser
    }

    fn with_tokens(
        text: &'a str,
        file: FileId,
        base: usize,
        lookup: Option<&'a HeadLookup<'a>>,
        tokens: Vec<Token>,
        interpolations: Rc<BTreeMap<usize, Vec<StringRegion>>>,
    ) -> Self {
        Self {
            text,
            file,
            base,
            tokens,
            interpolations,
            limit: text.len(),
            pos: 0,
            last_end: 0,
            builder: GreenNodeBuilder::new(),
            diagnostics: vec![],
            incomplete: false,
            depth: 0,
            budget_exhausted: false,
            grouped_values: BTreeSet::new(),
            lookup,
            delimiters: Vec::new(),
            angles: Vec::new(),
            type_pattern_depth: 0,
            probing_test_group: false,
        }
    }

    fn span(&self, start: usize) -> Span {
        self.span_range(start, self.last_end.max(start))
    }

    fn span_range(&self, start: usize, end: usize) -> Span {
        Span {
            file: self.file,
            start: (self.base + start) as u32,
            end: (self.base + end) as u32,
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
        self.look_index(n)
            .map_or("", |index| self.token_text(index))
    }
    fn token_text(&self, index: usize) -> &str {
        let token = self.tokens[index];
        &self.text[token.start..token.end]
    }
    fn look_index(&self, n: usize) -> Option<usize> {
        let mut i = self.significant();
        let mut seen = 0;
        while i < self.tokens.len() {
            if !matches!(
                self.tokens[i].kind,
                SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
            ) {
                if seen == n {
                    return Some(i);
                }
                seen += 1;
            }
            i += 1;
        }
        None
    }
    fn offset(&self) -> usize {
        self.tokens
            .get(self.significant())
            .map_or(self.limit, |t| t.start)
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
        match value.as_str() {
            "(" => self.delimiters.push(")"),
            "[" | "?[" => self.delimiters.push("]"),
            "{" => self.delimiters.push("}"),
            ")" | "]" | "}" if !self.delimiters.is_empty() => {
                self.delimiters.pop();
            }
            _ => {}
        }
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
        if self.at_type_close() {
            let index = self.significant();
            let start = self.tokens[index].start;
            let mut end = self.tokens[index].end;
            let mut next = index + 1;
            while let Some(token) = self.tokens.get(next)
                && token.start == end
                && self.text[token.start..token.end]
                    .bytes()
                    .all(|b| matches!(b, b'>' | b'='))
            {
                end = token.end;
                next += 1;
            }
            if end > start + 1 {
                let suffix = lex(&self.text[start + 1..end], self.file, 0);
                self.tokens[index].end = start + 1;
                self.tokens.splice(
                    index + 1..next,
                    suffix.tokens.into_iter().map(|mut token| {
                        token.start += start + 1;
                        token.end += start + 1;
                        token
                    }),
                );
            }
        }
        self.expect(">");
    }

    fn declaration_head(&self, path: &[String], span: Span) -> Option<DeclarationHead> {
        self.lookup
            .and_then(|lookup| lookup(path, span.start, HeadKind::Value))
    }

    fn application_signature(
        &self,
        path: &[String],
        start: usize,
        kind: HeadKind,
    ) -> Option<Vec<ArgumentSort>> {
        self.lookup?(path, self.span(start).start, kind)?.application
    }

    fn closes_angle(&self) -> bool {
        self.angles.last() == Some(&self.delimiters.len()) && self.at_type_close()
    }
    fn error(&mut self, code: &str, message: &str) {
        if self.budget_exhausted {
            return;
        }
        let start = self.offset();
        let end = self.tokens.get(self.significant()).map_or(start, |t| t.end);
        let code = if code == "E0121" && (!self.delimiters.is_empty() || !self.angles.is_empty()) {
            "E0122"
        } else {
            code
        };
        self.error_at(
            Span {
                file: self.file,
                start: (self.base + start) as u32,
                end: (self.base + end) as u32,
            },
            code,
            message,
        );
    }

    fn error_at(&mut self, span: Span, code: &str, message: &str) {
        self.diagnostics.push(diagnostic(
            span.file,
            span.start as usize,
            span.end as usize,
            code,
            message,
        ));
    }

    fn expect(&mut self, text: &str) {
        if !self.eat(text) {
            let code = if self.eof() {
                if matches!(text, ")" | "]" | "}" | ">") {
                    "E0122"
                } else {
                    "E0121"
                }
            } else if matches!(self.current(), ")" | "]" | "}")
                && matches!(text, ")" | "]" | "}" | ">")
            {
                "E0123"
            } else {
                "E0124"
            };
            self.error(code, &format!("expected '{text}'"));
            self.recovery(code == "E0123");
        }
    }
    fn recovery(&mut self, consume: bool) {
        self.start(SyntaxKind::Recovery);
        if consume {
            self.bump();
        }
        self.finish();
    }

    fn name(&mut self) -> String {
        match self.kind() {
            Some(SyntaxKind::Identifier) if !crate::lexer::primitive(self.current()) => self.bump(),
            Some(SyntaxKind::Keyword | SyntaxKind::Identifier) => {
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

    fn statement(&mut self, module: bool) -> Stmt {
        self.start(SyntaxKind::Statement);
        let start = self.offset();
        let visibility = if self.eat("pub") {
            Visibility::Public
        } else {
            Visibility::Private
        };
        let is_meta = self.eat("meta");
        let is_halt = self.eat("halt");
        let opaque = self.at("opaque") && self.look(1) == "type" && self.eat("opaque");
        let kind = match self.current() {
            "fn" => StmtKind::Function(self.function(visibility, is_meta, is_halt)),
            "type" => StmtKind::Type(self.type_declaration(visibility, is_halt, opaque)),
            "eff" => StmtKind::Effect(self.effect(visibility)),
            "sub" => {
                self.bump();
                let name = self.name();
                let block = self.block_items(true);
                if let Some(item) = block.where_items.first() {
                    self.diagnostics.push(diagnostic(
                        item.span.file,
                        item.span.start as usize,
                        item.span.end as usize,
                        "E0702",
                        "module declarations are placed directly in the sub body",
                    ));
                }
                StmtKind::Sub(SubDeclaration {
                    visibility,
                    name,
                    items: block.statements,
                })
            }
            "use" => StmtKind::Use(self.use_declaration(visibility)),
            "let" | "var" => StmtKind::Binding(Box::new(self.binding(visibility, is_meta, module))),
            "with" => self.handler(),
            _ => {
                if visibility == Visibility::Public || is_meta || is_halt || opaque {
                    self.error("E0120", "declaration modifier has no matching declaration");
                }
                let expression = self.expression(0, false);
                StmtKind::Expr {
                    expression,
                    terminated: self.at(";"),
                }
            }
        };
        let span = self.span(start);
        self.finish();
        Stmt { kind, span }
    }

    fn binding(&mut self, visibility: Visibility, is_meta: bool, module: bool) -> Binding {
        let variable = self.eat("var");
        if !variable {
            self.expect("let");
        }
        let mode = if variable {
            match self.current() {
                "ref" => {
                    self.bump();
                    BindingMode::VarRef
                }
                "^mut" => {
                    self.bump();
                    BindingMode::VarSharedMut
                }
                "mut" => {
                    self.bump();
                    BindingMode::VarMut
                }
                _ => BindingMode::Var,
            }
        } else {
            let modifier = self.look(1) != ":" && self.look(1) != "=";
            match self.current() {
                "ref" => {
                    self.bump();
                    BindingMode::Ref
                }
                "via" if modifier => {
                    self.bump();
                    BindingMode::Via
                }
                "^mut" => {
                    self.bump();
                    BindingMode::LetSharedMut
                }
                "mut" => {
                    self.bump();
                    BindingMode::LetMut
                }
                "scoped" if modifier => {
                    self.bump();
                    if self.eat("mut") {
                        BindingMode::ScopedMut
                    } else {
                        BindingMode::Scoped
                    }
                }
                _ => BindingMode::Let,
            }
        };
        self.rejected_annotations(
            "E0613",
            "passive bindings cannot carry effect or capability annotations",
        );
        let plain_name = self.kind() == Some(SyntaxKind::Identifier)
            && !matches!(self.look(1), "(" | "::" | ".");
        let mut pattern = if (self.kind() == Some(SyntaxKind::Keyword)
            || crate::lexer::primitive(self.current()))
            && matches!(self.look(1), "=" | ":")
            && !matches!(self.current(), "true" | "false")
        {
            // This spelling is a local identifier, not a control expression
            // whose operand may consume the binding's initializer.
            let start = self.offset();
            let name = self.name();
            Pattern {
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
            && (is_meta
                || module && mode == BindingMode::Let && screaming_name(&path[0])
                || !self
                    .declaration_head(path, pattern.span)
                    .is_some_and(|head| head.constructor))
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
            if self.at("{") {
                let block = self.block();
                Some(Expr {
                    span: block.span,
                    kind: ExprKind::Block(block),
                })
            } else {
                self.error("E0124", "a guarded binding requires an else block");
                Some(self.expression(0, false))
            }
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
        let parameters = self.parameters(")", ParameterSyntax::Named);
        self.expect(")");
        let annotations = self.annotations();
        let (return_mode, return_type) = self.return_annotation();
        let signature_where = self.signature_where();
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
            return_mode,
            annotations,
            signature_where,
            body,
            span,
        }
    }

    fn signature_where(&mut self) -> Vec<Stmt> {
        let mut items = vec![];
        if self.eat("where") {
            while matches!(
                self.current(),
                "type" | "halt" | "fn" | "eff" | "opaque" | "pub" | "meta" | "sub"
            ) {
                let before = self.pos;
                items.push(self.statement(false));
                if self.pos == before || matches!(self.current(), "{" | "=") {
                    break;
                }
                self.statement_separator();
            }
            if items.is_empty() {
                self.error("E0704", "signature where requires a type declaration");
            }
        }
        items
    }

    fn generics(&mut self) -> Vec<GenericParameter> {
        let mut result = vec![];
        if !self.eat("<") {
            return result;
        }
        self.angles.push(self.delimiters.len());
        if self.at_type_close() {
            self.error("E0120", "a generic parameter list requires a parameter");
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
                        text: String::new(),
                        kind: TypeKind::Error,
                        span,
                    })
                } else {
                    Some(self.type_sort(&name))
                }
            } else {
                None
            };
            let mut guards = vec![];
            while self.eat("|>") {
                guards.push(self.named_type());
            }
            let sort = GenericParameter::sort_for(&name, bound.as_ref());
            let default = if self.eat("=") {
                Some(self.generic_argument(Some(sort)))
            } else {
                None
            };
            result.push(GenericParameter {
                name,
                bound,
                guards,
                default,
                span: self.span(start),
            });
            if self.pos == before || self.at_type_close() || !self.list_separator(">") {
                break;
            }
        }
        self.expect_type_close();
        self.angles.pop();
        result
    }

    fn parameters(&mut self, closing: &str, syntax: ParameterSyntax) -> Vec<Parameter> {
        let mut parameters = vec![];
        while !self.at(closing)
            && !self.eof()
            && !(closing == "->" && matches!(self.current(), "@" | "&"))
        {
            let before = self.pos;
            let start = self.offset();
            if self.at("var") {
                self.error("E0403", "parameters cannot use the var binding mode");
                self.bump();
            }
            if self.at("infer")
                && self
                    .look(1)
                    .as_bytes()
                    .first()
                    .is_some_and(u8::is_ascii_alphabetic)
            {
                self.error("E0412", "infer is a result modifier");
                self.bump();
            }
            let mode = self.parameter_mode();
            let (pattern, ty) = if syntax == ParameterSyntax::Types && self.look(1) != ":" {
                let ty = self.type_expr();
                (
                    Pattern {
                        kind: PatternKind::Wildcard,
                        span: ty.span,
                    },
                    Some(ty),
                )
            } else {
                let start = self.offset();
                let pattern = if matches!(self.current(), "(" | "[" | "{" | "." | "<") {
                    self.error("E0120", "a callable parameter requires a name");
                    self.pattern(false)
                } else {
                    let name = self.name();
                    if name == "_" {
                        self.error_at(
                            self.span(start),
                            "E0120",
                            "a callable parameter requires a name",
                        );
                    }
                    Pattern {
                        kind: PatternKind::Name(name),
                        span: self.span(start),
                    }
                };
                let ty = if self.eat(":") {
                    Some(self.type_expr())
                } else {
                    None
                };
                (pattern, ty)
            };
            let default = if self.at("=") {
                if syntax == ParameterSyntax::Types {
                    self.error("E0120", "a parameter type cannot declare a default");
                }
                self.bump();
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
            if self.pos == before
                || closing == "->" && matches!(self.current(), "@" | "&")
                || !self.list_separator(closing)
            {
                break;
            }
        }
        parameters
    }

    fn parameter_mode(&mut self) -> ParameterMode {
        match self.current() {
            "mut" => {
                self.bump();
                ParameterMode::Mut
            }
            "^mut" => {
                self.bump();
                ParameterMode::SharedMut
            }
            "ref" => {
                self.bump();
                ParameterMode::Ref
            }
            "new" => {
                self.bump();
                ParameterMode::New
            }
            "via" if !matches!(self.look(1), ":" | "=" | ")" | "," | "->") => {
                self.bump();
                ParameterMode::Via
            }
            _ => ParameterMode::Read,
        }
    }

    fn return_annotation(&mut self) -> (ReturnMode, Option<TypeExpr>) {
        if !self.eat("->") {
            return (ReturnMode::Plain, None);
        }
        let mode = match self.current() {
            "new" => {
                self.bump();
                ReturnMode::New
            }
            "infer" if !matches!(self.look(1), "::" | "." | "<" | "{" | "") => {
                let start = self.offset();
                self.bump();
                ReturnMode::Infer(self.span(start))
            }
            "ref" | "^mut" => {
                let shared = self.bump() == "^mut";
                self.expect("(");
                let mut sources = vec![];
                loop {
                    let start = self.offset();
                    let name = self.name();
                    sources.push(ReturnSource {
                        name,
                        span: self.span(start),
                    });
                    if !self.eat("|") {
                        break;
                    }
                }
                self.expect(")");
                if shared {
                    ReturnMode::SharedMut(sources)
                } else {
                    ReturnMode::Ref(sources)
                }
            }
            _ => ReturnMode::Plain,
        };
        (mode, Some(self.type_expr()))
    }

    fn qualified_name(&mut self) -> Vec<String> {
        let mut path = vec![self.name()];
        while self.eat("::") {
            path.push(self.name());
        }
        path
    }

    fn annotations(&mut self) -> Vec<Annotation> {
        let mut result = vec![];
        while self.at("@") || self.at("&") {
            let start = self.offset();
            let kind = if self.eat("@") {
                AnnotationKind::Effects(self.effect_row())
            } else {
                self.bump();
                AnnotationKind::State(self.state_clause(start))
            };
            result.push(Annotation {
                kind,
                span: self.span(start),
            });
        }
        result
    }

    fn effect_row(&mut self) -> EffectRow {
        if self.eat("{") {
            self.expect("}");
            return EffectRow::Closed(vec![]);
        }
        if self.kind() != Some(SyntaxKind::Identifier) {
            return EffectRow::Open;
        }
        let mut effects = vec![self.named_type()];
        while self.eat("+") {
            effects.push(self.named_type());
        }
        EffectRow::Closed(effects)
    }

    fn state_clause(&mut self, start: usize) -> StateClause {
        match self.current() {
            "{" => {
                self.bump();
                self.expect("}");
                StateClause::Empty
            }
            "mut" => {
                self.bump();
                StateClause::Mut
            }
            "^mut" => {
                self.bump();
                StateClause::SharedMut
            }
            "capture" if self.look(1) != "::" => {
                self.bump();
                StateClause::Capture
            }
            "up" if self.look(1) != "::" => {
                self.bump();
                if matches!(self.current(), "(" | "{") {
                    self.state_source_group(start)
                } else {
                    StateClause::Environment
                }
            }
            "return" => {
                self.bump();
                StateClause::Return(self.return_dependencies(start))
            }
            _ if self.kind() == Some(SyntaxKind::Identifier) => {
                StateClause::Provider(self.name_ref())
            }
            _ => StateClause::Open,
        }
    }

    fn state_source_group(&mut self, start: usize) -> StateClause {
        let owner = if self.eat("(") {
            let owner = if self.eat("sub") {
                StateOwner::Module
            } else if self.at(")") {
                self.error("E0538", "a state source selector requires an owner");
                StateOwner::Implicit
            } else {
                let start = self.offset();
                let name = self.name();
                StateOwner::Named {
                    name,
                    span: self.span(start),
                }
            };
            self.expect(")");
            owner
        } else {
            StateOwner::Implicit
        };
        while self.eat("(") {
            self.error_at(
                self.span(start),
                "E0538",
                "a state source group has only one selector",
            );
            if !self.at(")") && !self.eat("sub") {
                self.name();
            }
            self.expect(")");
        }
        let mut items = vec![];
        if !self.eat("{") {
            self.error_at(
                self.span(start),
                "E0538",
                "a state source group requires a braced item list",
            );
        } else {
            while !self.at("}") && !self.eof() {
                let before = self.pos;
                let mode = if self.eat("mut") {
                    StateMode::Mut
                } else if self.eat("^mut") {
                    StateMode::SharedMut
                } else {
                    if self.at("ref") || self.at("var") {
                        self.error("E0538", "a state source accepts only mut or ^mut");
                        self.bump();
                    }
                    StateMode::Read
                };
                items.push(StateSource {
                    mode,
                    name: self.name_ref(),
                });
                if self.pos == before || !self.list_separator("}") {
                    break;
                }
            }
            self.expect("}");
            if items.is_empty() {
                self.error_at(
                    self.span(start),
                    "E0538",
                    "a state source group requires at least one item",
                );
            }
        }
        StateClause::Sources { owner, items }
    }

    fn return_dependencies(&mut self, start: usize) -> Vec<ReturnDependency> {
        let mut dependencies = vec![];
        if !self.eat("{") {
            self.error_at(
                self.span(start),
                "E0545",
                "return dependencies require a braced item list",
            );
            return dependencies;
        }
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let mode = if self.eat("^mut") {
                ReturnDependencyMode::SharedMut
            } else {
                if !self.eat("ref") {
                    self.error("E0545", "a return dependency requires ref or ^mut");
                }
                ReturnDependencyMode::Ref
            };
            dependencies.push(ReturnDependency {
                mode,
                name: self.name_ref(),
            });
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        if dependencies.is_empty() {
            self.error_at(
                self.span(start),
                "E0545",
                "a return dependency group requires at least one item",
            );
        }
        dependencies
    }

    fn name_ref(&mut self) -> NameRef {
        let start = self.offset();
        let path = self.qualified_name();
        NameRef {
            path,
            span: self.span(start),
        }
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
        let signature_where = self.signature_where();
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
                let payload = if self.at("(") {
                    Some(self.variant_payload())
                } else if self.at("{") {
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
        let signature_where = if nominal && signature_where.is_empty() {
            self.signature_where()
        } else {
            signature_where
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
            signature_where,
            opaque,
            nominal,
            span,
        }
    }

    fn variant_payload(&mut self) -> TypeExpr {
        let start = self.offset();
        self.expect("(");
        let mut items = vec![];
        while !self.at(")") && !self.eof() {
            let before = self.pos;
            let mode = self.member_mode(true);
            let label = if self.look(1) == ":" {
                let label = self.name();
                self.expect(":");
                Some(label)
            } else {
                None
            };
            let ty = self.type_expr();
            self.rejected_annotations("E0332", "a variant field cannot carry an invocation suffix");
            items.push(VariantField { label, mode, ty });
            if self.pos == before || !self.list_separator(")") {
                break;
            }
        }
        self.expect(")");
        TypeExpr {
            kind: TypeKind::VariantPayload(items),
            span: self.span(start),
            text: self.text[start..self.last_end].to_owned(),
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
        if self.at("}") {
            self.error(
                "E0120",
                "an effect declaration requires an operation or effect member",
            );
        }
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.look(1) == "(" {
                if !members.is_empty() {
                    self.error(
                        "E0120",
                        "an effect cannot mix operations and effect members",
                    );
                }
                let name = self.name();
                self.expect("(");
                let parameters = self.parameters(")", ParameterSyntax::Types);
                self.expect(")");
                let annotations = self.annotations();
                let (return_mode, return_type) = self.return_annotation();
                operations.push(Function {
                    visibility: Visibility::Public,
                    is_meta: false,
                    is_halt: false,
                    name,
                    generics: vec![],
                    parameters,
                    return_type,
                    return_mode,
                    annotations,
                    signature_where: vec![],
                    body: None,
                    span: self.span(start),
                });
            } else {
                if !operations.is_empty() {
                    self.error(
                        "E0120",
                        "an effect cannot mix operations and effect members",
                    );
                }
                members.push(self.named_type());
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
        let mut path = vec![self.import_segment()];
        while self.eat("/") {
            path.push(self.import_segment());
        }
        let mut namespaces = vec![];
        while self.at("::") && self.look(2) == "::" {
            self.bump();
            namespaces.push(self.name());
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
            namespaces,
            alias,
            members,
            glob,
            span: self.span(start),
        }
    }

    fn import_segment(&mut self) -> String {
        // File path segments are filesystem names. A primitive spelling
        // such as the bytes in ril/bytes is not a declaration identifier.
        if self.kind() == Some(SyntaxKind::Identifier) {
            self.bump()
        } else {
            self.name()
        }
    }

    fn handler(&mut self) -> StmtKind {
        self.expect("with");
        let grouped = self.eat("{");
        let mut arms = vec![];
        if grouped && self.at("}") {
            self.error("E0120", "a handler group requires an operation arm");
            self.bump();
            return StmtKind::Handler(arms);
        }
        loop {
            let start = self.offset();
            self.start(SyntaxKind::Expression);
            let operation = self.handler_target(start);
            if !grouped && !(self.at("(") && self.handler_parameters_ahead()) {
                let call = self.call(operation, start);
                self.finish();
                return StmtKind::HandlerApplication(call);
            }
            self.finish();
            self.expect("(");
            let mut parameters = vec![];
            while !self.at(")") && !self.eof() {
                let before = self.pos;
                let start = self.offset();
                let mode = self.parameter_mode();
                let pattern = self.pattern(true);
                parameters.push(Parameter {
                    pattern,
                    mode,
                    ty: None,
                    default: None,
                    span: self.span(start),
                });
                if self.pos == before || !self.list_separator(")") {
                    break;
                }
            }
            self.expect(")");
            self.expect("->");
            let body = self.expression(0, false);
            arms.push(HandlerArm {
                operation,
                parameters,
                body,
                span: self.span(start),
            });
            if !grouped || !self.list_separator("}") || self.at("}") || self.eof() {
                break;
            }
        }
        if grouped {
            self.expect("}");
        }
        StmtKind::Handler(arms)
    }

    fn handler_target(&mut self, start: usize) -> Expr {
        let mut path = self.qualified_name();
        let signature = self.application_signature(&path, start, HeadKind::Value);
        let kind = if path.len() == 1 {
            ExprKind::Name(path.remove(0))
        } else {
            ExprKind::Path(path)
        };
        let mut target = Expr {
            kind,
            span: self.span(start),
        };
        if self.at("<") {
            let arguments = self.type_arguments(signature.as_deref());
            target = Expr {
                kind: ExprKind::Generic {
                    base: Box::new(target),
                    arguments,
                },
                span: self.span(start),
            };
            if self.eat("::") {
                let name = self.name();
                target = Expr {
                    kind: ExprKind::EffectOperation {
                        effect: Box::new(target),
                        name,
                    },
                    span: self.span(start),
                };
            }
        }
        target
    }

    fn call(&mut self, callee: Expr, start: usize) -> Expr {
        let arguments = if self.eat("(") {
            let arguments = self.arguments();
            self.expect(")");
            arguments
        } else {
            self.expect("(");
            vec![]
        };
        Expr {
            kind: ExprKind::Call {
                callee: Box::new(callee),
                arguments,
            },
            span: self.span(start),
        }
    }

    /// The closing parenthesis distinguishes a handler's pattern list from an
    /// ordinary callable application before either list is parsed. Nested
    /// constructor/tuple parentheses and arrows inside them do not select it.
    fn handler_parameters_ahead(&self) -> bool {
        self.matching_parenthesis().is_some_and(|close| {
            self.tokens[close + 1..]
                .iter()
                .find(|token| {
                    !matches!(
                        token.kind,
                        SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
                    )
                })
                .is_some_and(|token| &self.text[token.start..token.end] == "->")
        })
    }

    fn matching_parenthesis(&self) -> Option<usize> {
        let mut depth = 0usize;
        for index in self.significant()..self.tokens.len() {
            match self.token_text(index) {
                "(" => depth += 1,
                ")" if depth == 1 => return Some(index),
                ")" => depth = depth.checked_sub(1)?,
                _ => {}
            }
        }
        None
    }

    fn block(&mut self) -> Block {
        self.block_items(false)
    }

    fn block_items(&mut self, module: bool) -> Block {
        self.start(SyntaxKind::Block);
        let start = self.offset();
        let mut statements = vec![];
        let mut where_items = vec![];
        self.depth += 1;
        if self.depth > 128 {
            self.exhaust_nesting();
        }
        if !self.eat("{") {
            self.expect("{");
            self.depth -= 1;
            self.finish();
            return Block {
                statements,
                where_items,
                span: self.span(start),
            };
        }
        self.separators();
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            if self.eat("where") {
                self.separators();
                while !self.at("}") && !self.eof() {
                    let before = self.pos;
                    where_items.push(self.statement(false));
                    if self.pos == before {
                        self.bump();
                    }
                    self.statement_separator();
                }
                break;
            }
            statements.push(self.statement(module));
            if self.pos == before {
                self.bump();
            }
            self.statement_separator();
        }
        self.expect("}");
        let span = self.span(start);
        self.depth -= 1;
        self.finish();
        Block {
            statements,
            where_items,
            span,
        }
    }

    fn named_type(&mut self) -> TypeExpr {
        let start = self.offset();
        let path = self.qualified_name();
        let signature = self.application_signature(&path, start, HeadKind::Type);
        let arguments = self.type_arguments(signature.as_deref());
        TypeExpr {
            kind: TypeKind::Name { path, arguments },
            text: self.text[start..self.last_end.max(start)].to_owned(),
            span: self.span(start),
        }
    }

    fn type_sort(&mut self, parameter: &str) -> TypeExpr {
        if parameter
            .as_bytes()
            .first()
            .is_some_and(u8::is_ascii_uppercase)
            && self.at("ril")
            && self.look(1) == "/"
            && self.look(2) == "reflect"
            && self.look(3) == "::"
            && self.look(4) == "MemberMode"
        {
            let start = self.offset();
            self.start(SyntaxKind::TypeExpression);
            for _ in 0..5 {
                self.bump();
            }
            self.finish();
            return TypeExpr {
                kind: TypeKind::QualifiedMemberMode,
                text: self.text[start..self.last_end].to_owned(),
                span: self.span(start),
            };
        }
        let first = self.type_expr();
        if !self.at("|") {
            return first;
        }
        let start = (first.span.start as usize).saturating_sub(self.base);
        let mut alternatives = vec![first];
        while self.eat("|") {
            alternatives.push(self.type_expr());
        }
        TypeExpr {
            kind: TypeKind::Alternatives(alternatives),
            span: self.span(start),
            text: self.text[start..self.last_end.max(start)].to_owned(),
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
            if self.type_pattern_depth > 0 {
                TypeKind::PatternRest(self.eat("let").then(|| self.name()))
            } else {
                TypeKind::Rest(Box::new(self.type_expr()))
            }
        } else if self.at("@") || self.at("&") {
            let code = if self.at("@") { "E0330" } else { "E0331" };
            self.rejected_annotations(code, "effects and capabilities are not data types");
            TypeKind::Error
        } else if self.at("[") && self.static_array_ahead() {
            TypeKind::Computation(Box::new(self.expression(11, true)))
        } else if self.eat("[") {
            self.collection_type()
        } else if self.at("(") && self.mapped_ahead() {
            self.bump();
            let kind = self.mapped_type(true);
            self.expect(")");
            kind
        } else if self.eat("(") {
            let mut items = vec![];
            let mut comma = false;
            while !self.at(")") && !self.eof() {
                let before = self.pos;
                let start = self.offset();
                let capture = if self.type_pattern_depth > 0
                    && self.at("let")
                    && !matches!(self.look(2), "," | ")" | ">")
                {
                    self.bump();
                    Some(self.name())
                } else {
                    None
                };
                let mode = self.member_mode(true);
                let ty = self.type_expr();
                items.push(if let Some(binder) = capture {
                    TypeExpr {
                        kind: TypeKind::PatternMode {
                            binder,
                            ty: Box::new(ty),
                        },
                        span: self.span(start),
                        text: self.text[start..self.last_end].to_owned(),
                    }
                } else if let Some(mode) = mode {
                    TypeExpr {
                        kind: TypeKind::Member {
                            mode,
                            ty: Box::new(ty),
                        },
                        span: self.span(start),
                        text: self.text[start..self.last_end].to_owned(),
                    }
                } else {
                    ty
                });
                self.rejected_annotations(
                    "E0333",
                    "a tuple constituent must put invocation annotations on a callable arrow",
                );
                comma |= self.at(",");
                if self.pos == before || !self.list_separator(")") {
                    break;
                }
            }
            if comma && items.len() == 1 {
                self.error(
                    "E0120",
                    "a tuple requires either zero or at least two elements",
                );
            }
            self.expect(")");
            if items.len() == 1 && !comma {
                items.remove(0).kind
            } else {
                TypeKind::Tuple(items)
            }
        } else if self.at("{") && self.mapped_ahead() {
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
                if row.is_some() {
                    self.error("E0120", "a record permits one final row tail");
                }
                if self.eat("..") {
                    let tail = self.record_tail(field_start);
                    row.get_or_insert_with(|| Box::new(tail));
                } else {
                    let capture = if self.type_pattern_depth > 0 && self.eat("let") {
                        Some(self.name())
                    } else {
                        None
                    };
                    let mode = self.member_mode(true);
                    let name = self.name();
                    self.expect(":");
                    let mut ty = self.type_expr();
                    if let Some(binder) = capture {
                        ty = TypeExpr {
                            span: ty.span,
                            text: ty.text.clone(),
                            kind: TypeKind::PatternMode {
                                binder,
                                ty: Box::new(ty),
                            },
                        };
                    }
                    self.rejected_annotations(
                        "E0333",
                        "a record constituent must put invocation annotations on a callable arrow",
                    );
                    fields.push(TypeField {
                        name,
                        mode,
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
            let parameters = self.parameters(")", ParameterSyntax::Types);
            self.expect(")");
            let annotations = self.annotations();
            let (return_mode, result) = self.return_annotation();
            let result = result.map(Box::new);
            TypeKind::Callable {
                parameters,
                result,
                return_mode,
                annotations,
            }
        } else if self.at("\\") {
            self.bump();
            let mut parameters = vec![];
            while !matches!(self.current(), "->" | "@" | "&") && !self.eof() {
                let start = self.offset();
                let name = self.name();
                let bound = if self.eat(":") {
                    Some(self.type_sort(&name))
                } else {
                    None
                };
                let mut guards = vec![];
                while self.eat("|>") {
                    guards.push(self.named_type());
                }
                let sort = GenericParameter::sort_for(&name, bound.as_ref());
                let default = if self.eat("=") {
                    Some(self.generic_argument(Some(sort)))
                } else {
                    None
                };
                parameters.push(GenericParameter {
                    name,
                    bound,
                    guards,
                    default,
                    span: self.span(start),
                });
                if matches!(self.current(), "@" | "&") || !self.list_separator("->") {
                    break;
                }
            }
            self.rejected_annotations(
                "E0335",
                "type functions cannot carry effects or capabilities",
            );
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
        } else if self.at("let") && self.type_pattern_depth > 0 {
            self.bump();
            let name = self.name();
            TypeKind::TypeBinder(name)
        } else if self.kind() == Some(SyntaxKind::Identifier) || self.at("never") || self.at("type")
        {
            let mut path = vec![self.bump()];
            while self.eat("::") {
                path.push(self.name());
            }
            let signature = self.application_signature(&path, start, HeadKind::Type);
            let arguments = self.type_arguments(signature.as_deref());
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
        let mut projections = 0;
        while self.eat(".") {
            projections += 1;
            if projections + self.depth > 128 {
                self.exhaust_nesting();
                let result = TypeExpr {
                    kind: TypeKind::Error,
                    text: String::new(),
                    span: self.span(start),
                };
                self.finish();
                return result;
            }
            let base = TypeExpr {
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
            text: self.text[start..self.last_end.max(start)].to_owned(),
            kind,
            span: self.span(start),
        };
        self.finish();
        result
    }
    fn member_mode(&mut self, declared: bool) -> Option<String> {
        let start = self.offset();
        let var = self.eat("var");
        let access = matches!(self.current(), "mut" | "^mut" | "ref")
            || declared && self.at("via") && self.look(1) != ":";
        if access {
            self.bump();
        }
        (var || access).then(|| self.text[start..self.last_end].to_owned())
    }

    fn record_tail(&mut self, dots: usize) -> TypeExpr {
        let (start, kind) = if self.type_pattern_depth > 0 {
            let name = self.eat("let").then(|| self.name());
            (dots, TypeKind::PatternRest(name))
        } else if matches!(self.current(), "}" | ",") || self.eof() {
            (dots, TypeKind::OpenRow)
        } else {
            let start = self.offset();
            let name = if self.at("never") {
                self.bump()
            } else {
                self.name()
            };
            (
                start,
                TypeKind::Name {
                    path: vec![name],
                    arguments: vec![],
                },
            )
        };
        TypeExpr {
            text: self.text[start..self.last_end.max(start)].to_owned(),
            kind,
            span: self.span(start),
        }
    }

    fn collection_type(&mut self) -> TypeKind {
        if self.type_pattern_depth > 0 && !self.type_pattern_map_ahead() {
            let length = if self.at("]") {
                None
            } else {
                Some(Box::new(self.expression(0, true)))
            };
            self.expect("]");
            return TypeKind::ArrayPattern {
                length,
                element: Box::new(self.type_expr()),
            };
        }
        let access = if self.type_pattern_depth == 0 {
            self.storage_mode(self.look(1) == "]")
        } else {
            None
        };
        if access.is_some() || self.at("]") {
            self.expect("]");
            return TypeKind::Array {
                access,
                element: Box::new(self.type_expr()),
            };
        }
        let key = self.type_expr();
        if matches!(self.current(), ")" | "}") || self.eof() {
            self.expect("]");
            return TypeKind::Error;
        }
        if !self.eat(":") {
            self.expect(":");
            if self.eat("]") {
                return TypeKind::Error;
            }
        }
        let access = if self.type_pattern_depth == 0 {
            self.storage_mode(starts_type(self.look(1)))
        } else {
            None
        };
        let value = self.type_expr();
        self.expect("]");
        TypeKind::Map {
            key: Box::new(key),
            access,
            value: Box::new(value),
        }
    }

    fn storage_mode(&mut self, named: bool) -> Option<StorageMode> {
        let start = self.offset();
        let kind = match self.current() {
            "mut" => StorageModeKind::Mut,
            "^mut" => StorageModeKind::SharedMut,
            "ref" => StorageModeKind::Ref,
            "via" => StorageModeKind::Via,
            name if named && name.as_bytes().first().is_some_and(u8::is_ascii_uppercase) => {
                StorageModeKind::Parameter(name.to_owned())
            }
            _ => return None,
        };
        self.bump();
        Some(StorageMode {
            kind,
            span: self.span(start),
        })
    }

    fn mapped_ahead(&self) -> bool {
        let mut depth = 0;
        for token in &self.tokens[self.significant() + 1..] {
            match &self.text[token.start..token.end] {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" if depth == 0 => return false,
                ")" | "]" | "}" => depth -= 1,
                "as" if depth == 1 => return true,
                "," | ":" if depth == 0 => return false,
                _ => {}
            }
        }
        false
    }

    fn mapped_type(&mut self, tuple: bool) -> TypeKind {
        let mode = if self.at("[") {
            None
        } else if let Some(mode) = self.member_mode(false) {
            Some(ModeExpression::Concrete(mode))
        } else {
            let start = self.offset();
            let expression = if self.eat("modeof") {
                let ty = self.type_expr();
                Expr {
                    kind: ExprKind::ModeOf(ty),
                    span: self.span(start),
                }
            } else if self.eat("(") {
                let value = self.expression(0, true);
                self.expect(")");
                value
            } else {
                let name = self.name();
                Expr {
                    kind: ExprKind::Name(name),
                    span: self.span(start),
                }
            };
            Some(ModeExpression::Static(Box::new(expression)))
        };
        self.expect("[");
        let keys = Box::new(self.expression(0, true));
        self.expect("as");
        let binder = self.name();
        self.expect("]");
        self.expect(":");
        let value = Box::new(self.type_expr());
        TypeKind::Mapped {
            mode,
            binder,
            keys,
            value,
            tuple,
        }
    }

    fn type_pattern_map_ahead(&self) -> bool {
        let mut depth = 0usize;
        for t in &self.tokens[self.significant()..] {
            let text = &self.text[t.start..t.end];
            match text {
                "[" | "?[" | "(" | "{" => depth += 1,
                "]" | ")" | "}" if depth == 0 => return false,
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
    fn type_arguments(&mut self, signature: Option<&[ArgumentSort]>) -> Vec<TypeExpr> {
        let mut args = vec![];
        if !self.eat("<") {
            return args;
        }
        self.angles.push(self.delimiters.len());
        if self.at_type_close() {
            self.error("E0120", "a generic application requires an argument");
        }
        while !self.at_type_close()
            && !self.eof()
            && !matches!(self.current(), ")" | "]" | "}")
            && !self.declaration_on_new_line()
        {
            let before = self.pos;
            let sort = signature.and_then(|sorts| sorts.get(args.len()));
            args.push(self.generic_argument(sort.copied()));
            if self.pos == before
                || self.at_type_close()
                || self.declaration_on_new_line()
                || !self.list_separator(">")
            {
                break;
            }
        }
        self.expect_type_close();
        self.angles.pop();
        args
    }

    fn declaration_on_new_line(&self) -> bool {
        self.newline()
            && matches!(
                self.current(),
                "let" | "var" | "pub" | "sub" | "meta" | "eff" | "use" | "type" | "halt"
            )
            && self.type_pattern_depth == 0
    }

    fn generic_argument(&mut self, sort: Option<ArgumentSort>) -> TypeExpr {
        // Rigid type patterns have their own argument grammar, including
        // wildcards and binders in the nested pattern positions.
        if self.type_pattern_depth > 0 {
            return self.type_expr();
        }
        let start = self.offset();
        if matches!(sort, None | Some(ArgumentSort::Mode))
            && let Some(mode) = self.member_mode(false)
        {
            return TypeExpr {
                text: mode,
                kind: TypeKind::ModeLiteral,
                span: self.span(start),
            };
        }
        if sort == Some(ArgumentSort::Value)
            || sort == Some(ArgumentSort::Mode) && !crate::lexer::primitive(self.current())
            || sort.is_none() && matches!(self.current(), "if" | "match" | "modeof")
            || self.at("<")
        {
            let expression = self.expression(0, true);
            return TypeExpr {
                text: self.text[start..self.last_end.max(start)].to_owned(),
                kind: TypeKind::Computation(Box::new(expression)),
                span: self.span(start),
            };
        }
        self.type_expr()
    }

    fn expression(&mut self, min: u8, multiline: bool) -> Expr {
        self.expression_with_bar_boundary(min, multiline, false)
    }

    fn expression_with_bar_boundary(
        &mut self,
        min: u8,
        multiline: bool,
        stop_at_bar: bool,
    ) -> Expr {
        self.start(SyntaxKind::Expression);
        let start = self.offset();
        self.depth += 1;
        if self.depth > 128 {
            let kind = ExprKind::Error;
            self.exhaust_nesting();
            self.depth -= 1;
            self.finish();
            return Expr {
                kind,
                span: self.span(start),
            };
        }
        let mut left = self.prefix(multiline, stop_at_bar);
        // A prefix range also occupies the range precedence level. A group
        // starts a separate expression, so its operators do not count here.
        let mut previous_infix = (matches!(left.kind, ExprKind::Range { .. })
            && !self
                .grouped_values
                .contains(&(left.span.start, left.span.end)))
        .then_some(RANGE_PRECEDENCE);
        let mut extensions = 0;
        loop {
            if self.eof() || self.closes_angle() || stop_at_bar && self.at("|") {
                break;
            }
            extensions += 1;
            if extensions + self.depth > 128 {
                self.exhaust_nesting();
                left = Expr {
                    kind: ExprKind::Error,
                    span: self.span(start),
                };
                break;
            }
            if !multiline && self.newline() && !matches!(self.current(), "|>" | "!>" | "??") {
                break;
            }
            if self.at("(") {
                left = self.call(left, start);
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
                        kind: ExprKind::Path(vec![first, name]),
                        span: self.span(start),
                    },
                    ExprKind::Path(mut path) => {
                        path.push(name);
                        Expr {
                            kind: ExprKind::Path(path),
                            span: self.span(start),
                        }
                    }
                    ExprKind::Generic { .. } => Expr {
                        kind: ExprKind::EffectOperation {
                            effect: Box::new(left),
                            name,
                        },
                        span: self.span(start),
                    },
                    _ => {
                        self.error("E0120", "a qualified path requires a declaration name");
                        Expr {
                            kind: ExprKind::Error,
                            span: self.span(start),
                        }
                    }
                };
                continue;
            }
            if self.at("<")
                && !self
                    .grouped_values
                    .contains(&(left.span.start, left.span.end))
            {
                let path = match &left.kind {
                    ExprKind::Name(name) => Some(std::slice::from_ref(name)),
                    ExprKind::Path(path) => Some(path.as_slice()),
                    _ => None,
                };
                let signature =
                    path.and_then(|path| self.application_signature(path, start, HeadKind::Value));
                // The skeleton pass is only used to find declarations and scopes.
                // Its guessed expressions are discarded before constructing HIR.
                if signature.is_some()
                    || self.lookup.is_none() && path.is_some() && self.generic_call_ahead()
                {
                    let arguments = self.type_arguments(signature.as_deref());
                    left = Expr {
                        kind: ExprKind::Generic {
                            base: Box::new(left),
                            arguments,
                        },
                        span: self.span(start),
                    };
                    continue;
                }
            }
            if self.at("?") {
                let operator_start = self.offset();
                self.bump();
                left = Expr {
                    kind: ExprKind::Control {
                        operation: ControlOperation::Propagate,
                        operator_span: self.span(operator_start),
                        value: Some(Box::new(left)),
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
                            kind: ExprKind::Call { callee, arguments },
                            span: self.span(start),
                        }
                    }
                    _ => Expr {
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
            let (binding, right_binding) = if assignment_operator(self.current()) {
                (ASSIGNMENT_PRECEDENCE, ASSIGNMENT_PRECEDENCE + 1)
            } else if let Some(precedence) = precedence(self.current()) {
                precedence
            } else {
                break;
            };
            if binding < min {
                break;
            }
            if previous_infix == Some(binding) {
                match binding {
                    ASSIGNMENT_PRECEDENCE => {
                        self.error("E0701", "chained assignment is prohibited")
                    }
                    COMPARISON_PRECEDENCE | RANGE_PRECEDENCE => self.error(
                        "E0120",
                        "parenthesize non-associative operators at the same precedence",
                    ),
                    _ => {}
                }
            }
            previous_infix = Some(binding);
            let operator = self.bump();
            if operator == "is" {
                let test = self.value_test(right_binding, multiline);
                left = Expr {
                    kind: ExprKind::Is {
                        value: Box::new(left),
                        test,
                    },
                    span: self.span(start),
                };
                continue;
            }
            if matches!(operator.as_str(), ".." | "..=") {
                let end = if matches!(self.current(), "]" | ")" | "," | "}" | ";" | "as")
                    || self.eof()
                    || self.closes_angle()
                {
                    None
                } else {
                    Some(Box::new(self.expression_with_bar_boundary(
                        right_binding,
                        multiline,
                        stop_at_bar,
                    )))
                };
                left = Expr {
                    kind: ExprKind::Range {
                        start: Some(Box::new(left)),
                        end,
                        inclusive: operator == "..=",
                    },
                    span: self.span(start),
                };
                continue;
            }
            let right = self.expression_with_bar_boundary(right_binding, multiline, stop_at_bar);
            let kind = if binding == ASSIGNMENT_PRECEDENCE {
                ExprKind::Assignment {
                    target: Box::new(left),
                    operator,
                    value: Box::new(right),
                }
            } else {
                ExprKind::Binary {
                    operator,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            };
            left = Expr {
                kind,
                span: self.span(start),
            };
        }
        self.depth -= 1;
        self.finish();
        left
    }

    fn prefix(&mut self, multiline: bool, stop_at_bar: bool) -> Expr {
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
            "-" | "!" | "~" | "typeof" | "^mut" | "new" => {
                let operator = self.bump();
                let operand = Box::new(self.expression(14, multiline));
                ExprKind::Unary { operator, operand }
            }
            ".." | "..=" => {
                let inclusive = self.bump() == "..=";
                let end = if matches!(self.current(), "]" | ")" | "," | "}") || self.eof() {
                    None
                } else {
                    Some(Box::new(self.expression_with_bar_boundary(
                        RANGE_PRECEDENCE + 1,
                        multiline,
                        stop_at_bar,
                    )))
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
                    ExprKind::Tuple(vec![])
                } else {
                    let first = self.tuple_value();
                    if self.eat(",") {
                        let mut items = vec![first];
                        while !self.at(")") && !self.eof() {
                            let before = self.pos;
                            items.push(self.tuple_value());
                            if self.pos == before || !self.list_separator(")") {
                                break;
                            }
                        }
                        if items.len() == 1 {
                            self.error(
                                "E0120",
                                "a tuple requires either zero or at least two elements",
                            );
                        }
                        self.expect(")");
                        ExprKind::Tuple(items)
                    } else {
                        self.expect(")");
                        let first = match first.kind {
                            ExprKind::TupleMember { mode, value } if mode == "^mut" => Expr {
                                span: first.span,
                                kind: ExprKind::Unary {
                                    operator: mode,
                                    operand: value,
                                },
                            },
                            ExprKind::TupleMember { .. } => {
                                self.error("E0120", "tuple member mode requires a tuple");
                                Expr {
                                    span: first.span,
                                    kind: ExprKind::Error,
                                }
                            }
                            _ => first,
                        };
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
                let pattern = if self.eat("let") {
                    Some(self.pattern(true))
                } else {
                    None
                };
                if pattern.is_some() {
                    self.expect("=");
                }
                let condition = Box::new(self.expression(0, true));
                let block = self.block();
                let then_branch = Box::new(Expr {
                    span: block.span,
                    kind: ExprKind::Block(block),
                });
                let else_branch = if self.eat("else") {
                    Some(Box::new(if self.at("if") {
                        self.expression(14, false)
                    } else {
                        let block = self.block();
                        Expr {
                            span: block.span,
                            kind: ExprKind::Block(block),
                        }
                    }))
                } else {
                    None
                };
                if let Some(pattern) = pattern {
                    ExprKind::IfLet {
                        pattern,
                        value: condition,
                        then_branch,
                        else_branch,
                    }
                } else {
                    ExprKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    }
                }
            }
            "match" => return self.match_expr(),
            "loop" => {
                self.bump();
                ExprKind::Loop(self.block())
            }
            "while" => {
                self.bump();
                let pattern = if self.eat("let") {
                    Some(self.pattern(true))
                } else {
                    None
                };
                if pattern.is_some() {
                    self.expect("=");
                }
                let condition = Box::new(self.expression(0, true));
                let body = self.block();
                if let Some(pattern) = pattern {
                    ExprKind::WhileLet {
                        pattern,
                        value: condition,
                        body,
                    }
                } else {
                    ExprKind::While { condition, body }
                }
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
                let operator_span = self.span(start);
                let value = if operation == ControlOperation::Resume
                    || operation != ControlOperation::Next
                        && !self.eof()
                        && !self.closes_angle()
                        && (multiline || !self.newline())
                        && !matches!(self.current(), ";" | "}" | "," | ")" | "]" | "where")
                {
                    Some(Box::new(self.expression(0, multiline)))
                } else {
                    None
                };
                ExprKind::Control {
                    operation,
                    operator_span,
                    value,
                }
            }
            "<" => ExprKind::TypeValue(self.quoted_type(false)),
            "keyof" => {
                self.bump();
                ExprKind::KeyOf(self.type_expr())
            }
            "modeof" => {
                self.bump();
                ExprKind::ModeOf(self.type_expr())
            }
            _ => match self.kind() {
                Some(SyntaxKind::Integer) => ExprKind::Literal(Literal::Integer(self.bump())),
                Some(SyntaxKind::Float) => ExprKind::Literal(Literal::Float(self.bump())),
                Some(SyntaxKind::String) => self.string_literal(),
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
            kind,
            span: self.span(start),
        }
    }

    fn string_literal(&mut self) -> ExprKind {
        let token = self.tokens[self.significant()];
        let interpolations = Rc::clone(&self.interpolations);
        let Some(regions) = interpolations.get(&token.start) else {
            return ExprKind::Literal(Literal::String(self.bump()));
        };
        self.trivia();
        self.start(SyntaxKind::InterpolatedString);
        let mut previous = token.start;
        let mut parts = vec![];
        for region in regions {
            self.emit_slice(SyntaxKind::String, previous, region.start);
            if let Some(decoded) =
                decode_string_text(&self.text[previous.max(token.start + 1)..region.start])
                && !decoded.is_empty()
            {
                parts.push(StringPart::Text(decoded));
            }
            parts.push(self.parse_interpolation(region));
            previous = region.end + 1;
        }
        self.emit_slice(SyntaxKind::String, previous, token.end);
        let closed = self.text.as_bytes()[token.end - 1] == b'"';
        let content_end = token.end - usize::from(closed);
        if previous < content_end
            && let Some(decoded) = decode_string_text(&self.text[previous..content_end])
        {
            parts.push(StringPart::Text(decoded));
        }
        self.finish();
        self.pos += 1;
        self.last_end = token.end;
        ExprKind::Interpolated(parts)
    }

    fn emit_slice(&mut self, kind: SyntaxKind, start: usize, end: usize) {
        if start < end {
            self.builder
                .token(RilLanguage::kind_to_raw(kind), &self.text[start..end]);
        }
    }

    fn parse_interpolation(&mut self, region: &StringRegion) -> StringPart {
        self.start(SyntaxKind::Interpolation);
        self.emit_slice(SyntaxKind::Punctuation, region.start, region.start + 1);
        let span = self.span_range(region.start, region.end + 1);
        let mut child = Self::with_tokens(
            self.text,
            self.file,
            self.base,
            self.lookup,
            region.tokens.clone(),
            Rc::clone(&self.interpolations),
        );
        child.limit = region.format.unwrap_or(region.end);
        child.last_end = region.start + 1;
        child.depth = self.depth;
        std::mem::swap(&mut self.builder, &mut child.builder);

        let expression = if child.eof() {
            child.error_at(span, "E0112", "interpolation requires an expression");
            Expr {
                kind: ExprKind::Error,
                span,
            }
        } else {
            child.expression(0, true)
        };
        let format_start = if child.at(":") {
            Some(child.offset())
        } else {
            if !child.eof() {
                child.error("E0120", "unexpected token after interpolation expression");
                while !child.eof() {
                    child.recovery(true);
                }
            }
            region.format
        };
        child.trivia();
        std::mem::swap(&mut self.builder, &mut child.builder);
        let expression_end = (self.base + format_start.unwrap_or(region.end)) as u32;
        self.diagnostics.extend(
            region
                .diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic
                        .labels
                        .first()
                        .is_none_or(|label| label.span.start < expression_end)
                })
                .cloned(),
        );
        self.diagnostics.extend(child.diagnostics);
        self.incomplete |= child.incomplete;

        let format = format_start.and_then(|colon| {
            self.emit_slice(SyntaxKind::Punctuation, colon, colon + 1);
            self.emit_slice(SyntaxKind::FormatText, colon + 1, region.end);
            let span = self.span_range(colon + 1, region.end);
            if let Some(spec) = FormatSpec::parse(&self.text[colon + 1..region.end]) {
                Some(InterpolationFormat { spec, span })
            } else {
                self.error_at(span, "E0112", "malformed interpolation format");
                None
            }
        });
        self.emit_slice(SyntaxKind::Punctuation, region.end, region.end + 1);
        self.finish();
        StringPart::Interpolation {
            expression: Box::new(expression),
            format,
            span,
        }
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
            } else if delimiters > 0 && matches!(text, ")" | "]" | "}" | ">") {
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
            let label = if self.kind() == Some(SyntaxKind::Identifier) && self.look(1) == ":" {
                let name = self.name();
                self.bump();
                Some(name)
            } else {
                None
            };
            let mode = if self.at("via") {
                ParameterMode::Read
            } else {
                self.parameter_mode()
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

    fn tuple_value(&mut self) -> Expr {
        let start = self.offset();
        let mode = self.member_mode(false);
        let value = self.expression(0, true);
        match mode {
            Some(mode) => Expr {
                kind: ExprKind::TupleMember {
                    mode,
                    value: Box::new(value),
                },
                span: self.span(start),
            },
            None => value,
        }
    }

    fn collection(&mut self) -> Expr {
        let start = self.offset();
        self.expect("[");
        if self.eat("]") {
            return Expr {
                kind: ExprKind::Array(vec![]),
                span: self.span(start),
            };
        }
        if self.eat(":") {
            self.expect("]");
            return Expr {
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
            kind,
            span: self.span(start),
        }
    }

    fn record(&mut self, ty: Option<TypeExpr>, start: usize) -> Expr {
        self.expect("{");
        let mut members = vec![];
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.eat("..") {
                let value = self.expression(0, true);
                members.push(RecordMember::Spread(value));
            } else {
                let mode = self.member_mode(false);
                let name = self.name();
                let value = if self.eat(":") {
                    self.expression(0, true)
                } else {
                    Expr {
                        kind: ExprKind::Name(name.clone()),
                        span: self.span(start),
                    }
                };
                let field = RecordField {
                    mode,
                    name,
                    value,
                    span: self.span(start),
                };
                members.push(RecordMember::Field(field));
            }
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        Expr {
            kind: ExprKind::Record { ty, members },
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
                kind: ExprKind::Accessor(path),
                span: self.span(start),
            };
        }
        let parameters = self.parameters("->", ParameterSyntax::Named);
        let annotations = self.annotations();
        self.expect("->");
        let body = Box::new(self.expression(0, false));
        Expr {
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
            kind: ExprKind::Match { value, arms },
            span: self.span(start),
        }
    }

    fn value_test(&mut self, min: u8, multiline: bool) -> ValueTest {
        self.start(SyntaxKind::ValueTest);
        let start = self.offset();
        self.depth += 1;
        let mut test = if self.depth > 128 {
            self.exhaust_nesting();
            ValueTest {
                kind: ValueTestKind::Error,
                span: self.span(start),
            }
        } else {
            self.value_test_alternative(min, multiline)
        };
        if self.at("|") && (multiline || !self.newline()) {
            let mut alternatives = vec![test];
            while self.at("|") && (multiline || !self.newline()) {
                self.bump();
                alternatives.push(self.value_test_alternative(min, multiline));
            }
            test = ValueTest {
                kind: ValueTestKind::Alternative(alternatives),
                span: self.span(start),
            };
        }
        if self.at("if") && (multiline || !self.newline()) {
            self.error("E0120", "is tests do not admit a trailing guard");
            self.bump();
            self.expression(min, multiline);
        }
        self.depth -= 1;
        self.finish();
        test
    }

    fn value_test_alternative(&mut self, min: u8, multiline: bool) -> ValueTest {
        let start = self.offset();
        if self.eat("_") {
            return ValueTest {
                kind: ValueTestKind::Wildcard,
                span: self.span(start),
            };
        }
        if self.at("(") && self.test_group_is_tuple() {
            self.bump();
            let tests = self.test_list(")");
            if tests.len() == 1 {
                self.error_at(
                    self.span(start),
                    "E0120",
                    "a tuple test requires at least two elements",
                );
            }
            return ValueTest {
                kind: ValueTestKind::Tuple(tests),
                span: self.span(start),
            };
        }
        if self.at(".") && self.look(1) == "{" {
            self.bump();
            return self.record_value_test(None, start);
        }
        if self.kind() == Some(SyntaxKind::Identifier) {
            let mut path = vec![self.current().to_owned()];
            let mut after = 1;
            while self.look(after) == "::" {
                path.push(self.look(after + 1).to_owned());
                after += 2;
            }
            let record = if self.look(after) == "<" {
                self.look_index(after)
                    .and_then(|open| self.after_angle_list(open))
                    .is_some_and(|after| {
                        let mut suffix = self.tokens[after..].iter().filter(|token| !matches!(
                            token.kind, SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
                        ));
                        matches!(suffix.next(), Some(token) if &self.text[token.start..token.end] == ".")
                            && matches!(suffix.next(), Some(token) if &self.text[token.start..token.end] == "{")
                    })
            } else {
                self.look(after) == "." && self.look(after + 1) == "{"
            };
            if record {
                let ty = self.named_type();
                self.expect(".");
                return self.record_value_test(Some(ty), start);
            }
            if self.look(after) != "<"
                && self
                    .declaration_head(&path, self.span(start))
                    .is_some_and(|head| head.constructor)
            {
                self.qualified_name();
                let head = self.span(start);
                let arguments = if (multiline || !self.newline()) && self.eat("(") {
                    Some(self.test_list(")"))
                } else {
                    None
                };
                return ValueTest {
                    kind: ValueTestKind::Constructor {
                        path,
                        head,
                        arguments,
                    },
                    span: self.span(start),
                };
            }
        }
        let expression = self.expression_with_bar_boundary(min, multiline, true);
        self.test_from_expression(expression)
    }

    fn test_group_is_tuple(&self) -> bool {
        if self.look(1) == ")" {
            return true;
        }
        if self.probing_test_group {
            return false;
        }
        let Some(close) = self.matching_parenthesis() else {
            return false;
        };
        let open = self.significant();
        let mut nested = 0usize;
        let possible_tuple = (open + 1..close).any(|index| {
            match self.token_text(index) {
                "(" | "[" | "?[" | "{" => nested += 1,
                ")" | "]" | "}" => nested = nested.saturating_sub(1),
                "," if nested == 0 => return true,
                _ => {}
            }
            false
        });
        if !possible_tuple {
            return false;
        }
        // The ordinary parenthesis grammar distinguishes a separator from
        // a comma in a generic application or anonymous callable head.
        let start = self.tokens[open].start;
        let end = self.tokens[close].end;
        let mut probe = Parser::new(
            &self.text[start..end],
            self.file,
            self.base + start,
            self.lookup,
        );
        probe.probing_test_group = true;
        probe.start(SyntaxKind::Root);
        let expression = probe.prefix(true, false);
        probe.finish();
        matches!(expression.kind, ExprKind::Tuple(_))
            && !probe
                .grouped_values
                .contains(&(expression.span.start, expression.span.end))
    }

    /// Find the suffix after an angle list followed by a structural form.
    /// An operator fragment attached to the final close is part of the suffix.
    fn after_angle_list(&self, open: usize) -> Option<usize> {
        let mut angles = 1usize;
        let mut delimiters = 0usize;
        for index in open + 1..self.tokens.len() {
            let token = self.token_text(index);
            match token {
                "(" | "[" | "?[" | "{" => delimiters += 1,
                ")" | "]" | "}" => delimiters = delimiters.checked_sub(1)?,
                _ if delimiters != 0 => {}
                "<" => angles += 1,
                ";" => return None,
                _ => {
                    let closes = token.bytes().take_while(|byte| *byte == b'>').count();
                    if closes >= angles {
                        return (closes == angles && closes == token.len()).then_some(index + 1);
                    }
                    angles -= closes;
                }
            }
        }
        None
    }

    fn test_list(&mut self, closing: &str) -> Vec<ValueTest> {
        let mut tests = vec![];
        while !self.at(closing) && !self.eof() {
            let before = self.pos;
            tests.push(self.value_test(0, true));
            if self.pos == before || !self.list_separator(closing) {
                break;
            }
        }
        self.expect(closing);
        tests
    }

    fn record_value_test(&mut self, ty: Option<TypeExpr>, start: usize) -> ValueTest {
        self.expect("{");
        let mut fields = vec![];
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.at("..") {
                self.error("E0120", "a record test lists fields rather than spreads");
                self.bump();
                self.expression(0, true);
            } else {
                if self.member_mode(false).is_some() {
                    self.error_at(
                        self.span(start),
                        "E0120",
                        "is tests do not admit binding modifiers",
                    );
                }
                let name = self.name();
                let test = if self.eat(":") {
                    self.value_test(0, true)
                } else {
                    let span = self.span(start);
                    ValueTest {
                        kind: ValueTestKind::Value(Box::new(Expr {
                            kind: ExprKind::Name(name.clone()),
                            span,
                        })),
                        span,
                    }
                };
                fields.push(ValueTestField {
                    name,
                    test,
                    span: self.span(start),
                });
            }
            if self.pos == before || !self.list_separator("}") {
                break;
            }
        }
        self.expect("}");
        ValueTest {
            kind: ValueTestKind::Record { ty, fields },
            span: self.span(start),
        }
    }

    fn test_from_expression(&mut self, expression: Expr) -> ValueTest {
        let span = expression.span;
        let kind = if self.grouped_values.contains(&(span.start, span.end)) {
            ValueTestKind::Value(Box::new(expression))
        } else {
            match expression.kind {
                ExprKind::Range {
                    start: Some(start),
                    end: Some(end),
                    inclusive,
                } if self.numeric_test_bound(&start) && self.numeric_test_bound(&end) => {
                    ValueTestKind::Range {
                        start,
                        end,
                        inclusive,
                    }
                }
                ExprKind::Unary { ref operator, .. } if operator == "^mut" => {
                    self.error_at(span, "E0120", "is tests do not admit binding modifiers");
                    ValueTestKind::Error
                }
                _ => ValueTestKind::Value(Box::new(expression)),
            }
        };
        ValueTest { kind, span }
    }

    fn numeric_test_bound(&self, expression: &Expr) -> bool {
        let span = expression.span;
        if self.grouped_values.contains(&(span.start, span.end)) {
            return false;
        }
        match &expression.kind {
            ExprKind::Literal(literal) => numeric_literal(literal),
            ExprKind::Unary { operator, operand } if operator == "-" => {
                let span = operand.span;
                !self.grouped_values.contains(&(span.start, span.end))
                    && matches!(&operand.kind, ExprKind::Literal(literal) if numeric_literal(literal))
            }
            _ => false,
        }
    }

    fn pattern(&mut self, alternatives: bool) -> Pattern {
        self.start(SyntaxKind::Pattern);
        let start = self.offset();
        let mut pattern = self.pattern_atom();
        if matches!(self.current(), ".." | "..=") {
            let inclusive = self.bump() == "..=";
            let end = self.pattern_atom();
            let span = self.span(start);
            let kind = match (pattern.kind, end.kind) {
                (PatternKind::Literal(start), PatternKind::Literal(end))
                    if numeric_literal(&start) && numeric_literal(&end) =>
                {
                    PatternKind::Range {
                        start,
                        end,
                        inclusive,
                    }
                }
                _ => {
                    self.error_at(
                        span,
                        "E0349",
                        "a range pattern requires numeric literal endpoints",
                    );
                    PatternKind::Error
                }
            };
            pattern = Pattern { kind, span };
        }
        if !matches!(self.current(), "|" | ".." | "..=")
            && let Some((_, right_binding)) = precedence(self.current())
        {
            self.error(
                "E0349",
                "match and binding patterns cannot evaluate a computed expression",
            );
            self.bump();
            self.expression(right_binding, true);
            pattern = Pattern {
                kind: PatternKind::Error,
                span: self.span(start),
            };
        }
        if alternatives && self.eat("|") {
            let mut choices = vec![pattern];
            loop {
                choices.push(self.pattern(false));
                if !self.eat("|") {
                    break;
                }
            }
            pattern = Pattern {
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
            "var" | "mut" | "^mut" | "ref" => {
                let mode = self.pattern_mode().expect("matched binding modifier");
                PatternKind::Mode {
                    mode,
                    pattern: Box::new(self.pattern_atom()),
                }
            }
            "<" => PatternKind::Type(self.quoted_type(true)),
            "(" => {
                self.bump();
                PatternKind::Tuple(self.sequence_patterns(")", false))
            }
            "[" => {
                self.bump();
                PatternKind::Array(self.sequence_patterns("]", true))
            }
            "." if self.look(1) == "{" => {
                self.bump();
                return self.record_pattern(None, start);
            }
            "{" => {
                self.error("E0120", "a record pattern starts with '.{'");
                return self.record_pattern(None, start);
            }
            "-" => {
                self.bump();
                match self.kind() {
                    Some(SyntaxKind::Integer) => {
                        PatternKind::Literal(Literal::Integer(format!("-{}", self.bump())))
                    }
                    Some(SyntaxKind::Float) => {
                        PatternKind::Literal(Literal::Float(format!("-{}", self.bump())))
                    }
                    _ => {
                        self.error_at(
                            self.span(start),
                            "E0349",
                            "a negative pattern requires a numeric literal",
                        );
                        self.expression(14, true);
                        PatternKind::Error
                    }
                }
            }
            "true" | "false" => PatternKind::Literal(Literal::Bool(self.bump() == "true")),
            _ => match self.kind() {
                Some(SyntaxKind::Integer) => PatternKind::Literal(Literal::Integer(self.bump())),
                Some(SyntaxKind::Float) => PatternKind::Literal(Literal::Float(self.bump())),
                Some(SyntaxKind::String) => match self.string_literal() {
                    ExprKind::Literal(literal) => PatternKind::Literal(literal),
                    _ => {
                        self.error_at(
                            self.span(start),
                            "E0349",
                            "an interpolated string is not a literal pattern",
                        );
                        PatternKind::Error
                    }
                },
                Some(SyntaxKind::RawString) => {
                    PatternKind::Literal(Literal::RawString(self.bump()))
                }
                Some(SyntaxKind::Bytes) => PatternKind::Literal(Literal::Bytes(self.bump())),
                Some(SyntaxKind::Identifier) => {
                    let mut path = self.qualified_name();
                    let signature = self.application_signature(&path, start, HeadKind::Type);
                    let applied = self.at("<");
                    let type_arguments = self.type_arguments(signature.as_deref());
                    if self.at(".") && self.look(1) == "{" {
                        let ty = TypeExpr {
                            text: self.text[start..self.last_end].to_owned(),
                            kind: TypeKind::Name {
                                path,
                                arguments: type_arguments,
                            },
                            span: self.span(start),
                        };
                        self.bump();
                        return self.record_pattern(Some(ty), start);
                    }
                    if applied {
                        self.error_at(
                            self.span(start),
                            "E0349",
                            "only typed record patterns use a type application",
                        );
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
                    self.error("E0120", "expected a binding pattern");
                    if !self.eof() && !matches!(self.current(), ")" | "]" | "}" | "," | "->") {
                        self.recovery(true);
                    }
                    PatternKind::Error
                }
            },
        };
        Pattern {
            kind,
            span: self.span(start),
        }
    }
    fn sequence_patterns(&mut self, close: &str, named_rest: bool) -> Vec<Pattern> {
        let mut parts = vec![];
        let mut has_rest = false;
        while !self.at(close) && !self.eof() {
            let before = self.pos;
            if self.at("..") {
                self.start(SyntaxKind::Pattern);
                let start = self.offset();
                self.bump();
                if has_rest {
                    self.error(
                        "E0347",
                        "one tuple or array pattern permits at most one rest",
                    );
                }
                has_rest = true;
                let name = if self.kind() == Some(SyntaxKind::Identifier) {
                    let name = self.name();
                    if !named_rest {
                        self.error("E0120", "tuple rest cannot introduce a binding");
                    }
                    Some(name)
                } else {
                    None
                };
                parts.push(Pattern {
                    kind: PatternKind::Rest(name),
                    span: self.span(start),
                });
                self.finish();
            } else {
                parts.push(self.pattern(true));
            }
            if self.pos == before || !self.list_separator(close) {
                break;
            }
        }
        self.expect(close);
        parts
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
                let mode = self.pattern_mode();
                let name = self.name();
                let mut pattern = if self.eat(":") {
                    self.pattern(true)
                } else {
                    Pattern {
                        kind: PatternKind::Name(name.clone()),
                        span: self.span(start),
                    }
                };
                if let Some(mode) = mode {
                    pattern = Pattern {
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
            kind: PatternKind::Record {
                ty,
                fields,
                rest,
                rest_binding,
            },
            span: self.span(start),
        }
    }

    fn pattern_mode(&mut self) -> Option<BindingMode> {
        let var = self.eat("var");
        let mode = match (var, self.current()) {
            (true, "mut") => BindingMode::VarMut,
            (true, "^mut") => BindingMode::VarSharedMut,
            (true, "ref") => BindingMode::VarRef,
            (true, _) => return Some(BindingMode::Var),
            (false, "mut") => BindingMode::LetMut,
            (false, "^mut") => BindingMode::LetSharedMut,
            (false, "ref") => BindingMode::Ref,
            (false, _) => return None,
        };
        self.bump();
        Some(mode)
    }

    fn quoted_type(&mut self, pattern: bool) -> TypeExpr {
        self.expect("<");
        self.angles.push(self.delimiters.len());
        self.type_pattern_depth += usize::from(pattern);
        let start = self.offset();
        let ty = if self.at_type_close() || self.eof() || matches!(self.current(), ")" | "]" | "}")
        {
            if self.at_type_close() {
                self.error("E0120", "a type quote requires one type");
            }
            TypeExpr {
                kind: TypeKind::Error,
                text: String::new(),
                span: self.span(start),
            }
        } else {
            self.type_expr()
        };
        if self.at(",") {
            self.error("E0120", "a type quote contains one type");
            while self.eat(",")
                && !self.at_type_close()
                && !self.eof()
                && !matches!(self.current(), ")" | "]" | "}")
                && !self.declaration_on_new_line()
            {
                let before = self.pos;
                self.type_expr();
                if self.pos == before {
                    break;
                }
            }
        }
        self.expect_type_close();
        self.type_pattern_depth -= usize::from(pattern);
        self.angles.pop();
        ty
    }
}

fn screaming_name(name: &str) -> bool {
    name.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
        && name
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'_')
}

fn starts_type(token: &str) -> bool {
    matches!(token, "?" | "?[" | "[" | "(" | "{" | "fn" | "typeof" | "\\")
        || crate::lexer::primitive(token)
        || token.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
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
        "==" | "!=" | "<" | "<=" | ">" | ">=" | "is" => {
            (COMPARISON_PRECEDENCE, COMPARISON_PRECEDENCE + 1)
        }
        ".." | "..=" => (RANGE_PRECEDENCE, RANGE_PRECEDENCE + 1),
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
        text: path.join("::"),
        kind: TypeKind::Name { path, arguments },
        span: expr.span,
    }
}
fn numeric_literal(literal: &Literal) -> bool {
    matches!(literal, Literal::Integer(_) | Literal::Float(_))
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
