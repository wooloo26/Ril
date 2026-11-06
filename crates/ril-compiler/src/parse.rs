//! Recovering recursive-descent declarations and Pratt expressions.
use crate::{
    RilLanguage, SyntaxKind, SyntaxNode,
    ast::*,
    lexer::{Token, diagnostic, lex},
};
use crate::{
    diagnostic::Diagnostic,
    source::{FileId, Span},
};
use rowan::{GreenNode, GreenNodeBuilder, Language};
use std::collections::BTreeSet;

type SignatureLookup<'a> = dyn Fn(&[String], u32) -> Option<Vec<ArgumentSort>> + Sync + 'a;

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

#[derive(Debug, Clone)]
struct ExpressionParse {
    pub expression: Expr,
    pub diagnostics: Vec<Diagnostic>,
    pub incomplete: bool,
}
fn parse_expression_inner(
    text: &str,
    file: FileId,
    offset: usize,
    lookup: Option<&SignatureLookup<'_>>,
) -> ExpressionParse {
    let mut parser = Parser::new(text, file, offset, lookup);
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
pub(crate) fn parse_with_heads(text: &str, file: FileId, lookup: &SignatureLookup<'_>) -> Parse {
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

fn parse_file_inner(text: &str, file: FileId, lookup: Option<&SignatureLookup<'_>>) -> Parse {
    let mut parser = Parser::new(text, file, 0, lookup);
    parser.start(SyntaxKind::Root);
    let mut statements = vec![];
    parser.separators();
    while !parser.eof() {
        let before = parser.pos;
        statements.push(parser.statement());
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
    pos: usize,
    last_end: usize,
    builder: GreenNodeBuilder<'static>,
    diagnostics: Vec<Diagnostic>,
    incomplete: bool,
    depth: usize,
    budget_exhausted: bool,
    grouped_values: BTreeSet<(u32, u32)>,
    lookup: Option<&'a SignatureLookup<'a>>,
    delimiters: Vec<&'static str>,
    angles: Vec<usize>,
    type_pattern_depth: usize,
}

impl<'a> Parser<'a> {
    fn exhaust_nesting(&mut self) {
        self.incomplete = true;
        self.budget_exhausted = true;
        while !self.eof() {
            self.bump();
        }
    }
    fn new(
        text: &'a str,
        file: FileId,
        base: usize,
        lookup: Option<&'a SignatureLookup<'a>>,
    ) -> Self {
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
            lookup,
            delimiters: Vec::new(),
            angles: Vec::new(),
            type_pattern_depth: 0,
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

    fn application_signature(&self, path: &[String], start: usize) -> Option<Vec<ArgumentSort>> {
        self.lookup
            .and_then(|lookup| lookup(path, (self.base + start) as u32))
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
        let opaque = self.at("opaque") && self.look(1) == "type" && self.eat("opaque");
        let kind = match self.current() {
            "fn" => StmtKind::Function(self.function(visibility, is_meta, is_halt)),
            "type" => StmtKind::Type(self.type_declaration(visibility, is_halt, opaque)),
            "eff" => StmtKind::Effect(self.effect(visibility)),
            "sub" => {
                self.bump();
                let name = self.name();
                let block = self.block();
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
            "let" | "var" => StmtKind::Binding(Box::new(self.binding(visibility, is_meta))),
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

    fn binding(&mut self, visibility: Visibility, is_meta: bool) -> Binding {
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
        let annotations = self.annotations(false);
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
                items.push(self.statement());
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
                    Some(self.type_sort())
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

    fn parameters(&mut self, closing: &str, typed: bool) -> Vec<Parameter> {
        let mut parameters = vec![];
        while !self.at(closing)
            && !self.eof()
            && !(closing == "->" && matches!(self.current(), "@" | "&"))
        {
            let before = self.pos;
            let start = self.offset();
            let mode = self.parameter_mode();
            let (pattern, ty) = if typed && self.look(1) != ":" && self.type_only_parameter() {
                let ty = self.type_expr();
                (
                    Pattern {
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
            if self.pos == before
                || closing == "->" && matches!(self.current(), "@" | "&")
                || !self.list_separator(closing)
            {
                break;
            }
        }
        parameters
    }
    fn type_only_parameter(&self) -> bool {
        matches!(self.current(), "[" | "{" | "?" | "?[" | "fn" | "(")
            || crate::lexer::primitive(self.current())
            || self
                .current()
                .as_bytes()
                .first()
                .is_some_and(u8::is_ascii_uppercase)
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
                self.bump();
                ReturnMode::Infer
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

    fn annotations(&mut self, open_rows: bool) -> Vec<Annotation> {
        let mut result = vec![];
        while self.at("@") || self.at("&") {
            let start = self.offset();
            let mut references = Vec::new();
            let kind = if self.eat("@") {
                if self.eat("{") {
                    self.expect("}");
                } else if !open_rows || self.kind() == Some(SyntaxKind::Identifier) {
                    loop {
                        references.push(AnnotationReference {
                            scope: AnnotationScope::Lexical,
                            name: self.named_type(),
                        });
                        if !self.eat("+") {
                            break;
                        }
                    }
                }
                AnnotationKind::Effect
            } else {
                self.bump();
                if self.eat("{") {
                    self.expect("}");
                } else if self.at("up") || self.at("return") {
                    let returning = self.bump() == "return";
                    let mut scope = if returning {
                        AnnotationScope::Lexical
                    } else {
                        AnnotationScope::Enclosing
                    };
                    let owner = !returning && self.eat("(");
                    if owner {
                        if self.eat("sub") {
                            scope = AnnotationScope::Module;
                        } else {
                            self.name();
                        }
                        self.expect(")");
                    }
                    if returning || owner || self.at("{") {
                        self.expect("{");
                        while !self.at("}") && !self.eof() {
                            let before = self.pos;
                            if returning {
                                if !self.eat("ref") && !self.eat("^mut") {
                                    self.error("E0124", "return dependency requires ref or ^mut");
                                }
                            } else if !self.eat("mut") {
                                self.eat("^mut");
                            }
                            let name_start = self.offset();
                            let path = self.qualified_name();
                            references.push(AnnotationReference {
                                scope,
                                name: TypeExpr {
                                    text: self.text[name_start..self.last_end.max(name_start)]
                                        .to_owned(),
                                    kind: TypeKind::Name {
                                        path,
                                        arguments: vec![],
                                    },
                                    span: self.span(name_start),
                                },
                            });
                            if self.pos == before || !self.list_separator("}") {
                                break;
                            }
                        }
                        self.expect("}");
                    }
                } else if !self.eat("mut")
                    && !self.eat("^mut")
                    && !self.eat("capture")
                    && (!open_rows || self.kind() == Some(SyntaxKind::Identifier))
                {
                    references.push(AnnotationReference {
                        scope: AnnotationScope::Lexical,
                        name: self.named_type(),
                    });
                }
                AnnotationKind::State
            };
            result.push(Annotation {
                kind,
                references,
                text: self.text[start..self.last_end].to_owned(),
                span: self.span(start),
            });
        }
        result
    }
    fn rejected_annotations(&mut self, code: &str, message: &str) {
        for annotation in self.annotations(false) {
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
                let annotations = self.annotations(false);
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
        while !self.at("}") && !self.eof() {
            let before = self.pos;
            let start = self.offset();
            if self.look(1) == "(" {
                let name = self.name();
                self.expect("(");
                let parameters = self.parameters(")", true);
                self.expect(")");
                let annotations = self.annotations(false);
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
        let signature = self.application_signature(&path, start);
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
        let mut depth = 0usize;
        let mut tokens = self.tokens[self.significant()..].iter().filter(|token| {
            !matches!(
                token.kind,
                SyntaxKind::Whitespace | SyntaxKind::Comment | SyntaxKind::Newline
            )
        });
        while let Some(token) = tokens.next() {
            match &self.text[token.start..token.end] {
                "(" => depth += 1,
                ")" => {
                    let Some(inner) = depth.checked_sub(1) else {
                        return false;
                    };
                    depth = inner;
                    if depth == 0 {
                        return tokens
                            .next()
                            .is_some_and(|token| &self.text[token.start..token.end] == "->");
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn block(&mut self) -> Block {
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
        let signature = self.application_signature(&path, start);
        let arguments = self.type_arguments(signature.as_deref());
        TypeExpr {
            kind: TypeKind::Name { path, arguments },
            text: self.text[start..self.last_end.max(start)].to_owned(),
            span: self.span(start),
        }
    }

    fn type_sort(&mut self) -> TypeExpr {
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
            let access = self.storage_mode();
            if self.eat("]") {
                TypeKind::Array {
                    length: None,
                    access,
                    element: Box::new(self.type_expr()),
                }
            } else if self.type_map_ahead() {
                let key = self.type_expr();
                self.expect(":");
                let access = self.storage_mode();
                let value = self.type_expr();
                self.expect("]");
                TypeKind::Map {
                    key: Box::new(key),
                    access,
                    value: Box::new(value),
                }
            } else {
                let length = self.expression(0, true);
                self.expect("]");
                TypeKind::Array {
                    length: Some(Box::new(length)),
                    access: None,
                    element: Box::new(self.type_expr()),
                }
            }
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
                if self.eat("..") {
                    let start = self.offset();
                    row = Some(Box::new(if self.type_pattern_depth > 0 {
                        let name = self.eat("let").then(|| self.name());
                        TypeExpr {
                            text: self.text[start..self.last_end.max(start)].to_owned(),
                            kind: TypeKind::PatternRest(name),
                            span: self.span(start),
                        }
                    } else if self.at("}") || self.at(",") {
                        TypeExpr {
                            text: String::new(),
                            kind: TypeKind::OpenRow,
                            span: self.span(start),
                        }
                    } else {
                        self.type_expr()
                    }));
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
            let parameters = self.parameters(")", true);
            self.expect(")");
            let annotations = self.annotations(true);
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
            while !self.at("->") && !self.eof() {
                let start = self.offset();
                let name = self.name();
                let bound = if self.eat(":") {
                    Some(self.type_sort())
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
            let signature = self.application_signature(&path, start);
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

    fn storage_mode(&mut self) -> Option<String> {
        let word = self.current();
        let mode = matches!(word, "mut" | "^mut" | "ref" | "via")
            || self.look(1) == "]" && word.as_bytes().first().is_some_and(u8::is_ascii_uppercase);
        mode.then(|| self.bump())
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
        let start = self.offset();
        if sort == Some(ArgumentSort::Mode)
            && let Some(mode) = self.member_mode(false)
        {
            return TypeExpr {
                text: mode,
                kind: TypeKind::ModeLiteral,
                span: self.span(start),
            };
        }
        if sort == Some(ArgumentSort::Value)
            || sort == Some(ArgumentSort::Mode) && self.at("modeof")
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
        let mut left = self.prefix(multiline);
        // A prefix range also occupies the range precedence level. A group
        // starts a separate expression, so its operators do not count here.
        let mut previous_infix = (matches!(left.kind, ExprKind::Range { .. })
            && !self
                .grouped_values
                .contains(&(left.span.start, left.span.end)))
        .then_some(RANGE_PRECEDENCE);
        let mut extensions = 0;
        loop {
            if self.eof() || self.closes_angle() {
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
            if self.at("<") {
                let path = match &left.kind {
                    ExprKind::Name(name) => Some(std::slice::from_ref(name)),
                    ExprKind::Path(path) => Some(path.as_slice()),
                    _ => None,
                };
                let signature = path.and_then(|path| self.application_signature(path, start));
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
                let value = self.expression(right_binding, multiline);
                if has_test_binding_mode(&value, &self.grouped_values) {
                    self.error(
                        "E0120",
                        "is tests do not introduce mutable pattern bindings",
                    );
                }
                let pattern = expr_test_pattern(value, &self.grouped_values);
                left = Expr {
                    kind: ExprKind::Is {
                        value: Box::new(left),
                        pattern,
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
                    Some(Box::new(self.expression(right_binding, multiline)))
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
            let right = self.expression(right_binding, multiline);
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
                    Some(Box::new(self.expression(RANGE_PRECEDENCE + 1, multiline)))
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
            "<" => {
                self.bump();
                self.angles.push(self.delimiters.len());
                let ty = self.type_expr();
                if self.at(",") {
                    self.error("E0120", "a type quote contains one type");
                }
                self.expect_type_close();
                self.angles.pop();
                ExprKind::TypeValue(ty)
            }
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
            let parsed = parse_expression_inner(
                &text[region.start + 1..region.expression_end],
                self.file,
                self.base + start + region.start + 1,
                self.lookup,
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
        let parameters = self.parameters("->", false);
        let annotations = self.annotations(false);
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
                kind: PatternKind::Value(Box::new(Expr {
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
            let end = self.expression(RANGE_PRECEDENCE + 1, true);
            let begin = pattern_value(&pattern);
            pattern = Pattern {
                kind: PatternKind::Value(Box::new(Expr {
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
                let var = self.eat("var");
                let mode = match (var, self.current()) {
                    (true, "mut") => {
                        self.bump();
                        BindingMode::VarMut
                    }
                    (true, "^mut") => {
                        self.bump();
                        BindingMode::VarSharedMut
                    }
                    (true, "ref") => {
                        self.bump();
                        BindingMode::VarRef
                    }
                    (true, _) => BindingMode::Var,
                    (false, "^mut") => {
                        self.bump();
                        BindingMode::LetSharedMut
                    }
                    (false, "ref") => {
                        self.bump();
                        BindingMode::Ref
                    }
                    (false, _) => {
                        self.bump();
                        BindingMode::LetMut
                    }
                };
                PatternKind::Mode {
                    mode,
                    pattern: Box::new(self.pattern_atom()),
                }
            }
            "<" => {
                self.bump();
                self.angles.push(self.delimiters.len());
                self.type_pattern_depth += 1;
                let ty = self.type_expr();
                self.type_pattern_depth -= 1;
                self.expect_type_close();
                self.angles.pop();
                PatternKind::Type(ty)
            }
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
fn expr_test_pattern(expr: Expr, groups: &BTreeSet<(u32, u32)>) -> Pattern {
    let span = expr.span;
    if groups.contains(&(span.start, span.end)) {
        return Pattern {
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
        ExprKind::Record { members, ty, .. }
            if members
                .iter()
                .all(|member| matches!(member, RecordMember::Field(_))) =>
        {
            PatternKind::Record {
                ty,
                fields: members
                    .into_iter()
                    .filter_map(|member| match member {
                        RecordMember::Field(field) => Some(field),
                        RecordMember::Spread(_) => None,
                    })
                    .map(|field| PatternField {
                        name: field.name,
                        pattern: expr_test_pattern(field.value, groups),
                        span: field.span,
                    })
                    .collect(),
                rest: false,
                rest_binding: None,
            }
        }
        _ => PatternKind::Value(Box::new(expr)),
    };
    Pattern { kind, span }
}
fn pattern_value(pattern: &Pattern) -> Expr {
    Expr {
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
        ExprKind::TupleMember { .. } => true,
        ExprKind::Tuple(items) | ExprKind::Array(items) => {
            items.iter().any(|item| has_test_binding_mode(item, groups))
        }
        ExprKind::Record { members, .. } => members.iter().any(|member| match member {
            RecordMember::Field(field) => has_test_binding_mode(&field.value, groups),
            RecordMember::Spread(value) => has_test_binding_mode(value, groups),
        }),
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
