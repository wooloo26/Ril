use ril_source::diag::Code;

use crate::{
    lexer::{Kind, Word},
    syntax::{
        ExprId, Function, Handler, Import, ImportTarget, Mode, Obligations, Parameter, Signature,
        StateClause, StateKind, Stmt, StmtId, StmtKind, Storage, TypeDecl, TypeDefinition,
        TypeKind, Variant, Visibility,
    },
};

use super::{
    Angle, FileKind, Layout, Parser, Result,
    expr::{ARGUMENT, ExprContext},
};

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum Context {
    Module,
    Sub,
    Snippet,
    Block,
    BlockWhere,
    SignatureWhere,
}

const PARAMETERS: &[Mode] = &[Mode::Mut, Mode::Ref, Mode::Shared, Mode::New, Mode::Via];

impl Parser<'_> {
    pub(super) fn sequence(
        &mut self,
        close: Option<&str>,
        context: Context,
    ) -> Result<Vec<StmtId>> {
        let mut items = Vec::new();
        self.separators();
        while self.current().kind != Kind::Eof
            && !close.is_some_and(|close| self.is(close))
            && !(context == Context::Block && self.is("where"))
        {
            let before = self.pos;
            let start = self.current().span;
            let delimiter_depth = self.delimiters.len();
            match self.nested(|p| p.statement(context)) {
                Ok(stmt) => {
                    items.push(stmt);
                    if !self.separators()
                        && self.current().kind != Kind::Eof
                        && !close.is_some_and(|close| self.is(close))
                        && !(context == Context::Block && self.is("where"))
                    {
                        let diag = self.unexpected("expected a newline or semicolon");
                        if !self.recover || matches!(diag.code, Some(Code::E0122 | Code::E0123)) {
                            return Err(diag);
                        }
                        self.diagnostics.push(diag);
                        self.sync_statement(close, context);
                    }
                }
                Err(diag) => {
                    if !self.recover || matches!(diag.code, Some(Code::E0122 | Code::E0123)) {
                        return Err(diag);
                    }
                    self.delimiters.truncate(delimiter_depth);
                    self.diagnostics.push(diag);
                    let err_stmt = self.ast.add_stmt(
                        start.join(self.last),
                        Stmt {
                            attrs: Vec::new(),
                            visibility: Visibility::Private,
                            kind: StmtKind::Error,
                        },
                    );
                    items.push(err_stmt);
                    if self.pos == before {
                        self.bump();
                    }
                    self.sync_statement(close, context);
                }
            }
        }
        Ok(items)
    }

    fn sync_statement(&mut self, close: Option<&str>, context: Context) {
        let mut brace_depth = 0usize;
        while self.current().kind != Kind::Eof {
            if brace_depth == 0 {
                if self.current().kind == Kind::Newline || self.is(";") {
                    self.separators();
                    return;
                }
                if close.is_some_and(|c| self.is(c))
                    || (context == Context::Block && self.is("where"))
                {
                    return;
                }
            }
            match self.text() {
                "{" | ".{" => brace_depth += 1,
                "}" => {
                    if brace_depth == 0 {
                        return;
                    }
                    brace_depth -= 1;
                }
                _ => {}
            }
            self.bump();
        }
    }

    fn statement(&mut self, context: Context) -> Result<StmtId> {
        let start = self.current().span;
        let attrs = if matches!(context, Context::Block | Context::Snippet) {
            self.tight_attributes()?
        } else {
            self.attributes()?
        };
        let visibility = if self.eat("pub") {
            Visibility::Public
        } else if self.eat("pkg") {
            Visibility::Package
        } else {
            Visibility::Private
        };
        let top = matches!(context, Context::Module | Context::Sub);
        if matches!(
            context,
            Context::Block | Context::BlockWhere | Context::SignatureWhere
        ) && visibility != Visibility::Private
        {
            return Err(self.error(
                Code::E0120,
                start,
                "visibility modifier is not allowed in local scope",
            ));
        }
        if context == Context::Module
            && self.kind == FileKind::Executable
            && visibility != Visibility::Private
        {
            return Err(self.error(
                Code::E0905,
                start,
                "executable root declarations are private",
            ));
        }
        let meta = self.is("meta") && matches!(self.next_text(), "let" | "fn");
        if meta {
            self.bump();
        }
        let third_text = self
            .tokens
            .get(self.pos + 2)
            .map_or("", |tok| tok.text(self.file));
        let is_opaque_type = self.is("opaque")
            && (self.next_text() == "type"
                || (self.next_text() == "linear" && third_text == "type"));
        let is_linear_type = self.is("linear")
            && (self.next_text() == "type"
                || (self.next_text() == "opaque" && third_text == "type"));
        let declaration = matches!(self.text(), "fn" | "type" | "eff" | "sub")
            || is_opaque_type
            || is_linear_type;
        if context == Context::Block && declaration {
            return Err(self.error(
                Code::E0703,
                start,
                "local declaration belongs in a trailing where clause",
            ));
        }
        if context == Context::BlockWhere && (!declaration || self.is("sub")) {
            return Err(self.error(
                Code::E0702,
                start,
                "invalid declaration in block where clause",
            ));
        }
        if context == Context::SignatureWhere
            && (!declaration || matches!(self.text(), "sub" | "eff"))
        {
            return Err(self.error(
                Code::E0704,
                start,
                "invalid declaration in signature where clause",
            ));
        }
        let kind = match self.text() {
            "fn" => {
                if self.next_text() == "main"
                    && (meta
                        || context == Context::Sub
                        || context == Context::Module && self.kind != FileKind::Executable)
                {
                    return Err(self.error(
                        Code::E0904,
                        start,
                        "main must be an ordinary function in the executable root",
                    ));
                }
                StmtKind::Function(Box::new(self.function(meta, false, false)?))
            }
            "type" => StmtKind::Type(Box::new(self.type_decl(false, false)?)),
            "opaque" if self.next_text() == "type" => {
                self.bump();
                StmtKind::Type(Box::new(self.type_decl(true, false)?))
            }
            "opaque" if self.next_text() == "linear" && third_text == "type" => {
                self.bump();
                self.bump();
                StmtKind::Type(Box::new(self.type_decl(true, true)?))
            }
            "linear" if self.next_text() == "type" => {
                self.bump();
                StmtKind::Type(Box::new(self.type_decl(false, true)?))
            }
            "linear" if self.next_text() == "opaque" && third_text == "type" => {
                return Err(self.error(
                    Code::E0120,
                    start,
                    "write 'opaque linear type' rather than 'linear opaque type'",
                ));
            }
            "sub" => {
                self.bump();
                let name = self.name(Some(Word::Pascal), false)?;
                self.open("{", "}", Layout::Block)?;
                let items = self.sequence(Some("}"), Context::Sub)?;
                self.close("}")?;
                StmtKind::Sub { name, items }
            }
            "eff" => self.effect()?,
            "use" => StmtKind::Import(self.import()?),
            "let" | "var" => self.binding(meta, top)?,
            "defer" if !top => {
                self.bump();
                let body = if self.is("{") {
                    self.block()?
                } else {
                    self.expr()?
                };
                StmtKind::Defer(body)
            }
            "with" if !top && self.next_text() != "{" => {
                self.bump();
                StmtKind::With(Box::new(self.handler()?))
            }
            _ if !top && visibility == Visibility::Private && attrs.is_empty() => {
                StmtKind::Expr(self.expr()?)
            }
            _ => return Err(self.unexpected("expected a declaration")),
        };
        if !attrs.is_empty()
            && (matches!(
                kind,
                StmtKind::Binding { .. } | StmtKind::Import(_) | StmtKind::Defer(_)
            ) || matches!(&kind, StmtKind::Type(decl) if decl.kind == TypeKind::Alias && !matches!(decl.definition, TypeDefinition::Sum(_))))
        {
            return Err(self.error(
                Code::E0708,
                start,
                "metadata is prohibited on this declaration",
            ));
        }
        Ok(self.ast.add_stmt(
            start.join(self.last),
            Stmt {
                visibility,
                attrs,
                kind,
            },
        ))
    }

    fn tight_attributes(&mut self) -> Result<Vec<ExprId>> {
        let mut attrs = Vec::new();
        while self.is("meta")
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|tok| tok.tight_left && tok.text(self.file) == "(")
        {
            self.bump();
            self.open("(", ")", Layout::List)?;
            attrs.extend(self.list(")", Self::expr)?);
            self.skip_lines();
        }
        Ok(attrs)
    }

    pub(super) fn attributes(&mut self) -> Result<Vec<ExprId>> {
        let mut attrs = Vec::new();
        while self.is("meta") && self.next_text() == "(" {
            self.bump();
            if !self.tight("(") {
                return Err(self.unexpected("metadata requires tightly attached parentheses"));
            }
            self.open("(", ")", Layout::List)?;
            attrs.extend(self.list(")", Self::expr)?);
            self.skip_lines();
        }
        Ok(attrs)
    }

    fn function(&mut self, meta: bool, operation: bool, is_ctl: bool) -> Result<Function> {
        if is_ctl {
            self.require("ctl")?;
        } else {
            self.require("fn")?;
        }
        let name = self.name(Some(Word::Value), false)?;
        let generics = self.generics()?;
        let signature = self.signature(true, operation, is_ctl)?;
        self.continue_lines(|tok| matches!(tok, "where" | "{"));
        let helpers = if !operation && self.eat("where") {
            self.sequence(Some("{"), Context::SignatureWhere)?
        } else {
            Vec::new()
        };
        let body = if self.is("{") && !operation {
            let block = self.block()?;
            if !meta
                && self.kind == FileKind::Interface
                && matches!(
                    &self.ast.expr(block).value,
                    crate::syntax::Expr::Block {
                        statements,
                        helpers
                    } if statements.is_empty() && helpers.is_empty()
                )
            {
                None
            } else {
                Some(block)
            }
        } else {
            None
        };
        Ok(Function {
            name,
            is_meta: meta,
            generics,
            signature,
            helpers,
            body,
        })
    }

    pub(super) fn signature(
        &mut self,
        named: bool,
        parameter_types: bool,
        is_ctl: bool,
    ) -> Result<Signature> {
        self.open("(", ")", Layout::List)?;
        let params = self.list(")", |p| p.parameter(named, parameter_types))?;
        let params_close_span = self.last;
        let obligations = self.obligations()?;
        self.continue_lines(|tok| tok == "->");
        let arrow_span = self.require("->")?.span;
        self.skip_lines();
        let (result_mode, result_mode_start) =
            self.mode_spanned(&[Mode::New, Mode::Ref, Mode::Shared, Mode::Infer]);
        let mut result_sources = Vec::new();
        if matches!(result_mode, Mode::Ref | Mode::Shared) {
            self.open("(", ")", Layout::List)?;
            loop {
                self.skip_lines();
                result_sources.push(self.name(Some(Word::Value), false)?);
                self.skip_lines();
                if !self.eat("|") {
                    break;
                }
            }
            self.close(")")?;
        }
        let result_mode_span = result_mode_start.map(|start| start.join(self.last));
        let result = self.ty()?;
        let guards = if !is_ctl { self.guards()? } else { Vec::new() };
        Ok(Signature {
            is_ctl,
            params,
            params_close_span,
            obligations,
            arrow_span,
            result_mode,
            result_mode_span,
            result_sources,
            result,
            guards,
        })
    }

    pub(super) fn parameter(&mut self, named: bool, types_only: bool) -> Result<Parameter> {
        self.layout();
        let meta = !types_only && self.eat("meta");
        let (mode, mode_span) = self.mode_spanned(PARAMETERS);
        if self.eat("var") {
            return Err(self.error(Code::E0403, self.last, "parameters cannot be reassignable"));
        }
        let pattern = if !named && !types_only && !meta {
            Some(self.pattern(false)?)
        } else {
            None
        };
        let name = if let Some(pattern) = pattern {
            match &self.ast.pattern(pattern).value {
                crate::syntax::Pattern::Binding(_, name) => Some(name.clone()),
                _ => None,
            }
        } else if !types_only || self.next_text() == ":" {
            Some(self.name(Some(Word::Value), true)?)
        } else {
            None
        };
        let ty = if types_only && name.is_none() || self.eat(":") {
            Some(self.ty()?)
        } else if named
            && matches!(
                self.current().kind,
                Kind::Word(Word::Primitive | Word::Pascal)
            )
        {
            self.require(":")?;
            None
        } else {
            None
        };
        let guards = self.guards()?;
        let default = if !types_only && self.eat("=") {
            Some(self.expr()?)
        } else {
            None
        };
        Ok(Parameter {
            name,
            pattern,
            is_meta: meta,
            mode,
            mode_span,
            ty,
            guards,
            default,
        })
    }

    fn guards(&mut self) -> Result<Vec<ExprId>> {
        let mut guards = Vec::new();
        self.continue_lines(|tok| tok == "|>");
        while self.eat("|>") {
            self.skip_lines();
            guards.push(self.expression(
                7,
                ExprContext {
                    guard: true,
                    ..ExprContext::default()
                },
            )?);
            self.continue_lines(|tok| tok == "|>");
        }
        Ok(guards)
    }

    pub(super) fn obligations(&mut self) -> Result<Obligations> {
        let mut obligations = Obligations::default();
        loop {
            self.continue_lines(|tok| matches!(tok, "@" | "&"));
            if self.eat("@") {
                let at_span = self.last;
                let effect = matches!(
                    self.current().kind,
                    Kind::Word(Word::Value | Word::Pascal | Word::Constant | Word::Primitive)
                );
                if effect && self.current().tight_left {
                    let path = self.path(Angle::Type, true)?;
                    obligations.effect_spans.push(at_span.join(path.span));
                    obligations.effects.push(path);
                } else {
                    obligations.open_effects = true;
                }
            } else if self.eat("&") {
                let start = self.last;
                let kind = match self.text() {
                    "mut" if self.current().tight_left => {
                        return Err(self.error(
                            Code::E0120,
                            start.join(self.current().span),
                            "`&mut` state clause has been removed; `mut` parameters imply mutation automatically (keep `&^mut` for retained shared writers)",
                        ));
                    }
                    "^mut" => Some(StateKind::Share),
                    "capture" => Some(StateKind::Capture),
                    "up" => Some(StateKind::Environment),
                    "return" => Some(StateKind::Return),
                    _ => None,
                };
                let Some(kind) = kind.filter(|_| self.current().tight_left) else {
                    obligations.open_state = true;
                    continue;
                };
                self.bump();
                let bindings = if matches!(kind, StateKind::Environment | StateKind::Return)
                    && self.tight("(")
                {
                    self.open("(", ")", Layout::List)?;
                    self.list(")", |p| {
                        let storage = p.storage(false)?;
                        let path = if p.is(")") && storage.mode == Mode::Ref {
                            crate::syntax::Path {
                                span: p.last,
                                segments: Vec::new(),
                            }
                        } else {
                            p.path(Angle::None, false)?
                        };
                        Ok((storage, path))
                    })?
                } else {
                    Vec::new()
                };
                obligations.state.push(StateClause {
                    kind,
                    bindings,
                    span: start.join(self.last),
                });
            } else {
                break;
            }
        }
        Ok(obligations)
    }

    fn type_decl(&mut self, opaque: bool, is_linear: bool) -> Result<TypeDecl> {
        self.require("type")?;
        let name = self.name(Some(Word::Pascal), false)?;
        let generics = self.generics()?;
        let (kind, definition, guards) = if self.eat("=") {
            if opaque {
                return Err(self.error(
                    Code::E0120,
                    self.last,
                    "opaque type does not use '='; write 'opaque type Name(Underlying)'",
                ));
            }
            if is_linear {
                return Err(self.error(
                    Code::E0120,
                    self.last,
                    "linear type does not use '='; write 'linear type Name(Underlying)' or 'linear type Name { ... }'",
                ));
            }
            self.skip_lines();
            let definition = if self.eat("\\") {
                if !generics.is_empty() {
                    return Err(self.error(
                        Code::E0120,
                        self.last,
                        "type function cannot also declare angle generic parameters",
                    ));
                }
                let mut params = Vec::new();
                loop {
                    let param = self.generic_param()?;
                    if param
                        .name
                        .value
                        .starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
                        && param.bound.is_empty()
                        && param.guards.is_empty()
                    {
                        return Err(self.error(
                            Code::E0544,
                            param.name.span,
                            "value type-function parameter requires a type or guard",
                        ));
                    }
                    params.push(param);
                    if matches!(self.text(), "@" | "&") {
                        return Err(self.error(
                            Code::E0335,
                            self.current().span,
                            "type functions are pure",
                        ));
                    }
                    if !self.eat(",") || self.is("->") {
                        break;
                    }
                }
                self.require("->")?;
                self.skip_lines();
                TypeDefinition::Function(params, self.expr()?)
            } else {
                let def = self.data_type_definition()?;
                if self.is("|>") {
                    return Err(self.error(
                        Code::E0120,
                        self.current().span,
                        "type aliases cannot carry static invariants; use a nominal or opaque type 'type Name(T) |> ...'",
                    ));
                }
                def
            };
            (TypeKind::Alias, definition, Vec::new())
        } else if self.is("{") {
            self.open("{", "}", Layout::Block)?;
            let mut variants = Vec::new();
            self.separators();
            while !self.is("}") {
                let attrs = self.attributes()?;
                let variant = if self.eat("..") {
                    if matches!(self.current().kind, Kind::Newline) || self.is("}") || self.is(";")
                    {
                        Variant::Extensible
                    } else {
                        Variant::Spread(self.ty()?)
                    }
                } else {
                    let name = self.name(Some(Word::Pascal), false)?;
                    let payload = if self.tight("(") {
                        let opening = self.open("(", ")", Layout::List)?;
                        let mut fields = self.list(")", Self::ty)?;
                        if fields.is_empty() {
                            fields.push(
                                self.ast
                                    .add_ty(opening.join(self.last), crate::syntax::Type::Unit),
                            );
                        }
                        Some(fields)
                    } else {
                        None
                    };
                    if matches!(self.text(), "@" | "&") {
                        return Err(self.error(
                            Code::E0332,
                            self.current().span,
                            "variant payload cannot have effect or state clauses",
                        ));
                    }
                    Variant::Constructor {
                        name,
                        payload,
                        attrs,
                    }
                };
                variants.push(variant);
                if !self.separators() {
                    break;
                }
            }
            self.close("}")?;
            if self.is("|>") {
                return Err(self.error(
                    Code::E0120,
                    self.current().span,
                    "sum types cannot carry static invariants",
                ));
            }
            let kind = if opaque {
                TypeKind::Opaque
            } else {
                TypeKind::Alias
            };
            (kind, TypeDefinition::Sum(variants), Vec::new())
        } else if self.tight("(") {
            let opening = self.open("(", ")", Layout::List)?;
            let mut elements = self.list(")", |p| {
                if matches!(p.text(), "@" | "&") {
                    return Err(p.error(
                        if p.is("@") { Code::E0330 } else { Code::E0331 },
                        p.current().span,
                        "effect and state clauses cannot be used as data representations",
                    ));
                }
                let storage_span = p.current().span;
                let storage = p.storage(false)?;
                let ty = p.ty()?;
                if matches!(p.text(), "@" | "&") {
                    return Err(p.error(
                        Code::E0333,
                        p.current().span,
                        "element effect/state belongs on a callable type",
                    ));
                }
                if p.is("|") {
                    return Err(p.error(
                        Code::E0318,
                        p.current().span,
                        "untagged union is not a data type",
                    ));
                }
                Ok((storage_span, storage, ty))
            })?;
            let full_span = opening.join(self.last);
            let ty = match elements.len() {
                0 => {
                    return Err(self.error(
                        Code::E0120,
                        full_span,
                        "empty nominal payload; omit parentheses for a unit nominal type",
                    ));
                }
                1 => {
                    let (storage_span, storage, only) = elements
                        .pop()
                        .unwrap_or_else(|| ril_source::ice!("missing nominal payload"));
                    if storage.variable
                        || storage.mode != Mode::Plain
                        || storage.mode_path.is_some()
                    {
                        return Err(self.error(
                            Code::E0356,
                            storage_span,
                            "single nominal payload cannot carry a member storage mode",
                        ));
                    }
                    only
                }
                _ => {
                    let tuple = elements
                        .into_iter()
                        .map(|(_, storage, ty)| (storage, ty))
                        .collect();
                    self.ast
                        .add_ty(full_span, crate::syntax::Type::Tuple(tuple))
                }
            };
            if matches!(self.text(), "@" | "&") {
                return Err(self.error(
                    Code::E0613,
                    self.current().span,
                    "type declaration cannot carry effect or state clauses",
                ));
            }
            let guards = self.guards()?;
            if is_linear && let Some(&first_guard) = guards.first() {
                return Err(self.error(
                    Code::E0120,
                    self.ast.expr(first_guard).span,
                    "linear types cannot carry static invariants",
                ));
            }
            let kind = if opaque {
                TypeKind::Opaque
            } else {
                TypeKind::Nominal
            };
            (kind, TypeDefinition::Data(ty), guards)
        } else if self.is("|>") {
            return Err(self.error(
                Code::E0120,
                self.current().span,
                "unit types cannot carry static invariants",
            ));
        } else if matches!(self.current().kind, Kind::Newline | Kind::Eof)
            || matches!(self.text(), ";" | "}")
        {
            let kind = if opaque {
                TypeKind::Opaque
            } else {
                TypeKind::Nominal
            };
            (kind, TypeDefinition::Opaque, Vec::new())
        } else {
            return Err(self.error(
                Code::E0120,
                self.current().span,
                "nominal and opaque representations require tight parentheses, e.g. 'type Name(Underlying)' or 'type Name(.{ ... })'",
            ));
        };
        Ok(TypeDecl {
            name,
            kind,
            is_linear,
            generics,
            definition,
            guards,
        })
    }

    fn data_type_definition(&mut self) -> Result<TypeDefinition> {
        if matches!(self.text(), "@" | "&") {
            return Err(self.error(
                if self.is("@") {
                    Code::E0330
                } else {
                    Code::E0331
                },
                self.current().span,
                "effect and state clauses cannot be used as data aliases",
            ));
        }
        let ty = self.ty()?;
        if matches!(self.text(), "@" | "&") {
            return Err(self.error(
                Code::E0613,
                self.current().span,
                "type alias cannot carry effect or state clauses",
            ));
        }
        if self.is("|") {
            return Err(self.error(
                Code::E0318,
                self.current().span,
                "untagged union is not a data type",
            ));
        }
        Ok(TypeDefinition::Data(ty))
    }

    fn effect(&mut self) -> Result<StmtKind> {
        self.require("eff")?;
        let name = self.name(Some(Word::Pascal), false)?;
        let generics = self.generics()?;
        self.open("{", "}", Layout::Block)?;
        let mut operations = Vec::new();
        let mut spreads = Vec::new();
        self.separators();
        while !self.is("}") {
            if self.eat("..") {
                spreads.push(self.ty()?);
            } else {
                let start = self.current().span;
                let attrs = self.attributes()?;
                let is_ctl = self.is("ctl");
                let function = self.function(false, true, is_ctl)?;
                operations.push(self.ast.add_stmt(
                    start.join(self.last),
                    Stmt {
                        visibility: Visibility::Public,
                        attrs,
                        kind: StmtKind::Function(Box::new(function)),
                    },
                ));
            }
            if !self.separators() {
                break;
            }
        }
        self.close("}")?;
        Ok(StmtKind::Effect {
            name,
            generics,
            operations,
            spreads,
        })
    }

    fn binding(&mut self, is_meta: bool, top: bool) -> Result<StmtKind> {
        let variable = self.eat("var");
        let keyword_span = if variable {
            Some(self.last)
        } else {
            Some(self.require("let")?.span)
        };
        let (mode, mode_span) = self.mode_spanned(&[Mode::Mut, Mode::Ref, Mode::Shared, Mode::Via]);
        if variable && mode == Mode::Via {
            return Err(self.error(Code::E0403, self.last, "var binding cannot use via mode"));
        }
        if top && (variable || mode != Mode::Plain) {
            return Err(self.error(
                Code::E0906,
                self.last,
                "top-level bindings cannot retain mutable or live state",
            ));
        }
        let pattern = if variable || is_meta {
            let name = self.name(
                Some(if is_meta { Word::Constant } else { Word::Value }),
                true,
            )?;
            let kind = if name.value == "_" {
                crate::syntax::Pattern::Wildcard
            } else {
                crate::syntax::Pattern::Binding(Storage::default(), name.clone())
            };
            self.ast.add_pattern(name.span, kind)
        } else {
            if matches!(self.current().kind, Kind::Word(Word::Constant)) {
                return Err(self.error(
                    Code::E0101,
                    self.current().span,
                    "plain binding requires a value name",
                ));
            }
            self.pattern(false)?
        };
        let ty = if self.eat(":") {
            self.skip_lines();
            Some(self.ty()?)
        } else {
            None
        };
        if matches!(self.text(), "@" | "&") {
            return Err(self.error(
                Code::E0613,
                self.current().span,
                "value binding cannot carry effect or state clauses",
            ));
        }
        self.require("=")?;
        self.skip_lines();
        let value = Some(self.expr()?);
        self.continue_lines(|tok| tok == "else");
        let fallback = if self.eat("else") {
            if variable || is_meta {
                return Err(self.error(
                    Code::E0120,
                    self.last,
                    "else fallback is only permitted on let bindings",
                ));
            }
            self.skip_lines();
            Some(self.block()?)
        } else {
            None
        };
        Ok(StmtKind::Binding {
            storage: Storage {
                variable,
                mode,
                mode_path: None,
                bind_mode: false,
                keyword_span,
                mode_span,
            },
            pattern,
            ty,
            value,
            fallback,
            is_meta,
        })
    }

    pub(super) fn handler(&mut self) -> Result<Handler> {
        let is_ctl = self.eat("ctl");
        let operation = self.path(Angle::Type, false)?;
        self.require("=")?;
        self.skip_lines();
        let (mode, mode_span) = self.mode_spanned(ARGUMENT);
        Ok(Handler {
            is_ctl,
            operation,
            mode,
            mode_span,
            value: self.expr()?,
        })
    }

    pub(super) fn is_handler_arm(&self) -> bool {
        if self.is("ctl") {
            return true;
        }
        let mut idx = self.pos;
        let tok_text = |i: usize| self.tokens.get(i).map(|t| t.text(self.file));
        let tok_kind = |i: usize| self.tokens.get(i).map(|t| t.kind);
        let mut seen_sep = false;
        loop {
            match tok_kind(idx) {
                Some(Kind::Word(Word::Pascal)) => {
                    idx += 1;
                    if tok_text(idx) == Some("<") {
                        let mut depth = 0usize;
                        while let Some(text) = tok_text(idx) {
                            match text {
                                "<" | "!<" => depth += 1,
                                ">" => {
                                    depth -= 1;
                                    idx += 1;
                                    if depth == 0 {
                                        break;
                                    }
                                    continue;
                                }
                                ">>" => {
                                    if depth < 2 {
                                        return false;
                                    }
                                    depth -= 2;
                                    idx += 1;
                                    if depth == 0 {
                                        break;
                                    }
                                    continue;
                                }
                                _ => {}
                            }
                            idx += 1;
                        }
                        if depth != 0 {
                            return false;
                        }
                    }
                    if tok_text(idx) == Some("::") {
                        seen_sep = true;
                        idx += 1;
                    } else {
                        return false;
                    }
                }
                Some(Kind::Word(Word::Value)) if seen_sep => {
                    idx += 1;
                    return tok_text(idx) == Some("=");
                }
                _ => return false,
            }
        }
    }

    fn import(&mut self) -> Result<Import> {
        let span = self.require("use")?.span;
        let mut file = None;
        let mut modules = Vec::new();
        if self.next_text() == "/" {
            let token = self.current();
            let root = if self.eat("pkg") {
                self.owned(token)
            } else {
                self.name(Some(Word::Value), false)?
            };
            let mut segments = vec![root];
            while self.eat("/") {
                let token = self.current();
                if token.kind == Kind::Word(Word::Primitive) {
                    self.bump();
                    segments.push(self.owned(token));
                } else {
                    segments.push(self.name(Some(Word::Value), false)?);
                }
            }
            file = Some(segments);
        } else if self.next_text() == "::" {
            modules.push(self.name(Some(Word::Pascal), false)?);
        } else {
            return Err(self.error(
                Code::E0208,
                span,
                "import requires a package path or qualified module",
            ));
        }
        let target = loop {
            if !self.eat("::") {
                let alias = if self.eat("as") {
                    Some(self.name(Some(Word::Pascal), false)?)
                } else {
                    None
                };
                break ImportTarget::Module(alias);
            }
            if self.eat("*") {
                break ImportTarget::Glob;
            }
            if self.is("(") {
                self.open("(", ")", Layout::List)?;
                let items = self.list(")", Self::import_item)?;
                break ImportTarget::Items(items);
            }
            if self.next_text() == "::" {
                modules.push(self.name(Some(Word::Pascal), false)?);
            } else {
                break ImportTarget::Items(vec![self.import_item()?]);
            }
        };
        Ok(Import {
            file,
            modules,
            target,
        })
    }

    fn import_item(&mut self) -> Result<(crate::syntax::Name, Option<crate::syntax::Name>)> {
        let name = self.name(None, false)?;
        let alias = if self.eat("as") {
            Some(self.name(None, false)?)
        } else {
            None
        };
        Ok((name, alias))
    }
}
