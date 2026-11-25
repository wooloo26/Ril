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
        let attrs = self.attributes()?;
        let visibility = if self.eat("pub") {
            Visibility::Public
        } else if self.eat("pkg") {
            Visibility::Package
        } else {
            Visibility::Private
        };
        let top = matches!(context, Context::Module | Context::Sub);
        let foreign = self.kind == FileKind::Foreign;
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
        if foreign && (!attrs.is_empty() || self.is("meta")) {
            return Err(self.error(
                Code::E0901,
                start,
                "meta forms are prohibited in foreign declarations",
            ));
        }
        let meta = self.is("meta") && matches!(self.next_text(), "let" | "fn");
        if meta {
            self.bump();
        }
        let declaration = matches!(self.text(), "fn" | "type" | "eff" | "sub")
            || matches!(self.text(), "opaque" | "nominal") && self.next_text() == "type";
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
                        || foreign
                        || context == Context::Sub
                        || context == Context::Module && self.kind != FileKind::Executable)
                {
                    return Err(self.error(
                        Code::E0904,
                        start,
                        "main must be an ordinary function in the executable root",
                    ));
                }
                StmtKind::Function(Box::new(self.function(meta, false)?))
            }
            "type" => StmtKind::Type(Box::new(self.type_decl(TypeKind::Alias)?)),
            "opaque" if self.next_text() == "type" => {
                self.bump();
                StmtKind::Type(Box::new(self.type_decl(TypeKind::Opaque)?))
            }
            "nominal" if self.next_text() == "type" => {
                self.bump();
                StmtKind::Type(Box::new(self.type_decl(TypeKind::Nominal)?))
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
            "use" if self.is_import() => StmtKind::Import(self.import()?),
            "let" | "var" | "use" => self.binding(meta, top)?,
            "with" if !top => StmtKind::With(self.handlers()?),
            _ if !top && visibility == Visibility::Private && attrs.is_empty() => {
                StmtKind::Expr(self.expr()?)
            }
            _ => return Err(self.unexpected("expected a declaration")),
        };
        if !attrs.is_empty()
            && (matches!(kind, StmtKind::Binding { .. } | StmtKind::Import(_))
                || matches!(&kind, StmtKind::Type(decl) if decl.kind == TypeKind::Alias && !matches!(decl.definition, TypeDefinition::Sum(_))))
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

    pub(super) fn attributes(&mut self) -> Result<Vec<ExprId>> {
        let mut attrs = Vec::new();
        while self.is("meta") && self.next_text() == "(" {
            let meta = self.bump();
            if !self.tight("(") {
                return Err(self.unexpected("metadata requires tightly attached parentheses"));
            }
            if self.kind == FileKind::Foreign {
                return Err(self.error(Code::E0901, meta.span, "metadata in foreign declaration"));
            }
            self.open("(", ")", Layout::List)?;
            attrs.extend(self.list(")", Self::expr)?);
            self.skip_lines();
        }
        Ok(attrs)
    }

    fn function(&mut self, meta: bool, operation: bool) -> Result<Function> {
        self.require("fn")?;
        let name = self.name(Some(Word::Value), false)?;
        let generics = self.generics()?;
        let signature = self.signature(true, operation)?;
        self.continue_lines(|tok| matches!(tok, "where" | "{"));
        let helpers = if !operation && self.eat("where") {
            if self.kind == FileKind::Foreign {
                return Err(self.error(
                    Code::E0901,
                    self.last,
                    "signature helpers in foreign declaration",
                ));
            }
            self.sequence(Some("{"), Context::SignatureWhere)?
        } else {
            Vec::new()
        };
        let body = if self.is("{") && !operation {
            if self.kind == FileKind::Foreign {
                return Err(self.error(
                    Code::E0901,
                    self.current().span,
                    "function body in foreign declaration",
                ));
            }
            Some(self.block()?)
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

    pub(super) fn signature(&mut self, named: bool, parameter_types: bool) -> Result<Signature> {
        self.open("(", ")", Layout::List)?;
        let params = self.list(")", |p| p.parameter(named, parameter_types))?;
        let obligations = self.obligations()?;
        self.continue_lines(|tok| tok == "->");
        self.require("->")?;
        self.skip_lines();
        let result_mode = self.mode(&[Mode::New, Mode::Ref, Mode::Shared, Mode::Infer]);
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
        let result = self.ty()?;
        let guards = if named && !parameter_types {
            self.guards()?
        } else {
            Vec::new()
        };
        Ok(Signature {
            params,
            obligations,
            result_mode,
            result_sources,
            result,
            guards,
        })
    }

    pub(super) fn parameter(&mut self, named: bool, types_only: bool) -> Result<Parameter> {
        self.layout();
        let meta = !types_only && self.eat("meta");
        let mode = self.mode(PARAMETERS);
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
        let guards = if types_only {
            Vec::new()
        } else {
            self.guards()?
        };
        let default = if !types_only && self.eat("=") {
            if self.kind == FileKind::Foreign {
                return Err(self.error(
                    Code::E0901,
                    self.last,
                    "parameter default in foreign declaration",
                ));
            }
            Some(self.expr()?)
        } else {
            None
        };
        Ok(Parameter {
            name,
            pattern,
            is_meta: meta,
            mode,
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
                let effect = matches!(
                    self.current().kind,
                    Kind::Word(Word::Value | Word::Pascal | Word::Constant | Word::Primitive)
                );
                if effect && self.current().tight_left {
                    obligations.effects.push(self.path(Angle::Type, true)?);
                } else {
                    obligations.open_effects = true;
                }
            } else if self.eat("&") {
                let start = self.last;
                let kind = match self.text() {
                    "mut" => Some(StateKind::Write),
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

    fn type_decl(&mut self, kind: TypeKind) -> Result<TypeDecl> {
        self.require("type")?;
        let name = self.name(Some(Word::Pascal), false)?;
        let generics = self.generics()?;
        let cleanup = if self.is("use") {
            self.bump();
            if !self.tight("(") {
                return Err(self.unexpected("cleanup name requires tightly attached parentheses"));
            }
            self.open("(", ")", Layout::List)?;
            let name = self.name(Some(Word::Value), false)?;
            self.close(")")?;
            Some(name)
        } else {
            None
        };
        let foreign = self.kind == FileKind::Foreign;
        let definition = if self.eat("=") {
            if foreign && kind != TypeKind::Alias {
                return Err(self.error(
                    Code::E0901,
                    self.last,
                    "foreign type representation is sealed",
                ));
            }
            self.skip_lines();
            if self.eat("\\") {
                if foreign {
                    return Err(self.error(
                        Code::E0901,
                        self.last,
                        "type function in foreign declaration",
                    ));
                }
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
                TypeDefinition::Data(ty)
            }
        } else if self.is("{") {
            if foreign && kind == TypeKind::Opaque {
                return Err(self.error(
                    Code::E0901,
                    self.current().span,
                    "opaque sum in foreign declaration",
                ));
            }
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
            TypeDefinition::Sum(variants)
        } else if kind != TypeKind::Alias {
            TypeDefinition::Opaque
        } else {
            self.require("=")?;
            ril_source::ice!("accepted absent type definition");
        };
        Ok(TypeDecl {
            name,
            kind,
            generics,
            cleanup,
            definition,
        })
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
                let function = self.function(false, true)?;
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
        let resource = self.eat("use");
        if resource && self.is("var") {
            return Err(self.error(
                Code::E0532,
                self.current().span,
                "scoped resource binding is pinned",
            ));
        }
        let variable = self.eat("var");
        if !resource && !variable {
            self.require("let")?;
        }
        let mode = self.mode(&[Mode::Mut, Mode::Ref, Mode::Shared, Mode::Via]);
        if variable && mode == Mode::Via {
            return Err(self.error(Code::E0403, self.last, "var binding cannot use via mode"));
        }
        if resource && !matches!(mode, Mode::Plain | Mode::Mut) {
            return Err(self.error(
                Code::E0532,
                self.last,
                "scoped resource binding only permits plain or mut mode",
            ));
        }
        if top && (resource || variable || mode != Mode::Plain) {
            return Err(self.error(
                Code::E0906,
                self.last,
                "top-level bindings cannot retain mutable or live state",
            ));
        }
        let pattern = if variable || resource || is_meta || top && self.kind == FileKind::Foreign {
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
        let value = if self.kind == FileKind::Foreign {
            if self.is("=") {
                return Err(self.error(
                    Code::E0901,
                    self.current().span,
                    "initializer in foreign declaration",
                ));
            }
            if ty.is_none() {
                self.require(":")?;
            }
            None
        } else {
            self.require("=")?;
            self.skip_lines();
            Some(self.expr()?)
        };
        self.continue_lines(|tok| tok == "else");
        let fallback = if self.eat("else") {
            if variable || resource || is_meta {
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
            },
            pattern,
            ty,
            value,
            fallback,
            is_meta,
            resource,
        })
    }

    fn handlers(&mut self) -> Result<Vec<Handler>> {
        self.require("with")?;
        let grouped = self.is("{");
        if grouped {
            self.open("{", "}", Layout::Block)?;
            self.separators();
        }
        let mut handlers = Vec::new();
        while !grouped || !self.is("}") {
            let operation = self.path(Angle::Type, false)?;
            self.require("=")?;
            self.skip_lines();
            let mode = self.mode(ARGUMENT);
            handlers.push(Handler {
                operation,
                mode,
                value: self.expr()?,
            });
            if !grouped || !self.separators() {
                break;
            }
        }
        if grouped {
            self.close("}")?;
        }
        Ok(handlers)
    }

    fn is_import(&self) -> bool {
        matches!(
            self.tokens
                .get(self.pos + 2)
                .map(|token| token.text(self.file)),
            Some("/" | "::" | "as" | "\n" | ";") | None
        ) && !matches!(self.next_text(), "mut" | "ref" | "^mut" | "via")
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
