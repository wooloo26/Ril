use ril_source::diag::Code;

use crate::{
    lexer::{Kind, Word},
    syntax::{
        FieldTail, GenericArg, GenericParam, LiteralKind, Mode, Storage, Type, TypeField, TypeId,
    },
};

use super::{Angle, Layout, Parser, Result, expr::ExprContext};

impl Parser<'_> {
    pub(super) fn ty(&mut self) -> Result<TypeId> {
        self.type_expr(false)
    }

    pub(super) fn type_expr(&mut self, pattern: bool) -> Result<TypeId> {
        self.nested(|p| p.type_inner(pattern))
    }

    fn type_inner(&mut self, pattern: bool) -> Result<TypeId> {
        self.layout();
        let start = self.current().span;
        if !pattern
            && matches!(
                self.current().kind,
                Kind::Int
                    | Kind::Float
                    | Kind::StringStart
                    | Kind::RawString
                    | Kind::Bytes
                    | Kind::RawBytes
            )
        {
            return Err(self.error(Code::E0318, start, "literal is not a data type"));
        }
        let ty = match self.text() {
            "?" | "??" => {
                self.consume_prefix();
                Type::Option(self.type_expr(pattern)?)
            }
            "typeof" if !pattern => {
                self.bump();
                Type::TypeOf(self.unary(self.delimiters.last().is_some_and(|d| d.close == ">"))?)
            }
            "fn" if !pattern => {
                self.bump();
                Type::Callable(Box::new(self.signature(false, true, false)?))
            }
            "fn" if pattern => self.callable_pattern(false)?,
            "ctl" if !pattern => {
                self.bump();
                Type::Callable(Box::new(self.signature(false, true, true)?))
            }
            "ctl" if pattern => self.callable_pattern(true)?,
            "<" if !pattern => {
                self.open("<", ">", Layout::List)?;
                let value = self.expression(
                    1,
                    ExprContext {
                        angle: true,
                        ..ExprContext::default()
                    },
                )?;
                self.skip_lines();
                self.close(">")?;
                Type::Unquote(value)
            }
            "!<" => {
                self.open("!<", ">", Layout::List)?;
                let ok = self.type_expr(pattern)?;
                self.skip_lines();
                self.require(",")?;
                let err = self.type_expr(pattern)?;
                self.skip_lines();
                self.eat(",");
                self.skip_lines();
                self.close(">")?;
                Type::Result(ok, err)
            }
            "(" => {
                self.open("(", ")", Layout::List)?;
                self.skip_lines();
                if pattern && self.eat("..") {
                    self.skip_lines();
                    self.close(")")?;
                    Type::TupleAny
                } else {
                    let mut elements = self.list(")", |p| {
                        let storage_span = p.current().span;
                        let storage = p.storage(false)?;
                        let ty = p.type_expr(pattern)?;
                        if matches!(p.text(), "@" | "&") {
                            return Err(p.error(
                                Code::E0333,
                                p.current().span,
                                "element effect/state belongs on a callable type",
                            ));
                        }
                        Ok((storage_span, storage, ty))
                    })?;
                    match elements.len() {
                        0 => Type::Unit,
                        1 => {
                            let (storage_span, storage, only) = elements
                                .pop()
                                .unwrap_or_else(|| ril_source::ice!("missing grouped type"));
                            if storage.variable
                                || storage.mode != Mode::Plain
                                || storage.mode_path.is_some()
                            {
                                return Err(self.error(
                                    Code::E0356,
                                    storage_span,
                                    "parenthesized single type cannot carry a member storage mode",
                                ));
                            }
                            self.ast.ty(only).value.clone()
                        }
                        _ => Type::Tuple(
                            elements
                                .into_iter()
                                .map(|(_, storage, ty)| (storage, ty))
                                .collect(),
                        ),
                    }
                }
            }
            "[" => {
                self.open("[", "]", Layout::List)?;
                self.skip_lines();
                let mode = self.type_storage(pattern, false, true)?;
                self.skip_lines();
                if self.is("]") {
                    self.close("]")?;
                    Type::Array(mode, self.type_expr(pattern)?)
                } else {
                    let key = self.type_expr(pattern)?;
                    self.skip_lines();
                    self.require(":")?;
                    self.skip_lines();
                    let storage = self.type_storage(pattern, false, false)?;
                    let value = self.type_expr(pattern)?;
                    self.skip_lines();
                    self.close("]")?;
                    Type::Map(key, storage, value)
                }
            }
            ".{" => self.record_type(pattern)?,
            "let" if pattern => {
                self.bump();
                Type::PatternBinding(self.name(None, false)?)
            }
            "_" if pattern => {
                self.bump();
                Type::PatternWildcard
            }
            "-" if pattern => {
                self.bump();
                let mut literal = self.literal()?;
                literal.text.insert(0, '-');
                Type::PatternLiteral(literal)
            }
            _ if pattern
                && matches!(
                    self.current().kind,
                    Kind::Int | Kind::Float | Kind::RawString | Kind::Bytes | Kind::RawBytes
                ) =>
            {
                Type::PatternLiteral(self.literal()?)
            }
            "true" | "false" if pattern => Type::PatternLiteral(self.literal()?),
            _ if pattern && self.current().kind == Kind::StringStart => {
                let expr = self.string()?;
                let text = match &self.ast.expr(expr).value {
                    crate::syntax::Expr::Literal(literal) => literal.text.clone(),
                    _ => return Err(self.unexpected("interpolated string in type pattern")),
                };
                Type::PatternLiteral(crate::syntax::Literal {
                    text,
                    kind: LiteralKind::String,
                })
            }
            _ if pattern => Type::Named(self.type_pattern_path()?),
            _ => Type::Named(self.path(Angle::Type, true)?),
        };
        let mut node = self.ast.add_ty(start.join(self.last), ty);
        while self.tight(".") {
            self.bump();
            let field = self.member(true)?;
            node = self
                .ast
                .add_ty(start.join(self.last), Type::Project { base: node, field });
        }
        Ok(node)
    }

    fn callable_pattern(&mut self, is_ctl: bool) -> Result<Type> {
        self.bump();
        self.open("(", ")", Layout::List)?;
        self.skip_lines();
        let (any_params, params) = if self.eat("..") {
            self.skip_lines();
            self.close(")")?;
            (true, Vec::new())
        } else {
            let params = self.list(")", |p| {
                let (mode, _) =
                    p.mode_spanned(&[Mode::Ref, Mode::Mut, Mode::Shared, Mode::New, Mode::Via]);
                let ty = p.type_expr(true)?;
                Ok((mode, ty))
            })?;
            (false, params)
        };
        let mut any_effects = false;
        let mut effects = Vec::new();
        loop {
            self.continue_lines(|tok| tok == "@");
            if !self.eat("@") {
                break;
            }
            if self.eat("..") {
                any_effects = true;
            } else if self.is("(") && self.current().tight_left {
                self.open("(", ")", Layout::List)?;
                self.close(")")?;
            } else {
                effects.push(self.path(Angle::Type, true)?);
            }
        }
        self.continue_lines(|tok| tok == "->");
        self.require("->")?;
        self.skip_lines();
        let (rm, rm_span) = self.mode_spanned(&[Mode::New, Mode::Ref, Mode::Shared]);
        let result_mode = rm_span.map(|_| rm);
        let result = self.type_expr(true)?;
        Ok(Type::CallablePattern {
            is_ctl,
            any_params,
            params,
            any_effects,
            effects,
            result_mode,
            result,
        })
    }

    fn record_type(&mut self, pattern: bool) -> Result<Type> {
        self.open(".{", "}", Layout::List)?;
        self.skip_lines();
        let mut fields = Vec::new();
        let mut tail = None;
        while !self.is("}") {
            if self.eat("..") {
                self.eat("let");
                tail = Some(if matches!(self.current().kind, Kind::Word(Word::Pascal)) {
                    FieldTail::Named(self.name(Some(Word::Pascal), false)?)
                } else {
                    FieldTail::Open
                });
                self.skip_lines();
                self.eat(",");
                self.skip_lines();
                break;
            }
            let attrs = self.attributes()?;
            let storage = self.type_storage(pattern, true, false)?;
            if self.eat("[") {
                let iterable = self.expression(
                    6,
                    ExprContext {
                        for_iterable: true,
                        ..ExprContext::default()
                    },
                )?;
                self.require("as")?;
                let pattern = self.pattern(false)?;
                self.require("]")?;
                self.require(":")?;
                let field = self.ty()?;
                self.skip_lines();
                self.close("}")?;
                return Ok(Type::Mapped {
                    storage,
                    pattern,
                    iterable,
                    field,
                });
            }
            let name = self.name(Some(Word::Value), false)?;
            self.require(":")?;
            let ty = self.type_expr(pattern)?;
            self.skip_lines();
            if matches!(self.text(), "@" | "&") {
                return Err(self.error(
                    Code::E0333,
                    self.current().span,
                    "field effect/state belongs on a callable type",
                ));
            }
            let default = if !pattern && self.eat("=") {
                Some(self.expr()?)
            } else {
                None
            };
            fields.push(TypeField {
                name,
                storage,
                ty,
                default,
                attrs,
            });
            self.skip_lines();
            if !self.eat(",") {
                break;
            }
            self.skip_lines();
        }
        self.close("}")?;
        Ok(Type::Record { fields, tail })
    }

    fn type_storage(
        &mut self,
        pattern: bool,
        record: bool,
        allow_bracket_mode: bool,
    ) -> Result<Storage> {
        if pattern && self.is("let") {
            let checkpoint = (self.pos, self.split, self.last, self.delimiters.len());
            self.bump();
            let parsed = if self.eat("_") {
                Some(None)
            } else if let Ok(path) = self.path(Angle::None, false) {
                Some(Some(path))
            } else {
                None
            };
            if let Some(mode_path) = parsed {
                let is_mode = if record {
                    true
                } else if allow_bracket_mode {
                    self.is("]")
                } else {
                    !matches!(
                        self.text(),
                        "]" | "," | ")" | ">" | "}" | ";" | ":" | "|" | "->" | "."
                    ) && !matches!(self.current().kind, Kind::Newline | Kind::Eof)
                };
                if is_mode {
                    return Ok(Storage {
                        mode_path,
                        bind_mode: true,
                        ..Storage::default()
                    });
                }
            }
            (self.pos, self.split, self.last) = (checkpoint.0, checkpoint.1, checkpoint.2);
            self.delimiters.truncate(checkpoint.3);
            Ok(Storage::default())
        } else if record {
            let mut storage = self.storage(true)?;
            if storage.mode_path.is_none()
                && self.next_text() == "["
                && matches!(self.current().kind, Kind::Word(Word::Value))
            {
                storage.mode_path = Some(self.path(Angle::None, false)?);
            }
            Ok(storage)
        } else {
            if self.is("var") {
                return Err(self.error(
                    Code::E0356,
                    self.current().span,
                    "array and map elements cannot be var",
                ));
            }
            let (mode, mode_span) =
                self.mode_spanned(&[Mode::Mut, Mode::Ref, Mode::Shared, Mode::Via]);
            let mode_path = if allow_bracket_mode
                && mode == Mode::Plain
                && matches!(
                    self.current().kind,
                    Kind::Word(Word::Pascal | Word::Constant)
                )
                && matches!(self.next_text(), "]" | "::")
            {
                Some(self.path(Angle::None, false)?)
            } else if !allow_bracket_mode
                && mode == Mode::Plain
                && matches!(
                    self.current().kind,
                    Kind::Word(Word::Pascal | Word::Constant)
                )
            {
                let checkpoint = (self.pos, self.split, self.last, self.delimiters.len());
                if let Ok(path) = self.path(Angle::None, false)
                    && !matches!(
                        self.text(),
                        "]" | "," | ")" | ">" | "}" | ";" | ":" | "|" | "->" | "." | "<"
                    )
                    && !matches!(self.current().kind, Kind::Newline | Kind::Eof)
                {
                    Some(path)
                } else {
                    (self.pos, self.split, self.last) = (checkpoint.0, checkpoint.1, checkpoint.2);
                    self.delimiters.truncate(checkpoint.3);
                    None
                }
            } else {
                None
            };
            Ok(Storage {
                variable: false,
                mode,
                mode_path,
                bind_mode: false,
                keyword_span: None,
                mode_span,
            })
        }
    }

    fn type_pattern_path(&mut self) -> Result<crate::syntax::Path> {
        use crate::syntax::{Path, Segment};

        let start = self.current().span;
        let mut segments = Vec::new();
        loop {
            let name = if matches!(self.current().kind, Kind::Word(Word::Primitive)) {
                let token = self.bump();
                self.owned(token)
            } else {
                self.name(Some(Word::Pascal), false)?
            };
            let arguments = if self.is("<") {
                self.open("<", ">", Layout::List)?;
                self.list(">", |p| {
                    if matches!(p.text(), "var" | "mut" | "^mut" | "ref") {
                        return Ok(GenericArg::Mode(p.storage(false)?));
                    }
                    Ok(GenericArg::Type(p.type_expr(true)?))
                })?
            } else {
                Vec::new()
            };
            segments.push(Segment { name, arguments });
            if !self.eat("::") {
                break;
            }
        }
        Ok(Path {
            segments,
            span: start.join(self.last),
        })
    }

    pub(super) fn generic_args(&mut self) -> Result<Vec<GenericArg>> {
        self.open("<", ">", Layout::List)?;
        self.list(">", Self::generic_arg)
    }

    fn generic_arg(&mut self) -> Result<GenericArg> {
        if self.is("@") {
            let start = self.current().span;
            let mut paths = Vec::new();
            while self.eat("@") {
                if self.is("(") && self.current().tight_left {
                    self.open("(", ")", Layout::List)?;
                    self.close(")")?;
                    break;
                }
                let path = self.path(Angle::Type, true)?;
                paths.push(path);
                self.skip_lines();
                if !self.is("@") {
                    break;
                }
            }
            return Ok(GenericArg::Effect(paths, start.join(self.last)));
        }
        if matches!(self.text(), "let" | "var" | "mut" | "^mut" | "ref") {
            return Ok(GenericArg::Mode(self.storage(false)?));
        }
        // A committed argument can be type or expression syntax. A full type ending at
        // the list separator is retained as such; static kind checking resolves names.
        let checkpoint = (self.pos, self.split, self.last, self.delimiters.len());
        if !self.is("<")
            && !matches!(
                self.current().kind,
                Kind::Word(Word::Value | Word::Constant)
            )
            && let Ok(ty) = self.ty()
        {
            self.skip_lines();
            if self.is(",") || self.is("->") || self.at_end(">") {
                return Ok(GenericArg::Type(ty));
            }
        }
        (self.pos, self.split, self.last) = (checkpoint.0, checkpoint.1, checkpoint.2);
        self.delimiters.truncate(checkpoint.3);
        let value = self.expression(
            1,
            ExprContext {
                angle: true,
                ..ExprContext::default()
            },
        )?;
        Ok(GenericArg::Value(value))
    }

    pub(super) fn generics(&mut self) -> Result<Vec<GenericParam>> {
        if !self.is("<") {
            return Ok(Vec::new());
        }
        self.open("<", ">", Layout::List)?;
        self.list(">", Self::generic_param)
    }

    pub(super) fn generic_param(&mut self) -> Result<GenericParam> {
        if self.eat("@") {
            let name = self.name(Some(Word::Pascal), false)?;
            let direct_only = if self.eat(":") {
                self.require("fn")?;
                true
            } else {
                false
            };
            let default = if self.eat("=") {
                Some(self.generic_arg()?)
            } else {
                None
            };
            return Ok(GenericParam {
                name,
                is_effect: true,
                direct_only,
                bound: Vec::new(),
                guards: Vec::new(),
                default,
            });
        }
        let name = self.name(None, false)?;
        let mut bound = Vec::new();
        let mut guards = Vec::new();
        if self.eat(":") {
            if matches!(self.text(), "@" | "&") {
                return Err(self.error(
                    Code::E0334,
                    self.current().span,
                    "effect or state cannot be a generic bound",
                ));
            }
            loop {
                bound.push(self.ty()?);
                self.layout();
                if !self.eat("|") {
                    break;
                }
                self.skip_lines();
            }
        }
        while self.eat("|>") {
            self.skip_lines();
            guards.push(self.path(Angle::Type, false)?);
        }
        let default = if self.eat("=") {
            Some(self.generic_arg()?)
        } else {
            None
        };
        Ok(GenericParam {
            name,
            is_effect: false,
            direct_only: false,
            bound,
            guards,
            default,
        })
    }
}
