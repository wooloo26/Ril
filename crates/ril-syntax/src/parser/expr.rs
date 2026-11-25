use crate::{
    lexer::{Kind, Word},
    syntax::{
        Argument, Condition, Expr, ExprId, Literal, LiteralKind, MatchArm, Member, Mode,
        StringPart, Transfer, ValueField,
    },
};
use ril_source::diag::Code;

use super::{Angle, Layout, Parser, Result, decl::Context};

#[derive(Clone, Copy, Default)]
pub(super) struct ExprContext {
    pub angle: bool,
    pub for_iterable: bool,
    pub slice: bool,
    pub guard: bool,
}

pub(super) const ARGUMENT: &[Mode] = &[Mode::Mut, Mode::Ref, Mode::Shared, Mode::New];

#[derive(Clone, Copy, Eq, PartialEq)]
enum Assoc {
    Left,
    Right,
    Non,
}

const PIPE: u8 = 6;
const RANGE: u8 = 7;
const UNARY: u8 = 14;

fn precedence(op: &str) -> Option<(u8, Assoc)> {
    use Assoc::{Left, Non, Right};
    Some(match op {
        "*" | "/" | "%" => (13, Left),
        "+" | "-" => (12, Left),
        "<<" | ">>" => (11, Left),
        "&" => (10, Left),
        "^" => (9, Left),
        "|" => (8, Left),
        ".." | "..=" => (RANGE, Non),
        "|>" | "as" => (PIPE, Left),
        "==" | "!=" | "<" | "<=" | ">" | ">=" => (5, Non),
        "&&" => (4, Left),
        "||" => (3, Left),
        "??" => (2, Right),
        "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" => (1, Non),
        _ => return None,
    })
}

impl Parser<'_> {
    pub(super) fn expr(&mut self) -> Result<ExprId> {
        self.expression(1, ExprContext::default())
    }

    pub(super) fn unary(&mut self, angle: bool) -> Result<ExprId> {
        self.expression(
            UNARY,
            ExprContext {
                angle,
                ..ExprContext::default()
            },
        )
    }

    pub(super) fn expression(&mut self, min: u8, context: ExprContext) -> Result<ExprId> {
        self.nested(|p| p.expr_inner(min, context))
    }

    fn expr_inner(&mut self, min: u8, context: ExprContext) -> Result<ExprId> {
        self.layout();
        let mut left = self.prefix(context)?;
        let mut previous_nonassoc = None;
        loop {
            self.layout();
            self.continue_lines(|tok| matches!(tok, "." | "?." | "|>" | "as" | "??"));
            if context.angle && self.text().starts_with('>')
                || context.for_iterable && self.is("as")
                || context.guard && matches!(self.text(), "|" | "|>" | "=")
            {
                break;
            }
            let Some((power, assoc)) = precedence(self.text()) else {
                break;
            };
            if power < min {
                break;
            }
            if previous_nonassoc == Some(power) {
                let code = if power == 1 { Code::E0701 } else { Code::E0120 };
                return Err(self.error(
                    code,
                    self.current().span,
                    "non-associative operators require parentheses",
                ));
            }
            previous_nonassoc = (assoc == Assoc::Non).then_some(power);
            let token = self.bump();
            let op = self.owned(token);
            self.skip_lines();
            let start = self.ast.expr(left).span;
            let node = match op.value.as_str() {
                "as" => Expr::Cast {
                    value: left,
                    target: self.ty()?,
                },
                "|>" => {
                    let mode = self.mode(ARGUMENT);
                    let target = self.atom(context)?;
                    let target = self.postfix(target, false, context)?;
                    let propagate = self.eat("?");
                    Expr::Pipeline {
                        value: left,
                        mode,
                        target,
                        propagate,
                    }
                }
                ".." | "..=" => {
                    let end = if context.slice && self.is("]") {
                        None
                    } else {
                        Some(self.expression(power + 1, context)?)
                    };
                    Expr::Range {
                        start: Some(left),
                        end,
                        inclusive: op.value == "..=",
                    }
                }
                _ => {
                    let right = self.expression(
                        if assoc == Assoc::Right {
                            power
                        } else {
                            power + 1
                        },
                        context,
                    )?;
                    Expr::Binary { op, left, right }
                }
            };
            left = self.ast.add_expr(start.join(self.last), node);
            if power == PIPE {
                left = self.postfix(left, true, context)?;
            }
        }
        Ok(left)
    }

    fn prefix(&mut self, context: ExprContext) -> Result<ExprId> {
        if matches!(self.text(), "-" | "!" | "~" | "ref" | "^mut" | "new") {
            let token = self.bump();
            let op = self.owned(token);
            self.skip_lines();
            let value = if op.value == "new" {
                let name = self.name(Some(Word::Value), false)?;
                self.ast.add_expr(
                    name.span,
                    Expr::Path(crate::syntax::Path {
                        span: name.span,
                        segments: vec![crate::syntax::Segment {
                            name,
                            arguments: Vec::new(),
                        }],
                    }),
                )
            } else if matches!(op.value.as_str(), "ref" | "^mut") {
                let atom = self.atom(context)?;
                self.postfix(atom, true, context)?
            } else {
                self.expression(UNARY, context)?
            };
            return Ok(self
                .ast
                .add_expr(token.span.join(self.last), Expr::Unary { op, value }));
        }
        let atom = self.atom(context)?;
        self.postfix(atom, true, context)
    }

    fn postfix(
        &mut self,
        mut value: ExprId,
        propagate: bool,
        context: ExprContext,
    ) -> Result<ExprId> {
        loop {
            self.layout();
            self.continue_lines(|tok| matches!(tok, "." | "?."));
            let start = self.ast.expr(value).span;
            let expr = if self.tight("(") {
                self.open("(", ")", Layout::List)?;
                let mut args = self.list(")", Self::argument)?;
                if self.is("\\") {
                    args.push(Argument {
                        name: None,
                        mode: Mode::Plain,
                        value: self.closure(context)?,
                    });
                }
                Expr::Call {
                    callee: value,
                    args,
                }
            } else if self.tight("[")
                || self.tight("?")
                    && self.next_text() == "["
                    && self.tokens.get(self.pos + 1).is_some_and(|t| t.tight_left)
            {
                let safe = self.eat("?");
                self.open("[", "]", Layout::List)?;
                self.skip_lines();
                let index_context = ExprContext {
                    slice: true,
                    ..ExprContext::default()
                };
                let index = if matches!(self.text(), ".." | "..=") {
                    let token = self.bump();
                    self.skip_lines();
                    let end = if self.is("]") {
                        None
                    } else {
                        Some(self.expression(RANGE + 1, index_context)?)
                    };
                    self.ast.add_expr(
                        token.span.join(self.last),
                        Expr::Range {
                            start: None,
                            end,
                            inclusive: token.text(self.file) == "..=",
                        },
                    )
                } else {
                    self.expression(1, index_context)?
                };
                self.skip_lines();
                self.close("]")?;
                Expr::Index {
                    base: value,
                    index,
                    safe,
                }
            } else if self.is(".") || self.is("?.") {
                let safe = self.eat("?.");
                if !safe {
                    self.bump();
                }
                self.skip_lines();
                Expr::Member {
                    base: value,
                    member: self.member(false)?,
                    safe,
                }
            } else if self.tight(".{") {
                let Expr::Path(name) = &self.ast.expr(value).value else {
                    break;
                };
                let name = name.clone();
                Expr::Record {
                    name: Some(name),
                    fields: self.value_fields()?,
                }
            } else if propagate && self.is("?") {
                let token = self.bump();
                Expr::Unary {
                    op: self.owned(token),
                    value,
                }
            } else if self.is("\\") {
                Expr::Call {
                    callee: value,
                    args: vec![Argument {
                        name: None,
                        mode: Mode::Plain,
                        value: self.closure(context)?,
                    }],
                }
            } else {
                break;
            };
            value = self.ast.add_expr(start.join(self.last), expr);
        }
        Ok(value)
    }

    fn argument(&mut self) -> Result<Argument> {
        let name = if self.next_text() == ":" {
            let name = self.name(Some(Word::Value), false)?;
            self.require(":")?;
            self.skip_lines();
            Some(name)
        } else {
            None
        };
        let mode = self.mode(ARGUMENT);
        Ok(Argument {
            name,
            mode,
            value: self.expr()?,
        })
    }

    pub(super) fn member(&mut self, type_member: bool) -> Result<Member> {
        if self.is("(") {
            self.open("(", ")", Layout::List)?;
            let expression = self.expr()?;
            self.skip_lines();
            self.close(")")?;
            Ok(Member::Computed(expression))
        } else if matches!(self.current().kind, Kind::TupleIndex) {
            let token = self.bump();
            Ok(Member::Index(self.owned(token)))
        } else {
            Ok(Member::Name(self.name(
                if type_member { None } else { Some(Word::Value) },
                false,
            )?))
        }
    }

    pub(super) fn atom(&mut self, context: ExprContext) -> Result<ExprId> {
        let start = self.current().span;
        let expression = match self.text() {
            "{" => return self.block(),
            "\\" => return self.closure(context),
            "if" => {
                self.bump();
                let condition = self.condition()?;
                self.skip_lines();
                let yes = self.block()?;
                self.continue_lines(|tok| tok == "else");
                let no = if self.eat("else") {
                    self.skip_lines();
                    Some(if self.is("if") {
                        self.nested(|p| p.atom(context))?
                    } else {
                        self.block()?
                    })
                } else {
                    None
                };
                Expr::If { condition, yes, no }
            }
            "while" => {
                self.bump();
                let condition = self.condition()?;
                self.skip_lines();
                Expr::While {
                    condition,
                    body: self.block()?,
                }
            }
            "for" => {
                self.bump();
                let mode = self.mode(&[Mode::Mut, Mode::Ref, Mode::Shared, Mode::New, Mode::Via]);
                let iterable = self.expression(
                    PIPE,
                    ExprContext {
                        for_iterable: true,
                        ..context
                    },
                )?;
                self.require("as")?;
                let pattern = self.pattern(true)?;
                self.skip_lines();
                Expr::For {
                    mode,
                    iterable,
                    pattern,
                    body: self.block()?,
                }
            }
            "match" => {
                self.bump();
                let mode = self.mode(&[Mode::Ref, Mode::Mut, Mode::Shared, Mode::Via]);
                let value = self.expr()?;
                self.skip_lines();
                self.open("{", "}", Layout::Block)?;
                self.separators();
                let mut arms = Vec::new();
                while !self.is("}") {
                    let pattern = self.pattern(true)?;
                    let guard = if self.eat("if") {
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    self.continue_lines(|tok| tok == "->");
                    self.require("->")?;
                    self.skip_lines();
                    arms.push(MatchArm {
                        pattern,
                        guard,
                        body: self.expr()?,
                    });
                    if !self.separators() {
                        break;
                    }
                }
                self.close("}")?;
                Expr::Match { mode, value, arms }
            }
            "return" | "break" | "continue" => {
                let kind = match self.text() {
                    "return" => Transfer::Return,
                    "break" => Transfer::Break,
                    _ => Transfer::Continue,
                };
                self.bump();
                let value = if kind == Transfer::Return
                    && !matches!(self.current().kind, Kind::Newline | Kind::Eof)
                    && !matches!(self.text(), ";" | "," | ")" | "]" | "}")
                {
                    Some(self.expression(1, context)?)
                } else {
                    None
                };
                Expr::Transfer { kind, value }
            }
            "(" => {
                self.open("(", ")", Layout::List)?;
                let mut elements = self.list(")", Self::expr)?;
                match elements.len() {
                    0 => Expr::Unit,
                    1 => {
                        let value = elements
                            .pop()
                            .unwrap_or_else(|| ril_source::ice!("missing grouped expression"));
                        return Ok(self.ast.add_group(start.join(self.last), value));
                    }
                    _ => Expr::Tuple(elements),
                }
            }
            "[" => return self.collection(),
            ".{" => Expr::Record {
                name: None,
                fields: self.value_fields()?,
            },
            "<" => {
                self.open("<", ">", Layout::List)?;
                let ty = self.ty()?;
                self.skip_lines();
                self.close(">")?;
                Expr::Quote(ty)
            }
            "..." => {
                self.bump();
                Expr::Hole
            }
            _ => match self.current().kind {
                Kind::StringStart => return self.string(),
                Kind::Int | Kind::Float | Kind::RawString | Kind::Bytes | Kind::RawBytes => {
                    Expr::Literal(self.literal()?)
                }
                Kind::Word(Word::Keyword) if matches!(self.text(), "true" | "false") => {
                    Expr::Literal(self.literal()?)
                }
                Kind::Word(Word::Wildcard) => {
                    let token = self.bump();
                    let name = self.owned(token);
                    Expr::Path(crate::syntax::Path {
                        span: token.span,
                        segments: vec![crate::syntax::Segment {
                            name,
                            arguments: Vec::new(),
                        }],
                    })
                }
                Kind::Word(Word::Pascal | Word::Constant | Word::Value | Word::Primitive) => {
                    Expr::Path(self.path(Angle::Expression, true)?)
                }
                _ => return Err(self.unexpected("expected expression")),
            },
        };
        Ok(self.ast.add_expr(start.join(self.last), expression))
    }

    fn condition(&mut self) -> Result<Condition> {
        self.skip_lines();
        if self.eat("let") {
            let mode = self.mode(&[Mode::Mut, Mode::Shared, Mode::Ref, Mode::Via]);
            let pattern = self.pattern(false)?;
            self.require("=")?;
            self.skip_lines();
            Ok(Condition::Binding {
                mode,
                pattern,
                value: self.expr()?,
            })
        } else {
            Ok(Condition::Expr(self.expr()?))
        }
    }

    pub(super) fn block(&mut self) -> Result<ExprId> {
        let start = self.open("{", "}", Layout::Block)?;
        let statements = self.sequence(Some("}"), Context::Block)?;
        let helpers = if self.eat("where") {
            self.skip_lines();
            self.sequence(Some("}"), Context::BlockWhere)?
        } else {
            Vec::new()
        };
        self.close("}")?;
        Ok(self.ast.add_expr(
            start.join(self.last),
            Expr::Block {
                statements,
                helpers,
            },
        ))
    }

    fn value_fields(&mut self) -> Result<Vec<ValueField>> {
        self.open(".{", "}", Layout::List)?;
        self.list("}", |p| {
            let storage = p.storage(false)?;
            let name = p.name(Some(Word::Value), false)?;
            let value = if p.eat(":") { Some(p.expr()?) } else { None };
            Ok(ValueField {
                name,
                storage,
                value,
            })
        })
    }

    fn collection(&mut self) -> Result<ExprId> {
        let start = self.open("[", "]", Layout::List)?;
        self.skip_lines();
        let expression = if self.eat(":") {
            self.skip_lines();
            self.close("]")?;
            Expr::Map(Vec::new())
        } else if self.is("]") {
            self.close("]")?;
            Expr::Array(Vec::new())
        } else {
            let first = self.expr()?;
            if self.eat(":") {
                let value = self.expr()?;
                let mut entries = vec![(first, value)];
                if self.eat(",") {
                    entries.extend(self.list("]", |p| {
                        let key = p.expr()?;
                        p.require(":")?;
                        Ok((key, p.expr()?))
                    })?);
                } else {
                    self.close("]")?;
                }
                Expr::Map(entries)
            } else {
                let mut elements = vec![first];
                if self.eat(",") {
                    elements.extend(self.list("]", Self::expr)?);
                } else {
                    self.close("]")?;
                }
                Expr::Array(elements)
            }
        };
        Ok(self.ast.add_expr(start.join(self.last), expression))
    }

    fn closure(&mut self, context: ExprContext) -> Result<ExprId> {
        self.nested(|p| {
            let start = p.require("\\")?.span;
            let expression = if matches!(p.text(), "." | "?.") {
                let mut path = Vec::new();
                while p.is(".") || p.is("?.") {
                    let safe = p.eat("?.");
                    if !safe {
                        p.bump();
                    }
                    path.push((safe, p.member(false)?));
                }
                Expr::Accessor(path)
            } else {
                let mut params = Vec::new();
                if !matches!(p.text(), "->" | "@" | "&") {
                    loop {
                        params.push(p.parameter(false, false)?);
                        if !p.eat(",") || matches!(p.text(), "->" | "@" | "&") {
                            break;
                        }
                    }
                }
                let obligations = p.obligations()?;
                p.require("->")?;
                p.skip_lines();
                let body = if p.is("{") {
                    p.block()?
                } else {
                    p.expression(1, context)?
                };
                Expr::Closure {
                    params,
                    obligations,
                    body,
                }
            };
            Ok(p.ast.add_expr(start.join(p.last), expression))
        })
    }

    pub(super) fn literal(&mut self) -> Result<Literal> {
        let kind = match self.current().kind {
            Kind::Int => LiteralKind::Int,
            Kind::Float => LiteralKind::F64,
            Kind::RawString => LiteralKind::RawString,
            Kind::Bytes => LiteralKind::Bytes,
            Kind::RawBytes => LiteralKind::RawBytes,
            Kind::Word(Word::Keyword) if matches!(self.text(), "true" | "false") => {
                LiteralKind::Bool
            }
            _ => return Err(self.unexpected("expected literal")),
        };
        let token = self.bump();
        Ok(Literal {
            kind,
            text: token.text(self.file).into(),
        })
    }

    pub(super) fn string(&mut self) -> Result<ExprId> {
        let start = self.bump().span;
        let mut parts = Vec::new();
        let mut interpolated = false;
        loop {
            match self.current().kind {
                Kind::StringChunk => {
                    parts.push(StringPart::Text(self.bump().text(self.file).into()));
                }
                Kind::InterpolationStart => {
                    self.bump();
                    let expression = self.expr()?;
                    if self.current().kind != Kind::InterpolationEnd {
                        return Err(self.error(
                            Code::E0112,
                            self.current().span,
                            "expected the end of interpolation",
                        ));
                    }
                    self.bump();
                    parts.push(StringPart::Interpolation(expression));
                    interpolated = true;
                }
                Kind::StringEnd => {
                    self.bump();
                    let node = if interpolated {
                        Expr::Interpolated(parts)
                    } else {
                        let text = self
                            .file
                            .text()
                            .get(start.end..self.last.start)
                            .unwrap_or_default()
                            .into();
                        Expr::Literal(Literal {
                            kind: LiteralKind::String,
                            text,
                        })
                    };
                    return Ok(self.ast.add_expr(start.join(self.last), node));
                }
                _ => return Err(self.unexpected("expected string continuation")),
            }
        }
    }
}
