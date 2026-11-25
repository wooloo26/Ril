use ril_source::diag::Code;

use crate::{
    lexer::{Kind, Word},
    syntax::{Expr, Literal, LiteralKind, Pattern, PatternField, PatternId, Storage},
};

use super::{Angle, Layout, Parser, Result};

impl Parser<'_> {
    pub(super) fn pattern(&mut self, modified: bool) -> Result<PatternId> {
        self.nested(|p| {
            let first = p.pattern_atom(modified)?;
            let mut alternatives = Vec::new();
            while p.eat("|") {
                p.skip_lines();
                alternatives.push(p.pattern_atom(modified)?);
            }
            if alternatives.is_empty() {
                return Ok(first);
            }
            alternatives.insert(0, first);
            let span = p.ast.pattern(first).span.join(p.last);
            Ok(p.ast.add_pattern(span, Pattern::Or(alternatives)))
        })
    }

    fn pattern_atom(&mut self, modified: bool) -> Result<PatternId> {
        self.layout();
        let start = self.current().span;
        let kind = match self.text() {
            "_" => {
                self.bump();
                Pattern::Wildcard
            }
            "<" => {
                self.open("<", ">", Layout::List)?;
                let ty = self.type_expr(true)?;
                self.skip_lines();
                self.close(">")?;
                Pattern::Type(ty)
            }
            "(" => {
                self.open("(", ")", Layout::List)?;
                let mut children = self.list(")", |p| p.pattern(true))?;
                match children.len() {
                    0 => Pattern::Unit,
                    1 => {
                        let id = children
                            .pop()
                            .unwrap_or_else(|| ril_source::ice!("missing grouped pattern"));
                        self.ast.pattern(id).value.clone()
                    }
                    _ => Pattern::Tuple(children),
                }
            }
            "[" | "str"
                if self.is("[")
                    || self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|tok| tok.tight_left && tok.text(self.file) == "[") =>
            {
                let text = self.eat("str");
                self.open("[", "]", Layout::List)?;
                let elements = self.list("]", |p| {
                    if p.eat("..") {
                        let start = p.last;
                        let name = (p.current().kind == Kind::Word(Word::Value))
                            .then(|| p.name(Some(Word::Value), false))
                            .transpose()?;
                        Ok(p.ast.add_pattern(start.join(p.last), Pattern::Rest(name)))
                    } else {
                        p.pattern(true)
                    }
                })?;
                Pattern::Slice { text, elements }
            }
            ".{" => self.record_pattern(None)?,
            ".." => {
                self.bump();
                Pattern::Subset {
                    ty: self.ty()?,
                    binding: None,
                }
            }
            "var" | "mut" | "^mut" | "ref" | "via" if modified => {
                let storage = self.storage(false)?;
                Pattern::Binding(storage, self.name(Some(Word::Value), false)?)
            }
            _ => match self.current().kind {
                Kind::Word(Word::Pascal) => {
                    let path = self.path(Angle::Type, false)?;
                    if self.tight("(") {
                        self.open("(", ")", Layout::List)?;
                        Pattern::Constructor(path, Some(self.list(")", |p| p.pattern(true))?))
                    } else if self.tight(".{") {
                        self.record_pattern(Some(path))?
                    } else if self.eat("as") {
                        let ty = self.ast.add_ty(path.span, crate::syntax::Type::Named(path));
                        let binding = self.nested(|p| p.pattern_atom(true))?;
                        Pattern::Subset {
                            ty,
                            binding: Some(binding),
                        }
                    } else {
                        Pattern::Constructor(path, None)
                    }
                }
                Kind::Word(Word::Constant) => {
                    return Err(self.error(
                        Code::E0103,
                        start,
                        "uppercase constant cannot bind in a pattern",
                    ));
                }
                Kind::Word(Word::Value) => {
                    Pattern::Binding(Storage::default(), self.name(Some(Word::Value), false)?)
                }
                Kind::StringStart => {
                    let expression = self.string()?;
                    match &self.ast.expr(expression).value {
                        Expr::Literal(text) => Pattern::Literal(text.clone()),
                        _ => {
                            return Err(self.error(
                                Code::E0349,
                                start,
                                "interpolation is not a literal pattern",
                            ));
                        }
                    }
                }
                _ if self.is("-")
                    || self.is("true")
                    || self.is("false")
                    || matches!(
                        self.current().kind,
                        Kind::Int | Kind::Float | Kind::RawString | Kind::Bytes | Kind::RawBytes
                    ) =>
                {
                    let low = self.pattern_literal()?;
                    if matches!(self.text(), ".." | "..=") {
                        let inclusive = self.bump().text(self.file) == "..=";
                        self.skip_lines();
                        let high = self.pattern_literal()?;
                        Pattern::Range {
                            low,
                            high,
                            inclusive,
                        }
                    } else {
                        Pattern::Literal(low)
                    }
                }
                Kind::Word(Word::Keyword | Word::Primitive) => {
                    self.name(Some(Word::Value), false)?;
                    ril_source::ice!("accepted a reserved binding name");
                }
                _ => return Err(self.unexpected("expected pattern")),
            },
        };
        Ok(self.ast.add_pattern(start.join(self.last), kind))
    }

    fn pattern_literal(&mut self) -> Result<Literal> {
        let minus = self.eat("-");
        let mut value = self.literal()?;
        if minus {
            if !matches!(value.kind, LiteralKind::Int | LiteralKind::F64) {
                return Err(self.unexpected("minus in pattern must precede a number"));
            }
            value.text.insert(0, '-');
        }
        Ok(value)
    }

    fn record_pattern(&mut self, name: Option<crate::syntax::Path>) -> Result<Pattern> {
        self.open(".{", "}", Layout::List)?;
        self.skip_lines();
        let mut fields = Vec::new();
        let mut rest = false;
        while !self.is("}") {
            if self.eat("..") {
                rest = true;
                self.skip_lines();
                self.eat(",");
                self.skip_lines();
                break;
            }
            let storage = self.storage(false)?;
            let name = self.name(Some(Word::Value), false)?;
            self.skip_lines();
            let pattern = if self.eat(":") {
                Some(self.pattern(true)?)
            } else {
                None
            };
            fields.push(PatternField {
                name,
                storage,
                pattern,
            });
            self.skip_lines();
            if !self.eat(",") {
                break;
            }
            self.skip_lines();
        }
        self.close("}")?;
        Ok(Pattern::Record { name, fields, rest })
    }
}
