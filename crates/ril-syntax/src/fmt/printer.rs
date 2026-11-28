//! AST + `TokenIndex` + `CommentStore` → Wadler-Lindig `DocId` lowering for `ril fmt`.

use ril_source::span::{SourceFile, Span};

use crate::{
    fmt::{
        comments::CommentStore,
        doc::{DocArena, DocId},
        tokens::TokenIndex,
    },
    syntax::{
        Argument, Ast, Condition, Expr, ExprId, FieldTail, Function, GenericArg, GenericParam,
        Handler, Import, ImportTarget, Literal, LiteralKind, MatchArm, Member, Mode, Obligations,
        Parameter, Path, Pattern, PatternField, PatternId, Segment, Signature, StateClause,
        StateKind, StmtId, StmtKind, Storage, StringPart, Transfer, Type, TypeDecl, TypeDefinition,
        TypeField, TypeId, TypeKind, ValueField, Variant, Visibility,
    },
};

pub(super) struct Printer<'src, 'a> {
    pub(super) source: &'src SourceFile,
    pub(super) ast: &'a Ast,
    pub(super) tokens: TokenIndex<'src>,
    pub(super) comments: CommentStore<'src>,
    pub(super) arena: DocArena<'src>,
}

impl<'src, 'a> Printer<'src, 'a> {
    pub(super) fn new(
        source: &'src SourceFile,
        ast: &'a Ast,
        tokens: TokenIndex<'src>,
        comments: CommentStore<'src>,
    ) -> Self {
        Self {
            source,
            ast,
            tokens,
            comments,
            arena: DocArena::new(),
        }
    }

    pub(super) fn print_file(&mut self) -> DocId {
        let items = self.ast.items.clone();
        let body = self.print_stmt_list(&items, 0, self.source.text().len(), false);
        let (dangling, had_dangling) = self.comments.emit_dangling(
            &mut self.arena,
            self.source.text().len(),
            !items.is_empty(),
        );
        let doc = if had_dangling {
            self.arena.concat(&[body, dangling])
        } else {
            body
        };
        self.comments.assert_exhausted();
        doc
    }

    fn line_of(&self, byte_offset: usize) -> usize {
        self.source.location(byte_offset).map_or(1, |loc| loc.line)
    }

    fn end_line_of(&self, span: Span) -> usize {
        let pos = span.end.saturating_sub(1).max(span.start);
        self.line_of(pos)
    }

    fn print_stmt_list(
        &mut self,
        stmts: &[StmtId],
        _container_start: usize,
        container_end: usize,
        inside_container: bool,
    ) -> DocId {
        let mut parts = Vec::new();
        let mut prev_end: Option<usize> = None;

        for (idx, &stmt_id) in stmts.iter().enumerate() {
            let span = self.ast.stmt(stmt_id).span;
            let next_limit = stmts
                .get(idx + 1)
                .map_or(container_end, |&next| self.ast.stmt(next).span.start);

            let (leading, had_leading) =
                self.comments
                    .emit_leading(&mut self.arena, span.start, prev_end.is_some());

            if let Some(pe) = prev_end {
                if !had_leading {
                    if self.tokens.has_blank_line_between(pe, span.start) {
                        parts.push(self.arena.blank_line());
                    } else {
                        parts.push(self.arena.hard_line());
                    }
                } else {
                    parts.push(self.arena.hard_line());
                }
            } else if inside_container && had_leading {
                // Inside a block, leading comments start directly at indented level.
            }

            if had_leading {
                parts.push(leading);
            }

            let stmt_doc = self.print_stmt(stmt_id);
            let end_line = self.end_line_of(span);

            // If a single-line statement ends with a `-- ril:` directive and may wrap across
            // multiple lines, hoist the directive immediately above the statement so it never
            // detaches across wrapped lines.
            let wraps =
                self.tokens.has_newline_in_span(span) || span.end.saturating_sub(span.start) > 90;
            if wraps
                && let Some(dir) = self
                    .comments
                    .take_trailing_directive_on_line(end_line, next_limit)
            {
                let dir_doc = self.arena.text(dir.text);
                let hl = self.arena.hard_line();
                parts.push(dir_doc);
                parts.push(hl);
                parts.push(stmt_doc);
            } else {
                parts.push(stmt_doc);
                if let Some(trailing) =
                    self.comments
                        .emit_trailing_on_line(&mut self.arena, end_line, next_limit)
                {
                    parts.push(trailing);
                }
            }
            prev_end = Some(span.end);
        }

        self.arena.concat(&parts)
    }

    fn print_stmt(&mut self, id: StmtId) -> DocId {
        let spanned = self.ast.stmt(id);
        let stmt_span = spanned.span;
        let stmt = spanned.value.clone();
        let mut parts = Vec::new();

        if !stmt.attrs.is_empty() {
            let attrs_doc = self.print_meta_attrs(stmt_span.start, stmt_span.end, &stmt.attrs);
            parts.push(attrs_doc);
            parts.push(self.arena.hard_line());
        }

        let vis = self.print_visibility(stmt.visibility);
        match stmt.kind {
            StmtKind::Function(fun) => {
                let d = self.print_function(vis, &fun, stmt_span, false);
                parts.push(d);
            }
            StmtKind::Type(decl) => {
                let d = self.print_type_decl(vis, &decl, stmt_span);
                parts.push(d);
            }
            StmtKind::Effect {
                name,
                generics,
                operations,
                spreads,
            } => {
                let d = self.print_effect(vis, &name, &generics, &operations, &spreads, stmt_span);
                parts.push(d);
            }
            StmtKind::Sub { name, items } => {
                let d = self.print_sub(vis, &name, &items, stmt_span);
                parts.push(d);
            }
            StmtKind::Import(import) => {
                let d = self.print_import(vis, &import, stmt_span);
                parts.push(d);
            }
            StmtKind::Binding {
                storage,
                pattern,
                ty,
                value,
                fallback,
                is_meta,
            } => {
                let d = self.print_binding(
                    vis, &storage, pattern, ty, value, fallback, is_meta, stmt_span,
                );
                parts.push(d);
            }
            StmtKind::Defer(expr_id) => {
                let kw = self.arena.text("defer ");
                let e = self.print_expr(expr_id);
                parts.push(self.arena.concat(&[kw, e]));
            }
            StmtKind::With(handler) => {
                let kw = self.arena.text("with ");
                let h = self.print_handler(&handler);
                parts.push(self.arena.concat(&[kw, h]));
            }
            StmtKind::Expr(expr_id) => {
                let e = self.print_expr(expr_id);
                parts.push(e);
            }
            StmtKind::Error => {
                let raw = self.tokens.raw_slice(stmt_span);
                parts.push(self.arena.raw_text(raw));
            }
        }

        self.arena.concat(&parts)
    }

    fn print_visibility(&mut self, vis: Visibility) -> DocId {
        match vis {
            Visibility::Private => self.arena.empty(),
            Visibility::Package => self.arena.text("pkg "),
            Visibility::Public => self.arena.text("pub "),
        }
    }

    fn print_meta_attrs(&mut self, stmt_start: usize, limit_end: usize, attrs: &[ExprId]) -> DocId {
        let ast = self.ast;
        let groups = self
            .tokens
            .meta_attr_groups(stmt_start, limit_end, attrs, |id| ast.expr(id).span);
        let mut parts = Vec::new();
        for (idx, (g_start, g_end, slice)) in groups.into_iter().enumerate() {
            if idx > 0 {
                parts.push(self.arena.hard_line());
            }
            let (leading, had_leading) =
                self.comments.emit_leading(&mut self.arena, g_start, false);
            if had_leading {
                parts.push(leading);
            }
            let items: Vec<(Span, DocId)> = slice
                .iter()
                .map(|&e| (self.ast.expr(e).span, self.print_expr(e)))
                .collect();
            let list = self.print_delimited_list("meta(", ")", items, g_start, g_end, false);
            parts.push(list);
        }
        self.arena.concat(&parts)
    }

    fn print_delimited_list(
        &mut self,
        open: &'static str,
        close: &'static str,
        items: Vec<(Span, DocId)>,
        open_search_start: usize,
        close_limit: usize,
        pad_flat: bool,
    ) -> DocId {
        let open_tok = match open {
            "meta(" => "(",
            "str[" => "[",
            "&up(" | "&return(" => "(",
            other => other,
        };
        let has_dangling_inside = self.comments.has_comment_in(open_search_start, close_limit);
        if items.is_empty() {
            if has_dangling_inside {
                let o = self.arena.text(open);
                let hl1 = self.arena.hard_line();
                let (dangling, _) =
                    self.comments
                        .emit_dangling(&mut self.arena, close_limit, false);
                let inner = self.arena.concat(&[hl1, dangling]);
                let indented = self.arena.indent(inner);
                let hl2 = self.arena.hard_line();
                let c = self.arena.text(close);
                return self.arena.concat(&[o, indented, hl2, c]);
            }
            let o = self.arena.text(open);
            let c = self.arena.text(close);
            return self.arena.concat(&[o, c]);
        }

        let force_break =
            self.tokens
                .has_trailing_comma_in(open_search_start, close_limit, open_tok)
                || has_dangling_inside;

        let mut inner = Vec::new();
        let first_pad = if pad_flat {
            self.arena.line()
        } else {
            self.arena.soft_line()
        };
        inner.push(first_pad);

        let len = items.len();
        for (idx, (item_span, item_doc)) in items.into_iter().enumerate() {
            let (leading, had_leading) =
                self.comments
                    .emit_leading(&mut self.arena, item_span.start, idx > 0);
            if had_leading {
                inner.push(leading);
            }
            inner.push(item_doc);
            let is_last = idx + 1 == len;
            let comma = self.arena.text(",");
            if !is_last {
                inner.push(comma);
                inner.push(self.arena.line());
            } else {
                let empty = self.arena.empty();
                let trailing_comma = self.arena.if_break(comma, empty);
                inner.push(trailing_comma);
            }
        }

        let (dangling, had_dangling) =
            self.comments
                .emit_dangling(&mut self.arena, close_limit, true);
        if had_dangling {
            inner.push(dangling);
        }

        let inner_doc = self.arena.concat(&inner);
        let indented = self.arena.indent(inner_doc);
        let close_pad = if pad_flat {
            self.arena.line()
        } else {
            self.arena.soft_line()
        };
        let o = self.arena.text(open);
        let c = self.arena.text(close);
        let body = self.arena.concat(&[o, indented, close_pad, c]);
        self.arena.group_forced(body, force_break || had_dangling)
    }

    fn print_function(
        &mut self,
        vis: DocId,
        fun: &Function,
        stmt_span: Span,
        is_eff_op: bool,
    ) -> DocId {
        let mut header_prefix = vec![vis];
        if fun.is_meta {
            header_prefix.push(self.arena.text("meta "));
        }
        if fun.signature.is_ctl {
            header_prefix.push(self.arena.text("ctl "));
        } else {
            header_prefix.push(self.arena.text("fn "));
        }
        header_prefix.push(self.arena.owned(fun.name.value.clone()));

        if !fun.generics.is_empty() {
            let gen_doc = self.print_generic_params(
                &fun.generics,
                fun.name.span.end,
                fun.signature.params_close_span.start,
            );
            header_prefix.push(gen_doc);
        }

        let params_start = fun
            .generics
            .last()
            .map_or(fun.name.span.end, |g| g.name.span.end);
        let sig_doc = self.print_signature_parts(
            &fun.signature,
            params_start,
            is_eff_op,
            fun.body.is_some() && fun.helpers.is_empty(),
        );
        header_prefix.push(sig_doc);

        let mut parts = vec![self.arena.group_concat(&header_prefix)];

        if !fun.helpers.is_empty() {
            let where_start = fun
                .helpers
                .first()
                .map_or(stmt_span.end, |&h| self.ast.stmt(h).span.start);
            let body_start = fun
                .body
                .map_or(stmt_span.end, |b| self.ast.expr(b).span.start);
            let (leading_where, had_lw) =
                self.comments
                    .emit_leading(&mut self.arena, where_start.min(stmt_span.end), false);
            parts.push(self.arena.hard_line());
            if had_lw {
                parts.push(leading_where);
            }
            parts.push(self.arena.text("where"));
            let hl = self.arena.hard_line();
            let helpers_doc = self.print_stmt_list(&fun.helpers, where_start, body_start, true);
            let block_helpers = self.arena.concat(&[hl, helpers_doc]);
            parts.push(self.arena.indent(block_helpers));
        }

        if let Some(body_id) = fun.body {
            let body_span = self.ast.expr(body_id).span;
            let (leading_body, had_lb) =
                self.comments
                    .emit_leading(&mut self.arena, body_span.start, false);
            if !fun.helpers.is_empty() || had_lb {
                parts.push(self.arena.hard_line());
                if had_lb {
                    parts.push(leading_body);
                }
            } else {
                // If signature tail broke into multiple lines, `{` drops to its own flush line;
                // otherwise `{` sits after a single space on the same line.
                let sp = self.arena.text(" ");
                parts.push(sp);
            }
            let body_doc = self.print_block(body_id, true);
            parts.push(body_doc);
        }

        self.arena.concat(&parts)
    }

    fn print_signature_parts(
        &mut self,
        sig: &Signature,
        params_search_start: usize,
        _types_only: bool,
        _followed_by_block: bool,
    ) -> DocId {
        let param_items: Vec<(Span, DocId)> = sig
            .params
            .iter()
            .map(|p| {
                let span = self.param_span(p);
                (span, self.print_parameter(p))
            })
            .collect();
        let params_doc = self.print_delimited_list(
            "(",
            ")",
            param_items,
            params_search_start,
            sig.params_close_span.end,
            false,
        );

        let mut tail_parts = Vec::new();
        let ob_doc = self.print_obligations(&sig.obligations, sig.arrow_span.start);
        if ob_doc != self.arena.empty() {
            tail_parts.push(self.arena.line());
            tail_parts.push(ob_doc);
        }

        tail_parts.push(self.arena.line());
        tail_parts.push(self.arena.text("-> "));
        if sig.result_mode != Mode::Plain {
            tail_parts.push(self.print_return_mode(sig.result_mode, &sig.result_sources));
            tail_parts.push(self.arena.text(" "));
        }
        let ret_ty = self.print_type(sig.result);
        tail_parts.push(ret_ty);

        for &guard in &sig.guards {
            let g_span = self.ast.expr(guard).span;
            let (leading, had) = self
                .comments
                .emit_leading(&mut self.arena, g_span.start, false);
            if had {
                tail_parts.push(self.arena.hard_line());
                tail_parts.push(leading);
            } else {
                tail_parts.push(self.arena.line());
            }
            tail_parts.push(self.arena.text("|> "));
            let g_doc = self.print_expr(guard);
            tail_parts.push(g_doc);
        }

        let tail_inner = self.arena.concat(&tail_parts);
        let tail_indented = self.arena.indent(tail_inner);
        let tail_group = self.arena.group(tail_indented);
        self.arena.concat(&[params_doc, tail_group])
    }

    fn print_return_mode(&mut self, mode: Mode, sources: &[crate::syntax::Name]) -> DocId {
        match mode {
            Mode::New => self.arena.text("new"),
            Mode::Infer => self.arena.text("infer"),
            Mode::Ref | Mode::Shared => {
                let kw = if mode == Mode::Ref { "ref(" } else { "^mut(" };
                let mut parts = vec![self.arena.text(kw)];
                for (i, src) in sources.iter().enumerate() {
                    if i > 0 {
                        parts.push(self.arena.text(" | "));
                    }
                    parts.push(self.arena.owned(src.value.clone()));
                }
                parts.push(self.arena.text(")"));
                self.arena.concat(&parts)
            }
            _ => self.arena.empty(),
        }
    }

    fn print_obligations(&mut self, ob: &Obligations, limit_end: usize) -> DocId {
        if ob.open_effects && ob.open_state && ob.effects.is_empty() && ob.state.is_empty() {
            return self.arena.text("@&");
        }
        let mut parts = Vec::new();
        if ob.open_effects {
            parts.push(self.arena.text("@"));
        }
        for eff in &ob.effects {
            if !parts.is_empty() {
                parts.push(self.arena.text(" "));
            }
            parts.push(self.arena.text("@"));
            parts.push(self.print_path(eff));
        }
        if ob.open_state {
            if !parts.is_empty() {
                parts.push(self.arena.text(" "));
            }
            parts.push(self.arena.text("&"));
        }
        for clause in &ob.state {
            if !parts.is_empty() {
                parts.push(self.arena.text(" "));
            }
            parts.push(self.print_state_clause(clause, limit_end));
        }
        self.arena.concat(&parts)
    }

    fn print_state_clause(&mut self, clause: &StateClause, _limit_end: usize) -> DocId {
        match clause.kind {
            StateKind::Write => self.arena.text("&mut"),
            StateKind::Share => self.arena.text("&^mut"),
            StateKind::Capture => self.arena.text("&capture"),
            StateKind::Environment => {
                if clause.bindings.is_empty() {
                    return self.arena.text("&up");
                }
                let items: Vec<(Span, DocId)> = clause
                    .bindings
                    .iter()
                    .map(|(storage, path)| {
                        let d = if path.segments.is_empty() && storage.mode == Mode::Ref {
                            self.arena.text("ref")
                        } else {
                            let s = self.print_storage(storage, true);
                            let p = self.print_path(path);
                            self.arena.concat(&[s, p])
                        };
                        (path.span, d)
                    })
                    .collect();
                self.print_delimited_list(
                    "&up(",
                    ")",
                    items,
                    clause.span.start,
                    clause.span.end,
                    false,
                )
            }
            StateKind::Return => {
                let items: Vec<(Span, DocId)> = clause
                    .bindings
                    .iter()
                    .map(|(storage, path)| {
                        let s = self.print_storage(storage, true);
                        let p = self.print_path(path);
                        (path.span, self.arena.concat(&[s, p]))
                    })
                    .collect();
                self.print_delimited_list(
                    "&return(",
                    ")",
                    items,
                    clause.span.start,
                    clause.span.end,
                    false,
                )
            }
        }
    }

    fn param_span(&self, p: &Parameter) -> Span {
        if let Some(span) = p.mode_span {
            return span;
        }
        if let Some(pat) = p.pattern {
            return self.ast.pattern(pat).span;
        }
        if let Some(name) = &p.name {
            return name.span;
        }
        if let Some(ty) = p.ty {
            return self.ast.ty(ty).span;
        }
        Span::default()
    }

    fn print_parameter(&mut self, p: &Parameter) -> DocId {
        let mut parts = Vec::new();
        if p.is_meta {
            parts.push(self.arena.text("meta "));
        }
        if let Some(m) = p.mode.as_str() {
            parts.push(self.arena.text(m));
            parts.push(self.arena.text(" "));
        }
        if let Some(pat) = p.pattern {
            parts.push(self.print_pattern(pat));
        } else if let Some(name) = &p.name {
            parts.push(self.arena.owned(name.value.clone()));
        }
        if let Some(ty) = p.ty {
            if p.name.is_some() || p.pattern.is_some() {
                parts.push(self.arena.text(": "));
            }
            parts.push(self.print_type(ty));
        }
        for &guard in &p.guards {
            parts.push(self.arena.text(" |> "));
            parts.push(self.print_expr(guard));
        }
        if let Some(def) = p.default {
            parts.push(self.arena.text(" = "));
            parts.push(self.print_expr(def));
        }
        self.arena.concat(&parts)
    }

    fn print_generic_params(
        &mut self,
        params: &[GenericParam],
        search_start: usize,
        limit_end: usize,
    ) -> DocId {
        let items: Vec<(Span, DocId)> = params
            .iter()
            .map(|g| {
                let mut parts = vec![self.arena.owned(g.name.value.clone())];
                if !g.bound.is_empty() {
                    parts.push(self.arena.text(": "));
                    for (i, &b) in g.bound.iter().enumerate() {
                        if i > 0 {
                            parts.push(self.arena.text(" | "));
                        }
                        parts.push(self.print_type(b));
                    }
                }
                for guard in &g.guards {
                    parts.push(self.arena.text(" |> "));
                    parts.push(self.print_path(guard));
                }
                if let Some(def) = &g.default {
                    parts.push(self.arena.text(" = "));
                    parts.push(self.print_generic_arg(def));
                }
                (g.name.span, self.arena.concat(&parts))
            })
            .collect();
        self.print_delimited_list("<", ">", items, search_start, limit_end, false)
    }

    fn print_generic_arg(&mut self, arg: &GenericArg) -> DocId {
        match arg {
            GenericArg::Type(t) => self.print_type(*t),
            GenericArg::Value(e) => self.print_expr(*e),
            GenericArg::Mode(s) => {
                if !s.variable && s.mode == Mode::Plain && s.mode_path.is_none() && !s.bind_mode {
                    self.arena.text("let")
                } else {
                    self.print_storage(s, false)
                }
            }
        }
    }

    fn print_type_decl(&mut self, vis: DocId, decl: &TypeDecl, stmt_span: Span) -> DocId {
        let mut parts = vec![vis];
        if decl.kind == TypeKind::Opaque {
            parts.push(self.arena.text("opaque "));
        }
        if decl.is_linear {
            parts.push(self.arena.text("linear "));
        }
        parts.push(self.arena.text("type "));
        parts.push(self.arena.owned(decl.name.value.clone()));
        if !decl.generics.is_empty() {
            parts.push(self.print_generic_params(
                &decl.generics,
                decl.name.span.end,
                stmt_span.end,
            ));
        }

        match &decl.definition {
            TypeDefinition::Opaque => {}
            TypeDefinition::Data(ty_id) => {
                if decl.kind == TypeKind::Alias {
                    parts.push(self.arena.text(" = "));
                    let ty_doc = self.print_type(*ty_id);
                    parts.push(ty_doc);
                } else {
                    let payload_start = decl
                        .generics
                        .last()
                        .map_or(decl.name.span.end, |g| g.name.span.end);
                    let ty_node = self.ast.ty(*ty_id);
                    if let Type::Tuple(elems) = &ty_node.value
                        && self.tokens.nominal_tuple_is_unwrapped(payload_start)
                    {
                        let elems = elems.clone();
                        let items: Vec<(Span, DocId)> = elems
                            .iter()
                            .map(|(st, tid)| {
                                let s = self.print_storage(st, true);
                                let t = self.print_type(*tid);
                                (self.ast.ty(*tid).span, self.arena.concat(&[s, t]))
                            })
                            .collect();
                        parts.push(self.print_delimited_list(
                            "(",
                            ")",
                            items,
                            payload_start,
                            stmt_span.end,
                            false,
                        ));
                    } else {
                        let ty_doc = self.print_type(*ty_id);
                        let p = self.arena.text("(");
                        let q = self.arena.text(")");
                        parts.push(self.arena.concat(&[p, ty_doc, q]));
                    }
                }
            }
            TypeDefinition::Function(params, body_id) => {
                parts.push(self.arena.text(" = \\"));
                for (i, g) in params.iter().enumerate() {
                    if i > 0 {
                        parts.push(self.arena.text(", "));
                    }
                    parts.push(self.arena.owned(g.name.value.clone()));
                    if !g.bound.is_empty() {
                        parts.push(self.arena.text(": "));
                        for (j, &b) in g.bound.iter().enumerate() {
                            if j > 0 {
                                parts.push(self.arena.text(" | "));
                            }
                            parts.push(self.print_type(b));
                        }
                    }
                    for guard in &g.guards {
                        parts.push(self.arena.text(" |> "));
                        parts.push(self.print_path(guard));
                    }
                }
                let body_is_block_or_match = matches!(
                    self.ast.expr(*body_id).value,
                    Expr::Block { .. } | Expr::Match { .. } | Expr::With { .. }
                );
                let body_doc = self.print_expr(*body_id);
                if body_is_block_or_match {
                    parts.push(self.arena.text(" -> "));
                    parts.push(body_doc);
                } else {
                    parts.push(self.arena.text(" ->"));
                    let l = self.arena.line();
                    let tail = self.arena.indent_concat(&[l, body_doc]);
                    parts.push(tail);
                    let grouped = self.arena.group_concat(&parts);
                    parts = vec![grouped];
                }
            }
            TypeDefinition::Sum(variants) => {
                let open_pos =
                    self.tokens
                        .find_bracket_span(decl.name.span.end, stmt_span.end, "{");
                let close_byte = open_pos.map_or(stmt_span.end, |(_, c)| c);
                if variants.is_empty()
                    && !self.comments.has_comment_in(decl.name.span.end, close_byte)
                {
                    parts.push(self.arena.text(" {}"));
                } else {
                    parts.push(self.arena.text(" {"));
                    let mut inner = Vec::new();
                    let mut prev_end: Option<usize> = None;
                    for (idx, variant) in variants.iter().enumerate() {
                        let v_span = self.variant_span(variant);
                        let next_lim = variants
                            .get(idx + 1)
                            .map_or(close_byte, |v| self.variant_span(v).start);
                        let (leading, had_leading) = self.comments.emit_leading(
                            &mut self.arena,
                            v_span.start,
                            prev_end.is_some(),
                        );
                        if let Some(pe) = prev_end {
                            if !had_leading && self.tokens.has_blank_line_between(pe, v_span.start)
                            {
                                inner.push(self.arena.blank_line());
                            } else {
                                inner.push(self.arena.hard_line());
                            }
                        } else {
                            inner.push(self.arena.hard_line());
                        }
                        if had_leading {
                            inner.push(leading);
                        }
                        let v_doc = self.print_variant(variant, next_lim);
                        inner.push(v_doc);
                        let v_end_line = self.end_line_of(v_span);
                        if let Some(trailing) = self.comments.emit_trailing_on_line(
                            &mut self.arena,
                            v_end_line,
                            next_lim,
                        ) {
                            inner.push(trailing);
                        }
                        prev_end = Some(v_span.end);
                    }
                    let (dangling, had_d) = self.comments.emit_dangling(
                        &mut self.arena,
                        close_byte,
                        !variants.is_empty(),
                    );
                    if had_d {
                        if variants.is_empty() {
                            inner.push(self.arena.hard_line());
                        }
                        inner.push(dangling);
                    }
                    let inner_doc = self.arena.concat(&inner);
                    parts.push(self.arena.indent(inner_doc));
                    parts.push(self.arena.hard_line());
                    parts.push(self.arena.text("}"));
                }
            }
        }

        if !decl.guards.is_empty() {
            let mut guard_parts = Vec::new();
            for &guard in &decl.guards {
                guard_parts.push(self.arena.line());
                guard_parts.push(self.arena.text("|> "));
                guard_parts.push(self.print_expr(guard));
            }
            let g_concat = self.arena.concat(&guard_parts);
            let g_indent = self.arena.indent(g_concat);
            parts.push(self.arena.group(g_indent));
        }

        self.arena.concat(&parts)
    }

    fn variant_span(&self, variant: &Variant) -> Span {
        match variant {
            Variant::Constructor {
                name,
                payload,
                attrs,
            } => {
                let start = attrs
                    .first()
                    .map_or(name.span.start, |&a| self.ast.expr(a).span.start);
                let end = payload
                    .as_ref()
                    .and_then(|p| p.last())
                    .map_or(name.span.end, |&t| self.ast.ty(t).span.end);
                Span::new(name.span.file, start, end)
            }
            Variant::Spread(t) => self.ast.ty(*t).span,
            Variant::Extensible => Span::default(),
        }
    }

    fn print_variant(&mut self, variant: &Variant, next_limit: usize) -> DocId {
        match variant {
            Variant::Constructor {
                name,
                payload,
                attrs,
            } => {
                let mut parts = Vec::new();
                if !attrs.is_empty() {
                    let attr_start = attrs.first().map_or(name.span.start, |&a| {
                        self.ast.expr(a).span.start.saturating_sub(5)
                    });
                    parts.push(self.print_meta_attrs(attr_start, name.span.start, attrs));
                    parts.push(self.arena.hard_line());
                }
                parts.push(self.arena.owned(name.value.clone()));
                if let Some(types) = payload {
                    if types.len() == 1
                        && let Some(&only) = types.first()
                        && matches!(self.ast.ty(only).value, Type::Unit)
                        && self.tokens.variant_has_empty_parens(name.span.end)
                    {
                        parts.push(self.arena.text("()"));
                    } else {
                        let items: Vec<(Span, DocId)> = types
                            .iter()
                            .map(|&t| (self.ast.ty(t).span, self.print_type(t)))
                            .collect();
                        parts.push(self.print_delimited_list(
                            "(",
                            ")",
                            items,
                            name.span.end,
                            next_limit,
                            false,
                        ));
                    }
                }
                self.arena.concat(&parts)
            }
            Variant::Spread(t) => {
                let dots = self.arena.text("..");
                let td = self.print_type(*t);
                self.arena.concat(&[dots, td])
            }
            Variant::Extensible => self.arena.text(".."),
        }
    }

    fn print_effect(
        &mut self,
        vis: DocId,
        name: &crate::syntax::Name,
        generics: &[GenericParam],
        operations: &[StmtId],
        spreads: &[TypeId],
        stmt_span: Span,
    ) -> DocId {
        let mut parts = vec![
            vis,
            self.arena.text("eff "),
            self.arena.owned(name.value.clone()),
        ];
        if !generics.is_empty() {
            parts.push(self.print_generic_params(generics, name.span.end, stmt_span.end));
        }

        // Merge operations and spreads in exact source order.
        enum EffMember {
            Op(StmtId, Span),
            Spread(TypeId, Span),
        }
        let mut members: Vec<EffMember> = Vec::with_capacity(operations.len() + spreads.len());
        for &op in operations {
            members.push(EffMember::Op(op, self.ast.stmt(op).span));
        }
        for &sp in spreads {
            members.push(EffMember::Spread(sp, self.ast.ty(sp).span));
        }
        members.sort_by_key(|m| match m {
            EffMember::Op(_, s) | EffMember::Spread(_, s) => s.start,
        });

        let open_pos = self
            .tokens
            .find_bracket_span(name.span.end, stmt_span.end, "{");
        let close_byte = open_pos.map_or(stmt_span.end, |(_, c)| c);

        if members.is_empty() && !self.comments.has_comment_in(name.span.end, close_byte) {
            parts.push(self.arena.text(" {}"));
            return self.arena.concat(&parts);
        }

        parts.push(self.arena.text(" {"));
        let mut inner = Vec::new();
        let mut prev_end: Option<usize> = None;
        for (idx, member) in members.iter().enumerate() {
            let m_span = match member {
                EffMember::Op(_, s) | EffMember::Spread(_, s) => *s,
            };
            let next_lim = members.get(idx + 1).map_or(close_byte, |m| match m {
                EffMember::Op(_, s) | EffMember::Spread(_, s) => s.start,
            });
            let (leading, had_leading) =
                self.comments
                    .emit_leading(&mut self.arena, m_span.start, prev_end.is_some());
            if let Some(pe) = prev_end {
                if !had_leading && self.tokens.has_blank_line_between(pe, m_span.start) {
                    inner.push(self.arena.blank_line());
                } else {
                    inner.push(self.arena.hard_line());
                }
            } else {
                inner.push(self.arena.hard_line());
            }
            if had_leading {
                inner.push(leading);
            }
            let doc = match member {
                EffMember::Op(stmt_id, _) => {
                    let s = self.ast.stmt(*stmt_id);
                    let mut op_parts = Vec::new();
                    if !s.value.attrs.is_empty() {
                        op_parts.push(self.print_meta_attrs(
                            s.span.start,
                            s.span.end,
                            &s.value.attrs,
                        ));
                        op_parts.push(self.arena.hard_line());
                    }
                    if let StmtKind::Function(fun) = &s.value.kind {
                        let empty = self.arena.empty();
                        op_parts.push(self.print_function(empty, fun, s.span, true));
                    }
                    self.arena.concat(&op_parts)
                }
                EffMember::Spread(ty_id, _) => {
                    let dots = self.arena.text("..");
                    let td = self.print_type(*ty_id);
                    self.arena.concat(&[dots, td])
                }
            };
            inner.push(doc);
            let m_end_line = self.end_line_of(m_span);
            if let Some(trailing) =
                self.comments
                    .emit_trailing_on_line(&mut self.arena, m_end_line, next_lim)
            {
                inner.push(trailing);
            }
            prev_end = Some(m_span.end);
        }
        let (dangling, had_d) =
            self.comments
                .emit_dangling(&mut self.arena, close_byte, !members.is_empty());
        if had_d {
            if members.is_empty() {
                inner.push(self.arena.hard_line());
            }
            inner.push(dangling);
        }
        let inner_doc = self.arena.concat(&inner);
        parts.push(self.arena.indent(inner_doc));
        parts.push(self.arena.hard_line());
        parts.push(self.arena.text("}"));
        self.arena.concat(&parts)
    }

    fn print_sub(
        &mut self,
        vis: DocId,
        name: &crate::syntax::Name,
        items: &[StmtId],
        stmt_span: Span,
    ) -> DocId {
        let mut parts = vec![
            vis,
            self.arena.text("sub "),
            self.arena.owned(name.value.clone()),
        ];
        let close_byte = self
            .tokens
            .find_bracket_span(name.span.end, stmt_span.end, "{")
            .map_or(stmt_span.end, |(_, c)| c);
        if items.is_empty() && !self.comments.has_comment_in(name.span.end, close_byte) {
            parts.push(self.arena.text(" {}"));
            return self.arena.concat(&parts);
        }
        parts.push(self.arena.text(" {"));
        let hl = self.arena.hard_line();
        let body = self.print_stmt_list(items, name.span.end, close_byte, true);
        let (dangling, had_d) =
            self.comments
                .emit_dangling(&mut self.arena, close_byte, !items.is_empty());
        let inner = if had_d {
            self.arena.concat(&[hl, body, dangling])
        } else {
            self.arena.concat(&[hl, body])
        };
        parts.push(self.arena.indent(inner));
        parts.push(self.arena.hard_line());
        parts.push(self.arena.text("}"));
        self.arena.concat(&parts)
    }

    fn print_import(&mut self, vis: DocId, import: &Import, stmt_span: Span) -> DocId {
        let mut parts = vec![vis, self.arena.text("use ")];
        let mut has_prefix = false;
        if let Some(file) = &import.file {
            for (i, seg) in file.iter().enumerate() {
                if i > 0 {
                    parts.push(self.arena.text("/"));
                }
                parts.push(self.arena.owned(seg.value.clone()));
            }
            has_prefix = true;
        }
        for seg in &import.modules {
            if has_prefix {
                parts.push(self.arena.text("::"));
            }
            parts.push(self.arena.owned(seg.value.clone()));
            has_prefix = true;
        }
        match &import.target {
            ImportTarget::Module(alias) => {
                if let Some(a) = alias {
                    parts.push(self.arena.text(" as "));
                    parts.push(self.arena.owned(a.value.clone()));
                }
            }
            ImportTarget::Glob => {
                parts.push(self.arena.text("::*"));
            }
            ImportTarget::Items(items) => {
                parts.push(self.arena.text("::"));
                if items.len() == 1
                    && !self.tokens.import_list_is_parenthesized(stmt_span)
                    && let Some((name, alias)) = items.first()
                {
                    parts.push(self.arena.owned(name.value.clone()));
                    if let Some(a) = alias {
                        parts.push(self.arena.text(" as "));
                        parts.push(self.arena.owned(a.value.clone()));
                    }
                } else {
                    let docs: Vec<(Span, DocId)> = items
                        .iter()
                        .map(|(name, alias)| {
                            let mut p = vec![self.arena.owned(name.value.clone())];
                            if let Some(a) = alias {
                                p.push(self.arena.text(" as "));
                                p.push(self.arena.owned(a.value.clone()));
                            }
                            (name.span, self.arena.concat(&p))
                        })
                        .collect();
                    parts.push(self.print_delimited_list(
                        "(",
                        ")",
                        docs,
                        stmt_span.start,
                        stmt_span.end,
                        false,
                    ));
                }
            }
        }
        self.arena.concat(&parts)
    }

    #[allow(clippy::too_many_arguments)]
    fn print_binding(
        &mut self,
        vis: DocId,
        storage: &Storage,
        pattern: PatternId,
        ty: Option<TypeId>,
        value: Option<ExprId>,
        fallback: Option<ExprId>,
        is_meta: bool,
        _stmt_span: Span,
    ) -> DocId {
        let mut parts = vec![vis];
        if is_meta {
            parts.push(self.arena.text("meta "));
        }
        if storage.variable {
            parts.push(self.arena.text("var "));
        } else {
            parts.push(self.arena.text("let "));
        }
        if let Some(m) = storage.mode.as_str() {
            parts.push(self.arena.text(m));
            parts.push(self.arena.text(" "));
        }
        parts.push(self.print_pattern(pattern));
        if let Some(ty_id) = ty {
            parts.push(self.arena.text(": "));
            parts.push(self.print_type(ty_id));
        }
        if let Some(val_id) = value {
            parts.push(self.arena.text(" = "));
            parts.push(self.print_expr(val_id));
        }
        if let Some(fb_id) = fallback {
            parts.push(self.arena.text(" else "));
            parts.push(self.print_block(fb_id, false));
        }
        self.arena.concat(&parts)
    }

    fn print_handler(&mut self, handler: &Handler) -> DocId {
        let mut parts = Vec::new();
        if handler.is_ctl {
            parts.push(self.arena.text("ctl "));
        }
        parts.push(self.print_path(&handler.operation));
        parts.push(self.arena.text(" = "));
        if let Some(m) = handler.mode.as_str() {
            parts.push(self.arena.text(m));
            parts.push(self.arena.text(" "));
        }
        parts.push(self.print_expr(handler.value));
        self.arena.concat(&parts)
    }

    fn print_storage(&mut self, storage: &Storage, trailing_space: bool) -> DocId {
        let mut parts = Vec::new();
        if storage.bind_mode {
            parts.push(self.arena.text("let "));
            if let Some(path) = &storage.mode_path {
                parts.push(self.print_path(path));
            } else {
                parts.push(self.arena.text("_"));
            }
        } else {
            if storage.variable {
                parts.push(self.arena.text("var"));
            }
            if let Some(m) = storage.mode.as_str() {
                if !parts.is_empty() {
                    parts.push(self.arena.text(" "));
                }
                parts.push(self.arena.text(m));
            }
            if let Some(path) = &storage.mode_path {
                if !parts.is_empty() {
                    parts.push(self.arena.text(" "));
                }
                parts.push(self.print_path(path));
            }
        }
        if parts.is_empty() {
            return self.arena.empty();
        }
        if trailing_space {
            parts.push(self.arena.text(" "));
        }
        self.arena.concat(&parts)
    }

    fn print_path(&mut self, path: &Path) -> DocId {
        let mut parts = Vec::new();
        for (idx, seg) in path.segments.iter().enumerate() {
            if idx > 0 {
                parts.push(self.arena.text("::"));
            }
            parts.push(self.print_segment(seg, path.span.end));
        }
        self.arena.concat(&parts)
    }

    fn print_segment(&mut self, seg: &Segment, path_end: usize) -> DocId {
        let mut parts = vec![self.arena.owned(seg.name.value.clone())];
        if !seg.arguments.is_empty()
            || self
                .tokens
                .raw_slice(Span::new(seg.name.span.file, seg.name.span.end, path_end))
                .starts_with("<>")
        {
            let items: Vec<(Span, DocId)> = seg
                .arguments
                .iter()
                .map(|arg| {
                    let span = match arg {
                        GenericArg::Type(t) => self.ast.ty(*t).span,
                        GenericArg::Value(e) => self.ast.expr(*e).span,
                        GenericArg::Mode(s) => {
                            s.mode_span.or(s.keyword_span).unwrap_or(seg.name.span)
                        }
                    };
                    (span, self.print_generic_arg(arg))
                })
                .collect();
            parts.push(self.print_delimited_list(
                "<",
                ">",
                items,
                seg.name.span.end,
                path_end,
                false,
            ));
        }
        self.arena.concat(&parts)
    }

    fn wrap_parens(&mut self, doc: DocId, depth: usize) -> DocId {
        let mut cur = doc;
        for _ in 0..depth {
            let l = self.arena.text("(");
            let r = self.arena.text(")");
            cur = self.arena.concat(&[l, cur, r]);
        }
        cur
    }

    fn print_type(&mut self, id: TypeId) -> DocId {
        let spanned = self.ast.ty(id);
        let span = spanned.span;
        let ty = spanned.value.clone();
        let self_is_parens = matches!(ty, Type::Unit | Type::Tuple(_) | Type::TupleAny);
        let pdepth = self.tokens.paren_depth(span, self_is_parens);

        let doc = match ty {
            Type::PatternBinding(name) => {
                let l = self.arena.text("let ");
                let n = self.arena.owned(name.value);
                self.arena.concat(&[l, n])
            }
            Type::PatternWildcard => self.arena.text("_"),
            Type::PatternLiteral(lit) => self.print_literal(&lit),
            Type::Named(path) => self.print_path(&path),
            Type::Unit => self.arena.text("()"),
            Type::TupleAny => self.arena.text("(..)"),
            Type::Tuple(elems) => {
                let items: Vec<(Span, DocId)> = elems
                    .iter()
                    .map(|(st, tid)| {
                        let s = self.print_storage(st, true);
                        let t = self.print_type(*tid);
                        (self.ast.ty(*tid).span, self.arena.concat(&[s, t]))
                    })
                    .collect();
                self.print_delimited_list("(", ")", items, span.start, span.end, false)
            }
            Type::Array(storage, elem) => {
                let l = self.arena.text("[");
                let st = self.print_storage(&storage, false);
                let r = self.arena.text("]");
                let e = self.print_type(elem);
                self.arena.concat(&[l, st, r, e])
            }
            Type::Map(k, storage, v) => {
                let l = self.arena.text("[");
                let kd = self.print_type(k);
                let col = self.arena.text(": ");
                let st = self.print_storage(&storage, true);
                let vd = self.print_type(v);
                let r = self.arena.text("]");
                self.arena.concat(&[l, kd, col, st, vd, r])
            }
            Type::Result(ok, err) => {
                let items = vec![
                    (self.ast.ty(ok).span, self.print_type(ok)),
                    (self.ast.ty(err).span, self.print_type(err)),
                ];
                self.print_delimited_list("!<", ">", items, span.start, span.end, false)
            }
            Type::Option(inner) => {
                let q = self.arena.text("?");
                let t = self.print_type(inner);
                self.arena.concat(&[q, t])
            }
            Type::Record { fields, tail } => self.print_record_type(&fields, tail.as_ref(), span),
            Type::Mapped {
                storage,
                pattern,
                iterable,
                field,
            } => {
                let o = self.arena.text(".{ ");
                let st = self.print_storage(&storage, true);
                let lb = self.arena.text("[");
                let it = self.print_expr(iterable);
                let a = self.arena.text(" as ");
                let pat = self.print_pattern(pattern);
                let rb = self.arena.text("]: ");
                let f = self.print_type(field);
                let c = self.arena.text(" }");
                self.arena.concat(&[o, st, lb, it, a, pat, rb, f, c])
            }
            Type::Callable(sig) => {
                let kw = if sig.is_ctl {
                    self.arena.text("ctl")
                } else {
                    self.arena.text("fn")
                };
                let rest = self.print_signature_parts(&sig, span.start, true, false);
                self.arena.group_concat(&[kw, rest])
            }
            Type::Unquote(expr_id) => {
                let l = self.arena.text("<");
                let e = self.print_expr(expr_id);
                let r = self.arena.text(">");
                self.arena.concat(&[l, e, r])
            }
            Type::TypeOf(expr_id) => {
                let kw = self.arena.text("typeof ");
                let e = self.print_expr(expr_id);
                self.arena.concat(&[kw, e])
            }
            Type::Project { base, field } => {
                let b = self.print_type(base);
                let dot = self.arena.text(".");
                let m = self.print_member(&field);
                self.arena.concat(&[b, dot, m])
            }
        };

        self.wrap_parens(doc, pdepth)
    }

    fn print_record_type(
        &mut self,
        fields: &[TypeField],
        tail: Option<&FieldTail>,
        span: Span,
    ) -> DocId {
        let mut items: Vec<(Span, DocId)> = Vec::new();
        let mut has_attrs = false;
        for f in fields {
            let mut fparts = Vec::new();
            if !f.attrs.is_empty() {
                has_attrs = true;
                let a_start = f.attrs.first().map_or(f.name.span.start, |&a| {
                    self.ast.expr(a).span.start.saturating_sub(5)
                });
                fparts.push(self.print_meta_attrs(a_start, f.name.span.start, &f.attrs));
                fparts.push(self.arena.hard_line());
            }
            fparts.push(self.print_storage(&f.storage, true));
            fparts.push(self.arena.owned(f.name.value.clone()));
            fparts.push(self.arena.text(": "));
            fparts.push(self.print_type(f.ty));
            if let Some(def) = f.default {
                fparts.push(self.arena.text(" = "));
                fparts.push(self.print_expr(def));
            }
            items.push((f.name.span, self.arena.concat(&fparts)));
        }
        if let Some(tail) = tail {
            match tail {
                FieldTail::Open => {
                    items.push((
                        Span::new(span.file, span.end.saturating_sub(3), span.end),
                        self.arena.text(".."),
                    ));
                }
                FieldTail::Named(name) => {
                    let prefix = if self.tokens.tail_has_let(
                        fields
                            .last()
                            .map_or(span.start, |f| self.ast.ty(f.ty).span.end),
                        name.span.start,
                    ) {
                        "..let "
                    } else {
                        ".."
                    };
                    let p = self.arena.text(prefix);
                    let n = self.arena.owned(name.value.clone());
                    items.push((name.span, self.arena.concat(&[p, n])));
                }
            }
        }
        let doc = self.print_delimited_list(".{", "}", items, span.start, span.end, true);
        if has_attrs {
            self.arena.group_forced(doc, true)
        } else {
            doc
        }
    }

    fn print_member(&mut self, member: &Member) -> DocId {
        match member {
            Member::Name(n) | Member::Index(n) => self.arena.owned(n.value.clone()),
            Member::Computed(e) => {
                let l = self.arena.text("(");
                let inner = self.print_expr(*e);
                let r = self.arena.text(")");
                self.arena.concat(&[l, inner, r])
            }
        }
    }

    fn print_literal(&mut self, lit: &Literal) -> DocId {
        match lit.kind {
            LiteralKind::String => self.arena.owned(format!("\"{}\"", lit.text)),
            LiteralKind::RawString | LiteralKind::RawBytes => {
                // Use raw_text so multi-line raw strings never get interior indentation added.
                let owned = lit.text.clone();
                // Look up verbatim slice if possible; otherwise owned.
                if owned.contains('\n') {
                    // Doc::Owned handles single-line; for multi-line raw literals we emit via
                    // RawText from source when called from Expr::Literal.
                    self.arena.owned(owned)
                } else {
                    self.arena.owned(owned)
                }
            }
            _ => self.arena.owned(lit.text.clone()),
        }
    }

    fn print_expr(&mut self, id: ExprId) -> DocId {
        let spanned = self.ast.expr(id);
        let span = spanned.span;
        let expr = spanned.value.clone();
        let self_is_parens = matches!(expr, Expr::Unit | Expr::Tuple(_));
        let pdepth = self.tokens.paren_depth(span, self_is_parens);

        let doc = match expr {
            Expr::Path(path) => self.print_path(&path),
            Expr::Unit => self.arena.text("()"),
            Expr::Literal(lit) => {
                if matches!(lit.kind, LiteralKind::RawString | LiteralKind::RawBytes) {
                    let raw = self.tokens.raw_slice(span);
                    if !raw.is_empty() {
                        self.arena.raw_text(raw)
                    } else {
                        self.print_literal(&lit)
                    }
                } else {
                    self.print_literal(&lit)
                }
            }
            Expr::Interpolated(parts) => {
                let mut out = vec![self.arena.text("\"")];
                for part in parts {
                    match part {
                        StringPart::Text(s) => out.push(self.arena.owned(s)),
                        StringPart::Interpolation(e) => {
                            out.push(self.arena.text("{"));
                            let inner = self.print_expr(e);
                            out.push(self.arena.force_flat(inner));
                            out.push(self.arena.text("}"));
                        }
                    }
                }
                out.push(self.arena.text("\""));
                self.arena.concat(&out)
            }
            Expr::Block { .. } => self.print_block(id, false),
            Expr::With {
                handlers,
                statements,
                helpers,
            } => self.print_with_expr(&handlers, &statements, &helpers, span),
            Expr::Unary { op, value } => {
                if op.value == "?" {
                    let v = self.print_expr(value);
                    let q = self.arena.text("?");
                    self.arena.concat(&[v, q])
                } else if matches!(op.value.as_str(), "ref" | "^mut") {
                    let o = self.arena.owned(op.value);
                    let sp = self.arena.text(" ");
                    let v = self.print_expr(value);
                    self.arena.concat(&[o, sp, v])
                } else {
                    let o = self.arena.owned(op.value);
                    let v = self.print_expr(value);
                    self.arena.concat(&[o, v])
                }
            }
            Expr::Binary { op, left, right } => self.print_binary(op, left, right),
            Expr::Cast { value, target } => {
                let v = self.print_expr(value);
                let l = self.arena.line();
                let kw = self.arena.text("as ");
                let t = self.print_type(target);
                let tail = self.arena.indent_concat(&[l, kw, t]);
                self.arena.group_concat(&[v, tail])
            }
            Expr::Pipeline { .. } => self.print_pipeline_chain(id),
            Expr::Member { base, member, safe } => {
                let b = self.print_expr(base);
                let op = if safe { "?." } else { "." };
                let o = self.arena.text(op);
                let m = self.print_member(&member);
                self.arena.concat(&[b, o, m])
            }
            Expr::Index { base, index, safe } => {
                let b = self.print_expr(base);
                let o = if safe { "?[" } else { "[" };
                let l = self.arena.text(o);
                let i = self.print_expr(index);
                let r = self.arena.text("]");
                self.arena.concat(&[b, l, i, r])
            }
            Expr::Range {
                start,
                end,
                inclusive,
            } => {
                let mut parts = Vec::new();
                if let Some(s) = start {
                    parts.push(self.print_expr(s));
                }
                parts.push(self.arena.text(if inclusive { "..=" } else { ".." }));
                if let Some(e) = end {
                    parts.push(self.print_expr(e));
                }
                self.arena.concat(&parts)
            }
            Expr::Call { callee, args } => self.print_call(callee, &args, span),
            Expr::Wrap { path, args } => {
                let p = self.print_path(&path);
                let col = self.arena.text("::");
                let items: Vec<(Span, DocId)> = args
                    .iter()
                    .map(|a| (self.ast.expr(a.value).span, self.print_argument(a)))
                    .collect();
                let list =
                    self.print_delimited_list("(", ")", items, path.span.end, span.end, false);
                self.arena.concat(&[p, col, list])
            }
            Expr::Record { name, fields } => {
                let prefix = match name.as_ref() {
                    Some(p) => self.print_path(p),
                    None => self.arena.empty(),
                };
                let search_start = name.as_ref().map_or(span.start, |p| p.span.end);
                let items: Vec<(Span, DocId)> = fields
                    .iter()
                    .map(|f| (f.name.span, self.print_value_field(f)))
                    .collect();
                let body =
                    self.print_delimited_list(".{", "}", items, search_start, span.end, true);
                self.arena.concat(&[prefix, body])
            }
            Expr::Array(items) => {
                let docs: Vec<(Span, DocId)> = items
                    .iter()
                    .map(|&e| (self.ast.expr(e).span, self.print_expr(e)))
                    .collect();
                self.print_delimited_list("[", "]", docs, span.start, span.end, false)
            }
            Expr::Tuple(items) => {
                let docs: Vec<(Span, DocId)> = items
                    .iter()
                    .map(|&e| (self.ast.expr(e).span, self.print_expr(e)))
                    .collect();
                self.print_delimited_list("(", ")", docs, span.start, span.end, false)
            }
            Expr::Map(entries) => {
                if entries.is_empty() && !self.comments.has_comment_in(span.start, span.end) {
                    self.arena.text("[:]")
                } else {
                    let docs: Vec<(Span, DocId)> = entries
                        .iter()
                        .map(|&(k, v)| {
                            let kd = self.print_expr(k);
                            let col = self.arena.text(": ");
                            let vd = self.print_expr(v);
                            (
                                self.ast.expr(k).span.join(self.ast.expr(v).span),
                                self.arena.concat(&[kd, col, vd]),
                            )
                        })
                        .collect();
                    self.print_delimited_list("[", "]", docs, span.start, span.end, false)
                }
            }
            Expr::Quote(ty_id) => {
                let l = self.arena.text("<");
                let t = self.print_type(ty_id);
                let r = self.arena.text(">");
                self.arena.concat(&[l, t, r])
            }
            Expr::Meta(inner) => {
                // Always emit a space after `meta` (mandatory before `(` per parser/expr.rs:156).
                let kw = self.arena.text("meta ");
                let e = self.print_expr(inner);
                self.arena.concat(&[kw, e])
            }
            Expr::If {
                is_meta,
                condition,
                yes,
                no,
            } => self.print_if(is_meta, &condition, yes, no),
            Expr::While { condition, body } => {
                let kw = self.arena.text("while ");
                let cond = self.print_condition(&condition);
                let sp = self.arena.text(" ");
                let b = self.print_block(body, true);
                self.arena.concat(&[kw, cond, sp, b])
            }
            Expr::For {
                mode,
                iterable,
                pattern,
                body,
            } => {
                let mut parts = vec![self.arena.text("for ")];
                if let Some(m) = mode.as_str() {
                    parts.push(self.arena.text(m));
                    parts.push(self.arena.text(" "));
                }
                parts.push(self.print_expr(iterable));
                parts.push(self.arena.text(" as "));
                parts.push(self.print_pattern(pattern));
                parts.push(self.arena.text(" "));
                parts.push(self.print_block(body, true));
                self.arena.concat(&parts)
            }
            Expr::Match {
                is_meta,
                mode,
                value,
                arms,
            } => self.print_match(is_meta, mode, value, &arms, span),
            Expr::Closure {
                params,
                obligations,
                body,
            } => self.print_closure(&params, &obligations, body, span),
            Expr::Accessor(steps) => {
                let mut parts = vec![self.arena.text("\\")];
                for (safe, mem) in steps {
                    parts.push(self.arena.text(if safe { "?." } else { "." }));
                    parts.push(self.print_member(&mem));
                }
                self.arena.concat(&parts)
            }
            Expr::Transfer { kind, value } => {
                let kw = match kind {
                    Transfer::Return => "return",
                    Transfer::Break => "break",
                    Transfer::Continue => "continue",
                };
                if let Some(val) = value {
                    let k = self.arena.text(kw);
                    let sp = self.arena.text(" ");
                    let v = self.print_expr(val);
                    self.arena.concat(&[k, sp, v])
                } else {
                    self.arena.text(kw)
                }
            }
            Expr::Hole => self.arena.text("..."),
        };

        self.wrap_parens(doc, pdepth)
    }

    fn print_block(&mut self, id: ExprId, always_multiline: bool) -> DocId {
        let spanned = self.ast.expr(id);
        let span = spanned.span;
        let Expr::Block {
            statements,
            helpers,
        } = spanned.value.clone()
        else {
            return self.print_expr(id);
        };

        let has_comments = self.comments.has_comment_in(span.start, span.end);
        if statements.is_empty() && helpers.is_empty() && !has_comments {
            return self.arena.text("{}");
        }

        // Single-line expression block preservation (e.g. `if c { <()> } else { <never> }`).
        if !always_multiline
            && helpers.is_empty()
            && !has_comments
            && statements.len() == 1
            && !self.tokens.has_newline_in_span(span)
            && let Some(&only) = statements.first()
            && let StmtKind::Expr(e_id) = self.ast.stmt(only).value.kind
            && self.ast.stmt(only).value.attrs.is_empty()
        {
            let inner = self.print_expr(e_id);
            let o = self.arena.text("{");
            let l1 = self.arena.line();
            let l2 = self.arena.line();
            let c = self.arena.text("}");
            let indented = self.arena.indent_concat(&[l1, inner]);
            return self.arena.group_concat(&[o, indented, l2, c]);
        }

        let helpers_start = helpers
            .first()
            .map_or(span.end, |&h| self.ast.stmt(h).span.start);
        let mut parts = vec![self.arena.text("{")];
        if !statements.is_empty() {
            let hl = self.arena.hard_line();
            let stmts_doc = self.print_stmt_list(&statements, span.start, helpers_start, true);
            let inner = self.arena.concat(&[hl, stmts_doc]);
            parts.push(self.arena.indent(inner));
        }

        if !helpers.is_empty() {
            let (leading_w, had_lw) =
                self.comments
                    .emit_leading(&mut self.arena, helpers_start, false);
            parts.push(self.arena.hard_line());
            if had_lw {
                parts.push(leading_w);
            }
            parts.push(self.arena.text("where"));
            let hl = self.arena.hard_line();
            let h_doc = self.print_stmt_list(&helpers, helpers_start, span.end, true);
            parts.push(self.arena.indent_concat(&[hl, h_doc]));
        }

        let (dangling, had_d) = self.comments.emit_dangling(
            &mut self.arena,
            span.end,
            !statements.is_empty() || !helpers.is_empty(),
        );
        if had_d {
            let extra = if statements.is_empty() && helpers.is_empty() {
                let hl = self.arena.hard_line();
                self.arena.concat(&[hl, dangling])
            } else {
                dangling
            };
            parts.push(self.arena.indent(extra));
        }
        parts.push(self.arena.hard_line());
        parts.push(self.arena.text("}"));
        self.arena.concat(&parts)
    }

    fn print_with_expr(
        &mut self,
        handlers: &[Handler],
        statements: &[StmtId],
        helpers: &[StmtId],
        span: Span,
    ) -> DocId {
        let mut parts = vec![self.arena.text("with {")];
        let mut inner = Vec::new();
        let mut prev_end: Option<usize> = None;

        let stmts_start = statements
            .first()
            .map_or(span.end, |&s| self.ast.stmt(s).span.start);
        for (idx, h) in handlers.iter().enumerate() {
            let h_span = h.operation.span.join(self.ast.expr(h.value).span);
            let next_lim = handlers
                .get(idx + 1)
                .map_or(stmts_start, |nh| nh.operation.span.start);
            let (leading, had_l) =
                self.comments
                    .emit_leading(&mut self.arena, h_span.start, prev_end.is_some());
            if let Some(pe) = prev_end {
                if !had_l && self.tokens.has_blank_line_between(pe, h_span.start) {
                    inner.push(self.arena.blank_line());
                } else {
                    inner.push(self.arena.hard_line());
                }
            } else {
                inner.push(self.arena.hard_line());
            }
            if had_l {
                inner.push(leading);
            }
            inner.push(self.print_handler(h));
            let h_end_line = self.end_line_of(h_span);
            if let Some(trailing) =
                self.comments
                    .emit_trailing_on_line(&mut self.arena, h_end_line, next_lim)
            {
                inner.push(trailing);
            }
            prev_end = Some(h_span.end);
        }

        let helpers_start = helpers
            .first()
            .map_or(span.end, |&h| self.ast.stmt(h).span.start);
        if !statements.is_empty() {
            if let Some(pe) = prev_end {
                if self.tokens.has_blank_line_between(pe, stmts_start) {
                    inner.push(self.arena.blank_line());
                } else {
                    inner.push(self.arena.hard_line());
                }
            } else {
                inner.push(self.arena.hard_line());
            }
            inner.push(self.print_stmt_list(statements, span.start, helpers_start, true));
        }

        let inner_doc = self.arena.concat(&inner);
        parts.push(self.arena.indent(inner_doc));

        if !helpers.is_empty() {
            parts.push(self.arena.hard_line());
            parts.push(self.arena.text("where"));
            let hl = self.arena.hard_line();
            let h_doc = self.print_stmt_list(helpers, helpers_start, span.end, true);
            parts.push(self.arena.indent_concat(&[hl, h_doc]));
        }

        let (dangling, had_d) = self.comments.emit_dangling(
            &mut self.arena,
            span.end,
            !handlers.is_empty() || !statements.is_empty(),
        );
        if had_d {
            parts.push(self.arena.indent(dangling));
        }
        parts.push(self.arena.hard_line());
        parts.push(self.arena.text("}"));
        self.arena.concat(&parts)
    }

    fn print_binary(&mut self, op: crate::syntax::Name, left: ExprId, right: ExprId) -> DocId {
        let l = self.print_expr(left);
        let r_span = self.ast.expr(right).span;
        let (leading_r, had_lr) = self
            .comments
            .emit_leading(&mut self.arena, r_span.start, false);
        let r = self.print_expr(right);

        if op.value == "??" {
            // `??` allows line break before `??` (parser/expr.rs:78).
            let sp = self.arena.line();
            let o = self.arena.text("?? ");
            let tail = if had_lr {
                let hl = self.arena.hard_line();
                self.arena.indent_concat(&[sp, o, hl, leading_r, r])
            } else {
                self.arena.indent_concat(&[sp, o, r])
            };
            return self.arena.group_concat(&[l, tail]);
        }

        // All other binary/assign ops break AFTER the operator (parser/expr.rs:102).
        let sp_before = self.arena.text(" ");
        let o = self.arena.owned(op.value);
        let brk = if had_lr {
            let hl = self.arena.hard_line();
            self.arena.concat(&[hl, leading_r])
        } else {
            self.arena.line()
        };
        let tail = self.arena.indent_concat(&[brk, r]);
        self.arena.group_concat(&[l, sp_before, o, tail])
    }

    fn print_pipeline_chain(&mut self, top: ExprId) -> DocId {
        struct PipeStep {
            mode: Mode,
            target: ExprId,
            propagate: bool,
            pipe_span: Span,
        }
        let mut steps = Vec::new();
        let mut cur = top;
        while let Expr::Pipeline {
            value,
            pipe_span,
            mode,
            target,
            propagate,
            ..
        } = self.ast.expr(cur).value
        {
            if cur != top && self.tokens.paren_depth(self.ast.expr(cur).span, false) > 0 {
                break;
            }
            steps.push(PipeStep {
                mode,
                target,
                propagate,
                pipe_span,
            });
            cur = value;
        }
        steps.reverse();

        let root_span = self.ast.expr(cur).span;
        let root_doc = self.print_expr(cur);
        let top_span = self.ast.expr(top).span;
        let force_break = (steps.len() >= 2 && self.tokens.has_newline_in_span(top_span))
            || self.comments.has_comment_in(root_span.end, top_span.end);

        let mut tail = Vec::new();
        for step in steps {
            let (leading, had_l) =
                self.comments
                    .emit_leading(&mut self.arena, step.pipe_span.start, false);
            if had_l {
                tail.push(self.arena.hard_line());
                tail.push(leading);
            } else {
                tail.push(self.arena.line());
            }
            tail.push(self.arena.text("|> "));
            if let Some(m) = step.mode.as_str() {
                tail.push(self.arena.text(m));
                tail.push(self.arena.text(" "));
            }
            tail.push(self.print_expr(step.target));
            if step.propagate {
                tail.push(self.arena.text("?"));
            }
        }
        let tail_doc = self.arena.indent_concat(&tail);
        self.arena
            .group_concat_forced(&[root_doc, tail_doc], force_break)
    }

    fn print_call(&mut self, callee: ExprId, args: &[Argument], span: Span) -> DocId {
        let callee_span = self.ast.expr(callee).span;
        let callee_doc = self.print_expr(callee);

        // Check for trailing closure syntax (`f(a) \x -> ...`, `f() \x -> ...`, `f \x -> ...`).
        if let Some(last) = args.last()
            && last.name.is_none()
            && last.mode == Mode::Plain
            && self
                .tokens
                .has_trailing_closure(self.ast.expr(last.value).span.start)
        {
            let closure_span = self.ast.expr(last.value).span;
            let init = args.get(..args.len().saturating_sub(1)).unwrap_or(&[]);
            let mut parts = vec![callee_doc];
            if !init.is_empty() {
                let items: Vec<(Span, DocId)> = init
                    .iter()
                    .map(|a| (self.ast.expr(a.value).span, self.print_argument(a)))
                    .collect();
                parts.push(self.print_delimited_list(
                    "(",
                    ")",
                    items,
                    callee_span.end,
                    closure_span.start,
                    false,
                ));
            } else if self
                .tokens
                .has_empty_parens_before_trailing_closure(callee_span.end, closure_span.start)
            {
                parts.push(self.arena.text("()"));
            }
            parts.push(self.arena.text(" "));
            parts.push(self.print_expr(last.value));
            return self.arena.concat(&parts);
        }

        // Block-hugging final argument (`derive(u, \mut d -> { ... })`): if no trailing comma
        // and no comments between args, and final arg is a block-bodied closure/record/array/match/with,
        // keep the call header flat when it fits.
        let has_trailing = self
            .tokens
            .has_trailing_comma_in(callee_span.end, span.end, "(");
        if !has_trailing
            && !args.is_empty()
            && let Some(last) = args.last()
            && self.is_huggable_arg(last.value)
            && !self
                .comments
                .has_comment_in(callee_span.end, self.ast.expr(last.value).span.start)
        {
            let mut parts = vec![callee_doc, self.arena.text("(")];
            for (idx, arg) in args.iter().enumerate() {
                if idx > 0 {
                    parts.push(self.arena.text(", "));
                }
                parts.push(self.print_argument(arg));
            }
            parts.push(self.arena.text(")"));
            return self.arena.concat(&parts);
        }

        let items: Vec<(Span, DocId)> = args
            .iter()
            .map(|a| (self.ast.expr(a.value).span, self.print_argument(a)))
            .collect();
        let args_doc = self.print_delimited_list("(", ")", items, callee_span.end, span.end, false);
        self.arena.concat(&[callee_doc, args_doc])
    }

    fn is_huggable_arg(&self, expr_id: ExprId) -> bool {
        match &self.ast.expr(expr_id).value {
            Expr::Closure { body, .. } => matches!(self.ast.expr(*body).value, Expr::Block { .. }),
            Expr::Block { .. } | Expr::With { .. } | Expr::Match { .. } => true,
            _ => false,
        }
    }

    fn print_argument(&mut self, arg: &Argument) -> DocId {
        let mut parts = Vec::new();
        if let Some(name) = &arg.name {
            parts.push(self.arena.owned(name.value.clone()));
            parts.push(self.arena.text(": "));
        }
        if let Some(m) = arg.mode.as_str() {
            parts.push(self.arena.text(m));
            parts.push(self.arena.text(" "));
        }
        parts.push(self.print_expr(arg.value));
        self.arena.concat(&parts)
    }

    fn print_value_field(&mut self, f: &ValueField) -> DocId {
        let mut parts = Vec::new();
        parts.push(self.print_storage(&f.storage, true));
        parts.push(self.arena.owned(f.name.value.clone()));
        if let Some(val) = f.value {
            parts.push(self.arena.text(": "));
            parts.push(self.print_expr(val));
        }
        self.arena.concat(&parts)
    }

    fn print_condition(&mut self, cond: &Condition) -> DocId {
        match cond {
            Condition::Expr(e) => self.print_expr(*e),
            Condition::Binding {
                mode,
                pattern,
                value,
            } => {
                let mut parts = vec![self.arena.text("let ")];
                if let Some(m) = mode.as_str() {
                    parts.push(self.arena.text(m));
                    parts.push(self.arena.text(" "));
                }
                parts.push(self.print_pattern(*pattern));
                parts.push(self.arena.text(" = "));
                parts.push(self.print_expr(*value));
                self.arena.concat(&parts)
            }
        }
    }

    fn print_if(
        &mut self,
        is_meta: bool,
        condition: &Condition,
        yes: ExprId,
        no: Option<ExprId>,
    ) -> DocId {
        let mut parts = Vec::new();
        if is_meta {
            parts.push(self.arena.text("meta "));
        }
        parts.push(self.arena.text("if "));
        parts.push(self.print_condition(condition));
        parts.push(self.arena.text(" "));

        // If either branch is already multi-line or the whole `if ... else ...` expression is long,
        // keep both branches uniformly multi-line instead of half-inline / half-multiline.
        let yes_span = self.ast.expr(yes).span;
        let no_span = no.map(|n| self.ast.expr(n).span);
        let total_span = no_span.map_or(yes_span, |ns| yes_span.join(ns));
        let force_multiline_branches = self.tokens.has_newline_in_span(yes_span)
            || no_span.is_some_and(|ns| {
                !matches!(self.ast.expr(no.unwrap_or(yes)).value, Expr::If { .. })
                    && self.tokens.has_newline_in_span(ns)
            })
            || total_span.end.saturating_sub(total_span.start) > 80;

        parts.push(self.print_block(yes, force_multiline_branches));
        if let Some(no_id) = no {
            let no_span = self.ast.expr(no_id).span;
            let (leading, had_l) =
                self.comments
                    .emit_leading(&mut self.arena, no_span.start, false);
            if had_l {
                parts.push(self.arena.hard_line());
                parts.push(leading);
                parts.push(self.arena.text("else "));
            } else {
                parts.push(self.arena.text(" else "));
            }
            match &self.ast.expr(no_id).value {
                Expr::If { .. } => parts.push(self.print_expr(no_id)),
                Expr::Block { .. } => parts.push(self.print_block(no_id, force_multiline_branches)),
                _ => parts.push(self.print_expr(no_id)),
            }
        }
        self.arena.concat(&parts)
    }

    fn print_match(
        &mut self,
        is_meta: bool,
        mode: Mode,
        value: ExprId,
        arms: &[MatchArm],
        span: Span,
    ) -> DocId {
        let mut parts = Vec::new();
        if is_meta {
            parts.push(self.arena.text("meta "));
        }
        parts.push(self.arena.text("match "));
        if let Some(m) = mode.as_str() {
            parts.push(self.arena.text(m));
            parts.push(self.arena.text(" "));
        }
        parts.push(self.print_expr(value));

        let open_start = self.ast.expr(value).span.end;
        if arms.is_empty() && !self.comments.has_comment_in(open_start, span.end) {
            parts.push(self.arena.text(" {}"));
            return self.arena.concat(&parts);
        }

        parts.push(self.arena.text(" {"));
        let mut inner = Vec::new();
        let mut prev_end: Option<usize> = None;
        for (idx, arm) in arms.iter().enumerate() {
            let pat_span = self.ast.pattern(arm.pattern).span;
            let body_span = self.ast.expr(arm.body).span;
            let arm_span = pat_span.join(body_span);
            let next_lim = arms
                .get(idx + 1)
                .map_or(span.end, |na| self.ast.pattern(na.pattern).span.start);
            let (leading, had_l) =
                self.comments
                    .emit_leading(&mut self.arena, arm_span.start, prev_end.is_some());
            if let Some(pe) = prev_end {
                if !had_l && self.tokens.has_blank_line_between(pe, arm_span.start) {
                    inner.push(self.arena.blank_line());
                } else {
                    inner.push(self.arena.hard_line());
                }
            } else {
                inner.push(self.arena.hard_line());
            }
            if had_l {
                inner.push(leading);
            }
            let mut arm_parts = vec![self.print_pattern(arm.pattern)];
            if let Some(g) = arm.guard {
                arm_parts.push(self.arena.text(" if "));
                arm_parts.push(self.print_expr(g));
            }
            arm_parts.push(self.arena.text(" ->"));
            let body_is_block = matches!(
                self.ast.expr(arm.body).value,
                Expr::Block { .. } | Expr::Match { .. } | Expr::With { .. }
            );
            let body_doc = self.print_expr(arm.body);
            if body_is_block {
                arm_parts.push(self.arena.text(" "));
                arm_parts.push(body_doc);
                inner.push(self.arena.concat(&arm_parts));
            } else {
                let l = self.arena.line();
                let tail = self.arena.indent_concat(&[l, body_doc]);
                arm_parts.push(tail);
                inner.push(self.arena.group_concat(&arm_parts));
            }
            let arm_end_line = self.end_line_of(arm_span);
            if let Some(trailing) =
                self.comments
                    .emit_trailing_on_line(&mut self.arena, arm_end_line, next_lim)
            {
                inner.push(trailing);
            }
            prev_end = Some(arm_span.end);
        }
        let (dangling, had_d) =
            self.comments
                .emit_dangling(&mut self.arena, span.end, !arms.is_empty());
        if had_d {
            if arms.is_empty() {
                inner.push(self.arena.hard_line());
            }
            inner.push(dangling);
        }
        let inner_doc = self.arena.concat(&inner);
        parts.push(self.arena.indent(inner_doc));
        parts.push(self.arena.hard_line());
        parts.push(self.arena.text("}"));
        self.arena.concat(&parts)
    }

    fn print_closure(
        &mut self,
        params: &[Parameter],
        obligations: &Obligations,
        body: ExprId,
        span: Span,
    ) -> DocId {
        let mut parts = vec![self.arena.text("\\")];
        for (i, p) in params.iter().enumerate() {
            if i > 0 {
                parts.push(self.arena.text(", "));
            }
            parts.push(self.print_parameter(p));
        }
        let ob_doc = self.print_obligations(obligations, self.ast.expr(body).span.start);
        if ob_doc != self.arena.empty() {
            if !params.is_empty() {
                parts.push(self.arena.text(" "));
            }
            parts.push(ob_doc);
        }
        if !params.is_empty() || ob_doc != self.arena.empty() {
            parts.push(self.arena.text(" "));
        }
        parts.push(self.arena.text("->"));
        let body_is_block = matches!(self.ast.expr(body).value, Expr::Block { .. });
        let body_doc = self.print_expr(body);
        if body_is_block || self.tokens.has_newline_in_span(span) && body_is_block {
            parts.push(self.arena.text(" "));
            parts.push(body_doc);
            self.arena.concat(&parts)
        } else {
            let l = self.arena.line();
            let tail = self.arena.indent_concat(&[l, body_doc]);
            parts.push(tail);
            self.arena.group_concat(&parts)
        }
    }

    fn print_pattern(&mut self, id: PatternId) -> DocId {
        let spanned = self.ast.pattern(id);
        let span = spanned.span;
        let pat = spanned.value.clone();
        let self_is_parens = matches!(pat, Pattern::Unit | Pattern::Tuple(_));
        let pdepth = self.tokens.paren_depth(span, self_is_parens);

        let doc = match pat {
            Pattern::Wildcard => self.arena.text("_"),
            Pattern::Unit => self.arena.text("()"),
            Pattern::Binding(storage, name) => {
                let s = self.print_storage(&storage, true);
                let n = self.arena.owned(name.value);
                self.arena.concat(&[s, n])
            }
            Pattern::Literal(lit) => self.print_literal(&lit),
            Pattern::Or(alts) => {
                // Break AFTER `|` (parser/pattern.rs:15 has no continue_lines before `|`).
                let mut parts = Vec::new();
                for (i, a) in alts.into_iter().enumerate() {
                    if i > 0 {
                        parts.push(self.arena.text(" |"));
                        parts.push(self.arena.line());
                    }
                    parts.push(self.print_pattern(a));
                }
                self.arena.group_concat(&parts)
            }
            Pattern::Tuple(items) => {
                let docs: Vec<(Span, DocId)> = items
                    .iter()
                    .map(|&p| (self.ast.pattern(p).span, self.print_pattern(p)))
                    .collect();
                self.print_delimited_list("(", ")", docs, span.start, span.end, false)
            }
            Pattern::Slice { text, elements } => {
                let open = if text { "str[" } else { "[" };
                let docs: Vec<(Span, DocId)> = elements
                    .iter()
                    .map(|&p| (self.ast.pattern(p).span, self.print_pattern(p)))
                    .collect();
                self.print_delimited_list(open, "]", docs, span.start, span.end, false)
            }
            Pattern::Rest(name) => {
                if let Some(n) = name {
                    let dots = self.arena.text("..");
                    let nd = self.arena.owned(n.value);
                    self.arena.concat(&[dots, nd])
                } else {
                    self.arena.text("..")
                }
            }
            Pattern::Constructor(path, payload) => {
                let p = self.print_path(&path);
                if let Some(args) = payload {
                    let docs: Vec<(Span, DocId)> = args
                        .iter()
                        .map(|&a| (self.ast.pattern(a).span, self.print_pattern(a)))
                        .collect();
                    let list =
                        self.print_delimited_list("(", ")", docs, path.span.end, span.end, false);
                    self.arena.concat(&[p, list])
                } else {
                    p
                }
            }
            Pattern::Wrap(path, args) => {
                let p = self.print_path(&path);
                let col = self.arena.text("::");
                let docs: Vec<(Span, DocId)> = args
                    .iter()
                    .map(|&a| (self.ast.pattern(a).span, self.print_pattern(a)))
                    .collect();
                let list =
                    self.print_delimited_list("(", ")", docs, path.span.end, span.end, false);
                self.arena.concat(&[p, col, list])
            }
            Pattern::Record { fields, rest } => {
                let mut items: Vec<(Span, DocId)> = fields
                    .iter()
                    .map(|f| (f.name.span, self.print_pattern_field(f)))
                    .collect();
                if rest {
                    items.push((
                        Span::new(span.file, span.end.saturating_sub(3), span.end),
                        self.arena.text(".."),
                    ));
                }
                self.print_delimited_list(".{", "}", items, span.start, span.end, true)
            }
            Pattern::Range {
                low,
                high,
                inclusive,
            } => {
                let l = self.print_literal(&low);
                let op = self.arena.text(if inclusive { "..=" } else { ".." });
                let h = self.print_literal(&high);
                self.arena.concat(&[l, op, h])
            }
            Pattern::Subset { ty, binding } => {
                if let Some(b) = binding {
                    let t = self.print_type(ty);
                    let a = self.arena.text(" as ");
                    let bd = self.print_pattern(b);
                    self.arena.concat(&[t, a, bd])
                } else {
                    let dots = self.arena.text("..");
                    let t = self.print_type(ty);
                    self.arena.concat(&[dots, t])
                }
            }
            Pattern::Type(ty_id) => {
                let l = self.arena.text("<");
                let t = self.print_type(ty_id);
                let r = self.arena.text(">");
                self.arena.concat(&[l, t, r])
            }
            Pattern::TypeBinding(name) => {
                let l = self.arena.text("let ");
                let n = self.arena.owned(name.value);
                self.arena.concat(&[l, n])
            }
        };

        self.wrap_parens(doc, pdepth)
    }

    fn print_pattern_field(&mut self, f: &PatternField) -> DocId {
        let mut parts = vec![
            self.print_storage(&f.storage, true),
            self.arena.owned(f.name.value.clone()),
        ];
        if let Some(pat) = f.pattern {
            parts.push(self.arena.text(": "));
            parts.push(self.print_pattern(pat));
        }
        self.arena.concat(&parts)
    }
}
