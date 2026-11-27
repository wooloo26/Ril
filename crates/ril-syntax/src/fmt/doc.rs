//! Arena-based Wadler-Lindig pretty-printer IR for `ril fmt`.
//!
//! Zero-config canonical parameters:
//! - Target line width: 100 Unicode scalar columns
//! - Indentation: 4 ASCII spaces
//! - Line endings: LF only, single trailing newline, max 1 consecutive blank line

pub(super) const MAX_WIDTH: usize = 100;
pub(super) const INDENT_WIDTH: usize = 4;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DocId(u32);

pub(super) enum Doc<'src> {
    Empty,
    Text(&'src str),
    Owned(String),
    RawText(&'src str),
    Concat { start: u32, len: u32 },
    Indent(DocId),
    Line,
    SoftLine,
    HardLine,
    BlankLine,
    IfBreak { broken: DocId, flat: DocId },
    Group { body: DocId, force_break: bool },
    LineSuffix(DocId),
    ForceFlat(DocId),
}

pub(super) struct DocArena<'src> {
    nodes: Vec<Doc<'src>>,
    items: Vec<DocId>,
}

impl<'src> DocArena<'src> {
    pub(super) fn new() -> Self {
        let mut arena = Self {
            nodes: Vec::with_capacity(256),
            items: Vec::with_capacity(256),
        };
        arena.nodes.push(Doc::Empty);
        arena
    }

    pub(super) fn empty(&self) -> DocId {
        DocId(0)
    }

    fn push(&mut self, doc: Doc<'src>) -> DocId {
        let id = u32::try_from(self.nodes.len()).unwrap_or(u32::MAX);
        self.nodes.push(doc);
        DocId(id)
    }

    pub(super) fn text(&mut self, s: &'src str) -> DocId {
        if s.is_empty() {
            self.empty()
        } else {
            self.push(Doc::Text(s))
        }
    }

    pub(super) fn owned(&mut self, s: String) -> DocId {
        if s.is_empty() {
            self.empty()
        } else {
            self.push(Doc::Owned(s))
        }
    }

    pub(super) fn raw_text(&mut self, s: &'src str) -> DocId {
        if s.is_empty() {
            self.empty()
        } else {
            self.push(Doc::RawText(s))
        }
    }

    pub(super) fn line(&mut self) -> DocId {
        self.push(Doc::Line)
    }

    pub(super) fn soft_line(&mut self) -> DocId {
        self.push(Doc::SoftLine)
    }

    pub(super) fn hard_line(&mut self) -> DocId {
        self.push(Doc::HardLine)
    }

    pub(super) fn blank_line(&mut self) -> DocId {
        self.push(Doc::BlankLine)
    }

    pub(super) fn indent(&mut self, body: DocId) -> DocId {
        if body == self.empty() {
            body
        } else {
            self.push(Doc::Indent(body))
        }
    }

    pub(super) fn if_break(&mut self, broken: DocId, flat: DocId) -> DocId {
        self.push(Doc::IfBreak { broken, flat })
    }

    pub(super) fn group(&mut self, body: DocId) -> DocId {
        self.push(Doc::Group {
            body,
            force_break: false,
        })
    }

    pub(super) fn group_forced(&mut self, body: DocId, force_break: bool) -> DocId {
        self.push(Doc::Group { body, force_break })
    }

    pub(super) fn line_suffix(&mut self, body: DocId) -> DocId {
        self.push(Doc::LineSuffix(body))
    }

    pub(super) fn force_flat(&mut self, body: DocId) -> DocId {
        self.push(Doc::ForceFlat(body))
    }

    pub(super) fn group_concat(&mut self, parts: &[DocId]) -> DocId {
        let c = self.concat(parts);
        self.group(c)
    }

    pub(super) fn group_concat_forced(&mut self, parts: &[DocId], force_break: bool) -> DocId {
        let c = self.concat(parts);
        self.group_forced(c, force_break)
    }

    pub(super) fn indent_concat(&mut self, parts: &[DocId]) -> DocId {
        let c = self.concat(parts);
        self.indent(c)
    }

    pub(super) fn concat(&mut self, parts: &[DocId]) -> DocId {
        let mut non_empty: Vec<DocId> = Vec::with_capacity(parts.len());
        for &part in parts {
            if part != self.empty() {
                non_empty.push(part);
            }
        }
        match non_empty.as_slice() {
            [] => self.empty(),
            [single] => *single,
            _ => {
                let start = u32::try_from(self.items.len()).unwrap_or(u32::MAX);
                let len = u32::try_from(non_empty.len()).unwrap_or(0);
                self.items.extend_from_slice(&non_empty);
                self.push(Doc::Concat { start, len })
            }
        }
    }

    fn get(&self, id: DocId) -> &Doc<'src> {
        self.nodes.get(id.0 as usize).unwrap_or(&Doc::Empty)
    }

    fn slice(&self, start: u32, len: u32) -> &[DocId] {
        let s = start as usize;
        let e = s.saturating_add(len as usize);
        self.items.get(s..e).unwrap_or(&[])
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Mode {
    Flat,
    Break,
    ForceFlat,
}

#[derive(Clone, Copy)]
struct Cmd {
    indent: usize,
    mode: Mode,
    doc: DocId,
}

fn fits(arena: &DocArena<'_>, mut remaining: isize, initial: &[Cmd], extra: Cmd) -> bool {
    let mut stack: Vec<Cmd> = Vec::with_capacity(32);
    stack.push(extra);
    let mut next_outer = initial.len();

    while remaining >= 0 {
        let cmd = if let Some(cmd) = stack.pop() {
            cmd
        } else if next_outer > 0 {
            next_outer -= 1;
            let Some(&outer) = initial.get(next_outer) else {
                return true;
            };
            outer
        } else {
            return true;
        };

        match arena.get(cmd.doc) {
            Doc::Empty => {}
            Doc::Text(s) => {
                remaining -= isize::try_from(s.chars().count()).unwrap_or(isize::MAX);
            }
            Doc::Owned(s) => {
                remaining -= isize::try_from(s.chars().count()).unwrap_or(isize::MAX);
            }
            Doc::RawText(s) => {
                if let Some(first_nl) = s.find('\n') {
                    let prefix = s.get(..first_nl).unwrap_or(s);
                    remaining -= isize::try_from(prefix.chars().count()).unwrap_or(isize::MAX);
                    // Multi-line raw literal forces breaking if we are still checking the group.
                    return if cmd.mode == Mode::ForceFlat {
                        remaining >= 0
                    } else {
                        false
                    };
                }
                remaining -= isize::try_from(s.chars().count()).unwrap_or(isize::MAX);
            }
            Doc::Concat { start, len } => {
                for &child in arena.slice(*start, *len).iter().rev() {
                    stack.push(Cmd {
                        indent: cmd.indent,
                        mode: cmd.mode,
                        doc: child,
                    });
                }
            }
            Doc::Indent(inner) => {
                stack.push(Cmd {
                    indent: cmd.indent + INDENT_WIDTH,
                    mode: cmd.mode,
                    doc: *inner,
                });
            }
            Doc::Line => match cmd.mode {
                Mode::Flat | Mode::ForceFlat => remaining -= 1,
                Mode::Break => return true,
            },
            Doc::SoftLine => match cmd.mode {
                Mode::Flat | Mode::ForceFlat => {}
                Mode::Break => return true,
            },
            Doc::HardLine | Doc::BlankLine => {
                return cmd.mode == Mode::Break;
            }
            Doc::IfBreak { broken, flat } => {
                let target = match cmd.mode {
                    Mode::Break => *broken,
                    Mode::Flat | Mode::ForceFlat => *flat,
                };
                stack.push(Cmd {
                    indent: cmd.indent,
                    mode: cmd.mode,
                    doc: target,
                });
            }
            Doc::Group { body, force_break } => {
                if *force_break && cmd.mode != Mode::ForceFlat {
                    return false;
                }
                let child_mode = if cmd.mode == Mode::ForceFlat {
                    Mode::ForceFlat
                } else {
                    Mode::Flat
                };
                stack.push(Cmd {
                    indent: cmd.indent,
                    mode: child_mode,
                    doc: *body,
                });
            }
            Doc::LineSuffix(_) => {
                // A trailing comment suffix always forces the enclosing group to break.
                if cmd.mode == Mode::Flat {
                    return false;
                }
            }
            Doc::ForceFlat(inner) => {
                stack.push(Cmd {
                    indent: cmd.indent,
                    mode: Mode::ForceFlat,
                    doc: *inner,
                });
            }
        }
    }
    false
}

pub(super) fn render(arena: &DocArena<'_>, root: DocId) -> String {
    let mut out = String::with_capacity(1024);
    let mut col: usize = 0;
    let mut emitted_any = false;
    let mut pending_newlines: usize = 0;
    let mut pending_indent: usize = 0;
    let mut line_suffixes: Vec<(usize, DocId)> = Vec::new();
    let mut stack = vec![Cmd {
        indent: 0,
        mode: Mode::Break,
        doc: root,
    }];

    let flush_pending_newlines = |out: &mut String,
                                  col: &mut usize,
                                  emitted_any: bool,
                                  pending_newlines: &mut usize,
                                  pending_indent: usize| {
        if *pending_newlines == 0 {
            return;
        }
        if emitted_any {
            // Strip any accidental trailing spaces before emitting line break.
            while out.ends_with(' ') {
                out.pop();
            }
            let count = (*pending_newlines).min(2);
            for _ in 0..count {
                out.push('\n');
            }
            for _ in 0..pending_indent {
                out.push(' ');
            }
            *col = pending_indent;
        }
        *pending_newlines = 0;
    };

    while let Some(cmd) = stack.pop() {
        match arena.get(cmd.doc) {
            Doc::Empty => {}
            Doc::Text(s) => {
                flush_pending_newlines(
                    &mut out,
                    &mut col,
                    emitted_any,
                    &mut pending_newlines,
                    pending_indent,
                );
                out.push_str(s);
                col += s.chars().count();
                emitted_any = true;
            }
            Doc::Owned(s) => {
                flush_pending_newlines(
                    &mut out,
                    &mut col,
                    emitted_any,
                    &mut pending_newlines,
                    pending_indent,
                );
                out.push_str(s);
                col += s.chars().count();
                emitted_any = true;
            }
            Doc::RawText(s) => {
                flush_pending_newlines(
                    &mut out,
                    &mut col,
                    emitted_any,
                    &mut pending_newlines,
                    pending_indent,
                );
                out.push_str(s);
                if let Some(last_nl) = s.rfind('\n') {
                    let tail = s.get(last_nl + 1..).unwrap_or("");
                    col = tail.chars().count();
                } else {
                    col += s.chars().count();
                }
                emitted_any = true;
            }
            Doc::Concat { start, len } => {
                for &child in arena.slice(*start, *len).iter().rev() {
                    stack.push(Cmd {
                        indent: cmd.indent,
                        mode: cmd.mode,
                        doc: child,
                    });
                }
            }
            Doc::Indent(inner) => {
                stack.push(Cmd {
                    indent: cmd.indent + INDENT_WIDTH,
                    mode: cmd.mode,
                    doc: *inner,
                });
            }
            Doc::Line => match cmd.mode {
                Mode::Flat | Mode::ForceFlat => {
                    flush_pending_newlines(
                        &mut out,
                        &mut col,
                        emitted_any,
                        &mut pending_newlines,
                        pending_indent,
                    );
                    out.push(' ');
                    col += 1;
                    emitted_any = true;
                }
                Mode::Break => {
                    if !line_suffixes.is_empty() {
                        // Re-queue this newline after flushing all pending line suffixes.
                        stack.push(cmd);
                        for (suffix_indent, suffix_doc) in line_suffixes.drain(..).rev() {
                            stack.push(Cmd {
                                indent: suffix_indent,
                                mode: Mode::ForceFlat,
                                doc: suffix_doc,
                            });
                        }
                    } else if emitted_any {
                        pending_newlines = pending_newlines.max(1);
                        pending_indent = cmd.indent;
                    }
                }
            },
            Doc::SoftLine => match cmd.mode {
                Mode::Flat | Mode::ForceFlat => {}
                Mode::Break => {
                    if !line_suffixes.is_empty() {
                        stack.push(cmd);
                        for (suffix_indent, suffix_doc) in line_suffixes.drain(..).rev() {
                            stack.push(Cmd {
                                indent: suffix_indent,
                                mode: Mode::ForceFlat,
                                doc: suffix_doc,
                            });
                        }
                    } else if emitted_any {
                        pending_newlines = pending_newlines.max(1);
                        pending_indent = cmd.indent;
                    }
                }
            },
            Doc::HardLine => {
                if !line_suffixes.is_empty() {
                    stack.push(cmd);
                    for (suffix_indent, suffix_doc) in line_suffixes.drain(..).rev() {
                        stack.push(Cmd {
                            indent: suffix_indent,
                            mode: Mode::ForceFlat,
                            doc: suffix_doc,
                        });
                    }
                } else if emitted_any {
                    pending_newlines = pending_newlines.max(1);
                    pending_indent = cmd.indent;
                }
            }
            Doc::BlankLine => {
                if !line_suffixes.is_empty() {
                    stack.push(cmd);
                    for (suffix_indent, suffix_doc) in line_suffixes.drain(..).rev() {
                        stack.push(Cmd {
                            indent: suffix_indent,
                            mode: Mode::ForceFlat,
                            doc: suffix_doc,
                        });
                    }
                } else if emitted_any {
                    pending_newlines = 2;
                    pending_indent = cmd.indent;
                }
            }
            Doc::IfBreak { broken, flat } => {
                let target = match cmd.mode {
                    Mode::Break => *broken,
                    Mode::Flat | Mode::ForceFlat => *flat,
                };
                stack.push(Cmd {
                    indent: cmd.indent,
                    mode: cmd.mode,
                    doc: target,
                });
            }
            Doc::Group { body, force_break } => {
                let mode = if cmd.mode == Mode::ForceFlat {
                    Mode::ForceFlat
                } else if *force_break {
                    Mode::Break
                } else {
                    let effective_col = if pending_newlines > 0 {
                        pending_indent
                    } else {
                        col
                    };
                    let remaining = isize::try_from(MAX_WIDTH).unwrap_or(100)
                        - isize::try_from(effective_col).unwrap_or(0);
                    let probe = Cmd {
                        indent: cmd.indent,
                        mode: Mode::Flat,
                        doc: *body,
                    };
                    if fits(arena, remaining, &stack, probe) {
                        Mode::Flat
                    } else {
                        Mode::Break
                    }
                };
                stack.push(Cmd {
                    indent: cmd.indent,
                    mode,
                    doc: *body,
                });
            }
            Doc::LineSuffix(suffix) => {
                line_suffixes.push((cmd.indent, *suffix));
            }
            Doc::ForceFlat(inner) => {
                stack.push(Cmd {
                    indent: cmd.indent,
                    mode: Mode::ForceFlat,
                    doc: *inner,
                });
            }
        }

        // Flush any remaining line suffixes when the stack reaches EOF.
        if stack.is_empty() && !line_suffixes.is_empty() {
            for (suffix_indent, suffix_doc) in line_suffixes.drain(..).rev() {
                stack.push(Cmd {
                    indent: suffix_indent,
                    mode: Mode::ForceFlat,
                    doc: suffix_doc,
                });
            }
        }
    }

    while out.ends_with([' ', '\n']) {
        out.pop();
    }
    if !out.is_empty() {
        out.push('\n');
    }
    out
}
