//! Arena-backed Typed High-Level IR (THIR).
//!
//! Coalesces per-span side tables from `TypedProgram` into per-definition arenas
//! (`Body`) and `typeof e` shadow bodies (`ShadowBody`), and computes exact
//! lexically-resolved closure capture sets (including shorthand record fields,
//! destructured `var` bindings, and transitive local `&up(...)` captures) so
//! downstream lowering does not rely on byte-offset heuristics.

mod build;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use ril_hir::{DefinitionId, DefinitionKind, Resolution, ScopeId};
use ril_source::span::{FileId, Span};
use ril_syntax::syntax::{Mode, Pattern, StmtKind, Storage, Type};

use crate::ty::{Ty, TypedProgram};
use build::BodyBuilder;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ThirExprId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ThirStmtId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ThirPatId(pub u32);

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub definition: DefinitionId,
    pub span: Span,
    pub ty: Ty,
    pub storage: Storage,
    pub boxed: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallTarget {
    Direct(DefinitionId),
    EffectOperation(DefinitionId),
    Primitive(DefinitionId),
    Constructor(DefinitionId),
    Indirect,
}

#[derive(Clone, Debug)]
pub struct ThirExpr {
    pub span: Span,
    pub ty: Ty,
    pub narrowing_depth: usize,
    pub has_static_value: bool,
    pub inspection_scope: Option<ScopeId>,
    pub navigation_ty: Option<Ty>,
    pub propagation_ty: Option<Ty>,
    pub kind: ThirExprKind,
}

#[derive(Clone, Debug)]
pub enum ThirExprKind {
    Unit,
    Literal,
    Local(DefinitionId),
    Global(DefinitionId),
    Call {
        callee: ThirExprId,
        target: CallTarget,
        args: Vec<(Mode, ThirExprId)>,
    },
    Closure {
        captures: Vec<DefinitionId>,
        body: ThirExprId,
    },
    Block {
        stmts: Vec<ThirStmtId>,
        helpers: Vec<ThirStmtId>,
    },
    Record {
        fields: Vec<(String, ThirExprId)>,
    },
    Array(Vec<ThirExprId>),
    Tuple(Vec<ThirExprId>),
    Map(Vec<(ThirExprId, ThirExprId)>),
    Unary {
        op: String,
        value: ThirExprId,
    },
    Binary {
        op: String,
        left: ThirExprId,
        right: ThirExprId,
    },
    Cast {
        value: ThirExprId,
    },
    Pipeline {
        value: ThirExprId,
        mode: Mode,
        target: ThirExprId,
        propagate: bool,
    },
    Member {
        base: ThirExprId,
        safe: bool,
    },
    Index {
        base: ThirExprId,
        index: ThirExprId,
        safe: bool,
    },
    Range {
        start: Option<ThirExprId>,
        end: Option<ThirExprId>,
        inclusive: bool,
    },
    If {
        cond: Option<ThirExprId>,
        yes: ThirExprId,
        no: Option<ThirExprId>,
    },
    While {
        cond: Option<ThirExprId>,
        body: ThirExprId,
    },
    For {
        mode: Mode,
        iterable: ThirExprId,
        pat: ThirPatId,
        body: ThirExprId,
    },
    Match {
        mode: Mode,
        scrutinee: ThirExprId,
        arms: Vec<(ThirPatId, Option<ThirExprId>, ThirExprId)>,
    },
    Interpolated(Vec<ThirExprId>),
    Quote,
    Accessor,
    Transfer(Option<ThirExprId>),
    Hole,
}

#[derive(Clone, Debug)]
pub struct ThirStmt {
    pub span: Span,
    pub kind: ThirStmtKind,
}

#[derive(Clone, Debug)]
pub enum ThirStmtKind {
    Binding {
        pat: ThirPatId,
        storage: Storage,
        value: Option<ThirExprId>,
        fallback: Option<ThirExprId>,
    },
    Resource {
        pat: ThirPatId,
        mode: Mode,
        value: ThirExprId,
        fallback: Option<ThirExprId>,
    },
    With {
        handlers: Vec<ThirExprId>,
    },
    Expr(ThirExprId),
    NestedDecl(DefinitionId),
    Other,
}

#[derive(Clone, Debug)]
pub struct ThirPat {
    pub span: Span,
    pub ty: Ty,
    pub binding: Option<(DefinitionId, Storage)>,
    pub children: Vec<ThirPatId>,
}

/// Arena body for a function, constant, `meta fn`, or type-level helper.
#[derive(Clone, Debug)]
pub struct Body {
    pub owner: DefinitionId,
    pub file: FileId,
    pub exprs: Vec<ThirExpr>,
    pub stmts: Vec<ThirStmt>,
    pub pats: Vec<ThirPat>,
    pub locals: Vec<LocalDecl>,
    pub expr_by_span: HashMap<Span, ThirExprId>,
    pub root_expr: Option<ThirExprId>,
}

impl Body {
    pub fn expr(&self, id: ThirExprId) -> Option<&ThirExpr> {
        self.exprs.get(id.0 as usize)
    }

    pub fn stmt(&self, id: ThirStmtId) -> Option<&ThirStmt> {
        self.stmts.get(id.0 as usize)
    }

    pub fn pat(&self, id: ThirPatId) -> Option<&ThirPat> {
        self.pats.get(id.0 as usize)
    }

    pub fn expr_at(&self, span: Span) -> Option<&ThirExpr> {
        let id = self.expr_by_span.get(&span).copied()?;
        self.expr(id)
    }
}

/// Dedicated shadow THIR body for `typeof e` expressions in type/declaration positions.
#[derive(Clone, Debug)]
pub struct ShadowBody {
    pub span: Span,
    pub file: FileId,
    pub exprs: Vec<ThirExpr>,
    pub stmts: Vec<ThirStmt>,
    pub pats: Vec<ThirPat>,
    pub root: ThirExprId,
}

#[derive(Clone, Debug, Default)]
pub struct ThirProgram {
    pub bodies: BTreeMap<DefinitionId, Body>,
    pub shadow_bodies: BTreeMap<Span, ShadowBody>,
    /// Exact set of `var` local bindings captured by any anonymous closure or local `&up(var x)`.
    pub boxed_var_captures: BTreeSet<DefinitionId>,
    /// Exact pre-resolved referenced definitions for every closure expression span
    /// (including record shorthand fields and transitive local `&up(...)` captures).
    pub closure_references: BTreeMap<Span, BTreeSet<DefinitionId>>,
}

impl ThirProgram {
    pub fn build(typed: &TypedProgram) -> Self {
        let mut program = Self::default();
        let mut all_var_defs: BTreeSet<DefinitionId> = BTreeSet::new();

        // Collect all mutable `var` definitions (both direct and destructured patterns)
        // and all `&up(var x)` clauses on local named functions.
        for file in typed.hir.files() {
            for node in file.ast.patterns() {
                if let Pattern::Binding(storage, name) = &node.value
                    && storage.variable
                    && let Some(Resolution::Definition(id)) = typed.hir.resolve(name.span)
                {
                    all_var_defs.insert(id);
                }
            }
            for node in file.ast.statements() {
                if let StmtKind::Binding {
                    pattern, storage, ..
                } = &node.value.kind
                    && storage.variable
                    && let Pattern::Binding(_, name) = &file.ast.pattern(*pattern).value
                    && let Some(Resolution::Definition(id)) = typed.hir.resolve(name.span)
                {
                    all_var_defs.insert(id);
                }
            }
        }

        // Precompute `&up(...)` clauses of every local named function for transitive capture resolution.
        let mut fn_up_captures: HashMap<DefinitionId, Vec<DefinitionId>> = HashMap::new();
        for (def_id, def) in typed.hir.definitions() {
            let Some(stmt_id) = def.stmt else {
                continue;
            };
            if def.name.span.file == FileId::BUILTIN {
                continue;
            }
            let ast = &typed.hir.file(def.name.span.file).ast;
            if let StmtKind::Function(fun) = &ast.stmt(stmt_id).value.kind {
                let mut ups = Vec::new();
                for (storage, path) in fun
                    .signature
                    .obligations
                    .state
                    .iter()
                    .flat_map(|clause| &clause.bindings)
                {
                    if let Some(Resolution::Definition(target)) = typed.hir.resolve(path.span) {
                        ups.push(target);
                        if storage.variable {
                            program.boxed_var_captures.insert(target);
                        }
                    }
                }
                if !ups.is_empty() {
                    fn_up_captures.insert(def_id, ups);
                }
            }
        }

        // Lower every function and constant body into an Arena `Body`.
        for (def_id, def) in typed.hir.definitions() {
            let Some(stmt_id) = def.stmt else {
                continue;
            };
            let file_id = def.name.span.file;
            if file_id == FileId::BUILTIN {
                continue;
            }
            let ast = &typed.hir.file(file_id).ast;
            match &ast.stmt(stmt_id).value.kind {
                StmtKind::Function(fun) => {
                    if let Some(body_expr) = fun.body {
                        let mut builder = BodyBuilder::new(
                            typed,
                            ast,
                            Some(def_id),
                            file_id,
                            &all_var_defs,
                            &fn_up_captures,
                            &mut program.boxed_var_captures,
                            &mut program.closure_references,
                        );
                        for param in &fun.signature.params {
                            if let Some(default_expr) = param.default {
                                let _ = builder.lower_expr(default_expr, None);
                            }
                            if let Some(name) = &param.name
                                && let Some(Resolution::Definition(pid)) =
                                    typed.hir.resolve(name.span)
                            {
                                builder.record_local(
                                    pid,
                                    name.span,
                                    Storage {
                                        variable: false,
                                        mode: param.mode,
                                        mode_path: None,
                                        bind_mode: false,
                                    },
                                );
                            }
                        }
                        let root = builder.lower_expr(body_expr, None);
                        let body = builder.finish(Some(root));
                        program.bodies.insert(def_id, body);
                    }
                }
                StmtKind::Binding {
                    value: Some(expr), ..
                } if matches!(def.kind, DefinitionKind::Constant) => {
                    let mut builder = BodyBuilder::new(
                        typed,
                        ast,
                        Some(def_id),
                        file_id,
                        &all_var_defs,
                        &fn_up_captures,
                        &mut program.boxed_var_captures,
                        &mut program.closure_references,
                    );
                    let root = builder.lower_expr(*expr, None);
                    let body = builder.finish(Some(root));
                    program.bodies.insert(def_id, body);
                }
                _ => {}
            }
        }

        // Also lower top-level snippet / non-function statements so closures inside snippets
        // populate `boxed_var_captures` and `closure_references`.
        for file in typed.hir.files() {
            let mut builder = BodyBuilder::new(
                typed,
                &file.ast,
                None,
                file.id,
                &all_var_defs,
                &fn_up_captures,
                &mut program.boxed_var_captures,
                &mut program.closure_references,
            );
            for &stmt_id in &file.ast.items {
                if !matches!(
                    file.ast.stmt(stmt_id).value.kind,
                    StmtKind::Function(_)
                        | StmtKind::Type(_)
                        | StmtKind::Effect { .. }
                        | StmtKind::Sub { .. }
                ) {
                    let _ = builder.lower_stmt(stmt_id, None, None);
                }
            }
        }

        // Build explicit `ShadowBody` arenas for all `typeof e` nodes in type positions.
        for file in typed.hir.files() {
            for ty_node in file.ast.types_iter() {
                if let Type::TypeOf(expr_id) = ty_node.value {
                    let mut dummy_boxed = BTreeSet::new();
                    let mut dummy_closures = BTreeMap::new();
                    let mut builder = BodyBuilder::new(
                        typed,
                        &file.ast,
                        None,
                        file.id,
                        &all_var_defs,
                        &fn_up_captures,
                        &mut dummy_boxed,
                        &mut dummy_closures,
                    );
                    let root = builder.lower_expr(expr_id, None);
                    program.shadow_bodies.insert(
                        ty_node.span,
                        ShadowBody {
                            span: ty_node.span,
                            file: file.id,
                            exprs: builder.exprs,
                            stmts: builder.stmts,
                            pats: builder.pats,
                            root,
                        },
                    );
                }
            }
        }

        // Update `boxed` flags on all recorded local declarations.
        for body in program.bodies.values_mut() {
            for local in &mut body.locals {
                local.boxed = program.boxed_var_captures.contains(&local.definition);
            }
        }

        program
    }

    pub fn body(&self, id: DefinitionId) -> Option<&Body> {
        self.bodies.get(&id)
    }
}
