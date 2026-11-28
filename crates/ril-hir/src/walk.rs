use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};

use ril_syntax::syntax::{
    Ast, Condition, Expr, ExprId, FieldTail, Function, GenericArg, GenericParam, Import,
    ImportTarget, Member, Name, Obligations, Parameter, Path, Pattern, PatternId, Signature,
    StmtId, StmtKind, Storage, StringPart, Transfer, Type, TypeDefinition, TypeId, TypeKind,
    Variant, Visibility,
};

use super::{DefinitionId, DefinitionKind, Program, Resolution, ScopeId, Target};

pub(super) fn check(program: &mut Program, errors: &mut Vec<Diagnostic>) {
    let units: Vec<_> = program
        .roots
        .iter()
        .map(|(&file, &scope)| (file, scope))
        .collect();
    for (file, scope) in units {
        let Some(ast) = program
            .files
            .get(&file)
            .map(|source| Arc::clone(&source.ast))
        else {
            continue;
        };
        let mut walk = Walk {
            ast: &ast,
            program,
            errors,
            scope,
            frames: Vec::new(),
            refs: HashMap::new(),
            local_types: HashSet::new(),
            helper: None,
            signature: None,
            exposure: Visibility::Private,
            funcs: 0,
            loops: 0,
            in_barrier: 0,
            fn_top_block: false,
            field_default: false,
        };
        for &item in &ast.items {
            walk.statement(item);
        }
    }
}

#[derive(Clone, Default)]
struct Frame {
    bound: BTreeMap<String, DefinitionId>,
    future: BTreeMap<String, DefinitionId>,
    imported: BTreeMap<String, Target>,
}

struct SignatureBarrier {
    names: HashSet<String>,
    code: Code,
}

struct Walk<'a> {
    ast: &'a Ast,
    program: &'a mut Program,
    errors: &'a mut Vec<Diagnostic>,
    scope: ScopeId,
    frames: Vec<Frame>,
    refs: HashMap<DefinitionId, HashSet<DefinitionId>>,
    local_types: HashSet<DefinitionId>,
    helper: Option<DefinitionId>,
    signature: Option<SignatureBarrier>,
    exposure: Visibility,
    funcs: usize,
    loops: usize,
    in_barrier: usize,
    fn_top_block: bool,
    field_default: bool,
}

impl Walk<'_> {
    fn report(&mut self, code: Code, span: Span, message: impl Into<String>) {
        self.errors.push(Diagnostic::error(code, span, message));
    }

    fn definition_at(&self, span: Span) -> Option<DefinitionId> {
        match self.program.resolve(span) {
            Some(Resolution::Definition(id)) => Some(id),
            _ => None,
        }
    }

    fn declaration_name(&self, item: StmtId) -> Option<&Name> {
        match &self.ast.stmt(item).value.kind {
            StmtKind::Function(fun) => Some(&fun.name),
            StmtKind::Type(decl) => Some(&decl.name),
            StmtKind::Effect { name, .. } | StmtKind::Sub { name, .. } => Some(name),
            _ => None,
        }
    }

    fn declare(
        &mut self,
        name: &Name,
        kind: DefinitionKind,
        stmt: Option<StmtId>,
        defer: bool,
    ) -> DefinitionId {
        if let Some(id) = self.definition_at(name.span) {
            return id;
        }
        let id = self
            .program
            .new_def(self.scope, name.clone(), kind, stmt, Visibility::Private);
        if name.value != "_"
            && let Some(frame) = self.frames.last_mut()
        {
            if matches!(name.value.as_str(), "Type" | "Super")
                || frame.bound.contains_key(&name.value)
                || frame.future.contains_key(&name.value)
            {
                self.report(
                    Code::E0203,
                    name.span,
                    format!("duplicate or protected name {}", name.value),
                );
            } else if defer {
                frame.future.insert(name.value.clone(), id);
            } else {
                frame.bound.insert(name.value.clone(), id);
            }
        }
        id
    }

    fn statement(&mut self, id: StmtId) {
        let stmt = self.ast.stmt(id);
        let previous = self.exposure;
        self.exposure = stmt
            .value
            .visibility
            .min(self.program.scope(self.scope).cap);
        for &attr in &stmt.value.attrs {
            self.expr(attr);
        }
        match &stmt.value.kind {
            StmtKind::Function(fun) => self.function(fun),
            StmtKind::Type(decl) => {
                self.frames.push(Frame::default());
                self.generics(&decl.generics);
                match &decl.definition {
                    TypeDefinition::Data(ty) => {
                        if decl.kind == TypeKind::Opaque {
                            self.exposure = Visibility::Private;
                        }
                        self.ty(*ty);
                        for &guard in &decl.guards {
                            self.guard(guard);
                        }
                    }
                    TypeDefinition::Sum(variants) => {
                        if decl.kind == TypeKind::Opaque {
                            self.exposure = Visibility::Private;
                        }
                        for variant in variants {
                            match variant {
                                Variant::Constructor { payload, attrs, .. } => {
                                    for &attr in attrs {
                                        self.expr(attr);
                                    }
                                    for &ty in payload.iter().flatten() {
                                        self.ty(ty);
                                    }
                                }
                                Variant::Spread(ty) => self.ty(*ty),
                                Variant::Extensible => {}
                            }
                        }
                    }
                    TypeDefinition::Function(params, expr) => {
                        self.generics(params);
                        self.expr(*expr);
                    }
                    TypeDefinition::Opaque => {}
                }
                self.frames.pop();
            }
            StmtKind::Effect {
                name,
                generics,
                operations,
                spreads,
            } => {
                let previous = self.scope;
                if let Some(id) = self.definition_at(name.span)
                    && let DefinitionKind::Effect(scope) = self.program.definition(id).kind
                {
                    self.scope = scope;
                    self.frames.push(Frame::default());
                    self.generics(generics);
                    // Signatures see the declaration scope and the effect parameters.
                    self.scope = previous;
                    for &spread in spreads {
                        self.ty(spread);
                    }
                    for &op in operations {
                        if let StmtKind::Function(fun) = &self.ast.stmt(op).value.kind {
                            self.function(fun);
                        }
                    }
                    self.frames.pop();
                }
                self.scope = previous;
            }
            StmtKind::Sub { name, items } => {
                if let Some(id) = self.definition_at(name.span)
                    && let DefinitionKind::Namespace(scope) = self.program.definition(id).kind
                {
                    let previous = std::mem::replace(&mut self.scope, scope);
                    for &item in items {
                        self.statement(item);
                    }
                    self.scope = previous;
                }
            }
            StmtKind::Binding {
                pattern,
                ty,
                value,
                fallback,
                ..
            } => {
                if let Some(ty) = ty {
                    self.ty(*ty);
                }
                self.exposure = Visibility::Private;
                if let Some(value) = value {
                    self.expr(*value);
                }
                if let Some(fallback) = fallback {
                    self.expr(*fallback);
                }
                self.bind_pattern(*pattern, false);
            }
            StmtKind::Defer(expr) => {
                let prev_funcs = std::mem::take(&mut self.funcs);
                let prev_loops = std::mem::take(&mut self.loops);
                let prev_top = std::mem::replace(&mut self.fn_top_block, false);
                self.in_barrier += 1;
                self.expr(*expr);
                self.in_barrier -= 1;
                self.fn_top_block = prev_top;
                self.loops = prev_loops;
                self.funcs = prev_funcs;
            }
            StmtKind::With(handler) => {
                self.path(&handler.operation);
                let prev_top = std::mem::replace(&mut self.fn_top_block, false);
                self.expr(handler.value);
                self.fn_top_block = prev_top;
            }
            StmtKind::Expr(expr) => self.expr(*expr),
            StmtKind::Import(import) => {
                if !self.frames.is_empty() {
                    self.local_import(import);
                }
            }
            StmtKind::Error => {}
        }
        self.exposure = previous;
    }

    fn function(&mut self, function: &Function) {
        let previous_loops = std::mem::take(&mut self.loops);
        let previous_barrier = self.signature.take();
        let mut below = HashSet::new();
        if let Some(body) = function.body
            && let Expr::Block { helpers, .. } = &self.ast.expr(body).value
        {
            below.extend(
                helpers
                    .iter()
                    .filter_map(|&item| self.declaration_name(item).map(|name| name.value.clone())),
            );
        }
        self.funcs += 1;
        self.frames.push(Frame::default());
        self.generics(&function.generics);
        self.hoist(&function.helpers);
        self.signature = Some(SignatureBarrier {
            names: below.clone(),
            code: Code::E0705,
        });
        for &item in &function.helpers {
            if let Some(name) = self.declaration_name(item)
                && below.contains(&name.value)
            {
                self.report(
                    Code::E0203,
                    name.span,
                    "duplicate declaration across where scopes",
                );
            }
            self.statement(item);
        }
        self.signature = Some(SignatureBarrier {
            names: below,
            code: Code::E0706,
        });
        for parameter in &function.signature.params {
            if let Some(name) = &parameter.name {
                self.declare(name, DefinitionKind::Local, None, false);
            }
        }
        self.signature(&function.signature);
        self.signature = previous_barrier;
        self.exposure = Visibility::Private;
        if let Some(body) = function.body {
            let prev_top = std::mem::replace(&mut self.fn_top_block, true);
            let prev_barrier = std::mem::take(&mut self.in_barrier);
            self.expr(body);
            self.in_barrier = prev_barrier;
            self.fn_top_block = prev_top;
        }
        self.frames.pop();
        self.funcs -= 1;
        self.loops = previous_loops;
    }

    fn signature(&mut self, signature: &Signature) {
        for parameter in &signature.params {
            self.parameter(parameter);
        }
        self.obligations(&signature.obligations);
        self.ty(signature.result);
        for &guard in &signature.guards {
            self.guard(guard);
        }
        for source in &signature.result_sources {
            self.resolve_name(source);
        }
    }

    fn parameter(&mut self, parameter: &Parameter) {
        if let Some(ty) = parameter.ty {
            self.ty(ty);
        }
        for &guard in &parameter.guards {
            self.guard(guard);
        }
        if let Some(value) = parameter.default {
            self.expr(value);
        }
    }

    fn guard(&mut self, expression: ExprId) {
        let is_pascal_head = {
            let mut node = self.ast.expr(expression);
            if let Expr::Unary { op, value } = &node.value
                && op.value == "ref"
            {
                node = self.ast.expr(*value);
            }
            if let Expr::Call { callee, .. } = &node.value {
                node = self.ast.expr(*callee);
            }
            if let Expr::Path(path) = &node.value {
                path.segments.last().is_some_and(|seg| {
                    seg.name
                        .value
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_uppercase())
                })
            } else {
                false
            }
        };
        if is_pascal_head {
            self.expr(expression);
        } else {
            let previous = std::mem::replace(&mut self.exposure, Visibility::Private);
            self.expr(expression);
            self.exposure = previous;
        }
    }

    fn generics(&mut self, parameters: &[GenericParam]) {
        for param in parameters {
            self.declare(&param.name, DefinitionKind::Generic, None, false);
        }
        for param in parameters {
            for &bound in &param.bound {
                self.ty(bound);
            }
            for guard in &param.guards {
                self.path(guard);
            }
            if let Some(default) = &param.default {
                self.argument(default);
            }
        }
    }

    fn obligations(&mut self, obligations: &Obligations) {
        for effect in &obligations.effects {
            if !matches!(effect.segments.as_slice(), [seg] if seg.name.value == "io") {
                let before = self.errors.len();
                self.path(effect);
                if let Some(def) = self.definition_at(effect.span) {
                    if !matches!(self.program.definition(def).kind, DefinitionKind::Effect(_)) {
                        self.report(
                            Code::E0620,
                            effect.span,
                            "effect label must name a declared effect",
                        );
                    }
                } else if self.errors.len() == before
                    || self
                        .errors
                        .get(before)
                        .is_some_and(|diag| diag.code == Some(Code::E0204))
                {
                    self.errors.truncate(before);
                    self.report(
                        Code::E0620,
                        effect.span,
                        "effect label must name a declared effect",
                    );
                }
            }
        }
        for clause in &obligations.state {
            for (mode, binding) in &clause.bindings {
                self.storage(mode);
                if !binding.segments.is_empty() {
                    self.path(binding);
                }
            }
        }
    }

    fn storage(&mut self, storage: &Storage) {
        if let Some(path) = &storage.mode_path {
            self.path(path);
        }
    }

    fn hoist(&mut self, helpers: &[StmtId]) {
        for &item in helpers {
            if let Some(name) = self.declaration_name(item).cloned() {
                let kind = match &self.ast.stmt(item).value.kind {
                    StmtKind::Function(_) => DefinitionKind::Function,
                    StmtKind::Type(declaration) => {
                        if let TypeDefinition::Sum(variants) = &declaration.definition {
                            self.hoist_sum(&name, item, variants);
                            continue;
                        }
                        DefinitionKind::Type
                    }
                    StmtKind::Effect { operations, .. } => {
                        let namespace = self.program.child(self.scope, Visibility::Private, false);
                        let effect = self.declare(
                            &name,
                            DefinitionKind::Effect(namespace),
                            Some(item),
                            false,
                        );
                        self.program.local_effects.insert(effect);
                        for &operation in operations {
                            if let StmtKind::Function(function) =
                                &self.ast.stmt(operation).value.kind
                                && let Err(error) = self.program.register(
                                    namespace,
                                    function.name.clone(),
                                    DefinitionKind::Function,
                                    operation,
                                    Visibility::Public,
                                )
                            {
                                self.errors.push(error);
                            }
                        }
                        continue;
                    }
                    _ => DefinitionKind::Type,
                };
                let id = self.declare(&name, kind, Some(item), false);
                if kind == DefinitionKind::Type {
                    self.local_types.insert(id);
                }
            }
        }
    }

    fn hoist_sum(&mut self, name: &Name, item: StmtId, variants: &[Variant]) {
        let namespace = self.program.child(self.scope, Visibility::Private, false);
        let sum = self.declare(name, DefinitionKind::Sum(namespace), Some(item), false);
        self.local_types.insert(sum);
        for variant in variants {
            let Variant::Constructor { name, .. } = variant else {
                continue;
            };
            if let Err(error) = self.program.register(
                namespace,
                name.clone(),
                DefinitionKind::Variant(sum),
                item,
                Visibility::Public,
            ) {
                self.errors.push(error);
            }
        }
    }

    fn block(&mut self, statements: &[StmtId], helpers: &[StmtId]) {
        let is_fn_top = std::mem::replace(&mut self.fn_top_block, false);
        self.frames.push(Frame::default());
        self.hoist(helpers);
        for &item in statements {
            if let StmtKind::Binding { pattern, .. } = self.ast.stmt(item).value.kind {
                self.reserve_pattern(pattern);
            }
        }
        if !helpers.is_empty() {
            let mut available = self.frames.last().cloned().unwrap_or_default();
            available.bound.append(&mut available.future);
            let saved = self.frames.pop();
            self.frames.push(available);
            for &item in helpers {
                let prev = self.helper;
                self.helper = self
                    .declaration_name(item)
                    .and_then(|name| self.definition_at(name.span));
                self.statement(item);
                self.helper = prev;
            }
            self.frames.pop();
            if let Some(saved) = saved {
                self.frames.push(saved);
            }
        }
        let saved_funcs = self.funcs;
        let saved_loops = self.loops;
        let saved_barrier = self.in_barrier;
        let mut entered_nested_ctl = false;
        for &item in statements {
            if !is_fn_top
                && !entered_nested_ctl
                && matches!(
                    &self.ast.stmt(item).value.kind,
                    StmtKind::With(handler) if handler.is_ctl
                )
            {
                self.statement(item);
                self.funcs = 0;
                self.loops = 0;
                self.in_barrier += 1;
                entered_nested_ctl = true;
            } else {
                self.statement(item);
            }
        }
        self.funcs = saved_funcs;
        self.loops = saved_loops;
        self.in_barrier = saved_barrier;
        self.frames.pop();
    }

    fn expr(&mut self, id: ExprId) {
        let node = self.ast.expr(id);
        match &node.value {
            Expr::Path(path) => self.path(path),
            Expr::Block {
                statements,
                helpers,
            } => self.block(statements, helpers),
            Expr::With {
                handlers,
                statements,
                helpers,
            } => {
                let prev_top = std::mem::replace(&mut self.fn_top_block, false);
                let has_ctl = handlers.iter().any(|handler| handler.is_ctl);
                for handler in handlers {
                    self.path(&handler.operation);
                    self.expr(handler.value);
                }
                if has_ctl {
                    let prev_funcs = std::mem::take(&mut self.funcs);
                    let prev_loops = std::mem::take(&mut self.loops);
                    self.in_barrier += 1;
                    self.block(statements, helpers);
                    self.in_barrier -= 1;
                    self.loops = prev_loops;
                    self.funcs = prev_funcs;
                } else {
                    self.block(statements, helpers);
                }
                self.fn_top_block = prev_top;
            }
            Expr::Unary { op, value } => {
                if op.value == "?" && self.funcs == 0 {
                    if self.in_barrier > 0 {
                        self.report(
                            Code::E0707,
                            op.span,
                            "propagation cannot escape a defer or ctl handler boundary",
                        );
                    } else {
                        self.report(
                            Code::E0205,
                            op.span,
                            "propagation requires an enclosing function",
                        );
                    }
                }
                self.expr(*value);
            }
            Expr::Binary { op, left, right } => {
                self.expr(*left);
                if op.value == "??" && matches!(self.ast.expr(*right).value, Expr::Transfer { .. })
                {
                    self.report(
                        Code::E0710,
                        self.ast.expr(*right).span,
                        "control transfer is prohibited in fallback operands",
                    );
                } else {
                    self.expr(*right);
                }
            }
            Expr::Cast { value, target } => {
                self.expr(*value);
                self.ty(*target);
            }
            Expr::Pipeline { value, target, .. } => {
                self.expr(*value);
                self.expr(*target);
            }
            Expr::Interpolated(parts) => {
                for part in parts {
                    if let StringPart::Interpolation(id) = part {
                        self.expr(*id);
                    }
                }
            }
            Expr::Member { base, member, .. } => {
                self.expr(*base);
                self.member(member);
            }
            Expr::Index { base, index, .. } => {
                self.expr(*base);
                self.expr(*index);
            }
            Expr::Range { start, end, .. } => {
                for &id in start.iter().chain(end) {
                    self.expr(id);
                }
            }
            Expr::Call { callee, args } => {
                self.expr(*callee);
                for argument in args {
                    self.expr(argument.value);
                }
            }
            Expr::Wrap { path, args } => {
                self.path(path);
                for argument in args {
                    self.expr(argument.value);
                }
            }
            Expr::Record { name, fields } => {
                if let Some(name) = name {
                    self.path(name);
                }
                let mut names = HashSet::new();
                for field in fields {
                    if !names.insert(&field.name.value) {
                        self.report(Code::E0210, field.name.span, "duplicate record field");
                    }
                    self.storage(&field.storage);
                    if let Some(value) = field.value {
                        self.expr(value);
                    } else {
                        self.resolve_name(&field.name);
                    }
                }
            }
            Expr::Array(values) | Expr::Tuple(values) => {
                for &value in values {
                    self.expr(value);
                }
            }
            Expr::Map(entries) => {
                for &(key, value) in entries {
                    self.expr(key);
                    self.expr(value);
                }
            }
            Expr::Quote(ty) => self.ty(*ty),
            Expr::Meta(inner) => {
                let prev_funcs = std::mem::take(&mut self.funcs);
                let prev_loops = std::mem::take(&mut self.loops);
                let prev_top = std::mem::replace(&mut self.fn_top_block, false);
                self.in_barrier += 1;
                self.expr(*inner);
                self.in_barrier -= 1;
                self.fn_top_block = prev_top;
                self.loops = prev_loops;
                self.funcs = prev_funcs;
            }
            Expr::If {
                condition, yes, no, ..
            } => {
                self.condition(condition, *yes);
                if let Some(no) = no {
                    self.expr(*no);
                }
            }
            Expr::While { condition, body } => {
                self.loops += 1;
                self.condition(condition, *body);
                self.loops -= 1;
            }
            Expr::For {
                iterable,
                pattern,
                body,
                ..
            } => {
                self.expr(*iterable);
                self.frames.push(Frame::default());
                self.bind_pattern(*pattern, false);
                self.loops += 1;
                self.expr(*body);
                self.loops -= 1;
                self.frames.pop();
            }
            Expr::Match { arms, value, .. } => {
                self.expr(*value);
                for arm in arms {
                    self.frames.push(Frame::default());
                    self.bind_pattern(arm.pattern, false);
                    if let Some(guard) = arm.guard {
                        self.expr(guard);
                    }
                    self.expr(arm.body);
                    self.frames.pop();
                }
            }
            Expr::Closure {
                params,
                obligations,
                body,
            } => {
                let loops = std::mem::take(&mut self.loops);
                self.funcs += 1;
                self.frames.push(Frame::default());
                for parameter in params {
                    self.parameter(parameter);
                    if let Some(pattern) = parameter.pattern {
                        self.bind_pattern(pattern, false);
                    } else if let Some(name) = &parameter.name {
                        self.declare(name, DefinitionKind::Local, None, false);
                    }
                }
                self.obligations(obligations);
                self.expr(*body);
                self.frames.pop();
                self.funcs -= 1;
                self.loops = loops;
            }
            Expr::Accessor(path) => {
                for (_, member) in path {
                    self.member(member);
                }
            }
            Expr::Transfer { kind, value } => {
                if (*kind == Transfer::Return && self.funcs == 0)
                    || (*kind != Transfer::Return && self.loops == 0)
                {
                    self.report(Code::E0707, node.span, "control transfer has no target");
                }
                if let Some(value) = value {
                    self.expr(*value);
                }
            }
            Expr::Literal(_) | Expr::Unit | Expr::Hole => {}
        }
    }

    fn condition(&mut self, condition: &Condition, body: ExprId) {
        self.frames.push(Frame::default());
        match condition {
            Condition::Expr(expr) => self.expr(*expr),
            Condition::Binding { value, pattern, .. } => {
                self.expr(*value);
                self.bind_pattern(*pattern, false);
            }
        }
        self.expr(body);
        self.frames.pop();
    }

    fn member(&mut self, member: &Member) {
        if let Member::Computed(expr) = member {
            self.expr(*expr);
        }
    }

    fn ty(&mut self, id: TypeId) {
        match &self.ast.ty(id).value {
            Type::Named(path) => self.path(path),
            Type::Proof(_) => {}
            Type::PatternBinding(name) => {
                self.declare(name, DefinitionKind::Generic, None, false);
            }
            Type::Tuple(items) => {
                for (mode, id) in items {
                    self.storage(mode);
                    self.ty(*id);
                }
            }
            Type::Array(mode, id) => {
                self.storage(mode);
                self.ty(*id);
            }
            Type::Map(key, mode, value) => {
                self.ty(*key);
                self.storage(mode);
                self.ty(*value);
            }
            Type::Result(ok, err) => {
                self.ty(*ok);
                self.ty(*err);
            }
            Type::Option(id) => self.ty(*id),
            Type::Record { fields, tail } => {
                let defaults = fields.iter().any(|field| field.default.is_some());
                if defaults {
                    self.frames.push(Frame::default());
                    for field in fields {
                        if !self
                            .frames
                            .last()
                            .is_some_and(|frame| frame.future.contains_key(&field.name.value))
                        {
                            self.declare(&field.name, DefinitionKind::Local, None, true);
                        }
                    }
                }
                let mut names = HashSet::new();
                for field in fields {
                    for &attr in &field.attrs {
                        self.expr(attr);
                    }
                    self.storage(&field.storage);
                    if !names.insert(&field.name.value) {
                        self.report(Code::E0210, field.name.span, "duplicate record field");
                    }
                    self.ty(field.ty);
                    if let Some(value) = field.default {
                        let previous = std::mem::replace(&mut self.field_default, true);
                        self.expr(value);
                        self.field_default = previous;
                    }
                    if defaults {
                        self.bind_name(&field.name, false);
                    }
                }
                if defaults {
                    self.frames.pop();
                }
                if let Some(FieldTail::Named(name)) = tail {
                    self.resolve_name(name);
                }
            }
            Type::Mapped {
                storage,
                pattern,
                iterable,
                field,
            } => {
                self.expr(*iterable);
                self.frames.push(Frame::default());
                self.bind_pattern(*pattern, false);
                self.storage(storage);
                self.ty(*field);
                self.frames.pop();
            }
            Type::Callable(signature) => {
                self.frames.push(Frame::default());
                for parameter in &signature.params {
                    if let Some(name) = &parameter.name {
                        self.declare(name, DefinitionKind::Local, None, false);
                    }
                }
                self.signature(signature);
                self.frames.pop();
            }
            Type::Unquote(expr) | Type::TypeOf(expr) => self.expr(*expr),
            Type::Project { base, field } => {
                self.ty(*base);
                self.member(field);
            }
            Type::Unit | Type::TupleAny | Type::PatternWildcard | Type::PatternLiteral(_) => {}
        }
    }

    fn bind_type_pattern_name(&mut self, name: &Name, alias: bool, seen: &mut HashSet<String>) {
        if name.value == "_" {
            return;
        }
        if alias {
            self.resolve_name(name);
            return;
        }
        if !seen.insert(name.value.clone()) {
            self.report(
                Code::E0203,
                name.span,
                format!("duplicate binding {}", name.value),
            );
            return;
        }
        self.declare(name, DefinitionKind::Generic, None, false);
    }

    fn ty_pattern_storage(&mut self, storage: &Storage, alias: bool, seen: &mut HashSet<String>) {
        if storage.bind_mode
            && let Some(path) = &storage.mode_path
            && let [seg] = path.segments.as_slice()
        {
            self.bind_type_pattern_name(&seg.name, alias, seen);
            if let Some(res) = self.program.resolve(seg.name.span) {
                self.program.resolutions.insert(path.span, res);
            }
        } else {
            self.storage(storage);
        }
    }

    fn ty_pattern(&mut self, id: TypeId, alias: bool, seen: &mut HashSet<String>) {
        match &self.ast.ty(id).value {
            Type::PatternBinding(name) => self.bind_type_pattern_name(name, alias, seen),
            Type::Named(path) => {
                // Resolve base path segments, then walk nested generic args as type patterns.
                let mut current = None;
                for (index, segment) in path.segments.iter().enumerate() {
                    for arg in &segment.arguments {
                        match arg {
                            GenericArg::Type(ty) => self.ty_pattern(*ty, alias, seen),
                            GenericArg::Value(expr) => self.expr(*expr),
                            GenericArg::Mode(storage) => {
                                self.ty_pattern_storage(storage, alias, seen);
                            }
                        }
                    }
                    let target = if let Some(prev) = current {
                        let Some(scope) = self.program.namespace(prev) else {
                            self.report(
                                Code::E0204,
                                segment.name.span,
                                format!("cannot access {} here", segment.name.value),
                            );
                            return;
                        };
                        match self
                            .program
                            .lookup(self.scope, scope, &segment.name, Code::E0204)
                        {
                            Ok(found) => found,
                            Err(err) => {
                                self.errors.push(err);
                                return;
                            }
                        }
                    } else if segment.name.value == "Super" {
                        let Some(parent) = self.program.scope(self.scope).parent else {
                            self.report(Code::E0204, segment.name.span, "no parent scope");
                            return;
                        };
                        Target::Module(parent)
                    } else {
                        let Some(found) = self.resolve_name(&segment.name) else {
                            return;
                        };
                        found
                    };
                    let res = match target {
                        Target::Def(def) => Resolution::Definition(def),
                        Target::Module(scope) => Resolution::Module(scope),
                        Target::TypeAndModule(def, scope) => Resolution::TypeAndModule(def, scope),
                    };
                    self.program.resolutions.insert(segment.name.span, res);
                    if index + 1 == path.segments.len() {
                        self.program.resolutions.insert(path.span, res);
                    }
                    current = Some(target);
                }
            }
            Type::Tuple(items) => {
                for (mode, id) in items {
                    self.ty_pattern_storage(mode, alias, seen);
                    self.ty_pattern(*id, alias, seen);
                }
            }
            Type::Array(mode, id) => {
                self.ty_pattern_storage(mode, alias, seen);
                self.ty_pattern(*id, alias, seen);
            }
            Type::Map(key, mode, value) => {
                self.ty_pattern(*key, alias, seen);
                self.ty_pattern_storage(mode, alias, seen);
                self.ty_pattern(*value, alias, seen);
            }
            Type::Result(ok, err) => {
                self.ty_pattern(*ok, alias, seen);
                self.ty_pattern(*err, alias, seen);
            }
            Type::Option(id) => self.ty_pattern(*id, alias, seen),
            Type::Record { fields, tail } => {
                for field in fields {
                    self.ty_pattern_storage(&field.storage, alias, seen);
                    self.ty_pattern(field.ty, alias, seen);
                }
                if let Some(FieldTail::Named(name)) = tail {
                    self.bind_type_pattern_name(name, alias, seen);
                }
            }
            _ => self.ty(id),
        }
    }

    fn bind_pattern(&mut self, id: PatternId, alias: bool) {
        let mut seen = HashSet::new();
        self.bind_pattern_in(id, alias, &mut seen);
    }

    fn bind_pattern_in(&mut self, id: PatternId, alias: bool, seen: &mut HashSet<String>) {
        match &self.ast.pattern(id).value {
            Pattern::Binding(storage, name) => {
                self.storage(storage);
                self.bind_pattern_name(name, alias, seen);
            }
            Pattern::Rest(Some(name)) => self.bind_pattern_name(name, alias, seen),
            Pattern::Tuple(children)
            | Pattern::Slice {
                elements: children, ..
            } => {
                for &item in children {
                    self.bind_pattern_in(item, alias, seen);
                }
            }
            Pattern::Or(children) => {
                let mut combined = seen.clone();
                for (index, &item) in children.iter().enumerate() {
                    let mut branch = seen.clone();
                    self.bind_pattern_in(item, alias || index > 0, &mut branch);
                    combined.extend(branch);
                }
                *seen = combined;
            }
            Pattern::Constructor(path, args) => {
                self.path(path);
                for &arg in args.iter().flatten() {
                    self.bind_pattern_in(arg, alias, seen);
                }
            }
            Pattern::Wrap(path, args) => {
                self.path(path);
                for &arg in args {
                    self.bind_pattern_in(arg, alias, seen);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    self.storage(&field.storage);
                    if let Some(pattern) = field.pattern {
                        self.bind_pattern_in(pattern, alias, seen);
                    } else {
                        self.bind_pattern_name(&field.name, alias, seen);
                    }
                }
            }
            Pattern::Subset { ty, binding } => {
                self.ty(*ty);
                if let Some(binding) = binding {
                    self.bind_pattern_in(*binding, alias, seen);
                }
            }
            Pattern::Type(ty) => self.ty_pattern(*ty, alias, seen),
            Pattern::TypeBinding(name) => {
                self.declare(name, DefinitionKind::Generic, None, false);
            }
            Pattern::Wildcard
            | Pattern::Unit
            | Pattern::Literal(_)
            | Pattern::Range { .. }
            | Pattern::Rest(None) => {}
        }
    }

    fn bind_pattern_name(&mut self, name: &Name, alias: bool, seen: &mut HashSet<String>) {
        if !seen.insert(name.value.clone()) {
            self.report(
                Code::E0347,
                name.span,
                format!("duplicate pattern binding {}", name.value),
            );
            return;
        }
        self.bind_name(name, alias);
    }

    fn bind_name(&mut self, name: &Name, alias: bool) {
        if let Some(frame) = self.frames.last_mut() {
            if let Some(id) = frame.future.remove(&name.value) {
                frame.bound.insert(name.value.clone(), id);
            }
            if alias && let Some(&id) = frame.bound.get(&name.value) {
                self.program
                    .resolutions
                    .insert(name.span, Resolution::Definition(id));
                return;
            }
        }
        self.declare(name, DefinitionKind::Local, None, false);
    }

    fn reserve_pattern(&mut self, id: PatternId) {
        let mut seen = HashSet::new();
        self.reserve_pattern_in(id, &mut seen);
    }

    fn reserve_pattern_in(&mut self, id: PatternId, seen: &mut HashSet<String>) {
        match &self.ast.pattern(id).value {
            Pattern::Binding(_, name) | Pattern::Rest(Some(name)) => {
                if seen.insert(name.value.clone()) {
                    self.declare(name, DefinitionKind::Local, None, true);
                }
            }
            Pattern::Tuple(children)
            | Pattern::Slice {
                elements: children, ..
            } => {
                for &item in children {
                    self.reserve_pattern_in(item, seen);
                }
            }
            Pattern::Or(children) => {
                if let Some(&item) = children.first() {
                    self.reserve_pattern_in(item, seen);
                }
            }
            Pattern::Constructor(_, args) => {
                for &arg in args.iter().flatten() {
                    self.reserve_pattern_in(arg, seen);
                }
            }
            Pattern::Wrap(_, args) => {
                for &arg in args {
                    self.reserve_pattern_in(arg, seen);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    if let Some(pattern) = field.pattern {
                        self.reserve_pattern_in(pattern, seen);
                    } else if seen.insert(field.name.value.clone()) {
                        self.declare(&field.name, DefinitionKind::Local, None, true);
                    }
                }
            }
            Pattern::Subset {
                binding: Some(id), ..
            } => self.reserve_pattern_in(*id, seen),
            _ => {}
        }
    }

    fn argument(&mut self, argument: &GenericArg) {
        match argument {
            GenericArg::Type(ty) => self.ty(*ty),
            GenericArg::Value(expr) => self.expr(*expr),
            GenericArg::Mode(mode) => self.storage(mode),
        }
    }

    fn path(&mut self, path: &Path) {
        let mut parts = path.segments.iter();
        let Some(first) = parts.next() else { return };
        let mut target = if first.name.value == "Super" {
            self.super_scope(self.scope, &first.name)
                .map(Target::Module)
        } else {
            self.resolve_name(&first.name)
        };
        for argument in &first.arguments {
            self.argument(argument);
        }
        for segment in parts {
            target = target.and_then(|current| {
                let Some(namespace) = self.program.namespace(current) else {
                    self.report(
                        Code::E0209,
                        segment.name.span,
                        "qualified name requires a module, sum, or effect",
                    );
                    return None;
                };
                if segment.name.value == "Super" {
                    self.super_scope(namespace, &segment.name)
                        .map(Target::Module)
                } else {
                    match self
                        .program
                        .lookup(self.scope, namespace, &segment.name, Code::E0209)
                    {
                        Ok(target) => {
                            self.record(&segment.name, target);
                            Some(target)
                        }
                        Err(err) => {
                            if self.program.defer_operation(
                                current,
                                self.scope,
                                &segment.name,
                                path,
                                &err,
                            ) {
                                return None;
                            }
                            self.errors.push(err);
                            None
                        }
                    }
                }
            });
            for argument in &segment.arguments {
                self.argument(argument);
            }
        }
        if let Some(target) = target {
            self.program.resolutions.insert(path.span, target.into());
        }
    }

    fn super_scope(&mut self, scope: ScopeId, name: &Name) -> Option<ScopeId> {
        let parent = self.program.scope(scope).parent;
        if parent.is_none() {
            self.report(Code::E0208, name.span, "Super has no enclosing scope");
        }
        parent
    }

    fn local_import(&mut self, import: &Import) {
        let mut namespace = self.scope;
        if let Some(parts) = &import.file {
            let path: std::path::PathBuf = parts.iter().map(|name| name.value.as_str()).collect();
            let anchor = parts
                .first()
                .unwrap_or_else(|| ril_source::ice!("empty import path"));
            let filename = parts.last().unwrap_or(anchor);
            let key = if anchor.value == "pkg" {
                let mut key = std::path::PathBuf::from(&self.program.scope(self.scope).package);
                key.extend(parts.iter().skip(1).map(|name| &name.value));
                key
            } else {
                path.clone()
            };
            let Some(&scope) = self.program.modules.get(&key) else {
                self.report(
                    Code::E0208,
                    filename.span,
                    format!("missing module {}", path.display()),
                );
                return;
            };
            if self.program.scope(scope).package != self.program.scope(self.scope).package
                && self.program.scope(scope).cap < Visibility::Public
            {
                self.report(Code::E0201, filename.span, "module has package visibility");
                return;
            }
            namespace = scope;
        }
        for (index, part) in import.modules.iter().enumerate() {
            if import.file.is_none() && part.value == "Super" {
                let Some(parent) = self.super_scope(namespace, part) else {
                    return;
                };
                namespace = parent;
                continue;
            }
            let target = if import.file.is_none() && index == 0 {
                let Some(target) = self.resolve_name(part) else {
                    return;
                };
                target
            } else {
                match self
                    .program
                    .lookup(self.scope, namespace, part, Code::E0209)
                {
                    Ok(target) => target,
                    Err(err) => {
                        self.errors.push(err);
                        return;
                    }
                }
            };
            let Some(next) = self.program.namespace(target) else {
                self.report(Code::E0208, part.span, "import path does not name a module");
                return;
            };
            namespace = next;
        }
        let import_span = import
            .modules
            .last()
            .or_else(|| import.file.as_ref().and_then(|parts| parts.last()))
            .map_or(Span::new(self.program.scope(self.scope).file, 0, 0), |n| {
                n.span
            });
        if namespace == self.scope
            || (import.file.is_some() && self.program.is_same_or_ancestor(namespace, self.scope))
        {
            self.report(Code::E0208, import_span, "module cannot import itself");
            return;
        }
        self.program
            .record_package_edge(self.scope, namespace, import_span);
        let mut entries: Vec<(Name, Target)> = Vec::new();
        match &import.target {
            ImportTarget::Module(alias) => {
                let name = if let Some(alias) = alias {
                    alias.clone()
                } else if let Some(name) = import.modules.last() {
                    name.clone()
                } else if let Some(filename) = import.file.as_ref().and_then(|parts| parts.last()) {
                    match super::collect::module_name(filename) {
                        Ok(name) => name,
                        Err(err) => {
                            self.errors.push(err);
                            return;
                        }
                    }
                } else {
                    return;
                };
                entries.push((name, Target::Module(namespace)));
            }
            ImportTarget::Items(items) => {
                for (name, alias) in items {
                    match self
                        .program
                        .lookup(self.scope, namespace, name, Code::E0209)
                    {
                        Ok(target) => {
                            if self.program.namespace(target) == Some(self.scope) {
                                self.report(Code::E0208, name.span, "module cannot import itself");
                                continue;
                            }
                            self.program.resolutions.insert(name.span, target.into());
                            entries.push((alias.as_ref().unwrap_or(name).clone(), target));
                        }
                        Err(err) => self.errors.push(err),
                    }
                }
            }
            ImportTarget::Glob => {
                let items: Vec<_> = self
                    .program
                    .scope(namespace)
                    .names
                    .iter()
                    .filter(|(_, entry)| {
                        self.program.namespace(entry.target) != Some(self.scope)
                            && self
                                .program
                                .visible(namespace, self.scope, entry.visibility)
                    })
                    .map(|(name, entry)| (name.clone(), entry.target))
                    .collect();
                let span = import
                    .modules
                    .last()
                    .or_else(|| import.file.as_ref()?.last())
                    .map_or(
                        ril_source::span::Span::new(self.program.scope(self.scope).file, 0, 0),
                        |n| n.span,
                    );
                for (name, target) in items {
                    entries.push((Name::new(name, span), target));
                }
            }
        }
        if let Some(frame) = self.frames.last_mut() {
            for (name, target) in entries {
                if frame.bound.contains_key(&name.value) || frame.imported.contains_key(&name.value)
                {
                    self.errors.push(Diagnostic::error(
                        Code::E0203,
                        name.span,
                        format!("duplicate local binding {}", name.value),
                    ));
                    continue;
                }
                match target {
                    Target::Def(def) => {
                        frame.bound.insert(name.value, def);
                    }
                    other => {
                        frame.imported.insert(name.value, other);
                    }
                }
            }
        }
    }

    fn resolve_name(&mut self, name: &Name) -> Option<Target> {
        let mut uninitialized = None;
        for frame in self.frames.iter().rev() {
            if let Some(&def) = frame.bound.get(&name.value) {
                let target = Target::Def(def);
                self.record(name, target);
                return Some(target);
            }
            if let Some(&target) = frame.imported.get(&name.value) {
                self.record(name, target);
                return Some(target);
            }
            uninitialized = uninitialized.or_else(|| frame.future.get(&name.value));
        }
        match self
            .program
            .lookup(self.scope, self.scope, name, Code::E0204)
        {
            Ok(target) => {
                self.record(name, target);
                return Some(target);
            }
            Err(err) if err.code != Some(Code::E0204) => {
                self.errors.push(err);
                return None;
            }
            Err(_) => {}
        }
        if let Ok(target) = self.program.lookup_prelude(self.scope, name) {
            self.record(name, target);
            return Some(target);
        }
        if let Some(barrier) = &self.signature
            && barrier.names.contains(&name.value)
        {
            self.report(
                barrier.code,
                name.span,
                "signature cannot refer to a block where declaration",
            );
        } else if uninitialized.is_some() {
            self.report(
                if self.field_default {
                    Code::E0408
                } else {
                    Code::E0207
                },
                name.span,
                format!("{} is used before initialization", name.value),
            );
        } else if name.value == "_" {
            self.report(Code::E0322, name.span, "wildcard is not a value");
        } else {
            self.report(
                Code::E0204,
                name.span,
                format!("unresolved name {}", name.value),
            );
        }
        None
    }

    fn record(&mut self, name: &Name, target: Target) {
        self.program.resolutions.insert(name.span, target.into());
        if let Target::Def(def) | Target::TypeAndModule(def, _) = target {
            let kind = self.program.definition(def).kind;
            if self.exposure > self.program.definition(def).visibility
                && !matches!(kind, DefinitionKind::Generic | DefinitionKind::Local)
                && !(matches!(kind, DefinitionKind::Primitive(_) | DefinitionKind::Type)
                    && self.program.is_stdlib_file(name.span.file))
                && !self.local_types.contains(&def)
            {
                self.report(
                    Code::E0910,
                    name.span,
                    format!("{} is less visible than this declaration", name.value),
                );
            }
            if let Some(helper) = self.helper {
                self.refs.entry(helper).or_default().insert(def);
            } else if self.refs.contains_key(&def) && self.captures_pending(def) {
                self.report(
                    Code::E0207,
                    name.span,
                    format!("{} captures a binding before it is initialized", name.value),
                );
            }
        }
    }

    fn captures_pending(&self, helper: DefinitionId) -> bool {
        let mut pending = vec![helper];
        let mut visited = HashSet::new();
        while let Some(def) = pending.pop() {
            if visited.insert(def) {
                if self
                    .frames
                    .iter()
                    .any(|frame| frame.future.values().any(|&local| local == def))
                {
                    return true;
                }
                pending.extend(self.refs.get(&def).into_iter().flatten().copied());
            }
        }
        false
    }
}
