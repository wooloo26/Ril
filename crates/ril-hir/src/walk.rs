use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use ril_source::{
    diag::{Code, Diagnostic},
    span::Span,
};

use ril_syntax::syntax::{
    Ast, Condition, Expr, ExprId, FieldTail, Function, GenericArg, GenericParam, Member, Name,
    Obligations, Parameter, Path, Pattern, PatternId, Signature, StmtId, StmtKind, Storage,
    StringPart, Transfer, Type, TypeDefinition, TypeId, TypeKind, Variant, Visibility,
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
    variants: BTreeMap<String, Vec<DefinitionId>>,
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
                if let Some(cleanup) = &decl.cleanup {
                    self.resolve_name(cleanup);
                }
                match &decl.definition {
                    TypeDefinition::Data(ty) => {
                        if decl.kind == TypeKind::Opaque {
                            self.exposure = Visibility::Private;
                        }
                        self.ty(*ty);
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
            StmtKind::With(handlers) => {
                for handler in handlers {
                    self.path(&handler.operation);
                    self.expr(handler.value);
                }
            }
            StmtKind::Expr(expr) => self.expr(*expr),
            StmtKind::Import(_) | StmtKind::Error => {}
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
            self.expr(body);
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
        let previous = std::mem::replace(&mut self.exposure, Visibility::Private);
        self.expr(expression);
        self.exposure = previous;
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
            if !matches!(effect.segments.as_slice(), [seg] if matches!(seg.name.value.as_str(), "io" | "fiber"))
            {
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
            match self.program.register(
                namespace,
                name.clone(),
                DefinitionKind::Variant(sum),
                item,
                Visibility::Public,
            ) {
                Ok(id) => {
                    if let Some(frame) = self.frames.last_mut() {
                        frame
                            .variants
                            .entry(name.value.clone())
                            .or_default()
                            .push(id);
                    }
                }
                Err(error) => self.errors.push(error),
            }
        }
    }

    fn block(&mut self, statements: &[StmtId], helpers: &[StmtId]) {
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
        for &item in statements {
            self.statement(item);
        }
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
            Expr::Unary { op, value } => {
                if op.value == "?" && self.funcs == 0 {
                    self.report(
                        Code::E0205,
                        op.span,
                        "propagation requires an enclosing function",
                    );
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
            Expr::If { condition, yes, no } => {
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
            Type::Unit | Type::PatternWildcard | Type::PatternLiteral(_) => {}
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
            Pattern::Record { name, fields, .. } => {
                if let Some(name) = name {
                    self.path(name);
                }
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
            Pattern::Type(ty) => self.ty(*ty),
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

    fn resolve_name(&mut self, name: &Name) -> Option<Target> {
        let mut uninitialized = None;
        for frame in self.frames.iter().rev() {
            if let Some(&def) = frame.bound.get(&name.value) {
                let target = Target::Def(def);
                self.record(name, target);
                return Some(target);
            }
            if let Some(variants) = frame.variants.get(&name.value) {
                if let [id] = variants.as_slice() {
                    let target = Target::Def(*id);
                    self.record(name, target);
                    return Some(target);
                }
                self.report(Code::E0206, name.span, "ambiguous local constructor");
                return None;
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
        if let Ok(target) = self
            .program
            .lookup(self.scope, self.program.prelude, name, Code::E0204)
        {
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
        if let Target::Def(def) = target {
            let kind = self.program.definition(def).kind;
            if self.exposure > self.program.definition(def).visibility
                && !matches!(kind, DefinitionKind::Generic | DefinitionKind::Local)
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
