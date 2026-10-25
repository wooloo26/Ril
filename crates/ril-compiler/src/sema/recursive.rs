//! Source-derived, finite summaries consumed at recursive call cutoffs.
//!
//! Whole aggregate alternatives stay aligned. A least fixed point starts with
//! no normal returns; that bottom is never an authority or freshness proof.
//! Recursive construction of growing reference graphs and projected recursive
//! arguments require regular shape ports and remain explicitly incomplete.
use super::{
    facts::{Permission, Slot},
    summary::Access,
};
use ril_compiler_core::ids::DefinitionId;
use ril_syntax::ast::*;
use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
#[cfg(test)]
#[path = "recursive_fixture.rs"]
pub(crate) mod review_fixture;

pub type FunctionKey = DefinitionId;
pub type Site = (u32, u32, u32);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Port {
    pub parameter: u32,
    pub path: Vec<Slot>,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AccessPort {
    pub port: Port,
    pub slot: Option<Slot>,
    pub access: Access,
}
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CallbackPort {
    pub parameter: u32,
    pub path: Vec<Slot>,
    pub arguments: Vec<Port>,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ScalarKind {
    Bool,
    Integer,
    Float,
    String,
    Bytes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reception {
    Construction,
    Immutable,
    Readonly,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ReturnValue {
    Bottom,
    Unknown,
    Unit,
    Scalar(ScalarKind),
    Parameter {
        port: Port,
        permission: Permission,
    },
    Global {
        name: String,
        path: Vec<Slot>,
        permission: Permission,
    },
    Clone {
        source: Port,
        site: Site,
        immutable: bool,
        reception: Reception,
    },
    Tuple {
        site: Site,
        items: Vec<ReturnValue>,
        reception: Reception,
    },
    Record {
        site: Site,
        type_name: Option<String>,
        fields: BTreeMap<String, ReturnValue>,
        field_modes: BTreeMap<String, bool>,
        reception: Reception,
    },
    Alternatives(Vec<ReturnValue>),
}
impl ReturnValue {
    pub fn join(self, other: Self) -> Self {
        if self == other {
            return self;
        }
        if self == Self::Unknown || other == Self::Unknown {
            return Self::Unknown;
        }
        if self == Self::Bottom {
            return other;
        }
        if other == Self::Bottom {
            return self;
        }
        let mut alternatives = BTreeSet::new();
        for value in [self, other] {
            match value {
                Self::Alternatives(values) => alternatives.extend(values),
                value => {
                    alternatives.insert(value);
                }
            }
        }
        Self::Alternatives(alternatives.into_iter().collect())
    }
    fn contains_site(&self, target: Site) -> bool {
        match self {
            Self::Tuple { site, items, .. } => {
                *site == target || items.iter().any(|value| value.contains_site(target))
            }
            Self::Record { site, fields, .. } => {
                *site == target || fields.values().any(|value| value.contains_site(target))
            }
            Self::Alternatives(values) => values.iter().any(|value| value.contains_site(target)),
            _ => false,
        }
    }
    fn project(self, slot: &Slot) -> Self {
        match self {
            Self::Parameter {
                mut port,
                permission,
            } => {
                port.path.push(slot.clone());
                Self::Parameter { port, permission }
            }
            Self::Global {
                name,
                mut path,
                permission,
            } => {
                path.push(slot.clone());
                Self::Global {
                    name,
                    path,
                    permission,
                }
            }
            Self::Tuple { items, .. } => {
                if let Slot::Tuple(index) = slot {
                    items.get(*index as usize).cloned().unwrap_or(Self::Unknown)
                } else {
                    Self::Unknown
                }
            }
            Self::Record { fields, .. } => {
                if let Slot::Field(name) = slot {
                    fields.get(name).cloned().unwrap_or(Self::Unknown)
                } else {
                    Self::Unknown
                }
            }
            Self::Alternatives(values) => values
                .into_iter()
                .map(|value| value.project(slot))
                .fold(Self::Bottom, Self::join),
            Self::Bottom => Self::Bottom,
            _ => Self::Unknown,
        }
    }
    fn substitute(&self, arguments: &[ReturnValue]) -> Self {
        match self {
            Self::Parameter { port, permission } => {
                let mut value = arguments
                    .get(port.parameter as usize)
                    .cloned()
                    .unwrap_or(Self::Unknown);
                for slot in &port.path {
                    value = value.project(slot);
                }
                value.restrict(*permission);
                value
            }
            Self::Clone {
                source,
                site,
                immutable,
                reception,
            } => {
                let value = Self::Parameter {
                    port: source.clone(),
                    permission: Permission::Read,
                }
                .substitute(arguments);
                match value {
                    Self::Bottom => Self::Bottom,
                    Self::Parameter { port, .. } => Self::Clone {
                        source: port,
                        site: *site,
                        immutable: *immutable,
                        reception: *reception,
                    },
                    _ => Self::Unknown,
                }
            }
            Self::Tuple {
                site,
                items,
                reception,
            } => {
                let items: Vec<_> = items
                    .iter()
                    .map(|value| value.substitute(arguments))
                    .collect();
                if items.iter().any(|value| value.contains_site(*site)) {
                    Self::Unknown
                } else {
                    Self::Tuple {
                        site: *site,
                        items,
                        reception: *reception,
                    }
                }
            }
            Self::Record {
                site,
                type_name,
                fields,
                field_modes,
                reception,
            } => {
                let fields: BTreeMap<_, _> = fields
                    .iter()
                    .map(|(name, value)| (name.clone(), value.substitute(arguments)))
                    .collect();
                if fields.values().any(|value| value.contains_site(*site)) {
                    Self::Unknown
                } else {
                    Self::Record {
                        site: *site,
                        type_name: type_name.clone(),
                        fields,
                        field_modes: field_modes.clone(),
                        reception: *reception,
                    }
                }
            }
            Self::Alternatives(values) => values
                .iter()
                .map(|value| value.substitute(arguments))
                .fold(Self::Bottom, Self::join),
            value => value.clone(),
        }
    }
    fn restrict(&mut self, permission: Permission) {
        match self {
            Self::Parameter {
                permission: actual, ..
            }
            | Self::Global {
                permission: actual, ..
            } => *actual = actual.meet(permission),
            Self::Tuple {
                items, reception, ..
            } => {
                if permission == Permission::Read && *reception == Reception::Construction {
                    *reception = Reception::Readonly;
                }
                for value in items {
                    value.restrict(permission)
                }
            }
            Self::Record {
                fields, reception, ..
            } => {
                if permission == Permission::Read && *reception == Reception::Construction {
                    *reception = Reception::Readonly;
                }
                for value in fields.values_mut() {
                    value.restrict(permission)
                }
            }
            Self::Clone { reception, .. } => {
                if permission == Permission::Read && *reception == Reception::Construction {
                    *reception = Reception::Readonly;
                }
            }
            Self::Alternatives(items) => {
                for value in items {
                    value.restrict(permission)
                }
            }
            _ => {}
        }
    }
    fn publish_immutable(&mut self) {
        match self {
            Self::Clone { reception, .. } => *reception = Reception::Immutable,
            Self::Tuple {
                reception, items, ..
            } => {
                *reception = Reception::Immutable;
                for value in items {
                    value.publish_immutable()
                }
            }
            Self::Record {
                reception, fields, ..
            } => {
                *reception = Reception::Immutable;
                for value in fields.values_mut() {
                    value.publish_immutable()
                }
            }
            Self::Alternatives(items) => {
                for value in items {
                    value.publish_immutable()
                }
            }
            _ => {}
        }
    }
    fn finish_permissions(&mut self, parameters: &[Parameter]) {
        match self {
            Self::Parameter { port, permission } => {
                if parameters
                    .get(port.parameter as usize)
                    .is_none_or(|parameter| parameter.mode != ParameterMode::SharedMut)
                {
                    *permission = Permission::Read;
                }
            }
            Self::Tuple { items, .. } | Self::Alternatives(items) => {
                for value in items {
                    value.finish_permissions(parameters)
                }
            }
            Self::Record { fields, .. } => {
                for value in fields.values_mut() {
                    value.finish_permissions(parameters)
                }
            }
            _ => {}
        }
    }
    fn has_unknown(&self) -> bool {
        match self {
            Self::Unknown => true,
            Self::Tuple { items, .. } | Self::Alternatives(items) => {
                items.iter().any(Self::has_unknown)
            }
            Self::Record { fields, .. } => fields.values().any(Self::has_unknown),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Summary {
    pub complete: bool,
    pub productive: bool,
    pub return_value: ReturnValue,
    pub accesses: BTreeSet<AccessPort>,
    pub callbacks: BTreeSet<CallbackPort>,
    /// Equality eligibility is a use of these inputs, even when a recursive
    /// application obtains its answer from the fixed point instead of a body.
    pub equality_inputs: BTreeSet<ReturnValue>,
    pub effects: BTreeSet<String>,
    pub named: BTreeMap<String, Access>,
    pub reason: Option<String>,
}
impl Default for Summary {
    fn default() -> Self {
        Self {
            complete: true,
            productive: false,
            return_value: ReturnValue::Bottom,
            accesses: BTreeSet::new(),
            callbacks: BTreeSet::new(),
            equality_inputs: BTreeSet::new(),
            effects: BTreeSet::new(),
            named: BTreeMap::new(),
            reason: None,
        }
    }
}
impl Summary {
    fn incomplete(&mut self, reason: impl Into<String>) {
        self.complete = false;
        if self.reason.is_none() {
            self.reason = Some(reason.into());
        }
    }
    fn include(&mut self, other: &Self) {
        self.complete &= other.complete;
        self.accesses.extend(other.accesses.iter().cloned());
        self.callbacks.extend(other.callbacks.iter().cloned());
        self.equality_inputs
            .extend(other.equality_inputs.iter().cloned());
        self.effects.extend(other.effects.iter().cloned());
        for (name, access) in &other.named {
            self.named
                .entry(name.clone())
                .and_modify(|mode| *mode = (*mode).max(*access))
                .or_insert(*access);
        }
        if self.reason.is_none() {
            self.reason = other.reason.clone();
        }
    }
}
#[derive(Debug, Clone, Default)]
pub struct Analysis {
    pub summaries: BTreeMap<FunctionKey, Summary>,
}
pub fn site_span(site: Site) -> ril_compiler_core::source::Span {
    ril_compiler_core::source::Span {
        file: ril_compiler_core::source::FileId(site.0),
        start: site.1,
        end: site.2,
    }
}
fn site(expr: &Expr) -> Site {
    (expr.span.file.0, expr.span.start, expr.span.end)
}

/// The transfer never unrolls recursive frames. Calls compose canonical ports;
/// unsupported port/shape growth becomes Unknown rather than a proof by cutoff.
/// Callers supply canonical declaration identities, independent of diagnostic
/// spans. Repeated registrations require the same original symbolic syntax;
/// differing instances of one identity cannot provide a declaration summary.
pub fn analyze<'a>(functions: impl IntoIterator<Item = (DefinitionId, &'a Function)>) -> Analysis {
    let work = Cell::new(4_000_000usize);
    let mut by_name = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    let mut declared_names = BTreeSet::new();
    let mut by_key = BTreeMap::new();
    let mut conflicting = BTreeSet::new();
    for (definition, function) in functions {
        declared_names.insert(function.name.clone());
        if by_name
            .insert(function.name.clone(), definition)
            .is_some_and(|previous| previous != definition)
        {
            ambiguous.insert(function.name.clone());
        }
        // Repeated semantic instances may share the original symbolic syntax,
        // but a substituted instance must never stand in for its declaration.
        if let Some(previous) = by_key.get(&definition) {
            if *previous != function {
                conflicting.insert(definition);
            }
        } else {
            by_key.insert(definition, function);
        }
    }
    for name in ambiguous {
        by_name.remove(&name);
    }
    let mut summaries: BTreeMap<_, _> = by_key
        .keys()
        .map(|key| {
            let mut summary = Summary::default();
            if conflicting.contains(key) {
                summary.return_value = ReturnValue::Unknown;
                summary.incomplete(
                    "recursive declaration identity has conflicting symbolic or instantiated syntax",
                );
            }
            (*key, summary)
        })
        .collect();
    let mut dependencies: BTreeMap<FunctionKey, BTreeSet<FunctionKey>> = BTreeMap::new();
    let mut queue: VecDeque<_> = by_key
        .keys()
        .filter(|key| !conflicting.contains(key))
        .copied()
        .collect();
    let mut queued: BTreeSet<_> = queue.iter().copied().collect();
    while let Some(current) = queue.pop_front() {
        let Some(remaining) = work.get().checked_sub(1) else {
            for summary in summaries.values_mut() {
                summary.incomplete("recursive summary work exhausted");
            }
            break;
        };
        work.set(remaining);
        queued.remove(&current);
        let function = by_key[&current];
        let mut transfer = Transfer {
            work: &work,
            function,
            by_name: &by_name,
            declared_names: &declared_names,
            by_key: &by_key,
            summaries: &summaries,
            summary: Summary::default(),
            dependencies: BTreeSet::new(),
            returns: ReturnValue::Bottom,
            default_scope: false,
        };
        let mut environment = BTreeMap::new();
        for (index, parameter) in function.parameters.iter().enumerate() {
            let value = ReturnValue::Parameter {
                port: Port {
                    parameter: index as u32,
                    path: vec![],
                },
                permission: if parameter.mode == ParameterMode::Read {
                    Permission::Read
                } else {
                    Permission::Write
                },
            };
            transfer.bind(&parameter.pattern, value, &mut environment);
        }
        let normal = if let Some(body) = &function.body {
            transfer.block(body, &mut environment)
        } else {
            transfer
                .summary
                .incomplete("bodyless recursive dependency has no verified return relation");
            ReturnValue::Unknown
        };
        let mut next = transfer.summary;
        next.return_value = normal.join(transfer.returns);
        next.return_value.finish_permissions(&function.parameters);
        if next.return_value.has_unknown() {
            next.incomplete("recursive return ports or graph construction are unresolved");
        }
        next.productive =
            next.return_value != ReturnValue::Bottom && next.return_value != ReturnValue::Unknown;
        dependencies.insert(current, transfer.dependencies);
        let old = &summaries[&current];
        next.return_value = old.return_value.clone().join(next.return_value);
        next.include(old);
        next.productive =
            next.return_value != ReturnValue::Bottom && next.return_value != ReturnValue::Unknown;
        if &next != old {
            summaries.insert(current, next);
            for candidate in by_key.keys() {
                if dependencies
                    .get(candidate)
                    .is_some_and(|callees| callees.contains(&current))
                    && queued.insert(*candidate)
                {
                    queue.push_back(*candidate);
                }
            }
        }
    }
    // Unseeded SCCs retain an unresolved return, not vacuous fresh/empty proofs.
    let mut changed = true;
    while changed {
        changed = false;
        for current in by_key.keys() {
            let unresolved = summaries[current].return_value == ReturnValue::Bottom
                || dependencies.get(current).is_some_and(|callees| {
                    callees.iter().any(|callee| !summaries[callee].complete)
                });
            if unresolved && summaries[current].complete {
                let summary = summaries.get_mut(current).unwrap();
                summary.incomplete("recursive dependency has no established normal-return proof");
                if summary.return_value == ReturnValue::Bottom {
                    summary.return_value = ReturnValue::Unknown;
                }
                changed = true;
            }
        }
    }
    Analysis { summaries }
}

type Environment = BTreeMap<String, ReturnValue>;
struct Transfer<'a, 'w> {
    work: &'w Cell<usize>,
    function: &'a Function,
    by_name: &'a BTreeMap<String, FunctionKey>,
    declared_names: &'a BTreeSet<String>,
    by_key: &'a BTreeMap<FunctionKey, &'a Function>,
    summaries: &'a BTreeMap<FunctionKey, Summary>,
    summary: Summary,
    dependencies: BTreeSet<FunctionKey>,
    returns: ReturnValue,
    // A default sees only preceding callee formals and its own locals. The
    // analysis input has no declaration capture environment for free values.
    default_scope: bool,
}
impl Transfer<'_, '_> {
    fn equality_input(&mut self, value: &ReturnValue) {
        let cost = match value {
            ReturnValue::Parameter { port, .. } => 1 + port.path.len(),
            ReturnValue::Global { name, path, .. } => 1 + name.len() + path.len(),
            _ => 1,
        };
        let Some(remaining) = self.work.get().checked_sub(cost) else {
            self.summary.incomplete("recursive equality work exhausted");
            return;
        };
        self.work.set(remaining);
        match value {
            ReturnValue::Parameter { .. } | ReturnValue::Global { .. } => {
                let mut input = value.clone();
                input.restrict(Permission::Read);
                self.summary.equality_inputs.insert(input);
            }
            ReturnValue::Clone { source, .. } => self.equality_input(&ReturnValue::Parameter {
                port: source.clone(),
                permission: Permission::Read,
            }),
            ReturnValue::Tuple { items, .. } | ReturnValue::Alternatives(items) => {
                for item in items {
                    self.equality_input(item);
                }
            }
            ReturnValue::Record { fields, .. } => {
                for item in fields.values() {
                    self.equality_input(item);
                }
            }
            ReturnValue::Unknown => self
                .summary
                .incomplete("recursive equality has an unresolved constituent"),
            ReturnValue::Bottom | ReturnValue::Unit | ReturnValue::Scalar(_) => {}
        }
    }
    fn fail(&mut self, reason: &str) -> ReturnValue {
        self.summary.incomplete(reason);
        ReturnValue::Unknown
    }
    fn bind(&mut self, pattern: &Pattern, value: ReturnValue, env: &mut Environment) -> bool {
        let Some(remaining) = self.work.get().checked_sub(1) else {
            self.fail("recursive binding work exhausted");
            return false;
        };
        self.work.set(remaining);
        match &pattern.kind {
            PatternKind::Name(name) => {
                let Some(remaining) = self.work.get().checked_sub(
                    (1 + name.len().div_ceil(32))
                        .saturating_mul(1 + env.len().checked_ilog2().unwrap_or(0) as usize),
                ) else {
                    self.fail("recursive binding name work exhausted");
                    return false;
                };
                self.work.set(remaining);
                env.insert(name.clone(), value);
                true
            }
            PatternKind::Wildcard => true,
            PatternKind::Mode { pattern, .. } => self.bind(pattern, value, env),
            PatternKind::Tuple(patterns) => {
                for (index, pattern) in patterns.iter().enumerate() {
                    if !self.bind(
                        pattern,
                        value.clone().project(&Slot::Tuple(index as u32)),
                        env,
                    ) {
                        return false;
                    }
                }
                true
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    if !self.bind(
                        &field.pattern,
                        value.clone().project(&Slot::Field(field.name.clone())),
                        env,
                    ) {
                        return false;
                    }
                }
                true
            }
            _ => {
                self.summary
                    .incomplete("refutable recursive binding pattern");
                false
            }
        }
    }
    fn block(&mut self, block: &Block, env: &mut Environment) -> ReturnValue {
        let old = env.clone();
        let mut result = ReturnValue::Unit;
        let mut normal = true;
        for statement in block.where_items.iter().chain(&block.statements) {
            let value = match &statement.kind {
                StmtKind::Binding(binding) => {
                    if binding.is_meta || binding.fallback.is_some() {
                        self.summary
                            .incomplete("static or fallible recursive binding");
                    }
                    let mut value = self.expr(&binding.value, env);
                    if !binding.mode.is_mutable() {
                        value.restrict(Permission::Read);
                        if binding.mode == BindingMode::Let {
                            value.publish_immutable();
                        }
                    }
                    self.bind(&binding.pattern, value.clone(), env);
                    if value == ReturnValue::Bottom {
                        value
                    } else {
                        ReturnValue::Unit
                    }
                }
                StmtKind::Assignment { target, value, .. } => {
                    let value = self.expr(value, env);
                    if let ExprKind::Name(name) = &target.kind {
                        if env.contains_key(name) {
                            if matches!(value, ReturnValue::Unit | ReturnValue::Scalar(_)) {
                                env.insert(name.clone(), value.clone());
                            } else {
                                self.summary
                                    .incomplete("reference reassignment in recursive summary");
                            }
                        } else if self.default_scope {
                            self.fail("recursive default has no declaration lexical binding");
                        } else {
                            self.named(name, Access::Write);
                        }
                    } else {
                        let location = self.place(target, env);
                        self.access(&location, Access::Write);
                        if !matches!(value, ReturnValue::Unit | ReturnValue::Scalar(_)) {
                            self.summary.incomplete(
                                "reference field updates require regular recursive shape summaries",
                            );
                        }
                    }
                    if value == ReturnValue::Bottom {
                        value
                    } else {
                        ReturnValue::Unit
                    }
                }
                StmtKind::Expr {
                    expression,
                    terminated,
                } => {
                    let value = self.expr(expression, env);
                    if *terminated && value != ReturnValue::Bottom {
                        ReturnValue::Unit
                    } else {
                        value
                    }
                }
                _ => self.fail("nested declarations, handlers or imports in recursive body"),
            };
            if normal {
                if value == ReturnValue::Bottom {
                    normal = false;
                }
                result = value;
            }
        }
        *env = old;
        if normal { result } else { ReturnValue::Bottom }
    }
    fn named(&mut self, name: &str, access: Access) {
        self.summary
            .named
            .entry(name.into())
            .and_modify(|old| *old = (*old).max(access))
            .or_insert(access);
    }
    fn access(&mut self, value: &ReturnValue, access: Access) {
        match value {
            ReturnValue::Parameter { port, .. } => {
                self.summary.accesses.insert(AccessPort {
                    port: port.clone(),
                    slot: None,
                    access,
                });
            }
            ReturnValue::Global { name, .. } => self.named(name, access),
            ReturnValue::Alternatives(values) => {
                for value in values {
                    self.access(value, access)
                }
            }
            _ => {}
        }
    }
    fn field_access(&mut self, base: &ReturnValue, slot: &Slot, access: Access) {
        match base {
            ReturnValue::Parameter { port, .. } => {
                self.summary.accesses.insert(AccessPort {
                    port: port.clone(),
                    slot: Some(slot.clone()),
                    access,
                });
            }
            ReturnValue::Global { name, .. } => self.named(name, access),
            ReturnValue::Alternatives(values) => {
                for value in values {
                    self.field_access(value, slot, access)
                }
            }
            _ => {}
        }
    }
    fn place(&mut self, expr: &Expr, env: &mut Environment) -> ReturnValue {
        match &expr.kind {
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let base = self.expr(base, env);
                let slot = field
                    .parse::<u32>()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone()));
                self.field_access(&base, &slot, Access::Write);
                base.project(&slot)
            }
            ExprKind::Index {
                base,
                index,
                safe: false,
            } => {
                let base = self.expr(base, env);
                let _ = self.expr(index, env);
                let slot = Slot::AnyIndex;
                self.field_access(&base, &slot, Access::Write);
                base.project(&slot)
            }
            _ => self.expr(expr, env),
        }
    }
    fn expr(&mut self, expr: &Expr, env: &mut Environment) -> ReturnValue {
        let Some(remaining) = self.work.get().checked_sub(1) else {
            return self.fail("recursive summary work exhausted");
        };
        self.work.set(remaining);
        let value = match &expr.kind {
            ExprKind::Literal(literal) => match literal {
                Literal::Unit => ReturnValue::Unit,
                Literal::Bool(_) => ReturnValue::Scalar(ScalarKind::Bool),
                Literal::Integer(_) => ReturnValue::Scalar(ScalarKind::Integer),
                Literal::Float(_) => ReturnValue::Scalar(ScalarKind::Float),
                Literal::String(value) if value.contains('{') => {
                    self.fail("recursive string interpolation requires expression composition")
                }
                Literal::String(_) | Literal::RawString(_) => {
                    ReturnValue::Scalar(ScalarKind::String)
                }
                Literal::Bytes(_) => ReturnValue::Scalar(ScalarKind::Bytes),
            },
            ExprKind::Name(name) => env.get(name).cloned().unwrap_or_else(|| {
                if self.default_scope {
                    return self.fail("recursive default has no declaration lexical binding");
                }
                self.named(name, Access::Read);
                ReturnValue::Global {
                    name: name.clone(),
                    path: vec![],
                    permission: Permission::Read,
                }
            }),
            ExprKind::Path(path) => {
                let name = path.join("::");
                env.get(&name).cloned().unwrap_or_else(|| {
                    if self.default_scope {
                        return self.fail("recursive default has no declaration lexical binding");
                    }
                    self.named(&name, Access::Read);
                    ReturnValue::Global {
                        name,
                        path: vec![],
                        permission: Permission::Read,
                    }
                })
            }
            ExprKind::Generic { base, .. } => self.expr(base, env),
            ExprKind::Block(block) => self.block(block, env),
            ExprKind::Unary { operator, operand } => {
                let value = self.expr(operand, env);
                if value == ReturnValue::Bottom {
                    return value;
                }
                if operator == "^mut" {
                    self.access(&value, Access::Retain);
                    value
                } else if operator == "!" {
                    ReturnValue::Scalar(ScalarKind::Bool)
                } else {
                    ReturnValue::Scalar(ScalarKind::Integer)
                }
            }
            ExprKind::Binary {
                operator,
                left,
                right,
            } => {
                if operator == "|>" || operator == "!>" {
                    let left = self.expr(left, env);
                    if left == ReturnValue::Bottom {
                        return left;
                    }
                    let prefix = vec![left];
                    return if let ExprKind::Call { callee, arguments } = &right.kind {
                        self.call(callee, arguments, env, prefix)
                    } else {
                        self.call(right, &[], env, prefix)
                    };
                }
                let a = self.expr(left, env);
                let b = self.expr(right, env);
                self.access(&a, Access::Read);
                self.access(&b, Access::Read);
                if a == ReturnValue::Bottom || b == ReturnValue::Bottom {
                    return ReturnValue::Bottom;
                }
                let none = |value: &ReturnValue| {
                    matches!(value, ReturnValue::Global { name, path, .. }
                        if path.is_empty() && matches!(name.as_str(), "None" | "Prelude::None"))
                };
                if matches!(operator.as_str(), "==" | "!=") && !none(&a) && !none(&b) {
                    self.equality_input(&a);
                    self.equality_input(&b);
                }
                if operator == "??" {
                    return self.fail("recursive optional/result branch relation");
                }
                ReturnValue::Scalar(
                    if matches!(
                        operator.as_str(),
                        "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||"
                    ) {
                        ScalarKind::Bool
                    } else {
                        ScalarKind::Integer
                    },
                )
            }
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => {
                let base = self.expr(base, env);
                let slot = field
                    .parse::<u32>()
                    .map(Slot::Tuple)
                    .unwrap_or_else(|_| Slot::Field(field.clone()));
                self.field_access(&base, &slot, Access::Read);
                base.project(&slot)
            }
            ExprKind::Index {
                base,
                index,
                safe: false,
            } => {
                let base = self.expr(base, env);
                let _ = self.expr(index, env);
                self.field_access(&base, &Slot::AnyIndex, Access::Read);
                base.project(&Slot::AnyIndex)
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition_value = self.expr(condition, env);
                self.access(&condition_value, Access::Read);
                if condition_value == ReturnValue::Bottom {
                    return ReturnValue::Bottom;
                }
                if let ExprKind::Literal(Literal::Bool(value)) = &condition.kind {
                    return if *value {
                        self.expr(then_branch, env)
                    } else {
                        else_branch
                            .as_ref()
                            .map_or(ReturnValue::Unit, |branch| self.expr(branch, env))
                    };
                }
                let before = env.clone();
                let left = self.expr(then_branch, env);
                let left_env = env.clone();
                *env = before.clone();
                let right = else_branch
                    .as_ref()
                    .map_or(ReturnValue::Unit, |branch| self.expr(branch, env));
                for (name, value) in left_env {
                    if let Some(other) = env.get(&name).cloned() {
                        env.insert(name, value.join(other));
                    }
                }
                left.join(right)
            }
            ExprKind::Tuple(items) => {
                let mut values = Vec::new();
                for item in items {
                    let value = self.expr(item, env);
                    if value == ReturnValue::Bottom {
                        return value;
                    }
                    if value.contains_site(site(expr)) {
                        return self
                            .fail("growing recursive aggregate requires regular shape ports");
                    }
                    values.push(value);
                }
                ReturnValue::Tuple {
                    site: site(expr),
                    items: values,
                    reception: Reception::Construction,
                }
            }
            ExprKind::Record { ty, members } => {
                if members
                    .iter()
                    .any(|member| matches!(member, RecordMember::Spread(_)))
                {
                    return self.fail("recursive record spread requires shape composition");
                }
                let mut values = BTreeMap::new();
                for field in members.iter().filter_map(|member| match member {
                    RecordMember::Field(field) => Some(field),
                    RecordMember::Spread(_) => None,
                }) {
                    let value = self.expr(&field.value, env);
                    if value == ReturnValue::Bottom {
                        return value;
                    }
                    if value.contains_site(site(expr)) {
                        return self.fail("growing recursive record requires regular shape ports");
                    }
                    values.insert(field.name.clone(), value);
                }
                let type_name = ty.as_ref().and_then(|ty| {
                    if let TypeKind::Name { path, arguments } = &ty.kind {
                        arguments.is_empty().then(|| path.join("::"))
                    } else {
                        None
                    }
                });
                ReturnValue::Record {
                    site: site(expr),
                    type_name,
                    fields: values,
                    field_modes: ty
                        .as_ref()
                        .and_then(|ty| {
                            if let TypeKind::Record { fields, .. } = &ty.kind {
                                Some(
                                    fields
                                        .iter()
                                        .map(|field| (field.name.clone(), field.mutable))
                                        .collect(),
                                )
                            } else {
                                None
                            }
                        })
                        .unwrap_or_default(),
                    reception: Reception::Construction,
                }
            }
            ExprKind::Call { callee, arguments } => self.call(callee, arguments, env, vec![]),
            ExprKind::Control {
                operation: ControlOperation::Return,
                value,
            } => {
                if self.default_scope {
                    return self.fail("recursive default requires a separate control boundary");
                }
                let value = value
                    .as_ref()
                    .map_or(ReturnValue::Unit, |value| self.expr(value, env));
                self.returns =
                    std::mem::replace(&mut self.returns, ReturnValue::Bottom).join(value);
                ReturnValue::Bottom
            }
            _ => self.fail("recursive expression requires a richer finite shape transfer"),
        };
        if self.default_scope && value == ReturnValue::Unknown {
            self.summary
                .incomplete("recursive default value is unresolved");
        }
        value
    }
    fn call(
        &mut self,
        callee: &Expr,
        arguments: &[Argument],
        env: &mut Environment,
        mut values: Vec<ReturnValue>,
    ) -> ReturnValue {
        let prefix = values.len();
        for argument in arguments {
            let value = self.expr(&argument.value, env);
            if value == ReturnValue::Bottom {
                return value;
            }
            values.push(value);
        }
        let mut remaining = self.work.get();
        let base = crate::hir::application::callee_base_with_work(callee, &mut remaining);
        self.work.set(remaining);
        let base = match base {
            Ok(callee) => callee,
            Err(reason) => return self.fail(reason),
        };
        let name = match &base.kind {
            ExprKind::Name(name) => {
                let Some(left) = self.work.get().checked_sub(1 + name.len().div_ceil(32)) else {
                    return self.fail("recursive callee name work exhausted");
                };
                self.work.set(left);
                name.clone()
            }
            ExprKind::Path(path) => {
                for part in path {
                    let Some(left) = self.work.get().checked_sub(1 + part.len().div_ceil(32))
                    else {
                        return self.fail("recursive callee path work exhausted");
                    };
                    self.work.set(left);
                }
                path.join("::")
            }
            _ => return self.fail("dynamic recursive callee shape"),
        };
        if self.default_scope && !env.contains_key(&name) {
            return self.fail("recursive default callable has no declaration lexical binding");
        }
        if arguments.iter().any(|argument| argument.label.is_some())
            && !self.by_name.contains_key(&name)
        {
            return self.fail("named recursive arguments have no declared interface");
        }
        let builtin = name.strip_prefix("Prelude::").unwrap_or(&name);
        match builtin {
            _ if self.declared_names.contains(&name) || env.contains_key(&name) => {}
            "panic" => return ReturnValue::Bottom,
            "assert" => {
                for value in &values {
                    self.access(value, Access::Read)
                }
                return ReturnValue::Unit;
            }
            "len" => {
                for value in &values {
                    self.access(value, Access::Read)
                }
                return ReturnValue::Scalar(ScalarKind::Integer);
            }
            "clone" | "clone_immut" => {
                return match values.first() {
                    Some(ReturnValue::Parameter { port, .. }) => ReturnValue::Clone {
                        source: port.clone(),
                        site: site(callee),
                        immutable: builtin == "clone_immut",
                        reception: if builtin == "clone_immut" {
                            Reception::Immutable
                        } else {
                            Reception::Construction
                        },
                    },
                    Some(ReturnValue::Bottom) => ReturnValue::Bottom,
                    _ => self.fail("recursive clone source must be a resolved formal port"),
                };
            }
            _ => {}
        }
        if let Some(ReturnValue::Parameter { port, .. }) = env.get(&name) {
            if !values.is_empty() {
                return self.fail("recursive callback arguments need composed invocation ports");
            }
            let unit_callback=self.function.parameters.get(port.parameter as usize).and_then(|parameter|parameter.ty.as_ref()).is_some_and(|ty|matches!(&ty.kind,TypeKind::Callable{parameters,result,..}if parameters.is_empty()&&result.as_ref().is_none_or(|ty|matches!(&ty.kind,TypeKind::Tuple(items)if items.is_empty()))));
            if !unit_callback {
                return self.fail("recursive callback return provenance requires a result port");
            }
            self.summary.callbacks.insert(CallbackPort {
                parameter: port.parameter,
                path: port.path.clone(),
                arguments: vec![],
            });
            return ReturnValue::Unit;
        }
        if env.contains_key(&name) {
            return self.fail("shadowing local callable has no established recursive contract");
        }
        let Some(&callee_key) = self.by_name.get(&name) else {
            return self.fail("unknown recursive or external callable contract");
        };
        self.dependencies.insert(callee_key);
        let callee_summary = self.summaries[&callee_key].clone();
        if values.iter().any(|value| match value {
            ReturnValue::Unit | ReturnValue::Scalar(_) => false,
            ReturnValue::Parameter { port, .. } => !port.path.is_empty(),
            _ => true,
        }) {
            return self
                .fail("recursive projected/fresh arguments require regular interface ports");
        }
        let parameters = &self.by_key[&callee_key].parameters;
        let count = parameters.len() + values.len();
        let Some(left) = self
            .work
            .get()
            .checked_sub(count.saturating_mul(2 + count.checked_ilog2().unwrap_or(0) as usize))
        else {
            return self.fail("recursive parameter binding work exhausted");
        };
        self.work.set(left);
        let labels = crate::hir::application::parameter_labels(parameters);
        for label in labels.iter().flatten().copied().chain(
            arguments
                .iter()
                .filter_map(|argument| argument.label.as_deref()),
        ) {
            let Some(left) = self.work.get().checked_sub(
                (2 + count.checked_ilog2().unwrap_or(0) as usize)
                    .saturating_mul(label.len().div_ceil(32)),
            ) else {
                return self.fail("recursive argument label work exhausted");
            };
            self.work.set(left);
        }
        let mapping = crate::hir::application::bind_slots(
            &labels,
            std::iter::repeat_n(None, prefix)
                .chain(arguments.iter().map(|argument| argument.label.as_deref())),
        );
        let mut slots = vec![None; parameters.len()];
        for (value, slot) in values.into_iter().zip(mapping) {
            let Ok(slot) = slot else {
                return self.fail("recursive call violates its original parameter interface");
            };
            slots[slot] = Some(value);
        }
        let mut ordered = Vec::with_capacity(parameters.len());
        let mut default_environment = Environment::new();
        for (parameter, value) in parameters.iter().zip(slots) {
            let value = if let Some(value) = value {
                value
            } else if let Some(default) = &parameter.default {
                let previous_default_scope = self.default_scope;
                self.default_scope = true;
                let value = self.expr(default, &mut default_environment);
                self.default_scope = previous_default_scope;
                if value == ReturnValue::Bottom {
                    return value;
                }
                if match &value {
                    ReturnValue::Unit | ReturnValue::Scalar(_) => false,
                    ReturnValue::Parameter { port, .. } => !port.path.is_empty(),
                    _ => true,
                } {
                    return self.fail("recursive default needs a resolved regular interface port");
                }
                value
            } else {
                return self.fail("recursive call omitted an argument");
            };
            let mut binding = value.clone();
            if parameter.mode == ParameterMode::Read {
                binding.restrict(Permission::Read);
            }
            if !self.bind(&parameter.pattern, binding, &mut default_environment) {
                return self.fail("recursive callee parameter binding is unresolved");
            }
            ordered.push(value);
        }
        for access in &callee_summary.accesses {
            let value = ReturnValue::Parameter {
                port: access.port.clone(),
                permission: Permission::Read,
            }
            .substitute(&ordered);
            if let Some(slot) = &access.slot {
                self.field_access(&value, slot, access.access)
            } else {
                self.access(&value, access.access)
            }
        }
        for callback in &callee_summary.callbacks {
            let value = ReturnValue::Parameter {
                port: Port {
                    parameter: callback.parameter,
                    path: callback.path.clone(),
                },
                permission: Permission::Read,
            }
            .substitute(&ordered);
            if let ReturnValue::Parameter { port, .. } = value {
                self.summary.callbacks.insert(CallbackPort {
                    parameter: port.parameter,
                    path: port.path,
                    arguments: vec![],
                });
            } else {
                self.summary
                    .incomplete("recursive callback target does not resolve to an interface port");
            }
        }
        for input in &callee_summary.equality_inputs {
            self.equality_input(&input.substitute(&ordered));
        }
        self.summary
            .effects
            .extend(callee_summary.effects.iter().cloned());
        for (name, access) in &callee_summary.named {
            self.named(name, *access);
        }
        if !callee_summary.complete {
            self.summary.incomplete(
                callee_summary
                    .reason
                    .clone()
                    .unwrap_or_else(|| "incomplete recursive dependency".into()),
            );
        }
        callee_summary.return_value.substitute(&ordered)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn functions(source: &str) -> Vec<Function> {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        parsed
            .program
            .statements
            .into_iter()
            .filter_map(|statement| {
                if let StmtKind::Function(function) = statement.kind {
                    Some(function)
                } else {
                    None
                }
            })
            .collect()
    }
    fn summaries(source: &str) -> Analysis {
        let functions = functions(source);
        analyze(
            functions
                .iter()
                .enumerate()
                .map(|(index, function)| (DefinitionId(index as u32), function)),
        )
    }
    #[test]
    fn base_case_seeds_scalar_and_forwarded_reference_returns() {
        let analysis = summaries(
            "fn identity(n:int,value:Cell)->Cell{if n==0{value}else{identity(n-1,value)}}",
        );
        let summary = analysis.summaries.values().next().unwrap();
        assert!(summary.complete && summary.productive, "{summary:?}");
        assert!(matches!(
            summary.return_value,
            ReturnValue::Parameter {
                permission: Permission::Read,
                ..
            }
        ));
    }
    #[test]
    fn explicit_generic_calls_keep_the_same_original_return_ports_and_slot_binding() {
        use super::review_fixture as fixture;
        let analyze_program = |program: &Program| {
            analyze(
                program
                    .statements
                    .iter()
                    .filter_map(|statement| match &statement.kind {
                        StmtKind::Function(function) => Some(function),
                        _ => None,
                    })
                    .enumerate()
                    .map(|(index, function)| (DefinitionId(index as u32), function)),
            )
        };
        let original = fixture::program();
        let explicit = analyze_program(&original);
        let key = DefinitionId(1);
        let summary = &explicit.summaries[&key];
        assert!(summary.complete && summary.productive, "{summary:?}");
        assert!(
            matches!(&summary.return_value, ReturnValue::Parameter { port, .. } if port.parameter == 1)
        );
        let mut implicit = original.clone();
        let ExprKind::Call { callee, .. } =
            &mut fixture::call_mut(fixture::function_mut(&mut implicit, "recur")).kind
        else {
            unreachable!();
        };
        let ExprKind::Generic { base, .. } = &callee.kind else {
            panic!("original explicit prefix");
        };
        *callee = base.clone();
        fixture::identify(&mut implicit);
        assert_eq!(analyze_program(&implicit).summaries, explicit.summaries);
        let mut named = original.clone();
        let ExprKind::Call { arguments, .. } =
            &mut fixture::call_mut(fixture::function_mut(&mut named, "recur")).kind
        else {
            unreachable!();
        };
        arguments[0].label = Some("count".into());
        arguments[1].label = Some("value".into());
        arguments.swap(0, 1);
        fixture::identify(&mut named);
        assert_eq!(analyze_program(&named).summaries, explicit.summaries);
        let mut shadowed = original;
        fixture::function_mut(&mut shadowed, "recur").parameters[1]
            .pattern
            .kind = PatternKind::Name("recur".into());
        fixture::identify(&mut shadowed);
        assert!(!analyze_program(&shadowed).summaries[&key].complete);
    }
    #[test]
    fn defaults_bind_callee_formals_before_following_defaults_and_keep_actual_ports() {
        use super::review_fixture as fixture;
        let analyze_program = |program: &Program| {
            analyze(
                program
                    .statements
                    .iter()
                    .filter_map(|statement| match &statement.kind {
                        StmtKind::Function(function) => Some(function),
                        _ => None,
                    })
                    .enumerate()
                    .map(|(index, function)| (DefinitionId(index as u32), function)),
            )
        };
        let original = fixture::default_forwarding_program();
        let key = DefinitionId(1);
        let assert_port = |program: &Program, parameter| {
            let summary = &analyze_program(program).summaries[&key];
            assert!(summary.complete && summary.productive, "{summary:?}");
            assert!(
                matches!(&summary.return_value, ReturnValue::Parameter { port, .. } if port.parameter == parameter && port.path.is_empty()),
                "{summary:?}"
            );
        };
        assert_port(&original, 2);

        let mut chained = original.clone();
        let pick = fixture::function_mut(&mut chained, "pick");
        let mut last = pick.parameters[1].clone();
        last.pattern.kind = PatternKind::Name("last".into());
        last.default.as_mut().unwrap().kind = ExprKind::Name("answer".into());
        pick.parameters.push(last);
        fixture::body_expression_mut(pick).kind = ExprKind::Name("last".into());
        fixture::identify(&mut chained);
        assert_port(&chained, 2);

        let mut changed_actual = original.clone();
        let ExprKind::Call { arguments, .. } =
            &mut fixture::base_case_mut(fixture::function_mut(&mut changed_actual, "recur")).kind
        else {
            unreachable!();
        };
        arguments[0].value.kind = ExprKind::Name("first".into());
        fixture::identify(&mut changed_actual);
        assert_port(&changed_actual, 1);

        let mut scalar = original.clone();
        fixture::function_mut(&mut scalar, "pick").parameters[1]
            .default
            .as_mut()
            .unwrap()
            .kind = ExprKind::Literal(Literal::Integer("0".into()));
        fixture::identify(&mut scalar);
        let summary = &analyze_program(&scalar).summaries[&key];
        assert!(summary.complete && summary.productive, "{summary:?}");
        assert_eq!(
            summary.return_value,
            ReturnValue::Scalar(ScalarKind::Integer)
        );

        for mutation in 0..6 {
            let mut corrupted = original.clone();
            match mutation {
                0 | 1 => {
                    // `value` exists in the caller; `answer` is the current
                    // formal and must not become available before its default.
                    fixture::function_mut(&mut corrupted, "pick").parameters[1]
                        .default
                        .as_mut()
                        .unwrap()
                        .kind =
                        ExprKind::Name(if mutation == 0 { "value" } else { "answer" }.into());
                }
                2 => {
                    let ExprKind::Call { arguments, .. } =
                        &mut fixture::base_case_mut(fixture::function_mut(&mut corrupted, "recur"))
                            .kind
                    else {
                        unreachable!();
                    };
                    arguments[0].label = Some("answer".into());
                }
                3 => {
                    // An unresolved default is still evaluated if the result
                    // relation does not use that formal.
                    let pick = fixture::function_mut(&mut corrupted, "pick");
                    pick.parameters[1].default.as_mut().unwrap().kind =
                        ExprKind::Name("value".into());
                    fixture::body_expression_mut(pick).kind = ExprKind::Name("first".into());
                }
                4 => {
                    let pick = fixture::function_mut(&mut corrupted, "pick");
                    let mut callee = pick.parameters[1].default.as_ref().unwrap().clone();
                    callee.kind = ExprKind::Name("panic".into());
                    pick.parameters[1].default.as_mut().unwrap().kind = ExprKind::Call {
                        callee: Box::new(callee),
                        arguments: vec![],
                    };
                }
                5 => {
                    let pick = fixture::function_mut(&mut corrupted, "pick");
                    let mut callee = pick.parameters[1].default.as_ref().unwrap().clone();
                    callee.kind = ExprKind::Name("down".into());
                    let mut value = callee.clone();
                    value.kind = ExprKind::Literal(Literal::Integer("0".into()));
                    pick.parameters[1].default.as_mut().unwrap().kind = ExprKind::Call {
                        callee: Box::new(callee),
                        arguments: vec![Argument {
                            label: None,
                            mode: ParameterMode::Read,
                            span: value.span,
                            value,
                        }],
                    };
                }
                _ => unreachable!(),
            }
            fixture::identify(&mut corrupted);
            let summary = &analyze_program(&corrupted).summaries[&key];
            assert!(
                !summary.complete,
                "default mutation {mutation}: {summary:?}"
            );
            if mutation == 4 {
                assert!(!summary.productive, "{summary:?}");
            }
        }
    }
    #[test]
    fn a_cycle_without_a_normal_return_seed_stays_unknown() {
        let analysis = summaries("fn looped(value:Cell)->Cell{looped(value)}");
        let summary = analysis.summaries.values().next().unwrap();
        assert!(!summary.complete && !summary.productive);
        assert_eq!(summary.return_value, ReturnValue::Unknown);
    }
    #[test]
    fn repeated_registration_of_one_source_definition_keeps_its_call_identity() {
        let parsed = ril_syntax::parse("fn same(n:int)->int{if n==0{1}else{same(n-1)}}");
        assert!(parsed.is_ok());
        let StmtKind::Function(function) = &parsed.program.statements[0].kind else {
            panic!("function");
        };
        let definition = DefinitionId(7);
        let analysis = analyze([(definition, function); 3]);
        assert_eq!(analysis.summaries.len(), 1);
        let summary = &analysis.summaries[&definition];
        assert!(summary.complete && summary.productive, "{summary:?}");
        assert_eq!(
            summary.return_value,
            ReturnValue::Scalar(ScalarKind::Integer)
        );

        let ambiguous = analyze([(definition, function), (DefinitionId(8), function)]);
        assert_eq!(ambiguous.summaries.len(), 2);
        assert!(
            ambiguous
                .summaries
                .values()
                .all(|summary| !summary.complete)
        );
    }

    #[test]
    fn equal_diagnostic_spans_do_not_merge_distinct_return_relations() {
        let mut functions = functions(
            "fn recur(n:int,value:Cell)->Cell{if n==0{value}else{recur(n-1,value)}}\nfn fresh(n:int,value:Cell)->Cell{clone(value)}",
        );
        functions[1].span = functions[0].span;
        let analysis = analyze([
            (DefinitionId(3), &functions[0]),
            (DefinitionId(9), &functions[1]),
        ]);
        assert_eq!(analysis.summaries.len(), 2);
        assert!(matches!(
            analysis.summaries[&DefinitionId(3)].return_value,
            ReturnValue::Parameter {
                permission: Permission::Read,
                ..
            }
        ));
        assert!(matches!(
            analysis.summaries[&DefinitionId(9)].return_value,
            ReturnValue::Clone { .. }
        ));
    }

    #[test]
    fn conflicting_instances_cannot_supply_their_declarations_summary() {
        let mut functions = functions(
            "fn choose<T>(value:T)->T{value}\nfn concrete(value:int)->int{7}\nfn caller(value:int)->int{choose(value)}",
        );
        functions[1].name = functions[0].name.clone();
        for reverse in [false, true] {
            let first = usize::from(reverse);
            let analysis = analyze([
                (DefinitionId(0), &functions[first]),
                (DefinitionId(0), &functions[1 - first]),
                (DefinitionId(1), &functions[2]),
            ]);
            assert!(analysis.summaries.values().all(|summary| !summary.complete));
            assert_eq!(
                analysis.summaries[&DefinitionId(0)].return_value,
                ReturnValue::Unknown
            );
            assert!(!analysis.summaries[&DefinitionId(0)].productive);
        }
    }

    #[test]
    fn local_aliases_cannot_fall_back_to_a_same_named_function() {
        let analysis = summaries("fn fresh()->int{7}\nfn recur()->int{let fresh=unknown;fresh()}");
        let summary = &analysis.summaries[&DefinitionId(1)];
        assert!(!summary.complete);
        assert_eq!(summary.return_value, ReturnValue::Unknown);
        assert!(summary.reason.as_ref().unwrap().contains("shadowing local"));
    }

    #[test]
    fn parameter_callbacks_keep_their_port_instead_of_the_same_named_function() {
        let analysis =
            summaries("fn callback(){panic(\"global\")}\nfn recur(callback:fn()){callback()}");
        let summary = &analysis.summaries[&DefinitionId(1)];
        assert!(summary.complete && summary.productive, "{summary:?}");
        assert_eq!(summary.return_value, ReturnValue::Unit);
        assert_eq!(summary.callbacks.len(), 1);
        assert_eq!(summary.callbacks.iter().next().unwrap().parameter, 0);

        let analysis =
            summaries("fn callback()->int{7}\nfn recur(callback:fn()->int)->int{callback()}");
        assert!(!analysis.summaries[&DefinitionId(1)].complete);
        assert_eq!(
            analysis.summaries[&DefinitionId(1)].return_value,
            ReturnValue::Unknown
        );
    }

    #[test]
    fn ambiguous_declarations_do_not_fall_back_to_a_builtin() {
        let mut functions = functions(
            "fn clone(value:Cell)->Cell{value}\nfn other(value:Cell)->Cell{value}\nfn recur(value:Cell)->Cell{clone(value)}",
        );
        functions[1].name = functions[0].name.clone();
        let analysis = analyze(
            functions
                .iter()
                .enumerate()
                .map(|(index, function)| (DefinitionId(index as u32), function)),
        );
        assert!(!analysis.summaries[&DefinitionId(2)].complete);
        assert_eq!(
            analysis.summaries[&DefinitionId(2)].return_value,
            ReturnValue::Unknown
        );
    }
}
