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
use std::collections::{BTreeMap, BTreeSet, VecDeque};

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
        queued.remove(&current);
        let function = by_key[&current];
        let mut transfer = Transfer {
            function,
            by_name: &by_name,
            declared_names: &declared_names,
            by_key: &by_key,
            summaries: &summaries,
            summary: Summary::default(),
            dependencies: BTreeSet::new(),
            returns: ReturnValue::Bottom,
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
struct Transfer<'a> {
    function: &'a Function,
    by_name: &'a BTreeMap<String, FunctionKey>,
    declared_names: &'a BTreeSet<String>,
    by_key: &'a BTreeMap<FunctionKey, &'a Function>,
    summaries: &'a BTreeMap<FunctionKey, Summary>,
    summary: Summary,
    dependencies: BTreeSet<FunctionKey>,
    returns: ReturnValue,
}
impl Transfer<'_> {
    fn fail(&mut self, reason: &str) -> ReturnValue {
        self.summary.incomplete(reason);
        ReturnValue::Unknown
    }
    fn bind(&mut self, pattern: &Pattern, value: ReturnValue, env: &mut Environment) {
        match &pattern.kind {
            PatternKind::Name(name) => {
                env.insert(name.clone(), value);
            }
            PatternKind::Wildcard => {}
            PatternKind::Mode { pattern, .. } => self.bind(pattern, value, env),
            PatternKind::Tuple(patterns) => {
                for (index, pattern) in patterns.iter().enumerate() {
                    self.bind(
                        pattern,
                        value.clone().project(&Slot::Tuple(index as u32)),
                        env,
                    );
                }
            }
            PatternKind::Record { fields, .. } => {
                for field in fields {
                    self.bind(
                        &field.pattern,
                        value.clone().project(&Slot::Field(field.name.clone())),
                        env,
                    );
                }
            }
            _ => {
                self.summary
                    .incomplete("refutable recursive binding pattern");
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
        match &expr.kind {
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
            ExprKind::Record {
                ty,
                fields,
                spread,
                members,
            } => {
                if spread.is_some()
                    || members
                        .iter()
                        .any(|member| matches!(member, RecordMember::Spread(_)))
                {
                    return self.fail("recursive record spread requires shape composition");
                }
                let mut values = BTreeMap::new();
                for field in fields {
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
                let value = value
                    .as_ref()
                    .map_or(ReturnValue::Unit, |value| self.expr(value, env));
                self.returns =
                    std::mem::replace(&mut self.returns, ReturnValue::Bottom).join(value);
                ReturnValue::Bottom
            }
            _ => self.fail("recursive expression requires a richer finite shape transfer"),
        }
    }
    fn call(
        &mut self,
        callee: &Expr,
        arguments: &[Argument],
        env: &mut Environment,
        mut values: Vec<ReturnValue>,
    ) -> ReturnValue {
        for argument in arguments {
            if argument.label.is_some() {
                return self.fail("named recursive arguments require interface reordering");
            }
            let value = self.expr(&argument.value, env);
            if value == ReturnValue::Bottom {
                return value;
            }
            values.push(value);
        }
        let name = match &callee.kind {
            ExprKind::Name(name) => name.clone(),
            ExprKind::Path(path) => path.join("::"),
            _ => return self.fail("dynamic recursive callee shape"),
        };
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
        let mut ordered = values;
        let parameters = self.by_key[&callee_key].parameters.clone();
        if ordered.len() > parameters.len() {
            return self.fail("recursive call argument arity");
        }
        for parameter in parameters.iter().skip(ordered.len()) {
            if let Some(default) = &parameter.default {
                ordered.push(self.expr(default, env));
            } else {
                return self.fail("recursive call omitted an argument");
            }
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
