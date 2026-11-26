mod captures;
mod check;
mod coverage;
mod effects;
mod eval;
mod expr;
mod forms;
mod inspect;
mod narrowing;
mod pattern;
pub(crate) mod reception;
mod staging;
mod value;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt,
    sync::Arc,
};

use ril_hir::{DefinitionId, Program, ScopeId};
use ril_source::{diag::Diagnostic, span::Span};
use ril_syntax::syntax::{Mode, Visibility};

pub use pattern::text_slice_fragment;
pub use value::{LiteralError, Value, arithmetic, literal, render};

pub fn check(hir: Program, budget: Option<u64>) -> Result<TypedProgram, Vec<Diagnostic>> {
    check::check(hir, budget)
}

/// Partial typecheck for IDE/LSP use: returns the best-effort `TypedProgram`
/// alongside any type diagnostics.
pub fn check_partial(hir: Program, budget: Option<u64>) -> (TypedProgram, Vec<Diagnostic>) {
    check::check_partial(hir, budget)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ty {
    Unit,
    Bool,
    Int,
    F64,
    Str,
    Bytes,
    Never,
    Infer(u32),
    Unknown,
    Param(DefinitionId),
    Projection(Box<Ty>, DefinitionId),
    Adt(Arc<Adt>),
    Tuple(Vec<Member>),
    Record(BTreeMap<String, Member>, bool),
    Array(Box<Member>),
    Map(Box<Ty>, Box<Member>),
    Range,
    Callable(Arc<Callable>),
    TypeValue(Option<Box<Ty>>),
    Mode,
    Draft(Box<Ty>),
}

impl Ty {
    pub(super) fn has_via_members(&self) -> bool {
        let has_via = |item: &Member| item.mode.mode == Mode::Via || item.ty.has_via_members();
        match self {
            Self::Array(member) | Self::Map(_, member) => has_via(member),
            Self::Tuple(members) => members.iter().any(has_via),
            Self::Record(fields, _) => fields.values().any(has_via),
            _ => false,
        }
    }

    pub fn contains_type_value(&self) -> bool {
        match self {
            Self::TypeValue(_) => true,
            Self::Array(item) => item.ty.contains_type_value(),
            Self::Map(key, item) => key.contains_type_value() || item.ty.contains_type_value(),
            Self::Tuple(items) => items.iter().any(|m| m.ty.contains_type_value()),
            Self::Record(items, _) => items.values().any(|m| m.ty.contains_type_value()),
            Self::Projection(inner, _) | Self::Draft(inner) => inner.contains_type_value(),
            Self::Adt(adt) => adt
                .arguments
                .iter()
                .any(|arg| matches!(arg, GenericValue::Type(ty) if ty.contains_type_value())),
            Self::Callable(sig) => {
                sig.result.contains_type_value()
                    || sig.parameters.iter().any(|p| p.ty.contains_type_value())
            }
            _ => false,
        }
    }

    pub const fn is_primitive_value(&self) -> bool {
        matches!(
            self,
            Self::Unit | Self::Bool | Self::Int | Self::F64 | Self::Str | Self::Bytes | Self::Never
        )
    }

    pub fn as_option(&self, hir: &Program) -> Option<&Ty> {
        if let Self::Adt(adt) = self
            && hir.std_type(adt.definition) == Some(ril_hir::StdType::Option)
            && let [GenericValue::Type(inner)] = adt.arguments.as_slice()
        {
            Some(inner)
        } else {
            None
        }
    }

    pub fn is_option(&self, hir: &Program) -> bool {
        self.as_option(hir).is_some()
    }

    pub fn as_result(&self, hir: &Program) -> Option<(&Ty, &Ty)> {
        if let Self::Adt(adt) = self
            && hir.std_type(adt.definition) == Some(ril_hir::StdType::Result)
            && let [GenericValue::Type(ok), GenericValue::Type(err)] = adt.arguments.as_slice()
        {
            Some((ok, err))
        } else {
            None
        }
    }

    pub fn is_result(&self, hir: &Program) -> bool {
        self.as_result(hir).is_some()
    }

    pub fn as_set(&self, hir: &Program) -> Option<&Ty> {
        if let Self::Adt(adt) = self
            && hir.std_type(adt.definition) == Some(ril_hir::StdType::Set)
            && let [GenericValue::Type(elem)] = adt.arguments.as_slice()
        {
            Some(elem)
        } else {
            None
        }
    }

    pub fn is_set(&self, hir: &Program) -> bool {
        self.as_set(hir).is_some()
    }

    fn has_unresolved_static_type(&self) -> bool {
        let mut unresolved = false;
        check::transform(self, &mut |ty| {
            if matches!(ty, Self::Param(_) | Self::Projection(..) | Self::Infer(_)) {
                unresolved = true;
            }
            None
        });
        unresolved
    }

    pub fn specialize(&self, arguments: &BTreeMap<DefinitionId, Ty>) -> Self {
        if arguments.is_empty() {
            return self.clone();
        }
        check::transform(self, &mut |ty| match ty {
            Self::Param(id) => arguments.get(id).cloned(),
            _ => None,
        })
    }

    pub fn contains_writable_member_schema(&self) -> bool {
        let mut found = false;
        check::transform(self, &mut |ty| {
            match ty {
                Ty::Array(m) | Ty::Map(_, m) => {
                    if m.mode.variable || matches!(m.mode.mode, Mode::Mut | Mode::Shared) {
                        found = true;
                    }
                }
                Ty::Tuple(ms) => {
                    if ms
                        .iter()
                        .any(|m| m.mode.variable || matches!(m.mode.mode, Mode::Mut | Mode::Shared))
                    {
                        found = true;
                    }
                }
                Ty::Record(fields, _)
                    if fields.values().any(|m| {
                        m.mode.variable || matches!(m.mode.mode, Mode::Mut | Mode::Shared)
                    }) =>
                {
                    found = true;
                }
                _ => {}
            }
            None
        });
        found
    }

    pub fn display<'a>(&'a self, hir: &'a Program) -> Display<'a> {
        Display {
            ty: self,
            hir,
            qualified: false,
        }
    }

    pub fn qualified_display<'a>(&'a self, hir: &'a Program) -> Display<'a> {
        Display {
            ty: self,
            hir,
            qualified: true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Adt {
    pub definition: DefinitionId,
    pub kind: AdtKind,
    pub defining_scope: ScopeId,
    pub visibility: Visibility,
    pub arguments: Vec<GenericValue>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AdtKind {
    Nominal,
    Opaque,
    Sum,
    OpaqueSum,
    Foreign,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GenericValue {
    Type(Ty),
    Data(Value),
    Mode(MemberMode),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Member {
    pub mode: MemberMode,
    pub ty: Ty,
}

impl Member {
    pub const fn plain(ty: Ty) -> Self {
        Self {
            mode: MemberMode::PLAIN,
            ty,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct MemberMode {
    pub variable: bool,
    pub mode: Mode,
}

impl MemberMode {
    pub const PLAIN: Self = Self {
        variable: false,
        mode: Mode::Plain,
    };
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Parameter {
    pub label: Option<String>,
    pub mode: Mode,
    pub ty: Ty,
    pub optional: bool,
    pub is_meta: bool,
}

pub(crate) fn nested_type_argument(outer: &Adt, inner: &Adt) -> bool {
    // A finite type argument may use the same constructor. Following
    // that argument is distinct from expanding a recursive definition.
    outer.arguments.iter().any(|argument| {
        let GenericValue::Type(ty) = argument else {
            return false;
        };
        let mut nested = false;
        check::transform(ty, &mut |part| {
            nested |= matches!(part, Ty::Adt(application) if application.as_ref() == inner);
            None
        });
        nested
    })
}

impl Parameter {
    pub(crate) fn callable_mode_with(&self, is_value: bool) -> Mode {
        if self.mode == Mode::Via && is_value {
            Mode::Plain
        } else {
            self.mode
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Callable {
    pub is_ctl: bool,
    pub once: bool,
    pub parameters: Vec<Parameter>,
    pub result: Ty,
    pub result_mode: Mode,
    pub effects: Vec<String>,
    pub open_effects: bool,
    pub state: Vec<String>,
    pub open_state: bool,
}

impl Callable {
    pub(super) fn has_via_inputs(&self) -> bool {
        self.parameters
            .iter()
            .any(|param| param.mode == Mode::Via || param.ty.has_via_members())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NarrowDropCause {
    OverlappingWrite,
    OpenStateCall,
    AliasingMut,
}

impl NarrowDropCause {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::OverlappingWrite => "overlapping_write",
            Self::OpenStateCall => "open_state_call",
            Self::AliasingMut => "aliasing_mut",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NarrowDrop {
    pub span: Span,
    pub path: String,
    pub cause: NarrowDropCause,
}

pub struct TypedProgram {
    pub hir: Program,
    pub types: HashMap<Span, Ty>,
    pub type_arguments: HashMap<Span, BTreeMap<DefinitionId, Ty>>,
    pub bindings: HashMap<DefinitionId, Ty>,
    pub callables: BTreeMap<DefinitionId, Arc<Callable>>,
    pub imported_functions: BTreeMap<DefinitionId, crate::iface::Export>,
    pub imported_behaviors: BTreeMap<DefinitionId, crate::behavior::BehaviorSummary>,
    pub imported_must_consume: HashSet<DefinitionId>,
    pub narrow_drops: Vec<NarrowDrop>,
    pub static_values: HashMap<Span, Value>,
    meta_calls: HashMap<Span, staging::MetaCall>,
    static_folds: HashMap<Span, staging::StaticFold>,
    static_conditions: HashMap<Span, staging::StaticCondition>,
    static_matches: HashMap<Span, staging::StaticMatch>,
    pub meta_if_decisions: HashMap<Span, bool>,
    pub meta_match_decisions: HashMap<Span, usize>,
    static_generic_arguments: HashMap<Span, HashMap<DefinitionId, GenericValue>>,
    static_budget: u64,
    pub(crate) meta_parameters: HashSet<DefinitionId>,
    inspection_scopes: HashMap<Span, ScopeId>,
    pub narrowings: HashMap<Span, usize>,
    pub navigation_values: HashMap<Span, Ty>,
    pub(crate) propagation_inputs: HashMap<Span, Ty>,
    nominal_layouts: HashMap<DefinitionId, Ty>,
    record_adts: HashSet<DefinitionId>,
    pub subset_tags: HashMap<Span, Vec<String>>,
    pub tuple_payloads: HashMap<Span, usize>,
    pub(crate) receptions: HashMap<Span, Vec<reception::Adjustment>>,
    pub(crate) effect_instances: BTreeMap<String, effects::Instance>,
    pub(crate) operation_effects: HashMap<Span, String>,
    pub(crate) operation_instances: HashMap<Span, effects::Instance>,
    pub(crate) effect_applications: HashMap<Span, Vec<String>>,
    pub boxed_var_captures: BTreeSet<DefinitionId>,
}

impl TypedProgram {
    pub fn inspection_scope(&self, span: Span) -> Option<ScopeId> {
        self.inspection_scopes.get(&span).copied()
    }

    pub fn is_nominal_record(&self, id: DefinitionId) -> bool {
        self.record_adts.contains(&id)
    }

    pub fn unwrap_wrapper(&self, ty: &Ty) -> Ty {
        let mut cur = ty.clone();
        let mut active: Vec<Arc<Adt>> = Vec::new();
        while let Ty::Adt(adt) = &cur {
            if !matches!(adt.kind, AdtKind::Nominal | AdtKind::Opaque) {
                break;
            }
            if active
                .iter()
                .rev()
                .find(|outer| outer.definition == adt.definition)
                .is_some_and(|outer| !nested_type_argument(outer, adt))
            {
                break;
            }
            active.push(Arc::clone(adt));
            if self.hir.unit_constructor(adt.definition) {
                return Ty::Unit;
            }
            let Some(rep) = self.nominal_layout(adt) else {
                break;
            };
            cur = rep;
        }
        cur
    }

    pub fn is_value(&self, ty: &Ty) -> bool {
        self.unwrap_wrapper(ty).is_primitive_value()
    }

    pub fn is_must_consume(&self, ty: &Ty) -> bool {
        self.is_must_consume_inner(ty, &mut HashSet::new())
    }

    fn is_must_consume_inner(&self, ty: &Ty, seen: &mut HashSet<DefinitionId>) -> bool {
        match ty {
            Ty::Callable(c) => c.is_ctl,
            Ty::Adt(adt) if adt.kind == AdtKind::Foreign => true,
            Ty::Adt(adt) => {
                if !seen.insert(adt.definition) {
                    return false;
                }
                let result = if self.imported_must_consume.contains(&adt.definition) {
                    true
                } else if matches!(adt.kind, AdtKind::Nominal | AdtKind::Opaque) {
                    self.nominal_layout(adt)
                        .is_some_and(|rep| self.is_must_consume_inner(&rep, seen))
                } else {
                    adt.arguments.iter().any(|arg| {
                        matches!(arg, GenericValue::Type(inner) if self.is_must_consume_inner(inner, seen))
                    }) || self.hir.definitions().any(|(vid, def)| {
                        def.kind == ril_hir::DefinitionKind::Variant(adt.definition)
                            && self.callables.get(&vid).is_some_and(|sig| {
                                sig.parameters
                                    .iter()
                                    .any(|p| self.is_must_consume_inner(&p.ty, seen))
                            })
                    })
                };
                seen.remove(&adt.definition);
                result
            }
            Ty::Array(item) => self.is_must_consume_inner(&item.ty, seen),
            Ty::Map(key, item) => {
                self.is_must_consume_inner(key, seen) || self.is_must_consume_inner(&item.ty, seen)
            }
            Ty::Tuple(items) => items
                .iter()
                .any(|item| self.is_must_consume_inner(&item.ty, seen)),
            Ty::Record(fields, _) => fields
                .values()
                .any(|item| self.is_must_consume_inner(&item.ty, seen)),
            _ => false,
        }
    }

    pub(crate) fn parameter_callable_mode(&self, param: &Parameter) -> Mode {
        param.callable_mode_with(self.is_value(&param.ty))
    }

    pub fn nominal_layout(&self, adt: &Adt) -> Option<Ty> {
        let layout = self.nominal_layouts.get(&adt.definition)?;
        let definition = self.hir.definition(adt.definition);
        let ast = &self.hir.file(definition.name.span.file).ast;
        let ril_syntax::syntax::StmtKind::Type(decl) = &ast.stmt(definition.stmt?).value.kind
        else {
            return None;
        };
        let arguments = decl
            .generics
            .iter()
            .zip(&adt.arguments)
            .filter_map(|(parameter, argument)| {
                match (self.hir.resolve(parameter.name.span), argument) {
                    (Some(ril_hir::Resolution::Definition(id)), GenericValue::Type(ty)) => {
                        Some((id, ty.clone()))
                    }
                    _ => None,
                }
            })
            .collect();
        Some(layout.specialize(&arguments))
    }

    pub(crate) fn effect_definition(&self, label: &str) -> Option<DefinitionId> {
        self.effect_instances
            .get(label)
            .map(|instance| instance.definition)
            .or_else(|| self.hir.effect_by_label(label))
    }

    pub(crate) fn effect_has_ctl(&self, label: &str) -> bool {
        self.effect_definition(label)
            .is_some_and(|id| self.hir.effect_has_ctl(id))
    }

    pub(crate) fn effect_covers(&self, covering: &str, actual: &str) -> bool {
        covering == actual
            || self.effect_instances.get(covering).map_or_else(
                || self.hir.effect_covers(covering, actual),
                |instance| instance.includes.contains(actual),
            )
    }

    pub fn operation_evidence(
        &self,
        operation: DefinitionId,
        occurrence: Span,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Option<String> {
        if let Some(instance) = self.operation_instances.get(&occurrence) {
            let label = instance.native_label(&self.hir, types);
            Some(format!(
                "{label}::{}",
                self.hir.definition(operation).name.value
            ))
        } else {
            self.hir.operation_label(operation)
        }
    }
}

pub struct Display<'a> {
    ty: &'a Ty,
    hir: &'a Program,
    qualified: bool,
}

impl fmt::Display for Display<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let show = |t| Display {
            ty: t,
            hir: self.hir,
            qualified: self.qualified,
        };
        match self.ty {
            Ty::Unit => f.write_str("()"),
            Ty::Bool => f.write_str("bool"),
            Ty::Int => f.write_str("int"),
            Ty::F64 => f.write_str("f64"),
            Ty::Str => f.write_str("str"),
            Ty::Bytes => f.write_str("bytes"),
            Ty::Never => f.write_str("never"),
            Ty::Range => f.write_str("Range"),
            Ty::Mode => f.write_str("FieldMode"),
            Ty::Infer(_) | Ty::Unknown => f.write_str("_"),
            Ty::Param(id) => f.write_str(&self.hir.definition(*id).name.value),
            Ty::Projection(base, key) => write!(
                f,
                "{}.({})",
                show(base),
                self.hir.definition(*key).name.value
            ),
            Ty::Adt(adt) => {
                if let Some(inner) = self.ty.as_option(self.hir) {
                    return write!(f, "?{}", show(inner));
                }
                if let Some((ok, err)) = self.ty.as_result(self.hir) {
                    return write!(f, "!<{}, {}>", show(ok), show(err));
                }
                if self.qualified {
                    f.write_str(&self.hir.export_name(adt.definition))?;
                } else {
                    f.write_str(&self.hir.definition(adt.definition).name.value)?;
                }
                if !adt.arguments.is_empty() {
                    f.write_str("<")?;
                    for (index, arg) in adt.arguments.iter().enumerate() {
                        comma(f, index)?;
                        match arg {
                            GenericValue::Type(ty) => write!(f, "{}", show(ty))?,
                            GenericValue::Data(value) => f.write_str(&render(value))?,
                            GenericValue::Mode(mode) => f.write_str(mode_name(*mode))?,
                        }
                    }
                    f.write_str(">")?;
                }
                Ok(())
            }
            Ty::Tuple(items) => {
                f.write_str("(")?;
                for (index, member) in items.iter().enumerate() {
                    comma(f, index)?;
                    member_mode(f, member.mode)?;
                    write!(f, "{}", show(&member.ty))?;
                }
                f.write_str(")")
            }
            Ty::Record(items, open) => {
                f.write_str(".{ ")?;
                for (index, (name, member)) in items.iter().enumerate() {
                    comma(f, index)?;
                    member_mode(f, member.mode)?;
                    write!(f, "{name}: {}", show(&member.ty))?;
                }
                if *open {
                    comma(f, items.len())?;
                    f.write_str("..")?;
                }
                f.write_str(" }")
            }
            Ty::Array(member) => {
                write!(f, "[{}]{}", mode_name(member.mode), show(&member.ty))
            }
            Ty::Map(key, member) => {
                write!(f, "[{}: ", show(key))?;
                member_mode(f, member.mode)?;
                write!(f, "{}]", show(&member.ty))
            }
            Ty::Callable(call) => {
                f.write_str(if call.is_ctl { "ctl(" } else { "fn(" })?;
                for (index, p) in call.parameters.iter().enumerate() {
                    comma(f, index)?;
                    member_mode(
                        f,
                        MemberMode {
                            mode: p.mode,
                            variable: false,
                        },
                    )?;
                    if let Some(label) = &p.label {
                        write!(f, "{label}: ")?;
                    }
                    write!(f, "{}", show(&p.ty))?;
                }
                f.write_str(")")?;
                if call.open_effects {
                    f.write_str(" @")?;
                }
                for effect in &call.effects {
                    write!(f, " @{effect}")?;
                }
                if call.open_state {
                    f.write_str(" &")?;
                }
                if call.once {
                    f.write_str(" &once")?;
                }
                for state in &call.state {
                    write!(f, " &{state}")?;
                }
                f.write_str(" -> ")?;
                member_mode(
                    f,
                    MemberMode {
                        mode: call.result_mode,
                        variable: false,
                    },
                )?;
                write!(f, "{}", show(&call.result))
            }
            Ty::TypeValue(Some(ty)) => write!(f, "Type<{}>", show(ty)),
            Ty::TypeValue(None) => f.write_str("Type"),
            Ty::Draft(ty) => write!(f, "Draft<{}>", show(ty)),
        }
    }
}

fn comma(f: &mut fmt::Formatter<'_>, index: usize) -> fmt::Result {
    if index != 0 {
        f.write_str(", ")?;
    }
    Ok(())
}

fn member_mode(f: &mut fmt::Formatter<'_>, mode: MemberMode) -> fmt::Result {
    let name = mode_name(mode);
    if !name.is_empty() {
        write!(f, "{name} ")?;
    }
    Ok(())
}

fn mode_name(mode: MemberMode) -> &'static str {
    match (mode.variable, mode.mode) {
        (false, Mode::Plain) => "",
        (false, Mode::Ref) => "ref",
        (false, Mode::Mut) => "mut",
        (false, Mode::Shared) => "^mut",
        (false, Mode::New) => "new",
        (false, Mode::Via) => "via",
        (false, Mode::Infer) => "infer",
        (true, Mode::Ref) => "var ref",
        (true, Mode::Mut) => "var mut",
        (true, Mode::Shared) => "var ^mut",
        (true, _) => "var",
    }
}
