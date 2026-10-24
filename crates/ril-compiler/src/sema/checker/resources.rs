use super::*;

/// Absence is evidence only after every reachable type constituent was read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ResourceScan {
    Present,
    Absent,
    Incomplete,
}
impl ResourceScan {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Present, _) | (_, Self::Present) => Self::Present,
            (Self::Incomplete, _) | (_, Self::Incomplete) => Self::Incomplete,
            _ => Self::Absent,
        }
    }
}

/// Shared by capability readers, never by type normalization. A growing
/// generic family is different from a backedge to the same complete instance.
#[derive(Default)]
pub(super) struct TypeScanBudget {
    nodes: usize,
    pub(super) instances: BTreeSet<String>,
}
impl TypeScanBudget {
    pub(super) fn node(&mut self) -> bool {
        if self.nodes == 4096 {
            return false;
        }
        self.nodes += 1;
        true
    }
    pub(super) fn instance(&mut self, key: &str) -> bool {
        if self.instances.contains(key) {
            return true;
        }
        self.instances.len() < 128 && self.instances.insert(key.into())
    }
    fn shape(&mut self, ty: &Ty) -> bool {
        let mut pending = vec![ty];
        while let Some(ty) = pending.pop() {
            if !self.node() {
                return false;
            }
            match ty {
                Ty::Immutable(inner)
                | Ty::Optional(inner)
                | Ty::Array(inner)
                | Ty::Set(inner)
                | Ty::Range(inner) => pending.push(inner),
                Ty::Map(a, b) | Ty::Result(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
                Ty::Tuple(items) => pending.extend(items),
                Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                    pending.extend(fields.values().map(|(_, ty)| ty))
                }
                Ty::Callable(parameters, result) => {
                    pending.extend(parameters);
                    pending.push(result);
                }
                Ty::Projection { base, .. } => pending.push(base),
                Ty::Applied { arguments, .. } => {
                    pending.extend(arguments.iter().filter_map(|argument| match argument {
                        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                            Some(ty.as_ref())
                        }
                        _ => None,
                    }))
                }
                _ => {}
            }
        }
        true
    }
    /// Charge before shallow conversion can allocate the syntax's structure.
    pub(super) fn syntax(&mut self, syntax: &TypeExpr) -> bool {
        let mut pending = vec![syntax];
        while let Some(syntax) = pending.pop() {
            if !self.node() {
                return false;
            }
            match &syntax.kind {
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    pending.extend(arguments)
                }
                TypeKind::Optional(inner)
                | TypeKind::Rest(inner)
                | TypeKind::KeyOf(inner)
                | TypeKind::Array { element: inner, .. } => pending.push(inner),
                TypeKind::Record { fields, row } => {
                    pending.extend(fields.iter().map(|field| &field.ty));
                    pending.extend(row.as_deref());
                }
                TypeKind::Map { key, value } => pending.extend([key.as_ref(), value.as_ref()]),
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    pending.extend(
                        parameters
                            .iter()
                            .filter_map(|parameter| parameter.ty.as_ref()),
                    );
                    pending.extend(result.as_deref());
                }
                TypeKind::Projection { base, .. } | TypeKind::ComputedProjection { base, .. } => {
                    pending.push(base)
                }
                _ => {}
            }
        }
        true
    }
}

impl Checker {
    /// Identity reads never expand aliases and retain every argument sort and
    /// the full normalized source key, including dimensions and callable modes.
    pub(super) fn capability_type_key(
        &self,
        ty: &Ty,
        budget: &mut TypeScanBudget,
    ) -> Option<String> {
        fn complete_argument(ty: &Ty) -> bool {
            let mut pending = vec![ty];
            let mut nodes = 0;
            while let Some(ty) = pending.pop() {
                nodes += 1;
                if nodes > 4096 {
                    return false;
                }
                match ty {
                    // These runtime shapes omit source identity metadata.
                    Ty::Array(_)
                    | Ty::Callable(..)
                    | Ty::OpenRecord { .. }
                    | Ty::Projection { .. }
                    | Ty::Unknown
                    | Ty::NumericHole(_) => return false,
                    Ty::Immutable(inner)
                    | Ty::Optional(inner)
                    | Ty::Set(inner)
                    | Ty::Range(inner) => pending.push(inner),
                    Ty::Map(a, b) | Ty::Result(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
                    Ty::Tuple(items) => pending.extend(items),
                    Ty::Record(fields) => pending.extend(fields.values().map(|(_, ty)| ty)),
                    Ty::Applied { arguments, .. } => {
                        pending.extend(arguments.iter().filter_map(|argument| match argument {
                            TypeArgument::Type(ty) => Some(ty.as_ref()),
                            _ => None,
                        }))
                    }
                    _ => {}
                }
            }
            true
        }
        if !budget.node() {
            return None;
        }
        let mut child = |ty: &Ty| self.capability_type_key(ty, budget);
        let key = match ty {
            Ty::Named(name) => format!(
                "named:{:?}",
                self.types.get(name).map_or(name, |decl| &decl.name)
            ),
            Ty::Applied {
                constructor,
                arguments,
            } => {
                let name = self
                    .types
                    .get(constructor)
                    .map_or(constructor, |decl| &decl.name);
                let mut keys = Vec::new();
                for argument in arguments {
                    keys.push(match argument {
                        TypeArgument::CanonicalType { key, ty } => {
                            // Budget the carried shape before any substitution
                            // clones it, but keep its complete source key.
                            let _ = child(ty)?;
                            format!("canonical:{key:?}")
                        }
                        TypeArgument::Static(key) => format!("static:{key:?}"),
                        TypeArgument::Symbolic(identity) => format!("symbolic:{identity:?}"),
                        TypeArgument::Type(ty) => {
                            if !complete_argument(ty) {
                                return None;
                            }
                            format!("type:{}", child(ty)?)
                        }
                    });
                }
                format!("applied:{name:?}:{keys:?}")
            }
            Ty::Immutable(inner) => format!("immutable:{}", child(inner)?),
            Ty::Optional(inner) => format!("optional:{}", child(inner)?),
            Ty::Array(inner) => format!("array:{}", child(inner)?),
            Ty::Set(inner) => format!("set:{}", child(inner)?),
            Ty::Range(inner) => format!("range:{}", child(inner)?),
            Ty::Result(a, b) => format!("result:({},{})", child(a)?, child(b)?),
            Ty::Map(a, b) => format!("map:({},{})", child(a)?, child(b)?),
            Ty::Tuple(items) => format!(
                "tuple:{:?}",
                items.iter().map(&mut child).collect::<Option<Vec<_>>>()?
            ),
            Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                let keys = fields
                    .iter()
                    .map(|(name, (mutable, ty))| Some((name, mutable, child(ty)?)))
                    .collect::<Option<Vec<_>>>()?;
                let row = match ty {
                    Ty::OpenRecord { row, .. } => Some(row),
                    _ => None,
                };
                format!("record:{keys:?}:{row:?}")
            }
            Ty::Callable(parameters, result) => format!(
                "callable:{:?}:{}",
                parameters
                    .iter()
                    .map(&mut child)
                    .collect::<Option<Vec<_>>>()?,
                child(result)?
            ),
            Ty::Projection { base, key } => format!("projection:{}:{key:?}", child(base)?),
            _ => format!("{ty:?}"),
        };
        Some(key)
    }
    /// Peel top aliases only. Descendants are read independently rather than
    /// duplicated into an exponentially large representation tree.
    pub(super) fn capability_shallow_type(&self, ty: &Ty) -> Option<Ty> {
        self.capability_shallow_type_with_budget(ty, &mut TypeScanBudget::default())
    }
    pub(super) fn capability_shallow_type_with_budget(
        &self,
        ty: &Ty,
        budget: &mut TypeScanBudget,
    ) -> Option<Ty> {
        if !budget.shape(ty) {
            return None;
        }
        self.capability_type_key(ty, budget)?;
        let mut active = BTreeSet::new();
        let mut shape = ty.clone();
        loop {
            if let Ty::Named(name) = &shape
                && !self.types.contains_key(name)
                && let Some(builtin) =
                    concurrent::builtin_type(name).or_else(|| standard::file_type(name))
                && builtin != shape
            {
                if !budget.shape(&builtin) {
                    return None;
                }
                shape = builtin;
                continue;
            }
            let declaration = match &shape {
                Ty::Named(name) => self.types.get(name),
                Ty::Applied {
                    constructor,
                    arguments,
                } => self
                    .types
                    .get(constructor)
                    .filter(|decl| decl.generics.len() == arguments.len()),
                _ => None,
            };
            let Some(declaration) = declaration else {
                return Some(shape);
            };
            if declaration.nominal
                || !declaration.variants.is_empty()
                || (declaration.opaque && self.declaration_files.contains(&declaration.span.file.0))
            {
                return Some(shape);
            }
            let Some(body) = &declaration.value else {
                return Some(shape);
            };
            let key = self.capability_type_key(&shape, budget)?;
            if !active.insert(key.clone()) || !budget.instance(&key) || !budget.syntax(body) {
                return None;
            }
            let substitutions = match &shape {
                Ty::Applied { arguments, .. } => declaration
                    .generics
                    .iter()
                    .zip(arguments)
                    .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
                    .collect(),
                _ => BTreeMap::new(),
            };
            shape = self.ty_substituted_shallow(body, &substitutions);
        }
    }
    /// Resource eligibility follows the private graph as well as public shape.
    /// A wrapper or immutable/read-only path is not an exemption.
    pub(super) fn foreign_opaque_type(&self, ty: &Ty) -> bool {
        let name = match ty {
            Ty::Named(name)
            | Ty::Applied {
                constructor: name, ..
            } => name,
            _ => return false,
        };
        self.types.get(name).is_some_and(|decl| {
            decl.value.is_none()
                && decl.variants.is_empty()
                && self.declaration_files.contains(&decl.span.file.0)
        })
    }
    pub(super) fn resource_scan_type(&self, ty: &Ty) -> ResourceScan {
        ResourceTypeReader::default().visit(self, ty)
    }
    /// Compatibility entry point: false is not an absence proof.
    pub(super) fn resource_type(&self, ty: &Ty) -> bool {
        self.resource_scan_type(ty) == ResourceScan::Present
    }
    pub(super) fn resource_scan_value(&self, value: &Value) -> ResourceScan {
        let mut reader = ResourceTypeReader::default();
        let mut result = ResourceScan::Absent;
        let mut pending = vec![value];
        let mut nodes = BTreeSet::new();
        let mut bindings = BTreeSet::new();
        while let Some(value) = pending.pop() {
            if !reader.budget.node() {
                return result.merge(ResourceScan::Incomplete);
            }
            result = result.merge(reader.value_type(self, value, &value.ty));
            if result == ResourceScan::Present {
                return result;
            }
            pending.extend(
                [
                    &value.variant_payload,
                    &value.option_payload,
                    &value.result_payload,
                    &value.result_success,
                    &value.result_error,
                ]
                .into_iter()
                .flatten()
                .map(Box::as_ref),
            );
            pending.extend(value.variant_witnesses.values().map(Box::as_ref));
            for origin in &value.origins.nodes {
                if nodes.insert(*origin) {
                    pending.extend(
                        self.fields
                            .iter()
                            .filter_map(|((parent, _), child)| (parent == origin).then_some(child)),
                    );
                }
            }
            for callable in &value.callables {
                let captures = match callable {
                    Callable::Named(id, _) => Some(&self.functions[*id].captures),
                    Callable::Closure(id) => Some(&self.closures[*id].captures),
                    Callable::Symbolic(..) => {
                        result = result.merge(ResourceScan::Incomplete);
                        None
                    }
                    _ => None,
                };
                if let Some(captures) = captures {
                    for binding in captures {
                        if bindings.insert(*binding) {
                            pending.push(&self.bindings[*binding].value);
                        }
                    }
                }
            }
        }
        result
    }
    /// Positive evidence only. Use `resource_free` when absence is required.
    pub(super) fn contains_resource(&self, value: &Value) -> bool {
        self.resource_scan_value(value) == ResourceScan::Present
    }
    pub(super) fn resource_free(&self, value: &Value) -> bool {
        !self.has_unresolved_row(value) && self.resource_scan_value(value) == ResourceScan::Absent
    }
    pub(super) fn is_file_handle(&self, value: &Value) -> bool {
        matches!(self.expanded(&value.ty,&mut BTreeSet::new()),Ty::Named(name)if name=="File::Handle")
    }
}

#[derive(Default)]
struct ResourceTypeReader {
    budget: TypeScanBudget,
    active: BTreeSet<String>,
    complete: BTreeMap<String, ResourceScan>,
}
impl ResourceTypeReader {
    /// Selected sum payloads and complete closed storage are actual value
    /// evidence. Inactive inference holes do not denote reachable resources.
    fn value_type(&mut self, checker: &Checker, value: &Value, ty: &Ty) -> ResourceScan {
        use ResourceScan::*;
        fn complete_slots(checker: &Checker, value: &Value, slots: &[Slot]) -> bool {
            !value.origins.nodes.is_empty()
                && value.origins.nodes.iter().all(|node| {
                    slots.iter().all(|slot| {
                        checker.fields.contains_key(&(*node, slot.clone()))
                            && !checker.uncertain_slots.contains(&(*node, slot.clone()))
                    })
                })
        }
        match ty {
            Ty::Named(_) | Ty::Applied { .. } => {
                if let Some(shape) =
                    checker.capability_shallow_type_with_budget(ty, &mut self.budget)
                    && shape != *ty
                {
                    return self.value_type(checker, value, &shape);
                }
                self.visit(checker, ty)
            }
            Ty::Immutable(inner) => {
                if !self.budget.node() {
                    return Incomplete;
                }
                self.value_type(checker, value, inner)
            }
            Ty::Optional(_) if value.option_tag == Some(false) => Absent,
            Ty::Optional(_) if value.option_tag == Some(true) && value.option_payload.is_some() => {
                Absent
            }
            Ty::Result(_, _)
                if match value.result_tag {
                    Some(true) => value.result_success.is_some() || value.result_payload.is_some(),
                    Some(false) => value.result_error.is_some() || value.result_payload.is_some(),
                    None => value.result_success.is_some() && value.result_error.is_some(),
                } =>
            {
                Absent
            }
            Ty::Record(fields)
                if complete_slots(
                    checker,
                    value,
                    &fields
                        .keys()
                        .map(|name| Slot::Field(name.clone()))
                        .collect::<Vec<_>>(),
                ) =>
            {
                Absent
            }
            Ty::Tuple(items)
                if complete_slots(
                    checker,
                    value,
                    &(0..items.len())
                        .map(|index| Slot::Tuple(index as u32))
                        .collect::<Vec<_>>(),
                ) =>
            {
                Absent
            }
            Ty::Array(_)
                if !value.origins.nodes.is_empty()
                    && value.origins.nodes.iter().all(|node| {
                        checker
                            .array_lengths
                            .get(node)
                            .copied()
                            .flatten()
                            .is_some_and(|length| {
                                (0..length).all(|index| {
                                    checker
                                        .fields
                                        .contains_key(&(*node, Slot::Index(index as i64)))
                                        && !checker
                                            .uncertain_slots
                                            .contains(&(*node, Slot::Index(index as i64)))
                                })
                            })
                    }) =>
            {
                Absent
            }
            _ => self.visit(checker, ty),
        }
    }
    fn visit(&mut self, checker: &Checker, ty: &Ty) -> ResourceScan {
        use ResourceScan::*;
        if !self.budget.node() {
            return Incomplete;
        }
        match ty {
            Ty::Unknown | Ty::NumericHole(_) | Ty::Generic(_) | Ty::Projection { .. } => Incomplete,
            Ty::Optional(inner)
            | Ty::Immutable(inner)
            | Ty::Array(inner)
            | Ty::Set(inner)
            | Ty::Range(inner) => self.visit(checker, inner),
            Ty::Map(a, b) | Ty::Result(a, b) => {
                let left = self.visit(checker, a);
                if left == Present {
                    return Present;
                }
                left.merge(self.visit(checker, b))
            }
            Ty::Tuple(items) => self.children(checker, items.iter()),
            Ty::Record(fields) => self.children(checker, fields.values().map(|(_, ty)| ty)),
            Ty::OpenRecord { fields, .. } => {
                Incomplete.merge(self.children(checker, fields.values().map(|(_, ty)| ty)))
            }
            Ty::Named(name)
            | Ty::Applied {
                constructor: name, ..
            } => {
                if matches!(
                    name.as_str(),
                    "File::Handle"
                        | "Process::Child"
                        | "Concurrent::Scope"
                        | "Concurrent::Task"
                        | "Channel::Sender"
                        | "Channel::Receiver"
                        | "Channel::Detached"
                ) || checker.foreign_opaque_type(ty)
                {
                    return Present;
                }
                if !checker.types.contains_key(name)
                    && let Some(builtin) =
                        concurrent::builtin_type(name).or_else(|| standard::file_type(name))
                    && builtin != *ty
                {
                    return self.visit(checker, &builtin);
                }
                let Some(key) = checker.capability_type_key(ty, &mut self.budget) else {
                    return Incomplete;
                };
                if self.active.contains(&key) {
                    return Absent;
                }
                if let Some(result) = self.complete.get(&key) {
                    return *result;
                }
                if !self.budget.instance(&key) {
                    return Incomplete;
                }
                self.active.insert(key.clone());
                let mut result = Absent;
                let substitutions = match ty {
                    Ty::Applied { arguments, .. } => {
                        for argument in arguments {
                            result = result.merge(match argument {
                                TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => {
                                    self.visit(checker, ty)
                                }
                                TypeArgument::Symbolic(_) => Incomplete,
                                TypeArgument::Static(_) => Absent,
                            });
                        }
                        checker
                            .types
                            .get(name)
                            .filter(|decl| decl.generics.len() == arguments.len())
                            .map(|decl| {
                                decl.generics
                                    .iter()
                                    .zip(arguments)
                                    .map(|(parameter, argument)| {
                                        (parameter.name.clone(), argument.clone())
                                    })
                                    .collect()
                            })
                    }
                    _ => Some(BTreeMap::new()),
                };
                if result != Present {
                    // Standard sums are registered semantic constructors even
                    // when they have no user TypeDeclaration entry.
                    let mut witnessed = false;
                    for constructor in checker
                        .constructors
                        .values()
                        .filter(|constructor| constructor.owner == *ty)
                    {
                        witnessed = true;
                        if constructor.has_payload {
                            result = result.merge(self.visit(checker, &constructor.payload));
                        }
                    }
                    if let Some(declaration) = checker.types.get(name) {
                        if let Some(substitutions) = substitutions {
                            if !declaration.nominal
                                && declaration.variants.is_empty()
                                && let Some(body) = &declaration.value
                            {
                                result = result.merge(if self.budget.syntax(body) {
                                    self.visit(
                                        checker,
                                        &checker.ty_substituted_shallow(body, &substitutions),
                                    )
                                } else {
                                    Incomplete
                                });
                            }
                            if !witnessed
                                && (declaration.nominal && declaration.value.is_some()
                                    || declaration
                                        .variants
                                        .iter()
                                        .any(|variant| variant.payload.is_some()))
                            {
                                result = result.merge(Incomplete);
                            }
                        } else {
                            result = result.merge(Incomplete);
                        }
                    } else if !witnessed
                        && !ty.scalar()
                        && !matches!(name.as_str(), "Random::Rng" | "Deque::Deque" | "Heap::Heap")
                    {
                        result = result.merge(Incomplete);
                    }
                }
                self.active.remove(&key);
                self.complete.insert(key, result);
                result
            }
            // Signatures are not captured graphs; the value reader independently
            // checks each environment and symbolic capture.
            _ => Absent,
        }
    }
    fn children<'a>(
        &mut self,
        checker: &Checker,
        children: impl Iterator<Item = &'a Ty>,
    ) -> ResourceScan {
        let mut result = ResourceScan::Absent;
        for ty in children {
            result = result.merge(self.visit(checker, ty));
            if result == ResourceScan::Present {
                break;
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checker(source: &str) -> Checker {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        checker
    }
    #[test]
    fn binary_recursive_aliases_are_finite_without_losing_a_resource_sibling() {
        for (extra, expected) in [
            ("", ResourceScan::Absent),
            (",file:File::Handle", ResourceScan::Present),
        ] {
            let checker = checker(&format!(
                "type Node={{mut left:?Node,mut right:?Node{extra}}}"
            ));
            let ty = Ty::Named("Node".into());
            assert_eq!(checker.resource_scan_type(&ty), expected);
            assert_eq!(
                checker.ordinary_data_type(&ty),
                expected == ResourceScan::Absent
            );
            let Ty::Record(fields) = checker.capability_shallow_type(&ty).unwrap() else {
                panic!()
            };
            assert_eq!(fields["left"].1, Ty::Optional(Box::new(ty)));
        }
    }
    #[test]
    fn different_and_growing_generic_instances_do_not_share_backedges() {
        let checker = checker(
            "type Node<T>={left:?Node<T>,right:?Node<T>,value:T}\ntype Grow<T>={left:?Grow<[]T>,right:?Grow<[]T>}",
        );
        let instance = |constructor: &str, ty: Ty, key: &str| Ty::Applied {
            constructor: constructor.into(),
            arguments: vec![TypeArgument::CanonicalType {
                ty: Box::new(ty),
                key: key.into(),
            }],
        };
        let ordinary = instance("Node", Ty::Int("int".into()), "int<>");
        let resource = instance("Node", Ty::Named("File::Handle".into()), "File::Handle<>");
        assert_eq!(checker.resource_scan_type(&ordinary), ResourceScan::Absent);
        assert_eq!(
            checker.resource_scan_type(&Ty::Tuple(vec![ordinary, resource])),
            ResourceScan::Present
        );
        let growing = instance("Grow", Ty::Int("int".into()), "int<>");
        assert_eq!(
            checker.resource_scan_type(&growing),
            ResourceScan::Incomplete
        );
        assert!(!checker.ordinary_data_type(&growing));
    }
    #[test]
    fn complete_keys_and_canonical_declaration_names_determine_instance_identity() {
        let mut checker = checker("type Token<T>(int)\ntype Node={following:?Node}");
        checker
            .types
            .insert("Renamed".into(), checker.types["Node"].clone());
        let key = |ty: &Ty| {
            checker
                .capability_type_key(ty, &mut TypeScanBudget::default())
                .unwrap()
        };
        assert_eq!(
            key(&Ty::Named("Node".into())),
            key(&Ty::Named("Renamed".into()))
        );
        let instance = |key: &str| Ty::Applied {
            constructor: "Token".into(),
            arguments: vec![TypeArgument::CanonicalType {
                ty: Box::new(Ty::Array(Box::new(Ty::Int("int".into())))),
                key: key.into(),
            }],
        };
        assert_ne!(
            key(&instance("[int:2]int<>")),
            key(&instance("[int:3]int<>"))
        );
        assert_ne!(
            key(&instance("fn(Read:int<>)->int<>")),
            key(&instance("fn(Mut:int<>)->int<>"))
        );
    }
    #[test]
    fn unknown_and_exhausted_shapes_never_establish_resource_absence() {
        let checker = Checker::new(FileId(0));
        for ty in [
            Ty::Unknown,
            Ty::Generic("T".into()),
            Ty::Tuple(vec![Ty::Unit; 4097]),
        ] {
            assert_eq!(checker.resource_scan_type(&ty), ResourceScan::Incomplete);
            let value = Value::scalar(ty, None, CauseId(0));
            assert!(!checker.resource_free(&value));
        }
        let mut absent = Value::scalar(Ty::Optional(Box::new(Ty::Unknown)), None, CauseId(0));
        absent.option_tag = Some(false);
        assert_eq!(checker.resource_scan_value(&absent), ResourceScan::Absent);
    }
    #[test]
    fn original_binary_recursive_clone_reaches_session_and_core() {
        let source = "type Node={mut left:?Node,mut right:?Node}\nfn example(){let mut node=Node.{left:None,right:None};node.left=Some(^mut node);node.right=Some(^mut node);let mut copied=^mut clone(node);copied.left=None}";
        let verified = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .expect("finite original Session");
        let _core = crate::lower::lower_core(&verified).expect("finite original Core");
    }
    #[test]
    fn cancelling_scope_keeps_its_closed_standard_fault_graph_publishable() {
        let source = r#"
use ril/concurrent::{scope, TaskFault}
use ril/time
eff Read { get() -> int }
type Guard = { on_close: fn() -> () }
var trace = 0
fn clean() &{mut trace} { with Read::get() -> resume 1; trace += Read::get() }
pub fn test_native() @Async &{mut trace} {
    let result = scope \mut s -> {
        s.fork(\-> { Time::sleep(Time::duration_nanos(50000000i64)); panic("child") })
        let scoped guard = Guard.{on_close: clean}
        loop { Fiber::yield() }
        Ok()
    }
    assert(result is Err(TaskFault::Panicked(_)))
    assert(trace == 1)
}
"#;
        crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .expect("closed TaskFault / UnwindCause constructors are complete evidence");
        let mut checker = Checker::new(FileId(0));
        checker.run(&ril_syntax::parse("fn example(){}").program);
        assert_eq!(
            checker.resource_scan_type(&Ty::Named("Concurrent::TaskFault".into())),
            ResourceScan::Absent
        );
        assert_eq!(
            checker.resource_scan_type(&Ty::Named("Concurrent::UnwindCause".into())),
            ResourceScan::Absent
        );
        assert_eq!(
            checker.resource_scan_type(&Ty::Named("unregistered".into())),
            ResourceScan::Incomplete
        );
    }
}
