//! Complete scoped source identity preparation. An open key is never made into
//! a closed witness; closed product identities select their actual stored T.
use super::*;
use crate::sema::{
    copy_contract::CopyValueSnapshot,
    effect_identity::{ArgumentKey, StaticBinderSort},
    scoped_source_identity::{FormalSourceAnchor, ScopedSourceIdentity, ScopedSourceOccurrence},
};
use ril_compiler_core::ids::ScopedSourceIdentityId;
use std::sync::Arc;

fn selected_entry<'a>(
    snapshot: &'a CopyValueSnapshot,
    path: &[BoundTypeSelectionStep],
) -> Option<&'a Value> {
    let mut value = &snapshot.value;
    for step in path {
        let slot = match step {
            BoundTypeSelectionStep::Tuple(index) => Slot::Tuple(*index),
            BoundTypeSelectionStep::Field(label) => Slot::Field(label.clone()),
            _ => return None,
        };
        if value.origins.nodes.len() != 1 {
            return None;
        }
        let origin = *value.origins.nodes.first()?;
        value = snapshot
            .nodes
            .iter()
            .find(|node| node.origin == origin)?
            .fields
            .iter()
            .find(|(stored, _)| stored == &slot)
            .map(|(_, value)| value)?;
    }
    Some(value)
}

fn exact_occurrences(ty: &Ty, binder: &str, depth: usize, work: &mut usize) -> Option<bool> {
    *work = work.checked_sub(1)?;
    if depth >= 64 {
        return None;
    }
    Some(match ty {
        Ty::Generic(_) => true,
        Ty::Tuple(items) => {
            let mut all = true;
            for item in items {
                all &= exact_occurrences(item, binder, depth + 1, work)?;
            }
            all
        }
        Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
            if matches!(ty,Ty::OpenRecord {row,..} if matches!(&row.identity,RowIdentity::Binder(identity) if identity == binder))
            {
                return Some(false);
            }
            let mut all = true;
            for (_, item) in fields.values() {
                all &= exact_occurrences(item, binder, depth + 1, work)?;
            }
            all
        }
        _ => {
            let mut mentioned = BTreeSet::new();
            ty.generic_names(&mut mentioned);
            !mentioned.contains(binder)
        }
    })
}

/// `ArgumentKey::is_closed` does not certify symbolic dimension strings.
/// Constant normalized dimensions are admitted here; unknown computations stay
/// an obligation. All other names are checked by independent source replay.
fn complete_key(key: &ArgumentKey, depth: usize, work: &mut usize) -> Option<()> {
    *work = work.checked_sub(1)?;
    if depth >= 64 {
        return None;
    }
    let mut child = |key| complete_key(key, depth + 1, work);
    match key {
        ArgumentKey::Closed(_) => return None,
        ArgumentKey::Binder { .. } | ArgumentKey::GenericBuiltin(_) => {}
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
            for key in arguments {
                child(key)?;
            }
        }
        ArgumentKey::Array { length, element } => {
            if let Some(length) = length {
                length
                    .strip_prefix("const(int:")?
                    .strip_suffix(')')?
                    .parse::<u64>()
                    .ok()?;
            }
            child(element)?;
        }
        ArgumentKey::Map { key, value } => {
            child(key)?;
            child(value)?;
        }
        ArgumentKey::Record { fields, row } => {
            for (_, _, key) in fields {
                child(key)?;
            }
            if let Some(row) = row {
                child(row)?;
            }
        }
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => {
            if annotations.iter().any(|annotation| {
                !matches!(
                    annotation.as_str(),
                    "&mut" | "&^mut" | "&closure" | "&capture" | "@{}" | "&{}"
                )
            }) {
                return None;
            }
            for (_, key) in parameters {
                child(key)?;
            }
            child(result)?;
        }
    }
    Some(())
}

/// Different opaque rows alone are an unresolved equation. A different mode
/// or complete closed identity of the same known field is a concrete conflict.
fn known_field_conflict(left: &ArgumentKey, right: &ArgumentKey) -> bool {
    let (ArgumentKey::Record { fields: left, .. }, ArgumentKey::Record { fields: right, .. }) =
        (left, right)
    else {
        return false;
    };
    left.iter().any(|(name, mode, key)| {
        right.iter().any(|(other, other_mode, other_key)| {
            name == other
                && (mode != other_mode
                    || (key.is_closed() && other_key.is_closed() && key != other_key)
                    || super::symbolic_members::definite_member_conflict(key, other_key, 0))
        })
    })
}

impl Checker {
    pub(super) fn symbolic_schema_anchor(
        &self,
        value: &Value,
        context: &crate::sema::effect_identity::InvocationContext,
        schema: &StructuralSchema,
    ) -> bool {
        context.invocation.is_some_and(|invocation| {
            self.formal_source_anchor(invocation, value, schema)
                .is_some()
        })
    }
    /// The enclosing formal may have an open annotation while this invocation
    /// received a closed record. Select that actual existing T child instead of
    /// trying to close the enclosing annotation or inventing an element for T.
    pub(in crate::sema::checker) fn closed_product_bound_identity(
        &mut self,
        binder: &str,
        templates: &[Option<Ty>],
    ) -> Option<Arc<SourceTypeWitness>> {
        let required = *self.record_bounds_by_binder.get(binder)?;
        let bound = self.record_bounds.get(required.0 as usize)?;
        let invocation = *self.copy_invocation_stack.last()?;
        let call = self.copy_invocations.get(invocation.0 as usize)?;
        let function = self
            .functions
            .iter()
            .find(|function| function.definition == call.target)?;
        if call.target != bound.definition
            || call.entry.arguments.len() != function.syntax.parameters.len()
            || templates.len() != function.syntax.parameters.len()
        {
            return None;
        }
        let span = call.span;
        let context = self.invocation_context(Some(CallableOwner::Function(call.target)));
        let mut paths = Vec::new();
        let mut work = 4096;
        for (argument, template) in templates.iter().enumerate() {
            if let Some(template) = template {
                if !exact_occurrences(template, binder, 0, &mut work)? {
                    return None;
                }
                paths.extend(
                    Self::exact_record_bound_paths(template, binder)?
                        .into_iter()
                        .map(|path| (argument, path)),
                );
            }
        }
        if paths.is_empty() {
            return None;
        }
        let mut common: Option<Arc<SourceTypeWitness>> = None;
        for (argument, path) in paths {
            let (mode, entry) = self.copy_invocations[invocation.0 as usize]
                .entry
                .arguments
                .get(argument)?;
            if *mode != Mode::Read {
                return None;
            }
            let selected = selected_entry(entry, &path)?.clone();
            if !matches!(selected.ty, Ty::Record(_)) {
                return None;
            }
            let schema = self.structural_schema(&selected, &context, span)?;
            let StructuralSchemaSource::Closed(witness) = schema.source else {
                return None;
            };
            if !witness.validate_closed() {
                return None;
            }
            if common
                .as_ref()
                .is_some_and(|previous| previous.key != witness.key)
            {
                self.error("E0301",span,
                    "one generic structural type selected different complete actual product identities",
                    [selected.cause]);
                return None;
            }
            common = Some(witness);
        }
        common
    }

    /// A complete scoped descriptor replaces only the missing type-identity
    /// obligation. It never enters the closed witness table or authorizes an
    /// access. Missing original reception evidence keeps the caller's NI.
    pub(in crate::sema::checker) fn admit_scoped_source_identity(
        &mut self,
        binder: &str,
        templates: &[Option<Ty>],
    ) -> bool {
        let Some(ordinal) = u32::try_from(self.scoped_source_identities.len()).ok() else {
            return false;
        };
        let before = self.diagnostics.len();
        let Some(identity) =
            self.prepare_scoped_source_identity(ScopedSourceIdentityId(ordinal), binder, templates)
        else {
            return self.diagnostics[before..]
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301");
        };
        self.scoped_source_identities.push(identity);
        true
    }

    fn complete_rigid_key(&self, schema: &StructuralSchema) -> Option<ArgumentKey> {
        if !matches!(schema.source, StructuralSchemaSource::RigidParameter { .. }) {
            return None;
        }
        let row = match &schema.tail {
            RowTail::Open(OpenTail {
                identity: RowIdentity::Binder(identity),
                ..
            }) => Some(Box::new(ArgumentKey::Binder {
                identity: identity.clone(),
                sort: StaticBinderSort::Type,
            })),
            _ => return None,
        };
        let mut fields: Vec<_> = schema
            .fields
            .iter()
            .map(|field| (field.label.clone(), field.mutable, field.key.clone()))
            .collect();
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        let key = ArgumentKey::Record { fields, row };
        complete_key(&key, 0, &mut 4096)?;
        Some(key)
    }

    fn scoped_rigid_source(
        &self,
        invocation: super::super::super::copy_templates::InstanceId,
        selected: &Value,
    ) -> Option<(StructuralSchema, FormalSourceAnchor, ArgumentKey)> {
        let canonical = self.call_inference_type(&selected.ty);
        let Ty::OpenRecord { fields, row } = &canonical else {
            return None;
        };
        let mut found = None;
        let mut work = 4096usize;
        for schema in self.rigid_record_parameters.values().flatten() {
            work = work.checked_sub(1)?;
            if !matches!(&schema.tail, RowTail::Open(tail) if tail.identity == row.identity)
                || schema.fields.len() != fields.len()
                || !schema.fields.iter().all(|field| {
                    fields.get(&field.label) == Some(&(field.mutable, field.ty.clone()))
                })
            {
                continue;
            }
            // Equal erased Ty values do not choose a source header. Each
            // candidate must be the exact original stored child of this value.
            let Some(anchor) = self.formal_source_anchor(invocation, selected, schema) else {
                continue;
            };
            let key = self.complete_rigid_key(schema)?;
            if found.is_some() {
                return None;
            }
            found = Some((schema.clone(), anchor, key));
        }
        found
    }

    fn formal_source_anchor(
        &self,
        current: super::super::super::copy_templates::InstanceId,
        selected: &Value,
        schema: &StructuralSchema,
    ) -> Option<FormalSourceAnchor> {
        let StructuralSchemaSource::RigidParameter {
            definition,
            parameter_index,
            syntax,
            scope,
        } = &schema.source
        else {
            return None;
        };
        if selected.origins.nodes.is_empty() {
            return None;
        }
        let info = self
            .functions
            .iter()
            .find(|function| function.definition == *definition)?;
        let parameter = info.syntax.parameters.get(*parameter_index as usize)?;
        if parameter.mode != ParameterMode::Read {
            return None;
        }
        let PatternKind::Name(name) = &parameter.pattern.kind else {
            return None;
        };
        let header = parameter.ty.as_ref()?;
        let mut child = self.copy_invocations.get(current.0 as usize)?;
        let mut visited = BTreeSet::new();
        let (source, activation) = loop {
            let parent = child.parent?;
            if !visited.insert(parent) || visited.len() > 256 {
                return None;
            }
            let source = self.copy_invocations.get(parent.0 as usize)?;
            if source.target == *definition
                && child.caller == Some(*definition)
                && child.caller_owner == Some(CallableOwner::Function(*definition))
            {
                break (source, child.caller_activation?);
            }
            child = source;
        };
        // A present selected argument is not evidence that the rest of the
        // original entry table was recorded. Defaults need their own complete
        // receiving entry before this conservative path can admit them.
        if source.entry.arguments.len() != info.syntax.parameters.len() {
            return None;
        }
        let (mode, entry) = source.entry.arguments.get(*parameter_index as usize)?;
        if *mode != Mode::Read || source.entry.allocation_epoch != self.recency_moves.len() {
            return None;
        }
        let mut bindings = self.bindings.iter().enumerate().filter(|(_, binding)| {
            binding.parameter
                && binding.owner == activation
                && &binding.name == name
                && binding.span == parameter.pattern.span
        });
        let (binding_id, binding) = bindings.next()?;
        if bindings.next().is_some()
            || binding.root.0 != u32::try_from(binding_id).ok()?
            || binding.value.origins != entry.value.origins
            || binding.forwarded != entry.value.sources
            || binding.mode != BindingMode::Let
            || binding.value.sources != BTreeSet::from([binding_id])
        {
            return None;
        }
        // The frozen expression index is an execution occurrence. Its source
        // token and the complete Read reception are checked independently;
        // agreeing caller/activation metadata alone cannot provide this root.
        let root_expression = self
            .application_effect
            .contexts
            .iter()
            .enumerate()
            .find_map(|(index, observation)| {
                let expression = self
                    .application_effect
                    .expressions
                    .get(observation.expression)?;
                (observation.context.invocation == Some(source.id)
                    && observation.context.owner == Some(CallableOwner::Function(*definition))
                    && expression.value.sources == BTreeSet::from([binding_id])
                    && expression.value.origins == entry.value.origins
                    && expression.value.permission == Permission::Read)
                    .then_some(index)
            })?;

        // Pair source syntax with the immutable original argument graph. The
        // current value's metadata is not used to choose a header type.
        let mut pending = vec![(header, &entry.value, Vec::new(), 0usize)];
        let mut found = Vec::new();
        let mut work = 4096usize;
        while let Some((header, value, path, depth)) = pending.pop() {
            if work == 0 || depth >= 64 {
                return None;
            }
            work -= 1;
            if value.origins == selected.origins && header.span == syntax.span {
                // Scope is later reconstructed from the real declaration.
                if self.record_bound_key(header, scope)? == self.record_bound_key(syntax, scope)? {
                    found.push(path.clone());
                }
            }
            let children: Vec<_> = match &header.kind {
                TypeKind::Tuple(items) => items
                    .iter()
                    .enumerate()
                    .map(|(index, item)| {
                        Some((
                            BoundTypeSelectionStep::Tuple(u32::try_from(index).ok()?),
                            item,
                        ))
                    })
                    .collect::<Option<_>>()?,
                TypeKind::Record { fields, .. } => fields
                    .iter()
                    .map(|field| (BoundTypeSelectionStep::Field(field.name.clone()), &field.ty))
                    .collect(),
                _ => Vec::new(),
            };
            for (step, header) in children {
                let mut next = path.clone();
                next.push(step);
                if let Some(value) = selected_entry(entry, &next) {
                    pending.push((header, value, next, depth + 1));
                }
            }
        }
        if found.len() != 1 {
            return None;
        }
        Some(FormalSourceAnchor {
            definition: *definition,
            invocation: source.id,
            parameter_index: *parameter_index,
            type_path: found.pop()?,
            activation,
            binding: binding_id,
            root_expression,
            entry_allocation_epoch: source.entry.allocation_epoch,
        })
    }

    pub(super) fn prepare_scoped_source_identity(
        &mut self,
        id: ScopedSourceIdentityId,
        binder: &str,
        templates: &[Option<Ty>],
    ) -> Option<ScopedSourceIdentity> {
        let required = *self.record_bounds_by_binder.get(binder)?;
        let bound = self.record_bounds.get(required.0 as usize)?;
        let invocation = *self.copy_invocation_stack.last()?;
        let call = self.copy_invocations.get(invocation.0 as usize)?;
        let function = self
            .functions
            .iter()
            .find(|info| info.definition == call.target)?;
        if call.target != bound.definition
            || call.entry.arguments.len() != function.syntax.parameters.len()
            || templates.len() != function.syntax.parameters.len()
        {
            return None;
        }
        let context = self.invocation_context(Some(CallableOwner::Function(call.target)));
        let span = call.span;
        let mut paths = Vec::new();
        let mut work = 4096;
        for (argument, template) in templates.iter().enumerate() {
            if let Some(template) = template {
                if !exact_occurrences(template, binder, 0, &mut work)? {
                    return None;
                }
                paths.extend(
                    Self::exact_record_bound_paths(template, binder)?
                        .into_iter()
                        .map(|path| (argument, path)),
                );
            }
        }
        if paths.is_empty() {
            return None;
        }
        let mut common = None;
        let mut origin = None;
        let mut occurrences = Vec::new();
        let mut cause = None;
        for (argument_index, selection_path) in paths {
            let (mode, entry) = self.copy_invocations[invocation.0 as usize]
                .entry
                .arguments
                .get(argument_index)?;
            if *mode != Mode::Read {
                return None;
            }
            let selected = selected_entry(entry, &selection_path)?.clone();
            let (schema, formal, key) = self.scoped_rigid_source(invocation, &selected)?;
            if common.as_ref().is_some_and(|previous| previous != &key) {
                if common
                    .as_ref()
                    .is_some_and(|previous| known_field_conflict(previous, &key))
                {
                    self.error("E0301", span,
                        "one generic type requires different complete dimensions, callable modes or qualifications in a known field",
                        [selected.cause]);
                }
                return None;
            }
            let StructuralSchemaSource::RigidParameter { syntax, scope, .. } = &schema.source
            else {
                return None;
            };
            common = Some(key);
            origin.get_or_insert_with(|| (syntax.clone(), scope.clone()));
            cause.get_or_insert(selected.cause);
            occurrences.push(ScopedSourceOccurrence {
                argument_index: u32::try_from(argument_index).ok()?,
                selection_path,
                formal,
            });
        }
        let (syntax, scope) = origin?;
        Some(ScopedSourceIdentity {
            id,
            required,
            binder: binder.into(),
            context,
            syntax,
            scope,
            key: common?,
            occurrences,
            cause: cause?,
            span,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_formal_fixed_field_preparation_has_an_actual_entry_and_name_receipt() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(original_formal_fixed_field_probe)
            .unwrap()
            .join()
            .unwrap();
    }

    fn original_formal_fixed_field_probe() {
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/regressions/record-bounds.ril::nested-rigid-fixed",
        ));
        assert!(parsed.is_ok());
        let resolved = crate::modules::resolve(
            vec![crate::modules::ModuleUnit {
                path: std::path::PathBuf::from("/ril-memory-source.ril"),
                file: FileId(0),
                program: parsed.program,
                is_declaration: false,
            }],
            FileId(0),
        );
        let evaluated = crate::static_eval::evaluate(
            &resolved.program,
            ril_compiler_core::target::TargetLayout::POINTER64,
        );
        assert!(evaluated.diagnostics.is_empty() && evaluated.unsupported.is_empty());
        let mut checker = Checker::new(FileId(0));
        checker.declare_system_operations();
        checker.install_constants(&evaluated.constants);
        checker.run(&evaluated.program);
        assert!(checker.unsupported.is_empty(), "{:?}", checker.unsupported);
        assert!(
            !checker.scoped_source_identities.is_empty(),
            "{:?}",
            checker.unsupported
        );
    }

    fn int() -> ArgumentKey {
        ArgumentKey::Name {
            name: "int".into(),
            arguments: Vec::new(),
        }
    }

    #[test]
    fn symbolic_dimension_strings_are_not_proven_by_is_closed() {
        let unproved = ArgumentKey::Array {
            length: Some("n".into()),
            element: Box::new(int()),
        };
        assert!(unproved.is_closed());
        assert!(complete_key(&unproved, 0, &mut 4096).is_none());
        let known = ArgumentKey::Array {
            length: Some("const(int:2)".into()),
            element: Box::new(int()),
        };
        assert!(complete_key(&known, 0, &mut 4096).is_some());
    }

    #[test]
    fn callable_modes_and_immutable_qualification_remain_distinct_complete_keys() {
        let read = ArgumentKey::Callable {
            parameters: vec![(ParameterMode::Read, int())],
            result: Box::new(int()),
            annotations: Vec::new(),
        };
        let write = ArgumentKey::Callable {
            parameters: vec![(ParameterMode::Mut, int())],
            result: Box::new(int()),
            annotations: vec!["&mut".into()],
        };
        assert_ne!(read, write);
        assert!(complete_key(&read, 0, &mut 4096).is_some());
        assert!(complete_key(&write, 0, &mut 4096).is_some());
        let immutable = ArgumentKey::Name {
            name: "Immut".into(),
            arguments: vec![read.clone()],
        };
        assert_ne!(immutable, read);
        assert!(complete_key(&immutable, 0, &mut 4096).is_some());
    }

    #[test]
    fn identical_display_names_cannot_unify_different_genuine_row_binders() {
        let row = |identity: &str| ArgumentKey::Record {
            fields: vec![("id".into(), false, int())],
            row: Some(Box::new(ArgumentKey::Binder {
                identity: identity.into(),
                sort: StaticBinderSort::Type,
            })),
        };
        let first = row("function:1:generic:0");
        let second = row("function:2:generic:0");
        assert_ne!(first, second);
        assert!(!first.is_closed());
        assert!(complete_key(&first, 0, &mut 4096).is_some());
    }
}
