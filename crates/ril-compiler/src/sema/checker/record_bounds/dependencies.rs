//! Type equations from the actual complete structural input. No access or
//! source witness is inferred from an erased semantic array/callable type.
use super::*;
use crate::sema::effect_identity::{ArgumentKey, StaticBinderSort};

#[derive(Clone)]
struct Candidate {
    key: ArgumentKey,
    syntax: TypeExpr,
    scope: BoundScope,
}

struct EquationContext<'a> {
    scope: &'a BoundScope,
    owned: &'a BTreeSet<String>,
    selected: &'a mut BTreeMap<String, Candidate>,
    work: &'a mut usize,
}

fn equations(
    formal: &ArgumentKey,
    actual: &ArgumentKey,
    syntax: &TypeExpr,
    context: &mut EquationContext<'_>,
    depth: usize,
) -> Option<()> {
    *context.work = context.work.checked_sub(1)?;
    if depth >= 64 {
        return None;
    }
    if let ArgumentKey::Binder {
        identity,
        sort: StaticBinderSort::Type,
    } = formal
        && context.owned.contains(identity)
    {
        match actual {
            ArgumentKey::Binder {
                identity,
                sort: StaticBinderSort::Type,
            } if context
                .scope
                .types
                .values()
                .any(|actual| actual == identity) => {}
            ArgumentKey::Name { name, arguments }
                if arguments.is_empty()
                    && matches!(
                        name.as_str(),
                        "int"
                            | "i8"
                            | "i16"
                            | "i32"
                            | "i64"
                            | "u8"
                            | "u16"
                            | "u32"
                            | "u64"
                            | "bigint"
                            | "f32"
                            | "f64"
                            | "bool"
                            | "str"
                            | "bytes"
                            | "never"
                    ) => {}
            // Composite leaf selections need their own exact source-selection
            // projection. They cannot be reconstructed from the semantic Ty.
            _ => return None,
        }
        if let Some(previous) = context.selected.get(identity) {
            if previous.key != *actual {
                return None;
            }
        } else {
            context.selected.insert(
                identity.clone(),
                Candidate {
                    key: actual.clone(),
                    syntax: syntax.clone(),
                    scope: context.scope.clone(),
                },
            );
        }
        return Some(());
    }
    if formal == actual {
        return Some(());
    }
    let mut child = |formal, actual, syntax| equations(formal, actual, syntax, context, depth + 1);
    match (formal, actual, &syntax.kind) {
        (
            ArgumentKey::Array {
                length: a,
                element: f,
            },
            ArgumentKey::Array {
                length: b,
                element: v,
            },
            TypeKind::Array { element, .. },
        ) if a == b => child(f, v, element),
        (ArgumentKey::Tuple(a), ArgumentKey::Tuple(b), TypeKind::Tuple(items))
            if a.len() == b.len() && b.len() == items.len() =>
        {
            for ((a, b), syntax) in a.iter().zip(b).zip(items) {
                child(a, b, syntax)?;
            }
            Some(())
        }
        (
            ArgumentKey::Map { key: a, value: b },
            ArgumentKey::Map { key: c, value: d },
            TypeKind::Map { key, value },
        ) => {
            child(a, c, key)?;
            child(b, d, value)
        }
        (
            ArgumentKey::Name {
                name: a,
                arguments: f,
            },
            ArgumentKey::Name {
                name: b,
                arguments: v,
            },
            TypeKind::Name { arguments, .. },
        ) if a == b && f.len() == v.len() && v.len() == arguments.len() => {
            for ((f, v), syntax) in f.iter().zip(v).zip(arguments) {
                child(f, v, syntax)?;
            }
            Some(())
        }
        (
            ArgumentKey::Name {
                name: a,
                arguments: f,
            },
            ArgumentKey::Name {
                name: b,
                arguments: v,
            },
            TypeKind::Optional(inner),
        ) if a == "Option" && b == a && f.len() == 1 && v.len() == 1 => child(&f[0], &v[0], inner),
        (
            ArgumentKey::Callable {
                parameters: a,
                result: f,
                annotations: x,
            },
            ArgumentKey::Callable {
                parameters: b,
                result: v,
                annotations: y,
            },
            TypeKind::Callable {
                parameters, result, ..
            },
        ) if a.len() == b.len() && b.len() == parameters.len() && x == y => {
            for (((am, f), (bm, v)), syntax) in a.iter().zip(b).zip(parameters) {
                if am != bm {
                    return None;
                }
                child(f, v, syntax.ty.as_ref()?)?;
            }
            child(f, v, result.as_deref()?)
        }
        (
            ArgumentKey::Record {
                fields: a,
                row: None,
            },
            ArgumentKey::Record {
                fields: b,
                row: None,
            },
            TypeKind::Record { fields, row: None },
        ) if a.len() == b.len() && b.len() == fields.len() => {
            for (name, mode, f) in a {
                let (_, other_mode, v) = b.iter().find(|(label, _, _)| label == name)?;
                let syntax = fields.iter().find(|field| &field.name == name)?;
                if mode != other_mode || *mode != syntax.mutable {
                    return None;
                }
                child(f, v, &syntax.ty)?;
            }
            Some(())
        }
        _ => None,
    }
}

impl Checker {
    /// Syntactic reachability is only a deferred candidate. The actual bound
    /// transaction must later prove the source equation for this invocation.
    pub(in crate::sema::checker) fn potential_bound_numeric_inputs(
        &self,
        info: &FunctionInfo,
        templates: &[Option<Ty>],
    ) -> BTreeSet<String> {
        let owned: BTreeSet<_> = info.syntax.generics.iter().enumerate()
            .filter(|(_, parameter)| parameter.name.chars().next().is_some_and(char::is_uppercase)
                && parameter.bound.as_ref().is_none_or(|bound|
                    matches!(&bound.kind, TypeKind::Name { path, arguments }
                        if path == &["Type"] && arguments.is_empty())))
            .filter_map(|(index, parameter)| self.generic_binders.values().find(|binder|
                binder.definition == info.definition && binder.index == index as u32
                    && binder.name == parameter.name).map(|binder| binder.identity.clone()))
            .filter(|identity| !self.bound_rows.iter().any(|row| row.definition == info.definition
                && matches!(&row.role, BoundRowRole::DeclaredTypeParameter { binder } if binder == identity)))
            .collect();
        let mut reachable = BTreeSet::new();
        for bound in self
            .record_bounds
            .iter()
            .filter(|bound| bound.definition == info.definition)
        {
            if !templates.iter().flatten().any(|template| {
                Self::exact_record_bound_paths(template, &bound.binder)
                    .is_some_and(|paths| !paths.is_empty())
            }) {
                continue;
            }
            let mut pending: Vec<_> = bound
                .fields
                .iter()
                .map(|field| (&field.key, 0usize))
                .collect();
            let mut work = 4096;
            while let Some((key, depth)) = pending.pop() {
                if work == 0 || depth >= 64 {
                    return BTreeSet::new();
                }
                work -= 1;
                match key {
                    ArgumentKey::Binder { identity, .. } if owned.contains(identity) => {
                        reachable.insert(identity.clone());
                    }
                    ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                        pending.extend(arguments.iter().map(|key| (key, depth + 1)))
                    }
                    ArgumentKey::Array { element, .. } => pending.push((element, depth + 1)),
                    ArgumentKey::Map { key, value } => {
                        pending.push((key, depth + 1));
                        pending.push((value, depth + 1));
                    }
                    ArgumentKey::Record { fields, row } => {
                        pending.extend(fields.iter().map(|(_, _, key)| (key, depth + 1)));
                        pending.extend(row.iter().map(|key| (key.as_ref(), depth + 1)));
                    }
                    ArgumentKey::Callable {
                        parameters, result, ..
                    } => {
                        pending.extend(parameters.iter().map(|(_, key)| (key, depth + 1)));
                        pending.push((result, depth + 1));
                    }
                    _ => {}
                }
            }
        }
        reachable
    }

    fn bound_key_except(
        &self,
        key: &ArgumentKey,
        except: &str,
        depth: usize,
    ) -> Option<ArgumentKey> {
        if depth >= 64 {
            return None;
        }
        if let ArgumentKey::Binder { identity, .. } = key {
            return if identity == except {
                Some(key.clone())
            } else {
                self.selected_bound_key(key)
            };
        }
        let mut child = |key| self.bound_key_except(key, except, depth + 1);
        Some(match key {
            ArgumentKey::Name { name, arguments } => ArgumentKey::Name {
                name: name.clone(),
                arguments: arguments.iter().map(&mut child).collect::<Option<_>>()?,
            },
            ArgumentKey::Tuple(items) => {
                ArgumentKey::Tuple(items.iter().map(&mut child).collect::<Option<_>>()?)
            }
            ArgumentKey::Array { length, element } => ArgumentKey::Array {
                length: length.clone(),
                element: Box::new(child(element)?),
            },
            ArgumentKey::Map { key, value } => ArgumentKey::Map {
                key: Box::new(child(key)?),
                value: Box::new(child(value)?),
            },
            ArgumentKey::Record { fields, row } => ArgumentKey::Record {
                fields: fields
                    .iter()
                    .map(|(label, mode, key)| Some((label.clone(), *mode, child(key)?)))
                    .collect::<Option<_>>()?,
                row: match row {
                    Some(row) => Some(Box::new(child(row)?)),
                    None => None,
                },
            },
            ArgumentKey::Callable {
                parameters,
                result,
                annotations,
            } => ArgumentKey::Callable {
                parameters: parameters
                    .iter()
                    .map(|(mode, key)| Some((*mode, child(key)?)))
                    .collect::<Option<_>>()?,
                result: Box::new(child(result)?),
                annotations: annotations.clone(),
            },
            _ => key.clone(),
        })
    }

    pub(in crate::sema::checker) fn proved_bound_numeric_input(
        &self,
        info: &FunctionInfo,
        invocation: crate::sema::copy_templates::InstanceId,
        binder: &str,
        expected: &Ty,
    ) -> bool {
        let Some(call) = self.copy_invocations.get(invocation.0 as usize) else {
            return false;
        };
        if call.id != invocation
            || call.target != info.definition
            || call.status != crate::sema::copy_contract::CopyInvocationStatus::Incomplete
        {
            return false;
        }
        let Some(witness) = self.generic_type_witnesses.get(binder) else {
            return false;
        };
        if !witness.validate_closed() {
            return false;
        }
        let Some(witness_key) = self.record_bound_key(&witness.syntax, &BoundScope::default())
        else {
            return false;
        };
        let expected_key = match expected {
            Ty::Int(name) | Ty::Float(name) => ArgumentKey::Name {
                name: name.clone(),
                arguments: vec![],
            },
            _ => return false,
        };
        if witness_key != expected_key {
            return false;
        }
        for check in &self.generic_bound_checks {
            if check.context.invocation != Some(invocation)
                || check.context.owner != Some(CallableOwner::Function(info.definition))
                || check.allocation_epoch != call.entry_allocation_epoch
                || check.substitutions.get(binder) != Some(&expected_key)
            {
                continue;
            }
            let Some(bound) = self
                .record_bounds
                .get(check.required.0 as usize)
                .filter(|bound| bound.id == check.required && bound.definition == info.definition)
            else {
                continue;
            };
            let Some((_, entry)) = call.arguments.get(check.argument_index as usize) else {
                continue;
            };
            if entry.value != check.actual.value
                || entry.nodes.len() != check.actual.nodes.len()
                || entry.relations != check.actual.relations
                || !entry.nodes.iter().all(|node| {
                    check.actual.nodes.iter().any(|other| {
                        node.origin == other.origin
                            && node.fact == other.fact
                            && node.fields == other.fields
                            && node.length == other.length
                            && node.fixed == other.fixed
                    })
                })
            {
                continue;
            }
            let scope = match &check.actual_schema.source {
                StructuralSchemaSource::Closed(_) => BoundScope::default(),
                StructuralSchemaSource::RigidParameter { scope, .. } => {
                    if !self.scoped_source_identities.iter().any(|source| {
                        source.required == check.required && source.context == check.context
                    }) {
                        continue;
                    }
                    scope.clone()
                }
                StructuralSchemaSource::CallerBound(_) => continue,
            };
            let mut selected = BTreeMap::new();
            let owned = BTreeSet::from([binder.to_owned()]);
            let mut work = 4096;
            let valid = bound.fields.iter().all(|field| {
                let Some(actual) = check
                    .actual_schema
                    .fields
                    .iter()
                    .find(|actual| actual.label == field.label)
                else {
                    return false;
                };
                let Some(formal) = self.bound_key_except(&field.key, binder, 0) else {
                    return false;
                };
                actual.mutable == field.mutable
                    && self.record_bound_key(&actual.syntax, &scope).as_ref() == Some(&actual.key)
                    && equations(
                        &formal,
                        &actual.key,
                        &actual.syntax,
                        &mut EquationContext {
                            scope: &scope,
                            owned: &owned,
                            selected: &mut selected,
                            work: &mut work,
                        },
                        0,
                    )
                    .is_some()
            });
            if valid
                && selected
                    .get(binder)
                    .is_some_and(|selected| selected.key == expected_key)
            {
                return true;
            }
        }
        false
    }

    pub(super) fn infer_bound_input_dependencies(
        &mut self,
        function_id: usize,
        bound: &GenericRecordBound,
        actual: &StructuralSchema,
    ) -> bool {
        let function = self.functions[function_id].clone();
        let row_binders: BTreeSet<_> = self
            .bound_rows
            .iter()
            .filter(|row| row.definition == function.definition)
            .filter_map(|row| match &row.role {
                BoundRowRole::DeclaredTypeParameter { binder } => Some(binder.clone()),
                _ => None,
            })
            .collect();
        let owned: BTreeSet<_> = function
            .syntax
            .generics
            .iter()
            .enumerate()
            .filter(|(_, parameter)| {
                parameter
                    .name
                    .chars()
                    .next()
                    .is_some_and(char::is_uppercase)
                    && parameter.bound.as_ref().is_none_or(|bound| {
                        matches!(&bound.kind, TypeKind::Name { path, arguments }
                        if path == &["Type"] && arguments.is_empty())
                    })
            })
            .filter_map(|(index, parameter)| {
                bound
                    .scope
                    .types
                    .get(&parameter.name)
                    .filter(|identity| {
                        self.generic_binders.get(*identity).is_some_and(|binder| {
                            binder.definition == function.definition && binder.index == index as u32
                        })
                    })
                    .cloned()
            })
            .filter(|identity| {
                identity != &bound.binder
                    && !row_binders.contains(identity)
                    && !self.generic_key_bounds.contains_key(identity)
                    && !self.generic_substitutions.contains_key(identity)
            })
            .collect();
        if owned.is_empty() {
            return true;
        }
        let scope = match &actual.source {
            StructuralSchemaSource::Closed(_) => BoundScope::default(),
            StructuralSchemaSource::RigidParameter { scope, .. } => scope.clone(),
            StructuralSchemaSource::CallerBound(_) => return true,
        };
        let mut selected = BTreeMap::new();
        let mut work = 4096;
        for formal in &bound.fields {
            let Some(actual) = actual
                .fields
                .iter()
                .find(|field| field.label == formal.label)
            else {
                return false;
            };
            if actual.mutable != formal.mutable {
                return false;
            }
            let Some(formal_key) = self.selected_bound_key(&formal.key) else {
                return false;
            };
            if self.record_bound_key(&actual.syntax, &scope).as_ref() != Some(&actual.key)
                || equations(
                    &formal_key,
                    &actual.key,
                    &actual.syntax,
                    &mut EquationContext {
                        scope: &scope,
                        owned: &owned,
                        selected: &mut selected,
                        work: &mut work,
                    },
                    0,
                )
                .is_none()
            {
                return false;
            }
        }
        // Nothing is committed until every repeated U and every known coordinate
        // agreed. The enclosing whole-bound transaction rolls back on any later
        // field, row, source-identity or shape failure.
        let previous_types = self.generic_context.clone();
        let previous_rows = self.bound_row_context.clone();
        let mut types = BTreeMap::new();
        let mut witnesses = BTreeMap::new();
        let valid = (|| {
            for (identity, candidate) in selected {
                self.generic_context = candidate.scope.types.clone();
                self.bound_row_context = candidate.scope.rows.clone();
                let ty = match &candidate.key {
                    ArgumentKey::Binder {
                        identity: caller, ..
                    } => {
                        let binder = self.generic_binders.get(caller)?;
                        if binder.definition == function.definition {
                            return None;
                        }
                        Ty::Generic(caller.clone())
                    }
                    _ => {
                        let witness = self.source_type_from_syntax(&candidate.syntax)?;
                        if crate::static_eval::effects::bounded_argument_key(
                            &witness.syntax,
                            &BTreeMap::new(),
                        )
                        .as_ref()
                            != Some(&candidate.key)
                        {
                            return None;
                        }
                        let ty = self.ty(&witness.syntax);
                        witnesses.insert(identity.clone(), witness);
                        ty
                    }
                };
                types.insert(identity, ty);
            }
            Some(())
        })()
        .is_some();
        self.generic_context = previous_types;
        self.bound_row_context = previous_rows;
        if valid {
            self.generic_substitutions.extend(types);
            self.generic_type_witnesses.extend(witnesses);
        }
        valid
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn binder(name: &str) -> ArgumentKey {
        ArgumentKey::Binder {
            identity: name.into(),
            sort: StaticBinderSort::Type,
        }
    }
    fn scope() -> BoundScope {
        BoundScope {
            types: [
                ("U".into(), "caller:U".into()),
                ("V".into(), "caller:V".into()),
            ]
            .into(),
            rows: BTreeMap::new(),
        }
    }
    fn syntax() -> TypeExpr {
        TypeExpr {
            text: "U".into(),
            span: Span {
                file: FileId(0),
                start: 0,
                end: 1,
            },
            kind: TypeKind::Name {
                path: vec!["U".into()],
                arguments: vec![],
            },
        }
    }
    #[test]
    fn a_real_caller_coordinate_is_selected_without_closing_it() {
        let mut selected = BTreeMap::new();
        assert!(
            equations(
                &binder("callee:U"),
                &binder("caller:U"),
                &syntax(),
                &mut EquationContext {
                    scope: &scope(),
                    owned: &BTreeSet::from(["callee:U".into()]),
                    selected: &mut selected,
                    work: &mut 100
                },
                0
            )
            .is_some()
        );
        assert_eq!(selected["callee:U"].key, binder("caller:U"));
        assert!(!selected["callee:U"].key.is_closed());
    }
    #[test]
    fn a_caller_binder_is_never_a_flexible_callee_variable() {
        assert!(
            equations(
                &binder("caller:U"),
                &binder("caller:V"),
                &syntax(),
                &mut EquationContext {
                    scope: &scope(),
                    owned: &BTreeSet::from(["callee:U".into()]),
                    selected: &mut BTreeMap::new(),
                    work: &mut 100
                },
                0
            )
            .is_none()
        );
    }
    #[test]
    fn identical_erased_array_types_cannot_skip_known_dimension_matching() {
        let array = |n, element| ArgumentKey::Array {
            length: Some(format!("const(int:{n})")),
            element: Box::new(element),
        };
        let mut syntax = syntax();
        syntax.kind = TypeKind::Array {
            element: Box::new(syntax.clone()),
            length: None,
        };
        let mut selected = BTreeMap::new();
        assert!(
            equations(
                &array(2, binder("callee:U")),
                &array(3, binder("caller:U")),
                &syntax,
                &mut EquationContext {
                    scope: &scope(),
                    owned: &BTreeSet::from(["callee:U".into()]),
                    selected: &mut selected,
                    work: &mut 100
                },
                0
            )
            .is_none()
        );
        assert!(selected.is_empty());
    }
}
