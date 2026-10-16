//! Private universal bound environments for static ordinary typing.
//! Lexical identities and declaration promises are separate from closed actual
//! type witnesses and from the evaluator's dynamic EnvironmentId captures.
use super::*;
use crate::sema::model::rows::{OpenTail, RowIdentity};
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::static_eval) enum StaticParameterSort {
    Type,
    ConstInt,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::static_eval) struct StaticBinderId {
    pub(in crate::static_eval) declaration: String,
    pub(in crate::static_eval) index: u32,
    pub(in crate::static_eval) sort: StaticParameterSort,
}
impl StaticBinderId {
    pub(in crate::static_eval) fn key(&self) -> String {
        format!(
            "static:{}:{}:{}:{}",
            self.declaration.len(),
            self.declaration,
            match self.sort {
                StaticParameterSort::Type => "generic",
                StaticParameterSort::ConstInt => "const-int",
            },
            self.index
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::static_eval) struct StaticRowId {
    pub(in crate::static_eval) declaration: String,
    pub(in crate::static_eval) ordinal: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RowDeclaration {
    pub id: StaticRowId,
    pub name: String,
    pub identity: RowIdentity,
    pub declared_type: Option<StaticBinderId>,
    pub bound_indices: BTreeSet<u32>,
    pub lacks: BTreeSet<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Field {
    pub mutable: bool,
    pub ty: Ty,
    pub syntax: TypeExpr,
    pub key: crate::sema::effect_identity::ArgumentKey,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RecordBound {
    pub binder: StaticBinderId,
    pub syntax: TypeExpr,
    pub fields: BTreeMap<String, Field>,
    pub row: Option<StaticRowId>,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub(super) struct BoundEnvironment {
    pub values: Env,
    pub type_binders: BTreeMap<String, StaticBinderId>,
    pub type_ids: BTreeMap<String, StaticBinderId>,
    pub const_binders: BTreeMap<String, Option<StaticBinderId>>,
    pub const_ids: BTreeMap<String, StaticBinderId>,
    pub const_arguments: BTreeMap<StaticBinderId, super::const_int::ConstIntSelection>,
    pub views: BTreeMap<StaticBinderId, Arc<RecordBound>>,
    pub row_context: BTreeMap<String, StaticRowId>,
    pub rows: BTreeMap<StaticRowId, Arc<RowDeclaration>>,
    pub selected_types: BTreeMap<StaticBinderId, Arc<crate::sema::model::SourceTypeWitness>>,
    pub selected_rows: BTreeMap<StaticRowId, Arc<crate::sema::model::SourceTypeWitness>>,
    pub type_arguments: BTreeMap<StaticBinderId, Ty>,
    pub row_arguments:
        BTreeMap<StaticRowId, crate::sema::model::rows::Row<super::applications::SchemaField>>,
}

impl BoundEnvironment {
    pub(super) fn captured(values: Env) -> Self {
        Self {
            values,
            ..Self::default()
        }
    }

    fn admit_copy(&self, budget: &budget::Budget) -> Result<()> {
        self.admit_with_types(budget, &[])
    }
    pub(super) fn admit_with_types(&self, budget: &budget::Budget, extra: &[Ty]) -> Result<()> {
        if self
            .values
            .len()
            .saturating_add(self.type_arguments.len())
            .saturating_add(self.const_binders.len())
            .saturating_add(self.const_ids.len())
            .saturating_add(self.const_arguments.len())
            .saturating_add(extra.len())
            > 4096
        {
            return Err(Failure::Unsupported(
                "static bound environment copy exceeds its finite traversal allowance".into(),
            ));
        }
        let mut pending: Vec<_> = self
            .values
            .values()
            .chain(self.type_arguments.values())
            .chain(extra)
            .map(|ty| (ty, 0usize))
            .collect();
        let mut nodes = 0;
        for name in self.values.keys() {
            budget.work(name.len() as u64 + 1)?;
        }
        while let Some((ty, depth)) = pending.pop() {
            nodes += 1;
            if depth >= 64 || nodes > 4096 || pending.len() > 4096 {
                return Err(Failure::Unsupported(
                    "static bound environment copy exceeds its finite traversal allowance".into(),
                ));
            }
            budget.work(1)?;
            let children = match ty {
                Ty::Array(..) | Ty::Optional(_) => 1,
                Ty::Map(..) | Ty::Result(..) => 2,
                Ty::Tuple(items) => items.len(),
                Ty::Record(fields) => fields.len(),
                Ty::Callable(parameters, ..) => parameters.len().saturating_add(1),
                _ => 0,
            };
            if pending.len().saturating_add(children) > 4096 {
                return Err(Failure::Unsupported(
                    "static bound environment copy exceeds its finite traversal allowance".into(),
                ));
            }
            let mut child = |ty| pending.push((ty, depth + 1));
            match ty {
                Ty::Number(name) | Ty::Generic(name) | Ty::ForbiddenDefault(name) => {
                    budget.work(name.len() as u64)?
                }
                Ty::Array(inner, _) | Ty::Optional(inner) => child(inner),
                Ty::Map(a, b) | Ty::Result(a, b) => {
                    child(a);
                    child(b);
                }
                Ty::Tuple(items) => {
                    for item in items {
                        child(item);
                    }
                }
                Ty::Record(fields) => {
                    for (name, (_, ty)) in fields {
                        budget.work(name.len() as u64 + 1)?;
                        child(ty);
                    }
                }
                Ty::Callable(parameters, result, interfaces) => {
                    for parameter in parameters {
                        child(parameter);
                    }
                    child(result);
                    for parameter in interfaces.iter().flatten() {
                        budget.work(
                            1 + parameter
                                .label
                                .as_ref()
                                .map_or(0, |label| label.len() as u64),
                        )?;
                    }
                }
                _ => {}
            }
        }
        for (name, id) in self.type_binders.iter().chain(&self.type_ids) {
            budget.work(1 + name.len() as u64 + id.declaration.len() as u64)?;
        }
        for (name, id) in &self.const_binders {
            budget.work(
                1 + name.len() as u64 + id.as_ref().map_or(0, |id| id.declaration.len() as u64),
            )?;
        }
        for (key, id) in &self.const_ids {
            budget.work(1 + key.len() as u64 + id.declaration.len() as u64)?;
        }
        for id in self.const_arguments.keys() {
            budget.work(1 + id.declaration.len() as u64)?;
        }
        for id in self.views.keys() {
            budget.work(1 + id.declaration.len() as u64)?;
        }
        for (name, id) in &self.row_context {
            budget.work(1 + name.len() as u64 + id.declaration.len() as u64)?;
        }
        for id in self.rows.keys() {
            budget.work(1 + id.declaration.len() as u64)?;
        }
        let mut row_members = 0usize;
        for (id, row) in &self.row_arguments {
            budget.work(id.declaration.len() as u64 + 1)?;
            row_members = row_members.saturating_add(row.fields.len());
            if row_members > 4096 {
                return Err(Failure::Unsupported(
                    "static selected row copy exceeds its finite member allowance".into(),
                ));
            }
            for (name, (_, field)) in &row.fields {
                budget.work(name.len() as u64 + 1)?;
                clone_work::type_syntax(budget, &field.syntax)?;
            }
        }
        // Field syntax/keys and row declarations are immutable shared Arcs.
        // Capturing this environment does not recursively copy those graphs.
        Ok(())
    }

    pub(super) fn key_scope(&self) -> BTreeMap<String, String> {
        let mut scope: BTreeMap<_, _> = self
            .type_binders
            .iter()
            .map(|(name, id)| (name.clone(), id.key()))
            .collect();
        for (name, id) in &self.row_context {
            if !scope.contains_key(name)
                && let Some(row) = self.rows.get(id)
                && let RowIdentity::Binder(identity) = &row.identity
            {
                scope.insert(name.clone(), identity.clone());
            }
        }
        scope
    }

    pub(super) fn canonical_type(&self, ty: Ty) -> Ty {
        match ty {
            Ty::Generic(name) => {
                let id = self
                    .type_binders
                    .get(&name)
                    .or_else(|| self.type_ids.get(&name));
                if let Some(actual) = id.and_then(|id| self.type_arguments.get(id)) {
                    return actual.clone();
                }
                Ty::Generic(
                    self.type_binders
                        .get(&name)
                        .map(StaticBinderId::key)
                        .or_else(|| {
                            self.row_context
                                .get(&name)
                                .and_then(|id| self.rows.get(id))
                                .and_then(|row| match &row.identity {
                                    RowIdentity::Binder(identity) => Some(identity.clone()),
                                    _ => None,
                                })
                        })
                        .unwrap_or(name),
                )
            }
            Ty::Array(inner, length) => Ty::Array(Box::new(self.canonical_type(*inner)), length),
            Ty::Optional(inner) => Ty::Optional(Box::new(self.canonical_type(*inner))),
            Ty::Map(key, value) => Ty::Map(
                Box::new(self.canonical_type(*key)),
                Box::new(self.canonical_type(*value)),
            ),
            Ty::Result(ok, error) => Ty::Result(
                Box::new(self.canonical_type(*ok)),
                Box::new(self.canonical_type(*error)),
            ),
            Ty::Tuple(items) => Ty::Tuple(
                items
                    .into_iter()
                    .map(|ty| self.canonical_type(ty))
                    .collect(),
            ),
            Ty::Record(fields) => Ty::Record(
                fields
                    .into_iter()
                    .map(|(name, (mutable, ty))| (name, (mutable, self.canonical_type(ty))))
                    .collect(),
            ),
            Ty::Callable(parameters, result, interfaces) => Ty::Callable(
                parameters
                    .into_iter()
                    .map(|ty| self.canonical_type(ty))
                    .collect(),
                Box::new(self.canonical_type(*result)),
                interfaces,
            ),
            ty => ty,
        }
    }
}

impl Typer<'_> {
    pub(super) fn bound_type(&self, syntax: &TypeExpr, scope: &BoundEnvironment) -> Result<Ty> {
        if let Some(witness) = self.complete_source_syntax(syntax, scope)? {
            return self.ty_seen(&witness.syntax, &scope.values, &mut BTreeSet::new());
        }
        let expanded = self.symbolic_alias_syntax(syntax, scope)?;
        let syntax = expanded
            .as_ref()
            .map_or(syntax, |expanded| &expanded.syntax);
        self.reject_const_dependent_type(syntax, scope)?;
        // Scoped member syntax can contain a caller's stable internal name.
        // Only registered identities enter this environment; replacing them by
        // their visible spelling would capture a same-named callee parameter.
        scope.admit_with_types(&self.schema_work, &[])?;
        let mut values = scope.values.clone();
        for identity in scope.type_ids.keys() {
            values.entry(identity.clone()).or_insert(Ty::TypeParameter);
        }
        Ok(scope.canonical_type(self.ty_seen(syntax, &values, &mut BTreeSet::new())?))
    }

    pub(super) fn function_generic_environment(
        &self,
        function: &Function,
        captured: &BoundEnvironment,
    ) -> Result<BoundEnvironment> {
        // This pure admission charges implementation work only, before owned
        // syntax is retained. It does not enter a language evaluation root.
        let admission = budget::Budget::default();
        captured.admit_copy(&admission)?;
        for parameter in &function.generics {
            admission.work(parameter.name.len() as u64 + 1)?;
            for syntax in parameter.bound.iter().chain(&parameter.default) {
                clone_work::type_syntax(&admission, syntax)?;
            }
        }
        let mut scope = captured.clone();
        for (index, parameter) in function.generics.iter().enumerate() {
            let sort = super::const_int::parameter_sort(parameter)?;
            if sort == StaticParameterSort::ConstInt {
                let id = StaticBinderId {
                    declaration: function.name.clone(),
                    index: index as u32,
                    sort,
                };
                scope.const_ids.insert(id.key(), id.clone());
                scope
                    .const_binders
                    .insert(parameter.name.clone(), Some(id.clone()));
                scope.const_arguments.remove(&id);
                scope.type_binders.remove(&parameter.name);
                scope.row_context.remove(&parameter.name);
                scope
                    .values
                    .insert(parameter.name.clone(), Ty::Number("int".into()));
                continue;
            }
            if parameter.bound.as_ref().is_some_and(|bound| {
                !matches!(bound.kind, TypeKind::Record { .. })
                    && !matches!(&bound.kind, TypeKind::Name { path, arguments }
                        if path == &["Type"] && arguments.is_empty())
            }) {
                return Err(Failure::Unsupported(
                    "static generic bound requires a verified Type or structural Type sort".into(),
                ));
            }
            let id = StaticBinderId {
                declaration: function.name.clone(),
                index: index as u32,
                sort,
            };
            scope.type_ids.insert(id.key(), id.clone());
            scope.type_binders.insert(parameter.name.clone(), id);
            scope.const_binders.insert(parameter.name.clone(), None);
            scope
                .values
                .insert(parameter.name.clone(), Ty::TypeParameter);
            scope.row_context.remove(&parameter.name);
        }
        for (index, parameter) in function.generics.iter().enumerate() {
            let Some(TypeExpr {
                kind:
                    TypeKind::Record {
                        fields,
                        row: Some(row),
                    },
                ..
            }) = &parameter.bound
            else {
                continue;
            };
            let TypeKind::Name { path, arguments } = &row.kind else {
                return Err(Failure::Unsupported(
                    "static concrete bound tail needs its complete row equation".into(),
                ));
            };
            if path.len() != 1 || !arguments.is_empty() {
                return Err(Failure::Unsupported(
                    "static bound tail needs a lexical row identity".into(),
                ));
            }
            let name = &path[0];
            let declared_type = scope.type_binders.get(name).cloned();
            if declared_type.is_none() && self.evaluator.declarations.contains_key(name) {
                return Err(Failure::Unsupported(
                    "static named bound tail needs its complete row equation".into(),
                ));
            }
            let existing = scope.row_context.get(name).cloned().filter(|id| {
                scope
                    .rows
                    .get(id)
                    .is_some_and(|row| row.declared_type == declared_type)
            });
            let id = existing.unwrap_or_else(|| {
                let id = StaticRowId {
                    declaration: function.name.clone(),
                    ordinal: scope
                        .rows
                        .keys()
                        .filter(|id| id.declaration == function.name)
                        .count() as u32,
                };
                let identity = RowIdentity::Binder(
                    declared_type
                        .as_ref()
                        .map(StaticBinderId::key)
                        .unwrap_or_else(|| {
                            format!(
                                "static:{}:{}:bound-row:{}",
                                function.name.len(),
                                function.name,
                                id.ordinal
                            )
                        }),
                );
                scope.rows.insert(
                    id.clone(),
                    Arc::new(RowDeclaration {
                        id: id.clone(),
                        name: name.clone(),
                        identity,
                        declared_type: declared_type.clone(),
                        bound_indices: BTreeSet::new(),
                        lacks: BTreeSet::new(),
                    }),
                );
                id
            });
            scope.row_context.insert(name.clone(), id.clone());
            if declared_type.is_none() {
                scope
                    .values
                    .entry(name.clone())
                    .or_insert(Ty::TypeParameter);
            }
            if scope.rows[&id].id.declaration == function.name {
                let declaration =
                    Arc::make_mut(scope.rows.get_mut(&id).expect("registered static row"));
                declaration.bound_indices.insert(index as u32);
                declaration
                    .lacks
                    .extend(fields.iter().map(|field| field.name.clone()));
            }
        }
        let key_scope = scope.key_scope();
        for parameter in &function.generics {
            let Some(
                syntax @ TypeExpr {
                    kind: TypeKind::Record { fields, row },
                    ..
                },
            ) = &parameter.bound
            else {
                continue;
            };
            let mut checked = BTreeMap::new();
            for field in fields {
                if checked.contains_key(&field.name) {
                    return Err(Failure::Diagnostic(
                        "E0210",
                        "static record bound field declared twice".into(),
                    ));
                }
                self.type_names(&field.ty, &scope.values)?;
                let ty = self.bound_type(&field.ty, &scope)?;
                let key =
                    effects::bounded_argument_key(&field.ty, &key_scope).ok_or_else(|| {
                        Failure::Unsupported(
                            "static bound field needs its complete scoped syntax".into(),
                        )
                    })?;
                checked.insert(
                    field.name.clone(),
                    Field {
                        mutable: field.mutable,
                        ty,
                        syntax: field.ty.clone(),
                        key,
                    },
                );
            }
            let binder = scope.type_binders[&parameter.name].clone();
            let row = row.as_ref().map(|row| match &row.kind {
                TypeKind::Name { path, .. } => scope.row_context[&path[0]].clone(),
                _ => unreachable!("checked static row tail"),
            });
            scope.views.insert(
                binder.clone(),
                Arc::new(RecordBound {
                    binder,
                    syntax: syntax.clone(),
                    fields: checked,
                    row,
                }),
            );
        }
        Ok(scope)
    }

    pub(super) fn bound_view<'s>(
        &self,
        ty: &Ty,
        scope: &'s BoundEnvironment,
    ) -> Option<&'s RecordBound> {
        let Ty::Generic(identity) = ty else {
            return None;
        };
        scope
            .views
            .get(scope.type_ids.get(identity)?)
            .map(AsRef::as_ref)
    }

    pub(super) fn bound_projection(
        &self,
        ty: &Ty,
        label: &str,
        scope: &BoundEnvironment,
    ) -> Result<Ty> {
        let view = self.bound_view(ty, scope).ok_or_else(|| {
            Failure::Unsupported(
                "static generic projection needs its declaration bound view".into(),
            )
        })?;
        view.fields
            .get(label)
            .map(|field| field.ty.clone())
            .ok_or_else(|| {
                Failure::Diagnostic("E0336", "static bound has no guaranteed field".into())
            })
    }

    pub(super) fn bound_row_identity(&self, ty: &Ty, scope: &BoundEnvironment) -> Option<OpenTail> {
        let view = self.bound_view(ty, scope)?;
        let row = scope.rows.get(view.row.as_ref()?)?;
        let mut lacks = row.lacks.clone();
        lacks.extend(view.fields.keys().cloned());
        Some(OpenTail {
            identity: row.identity.clone(),
            lacks,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unexpected(failure: Failure) -> ! {
        match failure {
            Failure::Diagnostic(code, reason) => panic!("{code}: {reason}"),
            Failure::Unsupported(reason) => panic!("not implemented: {reason}"),
            _ => panic!("unexpected static control transfer"),
        }
    }

    fn evaluator(source: &str) -> Evaluator {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let collected = definitions::collect(&parsed.program);
        Evaluator {
            type_environment: Default::default(),
            type_application_sequence: 0,
            layout: TargetLayout::POINTER64,
            values: BTreeMap::new(),
            global_values: BTreeMap::new(),
            budget: budget::Budget::default(),
            declarations: collected.all_types,
            effect_declarations: collected.all_effects,
            functions: collected.all_functions,
            function_environments: BTreeMap::new(),
            environments: vec![],
            alias_instances: BTreeMap::new(),
            static_signatures: BTreeMap::new(),
            active_functions: vec![],
            type_depth: 0,
            call_depth: 0,
            tail_returns: false,
            tail_types: false,
            numeric_return: None,
            results: Default::default(),
            result_site: None,
            expression_depth: 0,
            loop_frames: vec![],
            next_loop_target: 0,
            type_calls: BTreeSet::new(),
            next_collection: 0,
            publications: Default::default(),
            constants: Default::default(),
        }
    }

    #[test]
    fn a_visible_name_shadow_does_not_erase_an_existing_values_bound_identity() {
        let evaluator = evaluator("meta fn read<T:{id:int,..R}>(value:T)->int{value.id}");
        let checker = Typer::new(&evaluator, None);
        let function = &evaluator.functions["read"];
        let mut scope = checker
            .function_generic_environment(function, &BoundEnvironment::default())
            .unwrap_or_else(|failure| unexpected(failure));
        let value = checker
            .bound_type(function.parameters[0].ty.as_ref().unwrap(), &scope)
            .unwrap_or_else(|failure| unexpected(failure));
        scope.values.insert("T".into(), Ty::Number("int".into()));
        assert_eq!(
            checker
                .bound_projection(&value, "id", &scope)
                .unwrap_or_else(|failure| unexpected(failure)),
            Ty::Number("int".into())
        );
        assert!(matches!(
            checker.bound_projection(&value, "missing", &scope),
            Err(Failure::Diagnostic("E0336", _))
        ));
        assert!(checker.bound_row_identity(&value, &scope).is_some());
    }

    #[test]
    fn shared_and_explicit_row_roles_have_stable_distinct_declaration_ids() {
        let evaluator = evaluator(
            "meta fn both<T:{id:int,..R},U:{flag:bool,..R}>(left:T,right:U)->int{left.id}\nmeta fn explicit<T:{peer:R,..R},R>(value:T)->int{7}",
        );
        let checker = Typer::new(&evaluator, None);
        let captured = BoundEnvironment::captured(Env::new());
        let first = checker
            .function_generic_environment(&evaluator.functions["both"], &captured)
            .unwrap_or_else(|failure| unexpected(failure));
        let second = checker
            .function_generic_environment(&evaluator.functions["both"], &captured)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(first.row_context, second.row_context);
        assert_eq!(first.rows.len(), 1);
        let row = first.rows.values().next().unwrap();
        assert_eq!(
            row.lacks.iter().map(String::as_str).collect::<Vec<_>>(),
            ["flag", "id"]
        );
        let explicit = checker
            .function_generic_environment(&evaluator.functions["explicit"], &captured)
            .unwrap_or_else(|failure| unexpected(failure));
        let row = explicit.rows.values().next().unwrap();
        let binder = &explicit.type_binders["R"];
        assert_eq!(row.declared_type.as_ref(), Some(binder));
        assert_eq!(row.identity, RowIdentity::Binder(binder.key()));
        let t = &explicit.views[&explicit.type_binders["T"]];
        assert_eq!(t.fields["peer"].ty, Ty::Generic(binder.key()));
    }

    #[test]
    fn a_captured_row_is_not_strengthened_by_an_inner_local_premise() {
        let evaluator = evaluator(
            "meta fn outer<T:{id:int,..R}>(value:T)->int{value.id}\nmeta fn inner<U:{flag:bool,..R}>(value:U)->bool{value.flag}",
        );
        let checker = Typer::new(&evaluator, None);
        let outer = checker
            .function_generic_environment(
                &evaluator.functions["outer"],
                &BoundEnvironment::default(),
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let inner = checker
            .function_generic_environment(&evaluator.functions["inner"], &outer)
            .unwrap_or_else(|failure| unexpected(failure));
        assert_eq!(outer.row_context["R"], inner.row_context["R"]);
        let row = &inner.rows[&inner.row_context["R"]];
        assert_eq!(
            row.lacks.iter().map(String::as_str).collect::<Vec<_>>(),
            ["id"]
        );
        let value = checker
            .bound_type(
                evaluator.functions["inner"].parameters[0]
                    .ty
                    .as_ref()
                    .unwrap(),
                &inner,
            )
            .unwrap_or_else(|failure| unexpected(failure));
        let tail = checker.bound_row_identity(&value, &inner).unwrap();
        assert!(tail.lacks.contains("id") && tail.lacks.contains("flag"));
        assert_ne!(inner.type_binders["U"], outer.type_binders["T"]);
    }
}
