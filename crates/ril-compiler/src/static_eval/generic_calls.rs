//! Private immutable type selections for one callable's lexical activation.
use super::typing::bounds::{
    StaticBinderId as BinderId, StaticParameterSort, StaticRowId as RowId,
};
use super::*;
use crate::sema::model::SourceTypeWitness;
use std::sync::Arc;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct TypeEnvironment {
    types: BTreeMap<BinderId, Arc<SourceTypeWitness>>,
    rows: BTreeMap<RowId, Arc<SourceTypeWitness>>,
    visible_types: BTreeMap<String, BinderId>,
    visible_rows: BTreeMap<String, RowId>,
    const_ints: BTreeMap<BinderId, i128>,
    visible_consts: BTreeMap<String, Option<BinderId>>,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct PreparedNamed {
    pub name: String,
    pub environment: environments::Environment,
    pub signature: signatures::Signature,
    pub raw_signature: signatures::Signature,
}

impl TypeEnvironment {
    pub(super) fn type_selections(&self) -> &BTreeMap<BinderId, Arc<SourceTypeWitness>> {
        &self.types
    }
    pub(super) fn row_selections(&self) -> &BTreeMap<RowId, Arc<SourceTypeWitness>> {
        &self.rows
    }
    pub(super) fn visible_types(&self) -> &BTreeMap<String, BinderId> {
        &self.visible_types
    }
    pub(super) fn visible_rows(&self) -> &BTreeMap<String, RowId> {
        &self.visible_rows
    }
    pub(super) fn const_selections(&self) -> &BTreeMap<BinderId, i128> {
        &self.const_ints
    }
    pub(super) fn visible_consts(&self) -> &BTreeMap<String, Option<BinderId>> {
        &self.visible_consts
    }
    pub(super) fn mask_const(&mut self, name: &str) {
        if self.visible_consts.get(name).is_some_and(Option::is_some) {
            self.visible_consts.insert(name.into(), None);
        }
    }
    pub(super) fn select_const(&mut self, name: &str, value: i128) -> Result<()> {
        let id = self
            .visible_consts
            .get(name)
            .and_then(Option::as_ref)
            .ok_or_else(|| {
                Failure::Unsupported(
                    "evaluated scalar const lacks its lexical binder identity".into(),
                )
            })?;
        if self.const_ints.get(id).is_some_and(|old| *old != value) {
            return Err(Failure::Diagnostic(
                "E0323",
                "one static int binder has inconsistent values".into(),
            ));
        }
        self.const_ints.insert(id.clone(), value);
        Ok(())
    }
    pub(super) fn admit_clone(&self, budget: &budget::Budget) -> Result<()> {
        for id in self.types.keys() {
            budget.work(1 + id.declaration.len() as u64)?;
        }
        for id in self.rows.keys() {
            budget.work(1 + id.declaration.len() as u64)?;
        }
        for (name, id) in &self.visible_types {
            budget.work(1 + name.len() as u64 + id.declaration.len() as u64)?;
        }
        for (name, id) in &self.visible_rows {
            budget.work(1 + name.len() as u64 + id.declaration.len() as u64)?;
        }
        for id in self.const_ints.keys() {
            budget.work(1 + id.declaration.len() as u64)?;
        }
        for (name, id) in &self.visible_consts {
            budget.work(
                1 + name.len() as u64 + id.as_ref().map_or(0, |id| id.declaration.len() as u64),
            )?;
        }
        Ok(())
    }

    pub(super) fn enter(
        &mut self,
        declaration: &str,
        parameters: &[GenericParameter],
        budget: &budget::Budget,
    ) -> Result<()> {
        // A same-spelled callee binder hides the captured token, not its
        // immutable historical selection. Outer row identities stay separate.
        self.visible_rows
            .retain(|_, id| id.declaration != declaration);
        self.rows.retain(|id, _| id.declaration != declaration);
        for (index, parameter) in parameters.iter().enumerate() {
            budget.work(1 + 2 * declaration.len() as u64 + parameter.name.len() as u64)?;
            self.mask_const(&parameter.name);
            let id = BinderId {
                declaration: declaration.into(),
                index: index as u32,
                sort: StaticParameterSort::Type,
            };
            self.visible_types
                .insert(parameter.name.clone(), id.clone());
            self.visible_rows.remove(&parameter.name);
            self.types.remove(&id);
        }
        Ok(())
    }

    pub(super) fn enter_named(
        &mut self,
        declaration: &str,
        parameters: &[GenericParameter],
        budget: &budget::Budget,
    ) -> Result<()> {
        self.visible_rows
            .retain(|_, id| id.declaration != declaration);
        self.rows.retain(|id, _| id.declaration != declaration);
        for (index, parameter) in parameters.iter().enumerate() {
            budget.work(1 + declaration.len() as u64 + parameter.name.len() as u64)?;
            let sort = typing::const_int::parameter_sort(parameter)?;
            let id = BinderId {
                declaration: declaration.into(),
                index: index as u32,
                sort,
            };
            self.visible_rows.remove(&parameter.name);
            match id.sort {
                StaticParameterSort::ConstInt => {
                    self.visible_types.remove(&parameter.name);
                    self.const_ints.remove(&id);
                    self.visible_consts.insert(parameter.name.clone(), Some(id));
                }
                StaticParameterSort::Type => {
                    self.mask_const(&parameter.name);
                    self.types.remove(&id);
                    self.visible_types.insert(parameter.name.clone(), id);
                }
            }
        }
        Ok(())
    }

    pub(super) fn select_type(
        &mut self,
        name: &str,
        witness: Arc<SourceTypeWitness>,
        budget: &budget::Budget,
    ) -> Result<()> {
        let id = self.visible_types.get(name).ok_or_else(|| {
            Failure::Unsupported(
                "static type selection has no declared lexical binder identity".into(),
            )
        })?;
        if self.types.get(id).is_some_and(|old| old.key != witness.key)
            || self
                .fixed_row(name)
                .is_some_and(|old| old.key != witness.key)
        {
            return Err(Failure::Diagnostic(
                "E0301",
                "one static type parameter has inconsistent complete selections".into(),
            ));
        }
        budget.work(id.declaration.len() as u64 + 1)?;
        self.types.insert(id.clone(), witness);
        Ok(())
    }

    pub(super) fn prepare_rows(
        &mut self,
        declaration: &str,
        parameters: &[GenericParameter],
        declarations: &BTreeMap<String, TypeDeclaration>,
        budget: &budget::Budget,
    ) -> Result<BTreeSet<String>> {
        let mut fresh = BTreeSet::new();
        let mut ordinal = 0;
        for parameter in parameters {
            let Some(TypeExpr {
                kind: TypeKind::Record { row: Some(row), .. },
                ..
            }) = &parameter.bound
            else {
                continue;
            };
            let TypeKind::Name { path, arguments } = &row.kind else {
                continue;
            };
            if path.len() != 1 || !arguments.is_empty() {
                continue;
            }
            let name = &path[0];
            if declarations.contains_key(name) && !self.visible_types.contains_key(name) {
                continue;
            }
            if self.visible_rows.contains_key(name) {
                continue;
            }
            budget.work(1 + 2 * declaration.len() as u64 + 2 * name.len() as u64)?;
            let id = RowId {
                declaration: declaration.into(),
                ordinal,
            };
            ordinal += 1;
            self.rows.remove(&id);
            self.visible_rows.insert(name.clone(), id);
            if !self.visible_types.contains_key(name) {
                fresh.insert(name.clone());
            }
        }
        Ok(fresh)
    }

    fn fixed_row(&self, name: &str) -> Option<&Arc<SourceTypeWitness>> {
        self.rows.get(self.visible_rows.get(name)?)
    }

    pub(super) fn select_row(
        &mut self,
        name: &str,
        witness: Arc<SourceTypeWitness>,
        budget: &budget::Budget,
    ) -> Result<()> {
        let Some(id) = self.visible_rows.get(name) else {
            return Ok(());
        };
        if !matches!(witness.syntax.kind, TypeKind::Record { row: None, .. }) {
            return Err(Failure::Diagnostic(
                "E0301",
                "a static residual must select a structural record type".into(),
            ));
        }
        if self.rows.get(id).is_some_and(|old| old.key != witness.key)
            || self
                .visible_types
                .get(name)
                .and_then(|id| self.types.get(id))
                .is_some_and(|old| old.key != witness.key)
        {
            return Err(Failure::Diagnostic(
                "E0301",
                "one static residual has inconsistent complete selections".into(),
            ));
        }
        budget.work(id.declaration.len() as u64 + 1)?;
        self.rows.insert(id.clone(), witness);
        Ok(())
    }
}

impl Evaluator {
    pub(super) fn prepare_named_result_context(
        &mut self,
        callable: StaticCallable,
        arguments: &[application::StaticArgument],
        expected: Option<&TypeExpr>,
        caller: Option<&environments::Environment>,
    ) -> Result<StaticCallable> {
        let StaticCallable::Named { name, captured } = &callable else {
            return Ok(callable);
        };
        let Some(expected) = expected else {
            return Ok(callable);
        };
        let function = self.functions.get(name).ok_or_else(|| {
            Failure::Unsupported("static result-context callee is unavailable".into())
        })?;
        if function.generics.is_empty() {
            return Ok(callable);
        }
        clone_work::function(&self.budget, function)?;
        let function = function.clone();
        let caller = caller.ok_or_else(|| {
            Failure::Unsupported("static result context has no captured caller environment".into())
        })?;
        let context =
            typing::runtime_applications::expected_result_context(self, expected, caller)?;
        let declaration = self.declaration_environment(*captured)?;
        self.type_application_sequence =
            self.type_application_sequence
                .checked_add(1)
                .ok_or_else(|| {
                    Failure::Unsupported(
                        "static type application activation identity exhausted".into(),
                    )
                })?;
        let types = typing::runtime_applications::infer_named_type_arguments(
            self,
            &function,
            &declaration,
            caller,
            arguments,
            Some(&context),
            self.type_application_sequence,
        )?;
        self.prepare_named(name, *captured, &types)
    }

    pub(super) fn prepare_named(
        &mut self,
        name: &str,
        captured: Option<environments::EnvironmentId>,
        arguments: &[TypeExpr],
    ) -> Result<StaticCallable> {
        let function = self.functions.get(name).ok_or_else(|| {
            Failure::Unsupported("static generic callee declaration is unavailable".into())
        })?;
        clone_work::function(&self.budget, function)?;
        let function = function.clone();
        let lexical = self.declaration_environment(captured)?;
        typing::const_int::check_signature(self, &function, &lexical.types)?;
        let saved = self.capture_environment()?;
        let result = (|| {
            self.bind_type_arguments_captured(&function.generics, arguments, name, captured)?;
            let raw_signature = signatures::Signature {
                parameters: function.parameters.clone(),
                result: function.return_type.clone(),
            };
            let mut signature = self.static_signature(&function)?;
            for parameter in &mut signature.parameters {
                if let Some(ty) = &mut parameter.ty {
                    *ty = self.resolve_type(ty, &mut vec![])?;
                }
            }
            if let Some(result) = &mut signature.result {
                *result = self.resolve_type(result, &mut vec![])?;
            }
            self.budget.work(name.len() as u64 + 1)?;
            Ok(StaticCallable::Prepared(Arc::new(PreparedNamed {
                name: name.into(),
                environment: self.capture_environment()?,
                signature,
                raw_signature,
            })))
        })();
        self.install_environment(saved);
        result
    }
}
