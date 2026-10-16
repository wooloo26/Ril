//! A lexical declaration group has one environment per evaluated block entry.
//! Sibling and recursive declarations refer back to its arena identity.
use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct EnvironmentId(usize);

#[derive(Debug, Clone, PartialEq)]
pub(super) struct Environment {
    pub values: BTreeMap<String, StaticValue>,
    pub declarations: BTreeMap<String, EnvironmentId>,
    pub types: generic_calls::TypeEnvironment,
}

pub(super) struct ActiveGroup {
    group: Option<EnvironmentId>,
    outer_declarations: BTreeMap<String, EnvironmentId>,
}

impl Evaluator {
    pub(super) fn copy_static_value(&self, value: &StaticValue) -> Result<StaticValue> {
        clone_work::value(&self.budget, value)?;
        Ok(value.clone())
    }
    pub(super) fn copy_static_callable(&self, value: &StaticCallable) -> Result<StaticCallable> {
        clone_work::callable(&self.budget, value)?;
        Ok(value.clone())
    }
    pub(super) fn capture_environment(&self) -> Result<Environment> {
        clone_work::values(&self.budget, &self.values)?;
        clone_work::declarations(&self.budget, &self.function_environments)?;
        self.type_environment.admit_clone(&self.budget)?;
        Ok(Environment {
            values: self.values.clone(),
            declarations: self.function_environments.clone(),
            types: self.type_environment.clone(),
        })
    }
    pub(super) fn copy_environment(&self, environment: &Environment) -> Result<Environment> {
        clone_work::environment(&self.budget, environment)?;
        Ok(environment.clone())
    }
    pub(super) fn snapshot_values(&self) -> Result<BTreeMap<String, StaticValue>> {
        self.copy_values(&self.values)
    }
    pub(super) fn copy_values(
        &self,
        values: &BTreeMap<String, StaticValue>,
    ) -> Result<BTreeMap<String, StaticValue>> {
        clone_work::values(&self.budget, values)?;
        Ok(values.clone())
    }
    pub(super) fn capture_dependencies(&self, names: &BTreeSet<String>) -> Result<Environment> {
        self.type_environment.admit_clone(&self.budget)?;
        // Admit every owned entry before constructing the filtered snapshot.
        for (name, value) in self.values.iter().filter(|(name, _)| names.contains(*name)) {
            self.budget.work(name.len() as u64)?;
            clone_work::value(&self.budget, value)?;
        }
        for name in self
            .function_environments
            .keys()
            .filter(|name| names.contains(*name))
        {
            self.budget.work(1 + name.len() as u64)?;
        }
        Ok(Environment {
            types: self.type_environment.clone(),
            values: self
                .values
                .iter()
                .filter(|(name, _)| names.contains(*name))
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect(),
            declarations: self
                .function_environments
                .iter()
                .filter(|(name, _)| names.contains(*name))
                .map(|(name, id)| (name.clone(), *id))
                .collect(),
        })
    }

    pub(super) fn declaration_environment(
        &self,
        captured: Option<EnvironmentId>,
    ) -> Result<Environment> {
        match captured {
            Some(id) => self.copy_environment(self.environments.get(id.0).ok_or_else(|| {
                Failure::Unsupported("static lexical environment identity is unavailable".into())
            })?),
            None => {
                clone_work::values(&self.budget, &self.global_values)?;
                Ok(Environment {
                    values: self.global_values.clone(),
                    declarations: BTreeMap::new(),
                    types: Default::default(),
                })
            }
        }
    }

    pub(super) fn install_environment(&mut self, environment: Environment) {
        self.values = environment.values;
        self.function_environments = environment.declarations;
        self.type_environment = environment.types;
    }

    pub(super) fn enter_block(&mut self, block: &Block) -> Result<()> {
        let names: Vec<_> = block
            .where_items
            .iter()
            .chain(&block.statements)
            .filter_map(|statement| match &statement.kind {
                StmtKind::Function(function) => Some(&function.name),
                StmtKind::Type(declaration) => Some(&declaration.name),
                _ => None,
            })
            .collect();
        clone_work::declarations(&self.budget, &self.function_environments)?;
        let outer_declarations = self.function_environments.clone();
        let group = if names.is_empty() {
            None
        } else {
            let id = EnvironmentId(self.environments.len());
            for name in &names {
                self.budget.work(name.len() as u64)?;
            }
            for name in names {
                self.function_environments.insert(name.clone(), id);
            }
            let captured = match self.capture_environment() {
                Ok(captured) => captured,
                Err(failure) => {
                    self.function_environments = outer_declarations;
                    return Err(failure);
                }
            };
            self.environments.push(captured);
            Some(id)
        };
        self.active_functions.push(ActiveGroup {
            group,
            outer_declarations,
        });
        Ok(())
    }

    pub(super) fn refresh_local_functions(&mut self) -> Result<()> {
        if let Some(id) = self.active_functions.last().and_then(|active| active.group) {
            // Late lexical bindings initialize this invocation's group only.
            clone_work::values(&self.budget, &self.values)?;
            self.type_environment.admit_clone(&self.budget)?;
            self.environments[id.0].values = self.values.clone();
            self.environments[id.0].types = self.type_environment.clone();
        }
        Ok(())
    }

    pub(super) fn exit_block(&mut self) {
        if let Some(active) = self.active_functions.pop() {
            self.function_environments = active.outer_declarations;
        }
    }
}
