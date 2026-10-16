//! Complete named-function Type arguments are selected together, then their
//! structural promises are checked together. This does not change the separate
//! left-to-right default preparation of type functions and type declarations.
use super::*;

impl Evaluator {
    pub(super) fn preselect_named_type_arguments(
        &mut self,
        parameters: &[GenericParameter],
        arguments: &[TypeExpr],
        declaration: &str,
        caller: &environments::Environment,
        bound: &mut environments::Environment,
    ) -> Result<Option<Vec<TypeExpr>>> {
        if parameters.is_empty()
            || arguments.len() != parameters.len()
            || !self.functions.contains_key(declaration)
            || parameters.iter().any(|parameter| {
                parameter.default.is_some()
                    || !parameter
                        .name
                        .chars()
                        .next()
                        .is_some_and(char::is_uppercase)
                    || parameter.bound.as_ref().is_some_and(|bound| {
                        !matches!(bound.kind, TypeKind::Record { .. })
                            && !matches!(&bound.kind, TypeKind::Name { path, arguments }
                                if path == &["Type"] && arguments.is_empty())
                    })
            })
        {
            return Ok(None);
        }
        let caller_loops = self.loop_frames.clone();
        let mut selected = Vec::with_capacity(arguments.len());
        for (parameter, argument) in parameters.iter().zip(arguments) {
            // Every explicit expression belongs to the caller, even if a
            // same-spelled callee binder has already acquired a selection.
            self.install_environment(self.copy_environment(caller)?);
            self.loop_frames = caller_loops.clone();
            let actual = self.resolve_type(argument, &mut Vec::new())?;
            clone_work::type_syntax(&self.budget, &actual)?;
            if let Some(witness) = self.source_type_witness(actual.clone())? {
                bound
                    .types
                    .select_type(&parameter.name, witness.clone(), &self.budget)?;
                // A declared Type binder can also name a residual. Keeping
                // this independent row selection is necessary when later
                // normalization expands that residual into ordinary fields.
                bound
                    .types
                    .select_row(&parameter.name, witness, &self.budget)?;
            }
            bound
                .values
                .insert(parameter.name.clone(), StaticValue::Type(actual.clone()));
            selected.push(actual);
        }
        Ok(Some(selected))
    }
}
