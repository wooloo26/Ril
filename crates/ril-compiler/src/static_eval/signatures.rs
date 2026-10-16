//! Closed static signatures evaluate once in their declaration environment.
//! Invocation and constant publication consume the resulting type witnesses.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct SignatureKey {
    declaration: String,
    environment: Option<environments::EnvironmentId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Signature {
    pub parameters: Vec<Parameter>,
    pub result: Option<TypeExpr>,
}

impl Evaluator {
    pub(super) fn frozen_static_signature(
        &self,
        name: &str,
        captured: Option<environments::EnvironmentId>,
    ) -> Option<&Signature> {
        self.static_signatures.get(&SignatureKey {
            declaration: name.into(),
            environment: captured,
        })
    }
    pub(super) fn static_parameter_witnesses(&self, function: &Function) -> Result<Vec<Parameter>> {
        let key = SignatureKey {
            declaration: function.name.clone(),
            environment: self.function_environments.get(&function.name).copied(),
        };
        if let Some(signature) = self.static_signatures.get(&key) {
            return Ok(signature.parameters.clone());
        }
        let mut parameters = function.parameters.clone();
        for parameter in &mut parameters {
            if let Some(ty) = &mut parameter.ty {
                *ty = self.numeric_context_witness(ty, 0)?;
            }
        }
        Ok(parameters)
    }
    pub(super) fn static_signature(&mut self, function: &Function) -> Result<Signature> {
        let mut signature = Signature {
            parameters: function.parameters.clone(),
            result: function.return_type.clone(),
        };
        // A generic signature needs its actual static arguments before it can
        // publish a witness. The existing instantiation path keeps that duty.
        if !function.generics.is_empty() || !function.signature_where.is_empty() {
            return Ok(signature);
        }
        let key = SignatureKey {
            declaration: function.name.clone(),
            environment: self.function_environments.get(&function.name).copied(),
        };
        if let Some(signature) = self.static_signatures.get(&key) {
            return Ok(signature.clone());
        }
        // At top-level elaboration each written annotation is a real root.
        // In an evaluated local declaration, an enclosing root is inherited.
        for parameter in &mut signature.parameters {
            if let Some(ty) = &mut parameter.ty {
                *ty = self.resolve_type(ty, &mut vec![])?;
            }
        }
        if let Some(ty) = &mut signature.result {
            *ty = self.resolve_type(ty, &mut vec![])?;
        }
        self.static_signatures.insert(key, signature.clone());
        Ok(signature)
    }
}
