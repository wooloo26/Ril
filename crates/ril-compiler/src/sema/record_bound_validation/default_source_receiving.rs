//! Source-first coverage of declaration defaults, including never-called ones.
//! A declaration probe is not an application and cannot invent body entry.
use super::*;
use crate::sema::{
    default_uses::{DefaultOrigin, DefaultUse},
    source_reception,
};

/// Only the immutable Source view is aligned here. Allocation recency changes
/// origins, while permissions, causes, Result duties and latent obligation
/// contracts retain their separate validators. Callable targets and the public
/// signature are stable Source coordinates, including labels/defaults.
fn same_default_source_view(left: &Value, right: &Value, work: &mut usize, depth: usize) -> Check {
    require(
        depth < 64 && *work > 0,
        "declaration default source view exceeds its bound",
    )?;
    *work -= 1;
    require(
        left.ty == right.ty
            && left.source_type_witness == right.source_type_witness
            && left.callables == right.callables
            && left.signature == right.signature,
        "declaration default root source view differs from its frozen snapshot",
    )?;
    for (left, right) in [
        (&left.option_payload, &right.option_payload),
        (&left.result_payload, &right.result_payload),
        (&left.result_success, &right.result_success),
        (&left.result_error, &right.result_error),
        (&left.variant_payload, &right.variant_payload),
    ] {
        match (left, right) {
            (Some(left), Some(right)) => same_default_source_view(left, right, work, depth + 1)?,
            (None, None) => {}
            _ => return Err("declaration default payload Source presence changed".into()),
        }
    }
    require(
        left.variant_witnesses
            .keys()
            .eq(right.variant_witnesses.keys()),
        "declaration default variant Source set changed",
    )?;
    for (tag, left) in &left.variant_witnesses {
        same_default_source_view(left, &right.variant_witnesses[tag], work, depth + 1)?;
    }
    Ok(())
}

fn needs_source(facts: &SemanticFacts, syntax: &TypeExpr) -> Check<bool> {
    let mut pending = vec![(syntax, 0)];
    let mut aliases = BTreeSet::new();
    let mut work = 4096usize;
    while let Some((syntax, depth)) = pending.pop() {
        require(
            depth < 64 && work > 0,
            "declaration default source predicate exceeds its bound",
        )?;
        work -= 1;
        match &syntax.kind {
            TypeKind::Array { .. } | TypeKind::Callable { .. } => return Ok(true),
            TypeKind::Optional(inner) => pending.push((inner, depth + 1)),
            TypeKind::Tuple(items) => pending.extend(items.iter().map(|item| (item, depth + 1))),
            TypeKind::Map { key, value } => {
                pending.extend([(key.as_ref(), depth + 1), (value.as_ref(), depth + 1)])
            }
            TypeKind::Record { fields, row } => {
                pending.extend(fields.iter().map(|field| (&field.ty, depth + 1)));
                pending.extend(row.iter().map(|row| (row.as_ref(), depth + 1)));
            }
            TypeKind::Name { path, arguments } => {
                pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
                let name = path.join("::");
                if aliases.insert(name.clone())
                    && let Some(declaration) = facts.external_type_declarations.get(&name)
                    && !declaration.nominal
                    && !declaration.opaque
                    && declaration.variants.is_empty()
                {
                    pending.extend(declaration.value.iter().map(|value| (value, depth + 1)));
                } else if !facts.external_type_declarations.contains_key(&name)
                    && arguments.is_empty()
                {
                    let matching: Vec<_> = facts
                        .generic_binders
                        .values()
                        .filter(|binder| {
                            binder.name == name
                                || format!("\0effect-binder:{}", binder.identity) == name
                        })
                        .collect();
                    if !matching.is_empty() {
                        for binder in matching {
                            let parameter = facts
                                .functions
                                .iter()
                                .find(|function| function.definition == binder.definition)
                                .and_then(|function| {
                                    function.syntax.generics.get(binder.index as usize)
                                })
                                .ok_or_else(|| {
                                    "declaration default binder lost its genuine header".to_owned()
                                })?;
                            if crate::sema::record_bounds::certifies_type_sort(
                                &binder.identity,
                                binder,
                                parameter,
                                &facts.record_bounds,
                            ) {
                                return Ok(true);
                            }
                        }
                    } else {
                        let head = crate::sema::model::SourceTypeWitness {
                            key: crate::static_eval::normalized_argument_key(syntax),
                            syntax: syntax.clone(),
                        };
                        if !crate::sema::source_type_validation::resolved_names(
                            &head,
                            &facts.external_type_declarations,
                        ) {
                            return Ok(true);
                        }
                    }
                }
            }
            _ => return Ok(true),
        }
    }
    Ok(false)
}

pub(super) fn has_sources(facts: &SemanticFacts) -> Check<bool> {
    super::explicit_named::source_sites(facts)?;
    for function in &facts.functions {
        for parameter in &function.syntax.parameters {
            if parameter.default.is_some()
                && let Some(syntax) = &parameter.ty
                && needs_source(facts, syntax)?
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

impl Replay<'_> {
    pub(super) fn declaration_default_sources(&self) -> Result<(), Failure> {
        let fallback = self
            .facts
            .functions
            .first()
            .map(|function| function.syntax.span)
            .unwrap_or(Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            });
        let sites = super::explicit_named::source_sites(self.facts)
            .map_err(|message| (fallback, None, message))?;
        for (&definition, function) in &self.functions {
            for (index, parameter) in function.syntax.parameters.iter().enumerate() {
                let (Some(syntax), Some(default)) = (&parameter.ty, &parameter.default) else {
                    continue;
                };
                let run = || -> Check {
                    if !needs_source(self.facts, syntax)? {
                        return Ok(());
                    }
                    let receipts: Vec<_> = self
                        .facts
                        .default_uses
                        .iter()
                        .filter(|receipt| {
                            receipt.origin == DefaultOrigin::DeclarationProbe
                                && receipt.target == Some(definition)
                                && receipt.parameter as usize == index
                        })
                        .collect();
                    require(
                        !receipts.is_empty(),
                        "declaration default Source lost every owned probe receipt",
                    )?;
                    for receipt in receipts {
                        self.declaration_default_receipt(
                            definition, index, syntax, default, receipt, &sites,
                        )?;
                    }
                    Ok(())
                };
                run().map_err(|message| (default.span, None, message))?;
            }
        }
        Ok(())
    }

    fn declaration_default_receipt(
        &self,
        definition: DefinitionId,
        index: usize,
        annotation: &TypeExpr,
        syntax: &Expr,
        receipt: &DefaultUse,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check {
        require(
            self.facts
                .default_uses
                .get(receipt.id.0 as usize)
                .is_some_and(|actual| std::ptr::eq(actual, receipt))
                && receipt.origin == DefaultOrigin::DeclarationProbe
                && receipt.target == Some(definition)
                && receipt.parameter as usize == index
                && receipt.owner == Some(CallableOwner::Function(definition))
                && receipt.caller.owner == receipt.owner
                && receipt.span == syntax.span
                && receipt.entered.is_empty()
                && !matches!(
                    receipt.status,
                    CopyInvocationStatus::Rejected | CopyInvocationStatus::Unsupported
                ),
            "declaration default receipt changed its genuine header, owner or outcome",
        )?;
        let token = receipt
            .result_expression
            .ok_or_else(|| "declaration default has no actual root token".to_owned())?;
        let observed = self
            .facts
            .expressions
            .get(token)
            .ok_or_else(|| "declaration default root token is outside its arena".to_owned())?;
        let mut context = receipt.caller;
        context.default_use = Some(receipt.id);
        require(
            observed.span == syntax.span
                && self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|row| row.expression == token && row.context == context)
                    .count()
                    == 1,
            "declaration default root belongs to another Source or default-use context",
        )?;
        let snapshot = receipt
            .result
            .as_ref()
            .ok_or_else(|| "declaration default lost its original snapshot".to_owned())?;
        let epoch = receipt
            .result_allocation_epoch
            .ok_or_else(|| "declaration default lost its actual result epoch".to_owned())?;
        // ExprFacts are remapped by subsequent allocate_site recency moves;
        // the result snapshot remains frozen at its completion epoch. Compare
        // in the observation's current coordinates, never transport backwards.
        self.input_value_transport(
            &snapshot.value,
            &observed.value,
            epoch,
            self.facts.allocation_history.len(),
        )?;
        same_default_source_view(&snapshot.value, &observed.value, &mut 4096, 0)?;
        require(
            receipt.evaluation_complete == (snapshot.value.ty != Ty::Never),
            "declaration default completion disagrees with its original root",
        )?;
        if snapshot.value.ty == Ty::Never {
            // This supplies no value, closed schema or normal body entry.
            return Ok(());
        }
        let scope = self.scope(definition)?;
        let selected = self.declaration_default_selections(definition, receipt)?;
        let mut work = 16384;
        let environment = self.function(definition)?.typing_environment.clone();
        let (expected, environment) =
            self.source_type_header_raw(annotation, &scope, environment, &mut work)?;
        let mut substitutions = BTreeMap::new();
        for (identity, key) in selected {
            let source = self
                .source_header_schema(&key, environment.clone(), &mut work)?
                .0;
            substitutions.insert(identity, source);
        }
        let expected = super::call_input_source::schema_work(&mut work, |budget| {
            expected.substitute(&substitutions, budget)
        })?;
        let actual = self
            .original_observed_source_schema_with_work(syntax, token, context, sites, &mut work)?;
        let fresh = source_reception::construction(syntax, &mut work)
            .ok_or_else(|| "declaration default construction exceeds its bound".to_owned())?;
        let fits = super::call_input_source::schema_work(&mut work, |budget| match actual {
            Some((actual, environment)) if !environment.is_poisoned() => {
                expected.receive_schema(&actual, Some(&fresh), budget)
            }
            Some(_) => Err(crate::sema::source_types::SourceTypesError::Unresolved),
            None => expected
                .empty_context(&fresh, budget)
                .map(|answer| answer == Some(true)),
        })?;
        require(
            fits,
            "declaration default original Source does not prove its receiving coordinates",
        )
    }

    pub(super) fn declaration_default_selections(
        &self,
        definition: DefinitionId,
        receipt: &DefaultUse,
    ) -> Check<BTreeMap<String, ArgumentKey>> {
        let function = self.function(definition)?;
        require(
            receipt.arguments.len() == function.syntax.generics.len(),
            "declaration default static rows lost owned positions",
        )?;
        for (index, argument) in receipt.arguments.iter().enumerate() {
            let binder = self.binder(definition, index as u32)?;
            require(
                argument.definition == definition
                    && argument.index as usize == index
                    && argument.binder == binder.identity,
                "declaration default static row changed its actual owned binder",
            )?;
            if crate::sema::record_bounds::certifies_type_sort(
                &binder.identity,
                binder,
                &function.syntax.generics[index],
                &self.facts.record_bounds,
            ) {
                require(argument.key.as_ref().is_none_or(|key| matches!(key, ArgumentKey::Binder { identity, sort: StaticBinderSort::Type } if identity == &binder.identity)),
                    "declaration default borrowed a closed actual own-Type specialization")?;
            }
        }
        let mut selected = BTreeMap::new();
        for argument in &receipt.captured_arguments {
            require(
                function
                    .typing_environment
                    .generic_context
                    .values()
                    .any(|identity| identity == &argument.binder)
                    && !receipt
                        .arguments
                        .iter()
                        .any(|owned| owned.binder == argument.binder)
                    && !selected.contains_key(&argument.binder),
                "declaration default captured Type changed its lexical role",
            )?;
            if let Some(key) = &argument.key {
                selected.insert(argument.binder.clone(), key.clone());
            }
        }
        Ok(selected)
    }
}
