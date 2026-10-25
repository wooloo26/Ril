//! Pattern type selection is reconstructed from original syntax and lexical
//! resolution. Runtime lengths and inferred erased shapes are not inputs.
use crate::hir::{
    lexical::{LexicalBindings, TypeNameBinding},
    nodes::{HirProgram, PatternKind},
};
use crate::sema::{
    context::FrozenEnvironment,
    model::ConstructorInfo,
    source_types::{SourceSchema, SourceTypesError as Error, WorkLimit},
};
use ril_compiler_core::{ids::PatternId, projection::TypeProjection as Path};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone)]
enum SourcePatternStep {
    Structural(Path),
    Constructor(PatternId),
}

pub(crate) fn contains_binding(
    hir: &HirProgram,
    root: PatternId,
    introducer: PatternId,
    name: &str,
    work: &mut WorkLimit,
) -> Result<bool, Error> {
    let mut remaining = work.remaining();
    let plan = hir.pattern_bindings(root, &mut remaining);
    work.charge(work.remaining() - remaining)?;
    let plan = plan.map_err(|error| match error {
        crate::hir::nodes::LowerError::Budget(_) => Error::BudgetExceeded,
        _ => Error::MissingNode,
    })?;
    work.charge(plan.len())?;
    Ok(plan
        .iter()
        .any(|binding| binding.pattern == introducer && binding.name == name))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn project_binding(
    source: &SourceSchema,
    environment: &FrozenEnvironment,
    hir: &HirProgram,
    lexical: &LexicalBindings,
    constructors: &BTreeMap<String, ConstructorInfo>,
    root: PatternId,
    introducer: PatternId,
    name: &str,
    work: &mut WorkLimit,
) -> Result<Option<SourceSchema>, Error> {
    if environment.is_poisoned() {
        return Err(Error::Unresolved);
    }
    if !contains_binding(hir, root, introducer, name, work)? {
        return Err(Error::InvalidEvidence(
            "pattern Source borrowed another introducer".into(),
        ));
    }
    let mut paths = Vec::new();
    Paths { hir, work, name }.visit(root, &mut Vec::new(), true, &mut paths, 0)?;
    if paths.is_empty() || paths.iter().any(Option::is_none) {
        return Ok(None);
    }
    let mut selected: Option<SourceSchema> = None;
    for path in paths.into_iter().flatten() {
        let mut projected = source.clone();
        for step in path {
            work.charge(1)?;
            projected = match step {
                SourcePatternStep::Structural(step) => projected.project_steps(&[step], work)?,
                SourcePatternStep::Constructor(pattern) => {
                    let Some(payload) = constructor_payload(
                        &projected,
                        environment,
                        hir,
                        lexical,
                        constructors,
                        pattern,
                        work,
                    )?
                    else {
                        return Ok(None);
                    };
                    payload
                }
            };
        }
        if let Some(previous) = &selected {
            if !previous.equivalent_in(&projected, environment, environment, work)? {
                return Err(Error::InvalidEvidence(
                    "or-pattern alternatives expose incompatible Source coordinates".into(),
                ));
            }
        } else {
            selected = Some(projected);
        }
    }
    Ok(selected)
}

fn constructor_payload(
    source: &SourceSchema,
    environment: &FrozenEnvironment,
    hir: &HirProgram,
    lexical: &LexicalBindings,
    constructors: &BTreeMap<String, ConstructorInfo>,
    pattern: PatternId,
    work: &mut WorkLimit,
) -> Result<Option<SourceSchema>, Error> {
    let original = hir.pattern(pattern).ok_or(Error::MissingNode)?;
    let PatternKind::Constructor { path, .. } = &original.kind else {
        return Err(Error::MissingNode);
    };
    work.charge(1 + path.len())?;
    for name in path {
        work.text(name)?;
    }
    let mut remaining = work.remaining();
    let binding = lexical.pattern_constructor_binding(pattern, &mut remaining);
    work.charge(work.remaining() - remaining)?;
    let binding = binding.map_err(|error| match error {
        crate::hir::nodes::LowerError::Budget(_) => Error::BudgetExceeded,
        _ => Error::MissingNode,
    })?;
    let name = path.join("::");
    if let TypeNameBinding::Declaration(declaration) = binding {
        return match crate::sema::source_types::declarations::constructor_payload(
            source,
            &name,
            declaration,
            hir,
            lexical,
            work,
        ) {
            Err(Error::NeedsStaticElaboration) => Ok(None),
            result => result,
        };
    }
    if binding != TypeNameBinding::Unbound {
        return Ok(None);
    }
    let tag = match path.as_slice() {
        [name] => Some(name.as_str()),
        [namespace, name] if namespace == "Prelude" => Some(name.as_str()),
        _ => None,
    };
    let sealed = match tag {
        Some("Some") => Some(Path::OptionalPayload),
        Some("Ok") => Some(Path::ResultSuccess),
        Some("Err") => Some(Path::ResultError),
        _ => None,
    };
    if let Some(step) = sealed {
        return source.project_steps(&[step], work).map(Some);
    }

    work.charge(1 + constructors.len().checked_ilog2().unwrap_or(0) as usize)?;
    let Some(constructor) = constructors.get(&name) else {
        return Ok(None);
    };
    if constructor.tag != name {
        return Err(Error::Unresolved);
    }
    let Some((owner, payload)) =
        crate::sema::source_types::standard_data::constructor_sources(constructor, work)?
    else {
        return Ok(None);
    };
    let catalog = &constructor.typing_environment;
    if !crate::sema::builtin_sources::is_catalog_environment(catalog)
        || !source.equivalent_in(&owner, environment, catalog, work)?
        || payload.requires_environment(work)?
    {
        return Err(Error::Unresolved);
    }
    // Catalog components are admitted only after proving the graph is closed
    // and independent of interpretation. A future scoped payload cannot borrow
    // this receiver's environment through this adapter.
    Ok(Some(payload))
}

struct Paths<'a, 'w> {
    hir: &'a HirProgram,
    work: &'w mut WorkLimit,
    name: &'a str,
}

impl Paths<'_, '_> {
    fn emit(
        &mut self,
        path: &[SourcePatternStep],
        known: bool,
        out: &mut Vec<Option<Vec<SourcePatternStep>>>,
    ) -> Result<(), Error> {
        self.work.charge(1 + path.len())?;
        for step in path {
            match step {
                SourcePatternStep::Structural(Path::Field(name)) => self.work.text(name)?,
                SourcePatternStep::Structural(Path::RecordRemainder(fields)) => {
                    self.work.charge(fields.len())?;
                    for name in fields {
                        self.work.text(name)?;
                    }
                }
                _ => {}
            }
        }
        out.push(known.then(|| path.to_vec()));
        Ok(())
    }

    fn visit(
        &mut self,
        id: PatternId,
        path: &mut Vec<SourcePatternStep>,
        known: bool,
        out: &mut Vec<Option<Vec<SourcePatternStep>>>,
        depth: usize,
    ) -> Result<(), Error> {
        self.work.charge(1)?;
        if depth >= 128 {
            return Err(Error::BudgetExceeded);
        }
        let original = self.hir.pattern(id).ok_or(Error::MissingNode)?;
        match &original.kind {
            PatternKind::Name(name) | PatternKind::Rest(Some(name))
                if name == self.name && name != "_" =>
            {
                self.emit(path, known, out)?
            }
            PatternKind::Mode { pattern, .. } => {
                self.visit(*pattern, path, known, out, depth + 1)?
            }
            PatternKind::Tuple(items) | PatternKind::Array(items) => {
                self.work.charge(items.len())?;
                let array = matches!(original.kind, PatternKind::Array(_));
                let rest = items.iter().position(|id| {
                    matches!(
                        self.hir.pattern(*id).map(|item| &item.kind),
                        Some(PatternKind::Rest(_))
                    )
                });
                for (index, item) in items.iter().enumerate() {
                    if !array && Some(index) == rest {
                        continue;
                    }
                    let step = if array {
                        if Some(index) == rest {
                            Path::ArrayRemainder {
                                prefix: u32::try_from(index)
                                    .map_err(|_| Error::IdentityExhausted)?,
                                suffix: u32::try_from(items.len() - index - 1)
                                    .map_err(|_| Error::IdentityExhausted)?,
                            }
                        } else {
                            Path::Element
                        }
                    } else if rest.is_some_and(|rest| index > rest) {
                        Path::TupleFromEnd(
                            u32::try_from(items.len() - index - 1)
                                .map_err(|_| Error::IdentityExhausted)?,
                        )
                    } else {
                        Path::Tuple(u32::try_from(index).map_err(|_| Error::IdentityExhausted)?)
                    };
                    path.push(SourcePatternStep::Structural(step));
                    self.visit(*item, path, known, out, depth + 1)?;
                    path.pop();
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                self.work.charge(fields.len())?;
                for field in fields {
                    self.work.text(&field.name)?;
                    path.push(SourcePatternStep::Structural(Path::Field(
                        field.name.clone(),
                    )));
                    self.visit(field.pattern, path, known, out, depth + 1)?;
                    path.pop();
                }
                if rest_binding.as_deref() == Some(self.name) {
                    let mut excluded = BTreeSet::new();
                    for field in fields {
                        self.work.text(&field.name)?;
                        excluded.insert(field.name.clone());
                    }
                    path.push(SourcePatternStep::Structural(Path::RecordRemainder(
                        excluded,
                    )));
                    self.emit(path, known, out)?;
                    path.pop();
                }
            }
            PatternKind::Constructor {
                path: constructor,
                arguments,
                ..
            } => {
                self.work.charge(arguments.len() + constructor.len())?;
                for name in constructor {
                    self.work.text(name)?;
                }
                path.push(SourcePatternStep::Constructor(id));
                for (index, argument) in arguments.iter().enumerate() {
                    if arguments.len() > 1 {
                        path.push(SourcePatternStep::Structural(Path::Tuple(
                            u32::try_from(index).map_err(|_| Error::IdentityExhausted)?,
                        )));
                    }
                    self.visit(*argument, path, known, out, depth + 1)?;
                    if arguments.len() > 1 {
                        path.pop();
                    }
                }
                path.pop();
            }
            PatternKind::Alternative(alternatives) => {
                self.work.charge(alternatives.len())?;
                for alternative in alternatives {
                    self.visit(*alternative, path, known, out, depth + 1)?;
                }
            }
            PatternKind::Type {
                binder: Some(name), ..
            } if name == self.name => self.emit(path, false, out)?,
            _ => {}
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::{SemanticFacts, source_types::standard_data};

    const TAG: &str = "Concurrent::TaskFault::DoubleFaultFatal";

    fn fixture() -> SemanticFacts {
        crate::Session::new(
            ril_test::case_bytes(
                "tests/regressions/generated-scopes.ril::scope-fault-declarations",
            )
            .to_vec(),
        )
        .verify()
        .unwrap()
        .facts()
        .clone()
    }

    fn site(hir: &HirProgram) -> (PatternId, PatternId, String) {
        let mut root = None;
        hir.walk(100_000, |node, _| {
            if let crate::hir::nodes::NodeId::Pattern(id) = node
                && let Some(pattern) = hir.pattern(id)
                && matches!(&pattern.kind, PatternKind::Constructor { path, .. } if path.join("::") == TAG)
            {
                root.get_or_insert(id);
            }
        }).unwrap();
        let root = root.unwrap();
        let binding = hir
            .pattern_bindings(root, &mut 4096)
            .unwrap()
            .into_iter()
            .next()
            .unwrap();
        (root, binding.pattern, binding.name)
    }

    #[test]
    fn catalog_pattern_receivers_keep_their_declared_payload_and_work_bound() {
        let facts = fixture();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let lexical = LexicalBindings::new(hir, &mut 100_000).unwrap();
        let (root, introducer, name) = site(hir);
        let constructor = &facts.constructors[TAG];
        let (owner, expected) =
            standard_data::constructor_sources(constructor, &mut WorkLimit::new(4096))
                .unwrap()
                .unwrap();
        let selected = project_binding(
            &owner,
            &constructor.typing_environment,
            hir,
            &lexical,
            &facts.constructors,
            root,
            introducer,
            &name,
            &mut WorkLimit::new(16384),
        )
        .unwrap()
        .unwrap();
        assert!(
            selected
                .equivalent(&expected, &mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(
            !selected
                .requires_environment(&mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(matches!(
            project_binding(
                &owner,
                &constructor.typing_environment,
                hir,
                &lexical,
                &facts.constructors,
                root,
                introducer,
                &name,
                &mut WorkLimit::new(0)
            ),
            Err(Error::BudgetExceeded)
        ));
    }

    #[test]
    fn catalog_pattern_projection_rejects_borrowed_declarations_and_interpretations() {
        let facts = fixture();
        let hir = facts.semantic_hir.as_deref().unwrap();
        let lexical = LexicalBindings::new(hir, &mut 100_000).unwrap();
        let (root, introducer, name) = site(hir);
        let constructor = &facts.constructors[TAG];
        let (owner, _) = standard_data::constructor_sources(constructor, &mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        for mutation in 0..3 {
            let mut changed = facts.constructors.clone();
            match mutation {
                0 => {
                    changed.get_mut(TAG).unwrap().typing_environment = FrozenEnvironment::default()
                }
                1 => changed.get_mut(TAG).unwrap().payload_syntax = None,
                _ => changed.get_mut(TAG).unwrap().tag = "Concurrent::UnwindCause::Panicked".into(),
            }
            assert!(
                project_binding(
                    &owner,
                    &constructor.typing_environment,
                    hir,
                    &lexical,
                    &changed,
                    root,
                    introducer,
                    &name,
                    &mut WorkLimit::new(16384)
                )
                .is_err(),
                "mutation {mutation} borrowed a catalog declaration"
            );
        }
        let unrelated = &facts.constructors["Concurrent::UnwindCause::Panicked"];
        let (unrelated, _) =
            standard_data::constructor_sources(unrelated, &mut WorkLimit::new(4096))
                .unwrap()
                .unwrap();
        assert!(
            project_binding(
                &unrelated,
                &constructor.typing_environment,
                hir,
                &lexical,
                &facts.constructors,
                root,
                introducer,
                &name,
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
    }

    #[test]
    fn shadowed_catalog_spelling_cannot_recover_a_catalog_payload() {
        let facts = fixture();
        let source = ril_test::case_source(
            "tests/regressions/generated-scopes.ril::reject-shadowed-catalog-pattern-namespace",
        );
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let hir = HirProgram::lower(&parsed.program).unwrap();
        let lexical = LexicalBindings::new(&hir, &mut 100_000).unwrap();
        let (root, introducer, name) = site(&hir);
        assert!(
            !lexical
                .pattern_constructor_unshadowed(root, &mut 4096)
                .unwrap()
        );
        let constructor = &facts.constructors[TAG];
        let (owner, _) = standard_data::constructor_sources(constructor, &mut WorkLimit::new(4096))
            .unwrap()
            .unwrap();
        assert!(
            project_binding(
                &owner,
                &constructor.typing_environment,
                &hir,
                &lexical,
                &facts.constructors,
                root,
                introducer,
                &name,
                &mut WorkLimit::new(16384)
            )
            .unwrap()
            .is_none()
        );
    }
}
