//! Resolve original declaration edges into finite source graphs. Actual type
//! occurrences keep their lexical declaration and generic parameter identities;
//! legacy views without an occurrence retain conservative module-only lookup.
use super::{
    LegacySourceExport, SourceSchema, SourceSensitivity, SourceTypeQueries, graph::*, legacy,
};
use crate::hir::lexical::{LexicalBindings, TypeNameBinding};
use crate::hir::nodes::{self as hir, HirProgram};
use crate::sema::effect_identity::ArgumentKey;
use ril_compiler_core::ids::{GenericParamId, StmtId, TypeExprId};
use std::collections::{BTreeMap, BTreeSet};
#[path = "original_header.rs"]
mod original_header;
pub(crate) use original_header::{DeclaredConstructorInstance, constructor_instance};
pub(crate) use original_header::{
    EffectSource, EffectSourceError, HeaderContext, effect_source, elaborate_original_header,
    original_header,
};

#[derive(Clone, Copy)]
struct Alias {
    declaration: StmtId,
    value: TypeExprId,
}

struct Resolve<'a> {
    hir: &'a HirProgram,
    aliases: BTreeMap<String, Option<Alias>>,
    definitions: BTreeMap<(StmtId, TypeScope), SourceTypeId>,
    syntax: BTreeMap<(TypeExprId, TypeScope), SourceTypeId>,
    lexical: Option<&'a LexicalBindings>,
    substitutions: BTreeMap<GenericParamId, SourceTypeId>,
    copied: BTreeMap<SourceTypeId, SourceTypeId>,
    builder: SourceBuilder,
}

type TypeScope = Vec<(GenericParamId, SourceTypeId)>;

fn lexical_error(error: hir::LowerError) -> SourceTypesError {
    match error {
        hir::LowerError::Budget(_) => SourceTypesError::BudgetExceeded,
        _ => SourceTypesError::Unresolved,
    }
}

/// Resolve an actual HIR type occurrence in its original lexical environment.
/// Legacy graph names lack this declaration identity and keep their separate
/// conservative ingress; they cannot borrow this lookup's local aliases.
#[cfg(test)]
pub(crate) fn type_schema(
    id: TypeExprId,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    work.charge(1)?;
    hir.type_expression(id)
        .ok_or(SourceTypesError::MissingNode)?;
    let mut remaining = work.remaining();
    let before = remaining;
    let lexical = LexicalBindings::new(hir, &mut remaining);
    work.charge(before - remaining)?;
    let lexical = lexical.map_err(lexical_error)?;
    type_schema_with_lexical(id, hir, &lexical, work)
}

pub(crate) fn type_schema_with_lexical(
    id: TypeExprId,
    hir: &HirProgram,
    lexical: &LexicalBindings,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    work.charge(1)?;
    hir.type_expression(id)
        .ok_or(SourceTypesError::MissingNode)?;
    work.charge(1)?;
    let mut resolver = Resolve {
        hir,
        aliases: BTreeMap::new(),
        definitions: BTreeMap::new(),
        syntax: BTreeMap::new(),
        lexical: Some(lexical),
        substitutions: BTreeMap::new(),
        copied: BTreeMap::new(),
        builder: SourceBuilder::new()?,
    };
    let root = resolver.ty(id, work, 0)?;
    let graph = resolver.freeze(root, work)?;
    SourceSchema::frozen_view(&graph.types, graph.root, Some(id), work)
}

struct DeclaredGraph {
    types: SourceTypes,
    root: SourceTypeId,
    declarations: BTreeSet<SourceTypeId>,
}

/// Resolve the original declaration graph directly into a complete schema.
/// Recursive declaration edges are copied as graph edges, never exported to a
/// finite legacy key merely to import the same coordinates again.
pub(crate) fn schema(
    key: &ArgumentKey,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    let graph = resolve(key, hir, work)?;
    SourceSchema::frozen_view(&graph.types, graph.root, None, work)
}

/// Resolve only original declaration edges in an already captured graph. The
/// caller keeps its frozen environment; neither graph copying nor expansion
/// can replace that environment with a later lexical interpretation.
pub(crate) fn resolve_schema(
    source: &SourceSchema,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    let (types, root) = source.graph();
    let mut resolver = Resolve::new(hir, work)?;
    let root = resolver.copy(types, root, work, 0)?;
    let graph = resolver.freeze(root, work)?;
    SourceSchema::frozen_view(&graph.types, graph.root, source.original(), work)
}

/// Expand only actual transparent module declarations. Recursive, captured or
/// ambiguous aliases stay unresolved; no runtime shape can fill the gap.
pub(crate) fn expanded_key(
    key: &ArgumentKey,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<ArgumentKey, SourceTypesError> {
    let graph = resolve(key, hir, work)?;
    let mut key = graph.types.legacy_key(graph.root, work)?;
    let mut pending = vec![&mut key];
    while let Some(key) = pending.pop() {
        work.charge(1)?;
        match key {
            ArgumentKey::Callable {
                parameters,
                result,
                annotations,
            } => {
                for text in annotations {
                    work.text(text)?;
                    *text = text.replace(' ', "");
                }
                pending.extend(parameters.iter_mut().map(|(_, ty)| ty));
                pending.push(result);
            }
            ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => {
                pending.extend(arguments)
            }
            ArgumentKey::Array { element, .. } => pending.push(element),
            ArgumentKey::Map { key, value } => {
                pending.push(key);
                pending.push(value);
            }
            ArgumentKey::Record { fields, row } => {
                pending.extend(fields.iter_mut().map(|(_, _, ty)| ty));
                if let Some(row) = row {
                    pending.push(row);
                }
            }
            _ => {}
        }
    }
    Ok(key)
}

/// A typed construction chooses its source view at its own HIR annotation.
/// Coordinate-free declaration graphs need no erased runtime shape or value
/// witness to recover that view. Sensitive/unresolved interpretations retain
/// their separate frozen source obligations.
pub(crate) fn construction(
    source: ril_compiler_core::ids::ExprId,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<Option<ArgumentKey>, SourceTypesError> {
    let (graph, _) = match construction_graph(source, hir, work) {
        Ok(Some(graph)) => graph,
        Ok(None) | Err(SourceTypesError::NeedsStaticElaboration) => return Ok(None),
        Err(error) => return Err(error),
    };
    if !matches!(
        graph.types.sensitivity(graph.root, work),
        SourceSensitivity::Absent { .. }
    ) {
        return Ok(None);
    }
    graph
        .types
        .declared_key(graph.root, &graph.declarations, work)
        .map(Some)
}

pub(crate) fn construction_schema(
    source: ril_compiler_core::ids::ExprId,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<Option<SourceSchema>, SourceTypesError> {
    let (graph, original) = match construction_graph(source, hir, work) {
        Ok(Some(graph)) => graph,
        Ok(None) | Err(SourceTypesError::NeedsStaticElaboration) => return Ok(None),
        Err(error) => return Err(error),
    };
    match graph.types.sensitivity(graph.root, work) {
        SourceSensitivity::Absent { .. } => {
            SourceSchema::frozen_view(&graph.types, graph.root, Some(original), work).map(Some)
        }
        SourceSensitivity::Sensitive { .. } => Ok(None),
        SourceSensitivity::Unknown { reason } => Err(reason),
    }
}

fn construction_graph(
    source: ril_compiler_core::ids::ExprId,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<Option<(DeclaredGraph, TypeExprId)>, SourceTypesError> {
    work.charge(1)?;
    let expression = hir
        .expression(source)
        .ok_or(SourceTypesError::MissingNode)?;
    let hir::ExprKind::Record { ty: Some(ty), .. } = &expression.kind else {
        return Ok(None);
    };
    let mut resolver = Resolve::new(hir, work)?;
    let root = resolver.ty(*ty, work, 0)?;
    let graph = resolver.freeze(root, work)?;
    Ok(Some((graph, *ty)))
}

fn resolve(
    key: &ArgumentKey,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<DeclaredGraph, SourceTypesError> {
    let mut resolver = Resolve::new(hir, work)?;
    let input = legacy::import(key, work)?;
    let root = resolver.copy(&input.types, input.root, work, 0)?;
    resolver.freeze(root, work)
}

impl<'a> Resolve<'a> {
    fn new(hir: &'a HirProgram, work: &mut WorkLimit) -> Result<Self, SourceTypesError> {
        let mut aliases = BTreeMap::new();
        for &id in hir.roots() {
            work.charge(1)?;
            let statement = hir.statement(id).ok_or(SourceTypesError::MissingNode)?;
            let hir::StmtKind::Type {
                name,
                generics,
                value: Some(value),
                variants,
                opaque: false,
                nominal: false,
                ..
            } = &statement.kind
            else {
                continue;
            };
            if statement.info.owner != hir::LexicalOwner::Module
                || !generics.is_empty()
                || !variants.is_empty()
            {
                continue;
            }
            work.text(name)?;
            if let Some(previous) = aliases.get_mut(name) {
                *previous = None;
            } else {
                aliases.insert(
                    name.clone(),
                    Some(Alias {
                        declaration: id,
                        value: *value,
                    }),
                );
            }
        }
        // Legacy names do not carry a lexical declaration ID. Until that
        // ingress is removed, a same-spelled local declaration/binder makes
        // the global-name interpretation ambiguous, never coordinate-free.
        work.charge(hir.statements().len() + hir.generics().len())?;
        for (_, statement) in hir.statements() {
            if statement.info.owner != hir::LexicalOwner::Module
                && let hir::StmtKind::Type { name, .. } = &statement.kind
                && let Some(alias) = aliases.get_mut(name)
            {
                *alias = None;
            }
        }
        for generic in hir.generics() {
            if let Some(alias) = aliases.get_mut(&generic.name) {
                *alias = None;
            }
        }
        Ok(Self {
            hir,
            aliases,
            definitions: BTreeMap::new(),
            syntax: BTreeMap::new(),
            lexical: None,
            substitutions: BTreeMap::new(),
            copied: BTreeMap::new(),
            builder: SourceBuilder::new()?,
        })
    }

    fn freeze(
        self,
        root: SourceTypeId,
        work: &mut WorkLimit,
    ) -> Result<DeclaredGraph, SourceTypesError> {
        work.charge(self.definitions.len())?;
        let declarations = self.definitions.values().copied().collect();
        Ok(DeclaredGraph {
            types: self.builder.freeze(work)?,
            root,
            declarations,
        })
    }
}

impl Resolve<'_> {
    fn step(work: &mut WorkLimit, depth: usize) -> Result<(), SourceTypesError> {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        Ok(())
    }

    fn scope_key(&self, work: &mut WorkLimit) -> Result<TypeScope, SourceTypesError> {
        work.charge(self.substitutions.len())?;
        Ok(self
            .substitutions
            .iter()
            .map(|(id, value)| (*id, *value))
            .collect())
    }

    fn type_binding(
        &self,
        syntax: TypeExprId,
        work: &mut WorkLimit,
    ) -> Result<Option<TypeNameBinding>, SourceTypesError> {
        let Some(lexical) = &self.lexical else {
            return Ok(None);
        };
        let mut remaining = work.remaining();
        let before = remaining;
        let result = lexical.lookup_type(syntax, &mut remaining);
        work.charge(before - remaining)?;
        result.map(Some).map_err(lexical_error)
    }

    fn declared_type(
        &mut self,
        declaration: StmtId,
        arguments: &[SourceTypeId],
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<SourceTypeId, SourceTypesError> {
        Self::step(work, depth)?;
        let statement = self
            .hir
            .statement(declaration)
            .ok_or(SourceTypesError::MissingNode)?;
        let hir::StmtKind::Type {
            name,
            generics,
            value,
            variants,
            opaque,
            nominal,
            ..
        } = &statement.kind
        else {
            return Err(SourceTypesError::Unresolved);
        };
        work.charge(generics.len() + arguments.len() + 1)?;
        work.text(name)?;
        if generics.len() != arguments.len() {
            return Err(SourceTypesError::NeedsStaticElaboration);
        }
        if *opaque || *nominal || !variants.is_empty() {
            return self.builder.insert(
                SourceNode::OpaqueName {
                    name: name.clone(),
                    arguments: arguments.to_vec(),
                },
                work,
            );
        }
        let value = value.ok_or(SourceTypesError::Unresolved)?;
        work.charge(self.substitutions.len() + generics.len())?;
        let mut substitutions = self.substitutions.clone();
        for (parameter, argument) in generics.iter().zip(arguments) {
            let generic = self
                .hir
                .generic(*parameter)
                .ok_or(SourceTypesError::MissingNode)?;
            if generic.info.owner != hir::LexicalOwner::Declaration(declaration) {
                return Err(SourceTypesError::Unresolved);
            }
            if let Some(bound) = generic.bound {
                let kind = &self
                    .hir
                    .type_expression(bound)
                    .ok_or(SourceTypesError::MissingNode)?
                    .kind;
                let hir::TypeKind::Name { path, arguments } = kind else {
                    return Err(SourceTypesError::NeedsStaticElaboration);
                };
                work.charge(path.len() + arguments.len())?;
                for part in path {
                    work.text(part)?;
                }
                if path.len() != 1
                    || path[0] != "Type"
                    || !arguments.is_empty()
                    || self.type_binding(bound, work)? != Some(TypeNameBinding::Unbound)
                {
                    return Err(SourceTypesError::NeedsStaticElaboration);
                }
            }
            substitutions.insert(*parameter, *argument);
        }
        work.charge(substitutions.len())?;
        let scope: TypeScope = substitutions
            .iter()
            .map(|(id, value)| (*id, *value))
            .collect();
        let key = (declaration, scope);
        if let Some(root) = self.definitions.get(&key) {
            return Ok(*root);
        }
        let root = self.builder.reserve(work)?;
        self.definitions.insert(key, root);
        let previous = std::mem::replace(&mut self.substitutions, substitutions);
        let target = self.ty(value, work, depth + 1);
        self.substitutions = previous;
        self.builder.define(
            root,
            SourceNode::Alias {
                declaration: name.clone(),
                target: target?,
            },
            work,
        )?;
        Ok(root)
    }

    fn alias(
        &mut self,
        name: &str,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<Option<SourceTypeId>, SourceTypesError> {
        Self::step(work, depth)?;
        let Some(alias) = self.aliases.get(name).copied().flatten() else {
            return Ok(None);
        };
        let key = (alias.declaration, Vec::new());
        if let Some(&id) = self.definitions.get(&key) {
            return Ok(Some(id));
        }
        work.text(name)?;
        let id = self.builder.reserve(work)?;
        self.definitions.insert(key, id);
        let target = self.ty(alias.value, work, depth + 1)?;
        self.builder.define(
            id,
            SourceNode::Alias {
                declaration: name.into(),
                target,
            },
            work,
        )?;
        Ok(Some(id))
    }

    fn copy(
        &mut self,
        input: &SourceTypes,
        id: SourceTypeId,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<SourceTypeId, SourceTypesError> {
        Self::step(work, depth)?;
        if let Some(&output) = self.copied.get(&id) {
            return Ok(output);
        }
        let node = input.get(id)?;
        node.charge(work)?;
        if let SourceNode::OpaqueName { name, arguments } = node
            && arguments.is_empty()
            && let Some(output) = self.alias(name, work, depth + 1)?
        {
            self.copied.insert(id, output);
            return Ok(output);
        }
        let output = self.builder.reserve(work)?;
        self.copied.insert(id, output);
        let node = node.map_children(|child| self.copy(input, child, work, depth + 1))?;
        self.builder.define(output, node, work)?;
        Ok(output)
    }

    fn ty(
        &mut self,
        id: TypeExprId,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<SourceTypeId, SourceTypesError> {
        Self::step(work, depth)?;
        let syntax_key = (id, self.scope_key(work)?);
        if let Some(&output) = self.syntax.get(&syntax_key) {
            return Ok(output);
        }
        let syntax = self
            .hir
            .type_expression(id)
            .ok_or(SourceTypesError::MissingNode)?;
        let node = match &syntax.kind {
            hir::TypeKind::Name { path, arguments } => {
                work.charge(path.len() + arguments.len())?;
                for name in path {
                    work.text(name)?;
                }
                let name = path.join("::");
                let binding = self.type_binding(id, work)?;
                match binding {
                    Some(TypeNameBinding::Other) => return Err(SourceTypesError::Unresolved),
                    Some(TypeNameBinding::Generic(parameter)) => {
                        if !arguments.is_empty() {
                            return Err(SourceTypesError::NeedsStaticElaboration);
                        }
                        let root = self
                            .substitutions
                            .get(&parameter)
                            .copied()
                            .ok_or(SourceTypesError::Unresolved)?;
                        self.syntax.insert(syntax_key, root);
                        return Ok(root);
                    }
                    _ => {}
                }
                let arguments = arguments
                    .iter()
                    .map(|id| self.ty(*id, work, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(TypeNameBinding::Declaration(declaration)) = binding {
                    let root = self.declared_type(declaration, &arguments, work, depth + 1)?;
                    self.syntax.insert(syntax_key, root);
                    return Ok(root);
                }
                if arguments.is_empty() {
                    if let Some(scalar) = legacy::scalar(&name) {
                        return self.remember(id, SourceNode::Scalar(scalar), work);
                    }
                    if binding.is_none()
                        && let Some(output) = self.alias(&name, work, depth + 1)?
                    {
                        self.syntax.insert(syntax_key, output);
                        return Ok(output);
                    }
                    if binding.is_some()
                        && let Some(schema) = super::standard_data::schema(&name)
                    {
                        let root = schema.insert(&mut self.builder, work)?;
                        self.syntax.insert(syntax_key, root);
                        return Ok(root);
                    }
                }
                if let Some(kind) = legacy::container(&name) {
                    SourceNode::Container { kind, arguments }
                } else if binding.is_some() {
                    return Err(SourceTypesError::Unresolved);
                } else {
                    SourceNode::OpaqueName { name, arguments }
                }
            }
            hir::TypeKind::Optional(inner) => SourceNode::Container {
                kind: SourceContainer::Option,
                arguments: vec![self.ty(*inner, work, depth + 1)?],
            },
            hir::TypeKind::Array {
                length: None,
                element,
            } => SourceNode::Array {
                length: SourceLength::Dynamic,
                element: self.ty(*element, work, depth + 1)?,
            },
            hir::TypeKind::Array {
                length: Some(_), ..
            } => {
                // Only the original ingress may delegate this request to its
                // frozen static evaluator. An actual graph's unresolved node
                // remains an error and can never take this branch.
                return Err(SourceTypesError::NeedsStaticElaboration);
            }
            hir::TypeKind::Map { key, value } => SourceNode::Map {
                key: self.ty(*key, work, depth + 1)?,
                value: self.ty(*value, work, depth + 1)?,
            },
            hir::TypeKind::Tuple(items) => {
                work.charge(items.len())?;
                if items.is_empty() {
                    SourceNode::Scalar(SourceScalar::Unit)
                } else {
                    SourceNode::Tuple(
                        items
                            .iter()
                            .map(|id| self.ty(*id, work, depth + 1))
                            .collect::<Result<_, _>>()?,
                    )
                }
            }
            hir::TypeKind::Record { fields, row } => {
                work.charge(fields.len())?;
                let mut members = Vec::new();
                for field in fields {
                    work.text(&field.name)?;
                    members.push(SourceField {
                        label: field.name.clone(),
                        mutable: field.mutable,
                        value: self.ty(field.ty, work, depth + 1)?,
                    });
                }
                SourceNode::Record {
                    fields: members,
                    row: row.map(|row| self.ty(row, work, depth + 1)).transpose()?,
                }
            }
            hir::TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                work.charge(parameters.len() + annotations.len())?;
                let mut inputs = Vec::new();
                for parameter in parameters {
                    let ty = match parameter.ty {
                        Some(ty) => self.ty(ty, work, depth + 1)?,
                        None => self.unknown("inferred callable parameter", work)?,
                    };
                    inputs.push((parameter.mode, ty));
                }
                let result = match result {
                    Some(result) => self.ty(*result, work, depth + 1)?,
                    None => self
                        .builder
                        .insert(SourceNode::Scalar(SourceScalar::Unit), work)?,
                };
                let mut rows = Vec::new();
                for annotation in annotations {
                    work.text(&annotation.text)?;
                    rows.push(annotation.text.clone());
                }
                SourceNode::Callable {
                    parameters: inputs,
                    result,
                    annotations: rows,
                }
            }
            _ => return Err(SourceTypesError::NeedsStaticElaboration),
        };
        self.remember(id, node, work)
    }

    fn unknown(
        &mut self,
        description: &str,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.text(description)?;
        self.builder.insert(
            SourceNode::Unresolved {
                description: description.into(),
                arguments: vec![],
            },
            work,
        )
    }

    fn remember(
        &mut self,
        syntax: TypeExprId,
        node: SourceNode,
        work: &mut WorkLimit,
    ) -> Result<SourceTypeId, SourceTypesError> {
        let id = self.builder.insert(node, work)?;
        let key = (syntax, self.scope_key(work)?);
        self.syntax.insert(key, id);
        Ok(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_syntax::ast::{StmtKind, TypeExpr, TypeField, TypeKind};

    fn parameter_header(program: &ril_syntax::ast::Program) -> (HirProgram, TypeExprId) {
        let hir = HirProgram::lower(program).unwrap();
        let header = hir
            .roots()
            .iter()
            .find_map(|id| {
                let hir::StmtKind::Function(function) = &hir.statement(*id)?.kind else {
                    return None;
                };
                function.parameters.first()?.ty
            })
            .unwrap();
        (hir, header)
    }

    #[test]
    fn original_type_headers_resolve_aliases_in_their_own_lexical_scope() {
        for (case, expected) in [
            ("floating-alias-patterns", SourceScalar::F32),
            ("alias-pattern-range-safe", SourceScalar::I8),
            ("shadowed-alias-pattern-safe", SourceScalar::I8),
        ] {
            let source = ril_test::case_source(&format!("tests/conformance/numeric.ril::{case}"));
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok());
            let (hir, header) = parameter_header(&parsed.program);
            let schema = type_schema(header, &hir, &mut WorkLimit::new(65_536)).unwrap();
            assert_eq!(schema.original(), Some(header));
            assert_eq!(
                schema.scalar_representation(&mut WorkLimit::new(4096)),
                Ok(Some(expected))
            );
            assert!(matches!(
                type_schema(header, &hir, &mut WorkLimit::new(0)),
                Err(SourceTypesError::BudgetExceeded)
            ));
            assert!(matches!(
                type_schema(TypeExprId(u32::MAX), &hir, &mut WorkLimit::new(4096)),
                Err(SourceTypesError::MissingNode)
            ));
        }
        let parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::nested-alias-patterns",
        ));
        let (hir, header) = parameter_header(&parsed.program);
        let tuple = type_schema(header, &hir, &mut WorkLimit::new(65_536)).unwrap();
        for index in 0..2 {
            let field = tuple
                .project_steps(
                    &[super::super::SourcePath::Tuple(index)],
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
            assert_eq!(
                field.scalar_representation(&mut WorkLimit::new(4096)),
                Ok(Some(SourceScalar::I8))
            );
        }
    }

    #[test]
    fn applied_alias_parameters_are_keyed_by_actual_generic_ids_and_arguments() {
        let mut parsed = ril_syntax::parse(ril_test::case_source(
            "tests/conformance/numeric.ril::floating-alias-patterns",
        ))
        .program;
        let StmtKind::Type(declaration) = &mut parsed.statements[0].kind else {
            unreachable!()
        };
        let span = declaration.span;
        declaration
            .generics
            .push(ril_syntax::ast::GenericParameter {
                name: "T".into(),
                bound: None,
                default: None,
                span,
                hir_id: None,
            });
        let name = |name: &str| TypeExpr {
            kind: TypeKind::Name {
                path: vec![name.into()],
                arguments: vec![],
            },
            text: String::new(),
            span,
            hir_id: None,
        };
        declaration.value = Some(name("T"));
        let StmtKind::Function(function) = &mut parsed.statements[1].kind else {
            unreachable!()
        };
        function.parameters[0].ty = Some(TypeExpr {
            kind: TypeKind::Tuple(
                ["i8", "f64"]
                    .into_iter()
                    .map(|argument| TypeExpr {
                        kind: TypeKind::Name {
                            path: vec!["Rounded".into()],
                            arguments: vec![name(argument)],
                        },
                        text: String::new(),
                        span,
                        hir_id: None,
                    })
                    .collect(),
            ),
            text: String::new(),
            span,
            hir_id: None,
        });
        let (hir, header) = parameter_header(&parsed);
        let schema = type_schema(header, &hir, &mut WorkLimit::new(65_536)).unwrap();
        for (index, expected) in [SourceScalar::I8, SourceScalar::F64]
            .into_iter()
            .enumerate()
        {
            let field = schema
                .project_steps(
                    &[super::super::SourcePath::Tuple(index as u32)],
                    &mut WorkLimit::new(4096),
                )
                .unwrap();
            assert_eq!(
                field.scalar_representation(&mut WorkLimit::new(4096)),
                Ok(Some(expected))
            );
        }
    }

    #[test]
    fn type_headers_do_not_bypass_value_shadows_or_invent_unselected_generic_uids() {
        let source =
            ril_test::case_source("tests/conformance/numeric.ril::floating-alias-patterns");
        let mut parsed = ril_syntax::parse(source).program;
        let StmtKind::Function(function) = &mut parsed.statements[1].kind else {
            unreachable!()
        };
        function.name = "f32".into();
        let (hir, header) = parameter_header(&parsed);
        assert!(matches!(
            type_schema(header, &hir, &mut WorkLimit::new(65_536)),
            Err(SourceTypesError::Unresolved)
        ));

        let mut parsed = ril_syntax::parse(source).program;
        let StmtKind::Function(function) = &mut parsed.statements[1].kind else {
            unreachable!()
        };
        function.generics.push(ril_syntax::ast::GenericParameter {
            name: "Rounded".into(),
            bound: None,
            default: None,
            span: function.span,
            hir_id: None,
        });
        let (hir, header) = parameter_header(&parsed);
        assert!(matches!(
            type_schema(header, &hir, &mut WorkLimit::new(65_536)),
            Err(SourceTypesError::Unresolved)
        ));
    }

    fn original() -> ril_syntax::ast::Program {
        ril_syntax::parse(ril_test::case_source(
            "tests/regressions/copy.ril::binary-recursive-copy",
        ))
        .program
    }
    fn key() -> ArgumentKey {
        ArgumentKey::Name {
            name: "Node".into(),
            arguments: vec![],
        }
    }

    #[test]
    fn complete_declaration_schemas_keep_recursive_graphs_and_original_annotations() {
        let hir = HirProgram::lower(&original()).unwrap();
        let input =
            SourceSchema::import(&key(), Some(TypeExprId(37)), &mut WorkLimit::new(4096)).unwrap();
        let selected = resolve_schema(&input, &hir, &mut WorkLimit::new(4096)).unwrap();
        let direct = schema(&key(), &hir, &mut WorkLimit::new(4096)).unwrap();
        assert_eq!(selected.original(), input.original());
        assert_eq!(
            selected.equivalent(&direct, &mut WorkLimit::new(4096)),
            Ok(true)
        );
        let member = selected
            .project_steps(
                &[
                    super::super::SourcePath::Field("left".into()),
                    super::super::SourcePath::OptionalPayload,
                    super::super::SourcePath::Field("value".into()),
                ],
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        assert_eq!(
            member.equivalent_key(
                &ArgumentKey::Name {
                    name: "int".into(),
                    arguments: vec![]
                },
                &mut WorkLimit::new(4096)
            ),
            Ok(true)
        );
        assert!(matches!(
            resolve_schema(&input, &hir, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn typed_extent_ingress_requests_static_elaboration_without_waiving_unknown_or_budget_errors() {
        let source = ril_test::case_source(
            "tests/regressions/source-observations.ril::matching-record-member-replacement",
        );
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok());
        let hir = HirProgram::lower(&parsed.program).unwrap();
        let typed_literal = |hir: &HirProgram| {
            let mut literal = None;
            hir.walk(4096, |id, _| {
                if let hir::NodeId::Expr(id) = id
                    && matches!(
                        &hir.expression(id).unwrap().kind,
                        hir::ExprKind::Record { ty: Some(_), .. }
                    )
                {
                    literal.get_or_insert(id);
                }
            })
            .unwrap();
            literal.unwrap()
        };
        // Query the actual typed construction, rather than recognizing a
        // description on an unresolved graph after the static context is lost.
        let literal = typed_literal(&hir);
        assert!(matches!(
            construction_graph(literal, &hir, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::NeedsStaticElaboration)
        ));
        assert!(
            construction_schema(literal, &hir, &mut WorkLimit::new(4096))
                .unwrap()
                .is_none()
        );
        assert!(
            construction(literal, &hir, &mut WorkLimit::new(4096))
                .unwrap()
                .is_none()
        );
        assert!(matches!(
            construction_schema(literal, &hir, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
        assert!(matches!(
            construction_schema(
                ril_compiler_core::ids::ExprId(u32::MAX),
                &hir,
                &mut WorkLimit::new(4096)
            ),
            Err(SourceTypesError::MissingNode)
        ));
        let mut unknown = parsed.program;
        let StmtKind::Type(declaration) = &mut unknown.statements[0].kind else {
            panic!()
        };
        let TypeKind::Record { fields, .. } = &mut declaration.value.as_mut().unwrap().kind else {
            panic!()
        };
        fields[0].ty.kind = TypeKind::Name {
            path: vec!["Missing".into()],
            arguments: vec![],
        };
        let hir = HirProgram::lower(&unknown).unwrap();
        assert!(matches!(
            construction_schema(typed_literal(&hir), &hir, &mut WorkLimit::new(4096)),
            Err(SourceTypesError::Unresolved)
        ));
    }

    #[test]
    fn real_recursive_declarations_project_without_an_erased_type_or_tree_unrolling() {
        let hir = HirProgram::lower(&original()).unwrap();
        let mut literal = None;
        hir.walk(4096, |id, _| {
            if let hir::NodeId::Expr(id) = id
                && matches!(
                    &hir.expression(id).unwrap().kind,
                    hir::ExprKind::Record { ty: Some(_), .. }
                )
            {
                literal.get_or_insert(id);
            }
        })
        .unwrap();
        assert_eq!(
            construction(literal.unwrap(), &hir, &mut WorkLimit::new(4096)).unwrap(),
            Some(key())
        );
        assert!(matches!(
            schema(&key(), &hir, &mut WorkLimit::new(4096))
                .unwrap()
                .sensitivity(&mut WorkLimit::new(4096)),
            SourceSensitivity::Absent { .. }
        ));
        let source = schema(&key(), &hir, &mut WorkLimit::new(4096)).unwrap();
        let member = source
            .project_steps(
                &[
                    super::super::SourcePath::Field("left".into()),
                    super::super::SourcePath::OptionalPayload,
                ],
                &mut WorkLimit::new(4096),
            )
            .unwrap();
        assert!(
            member
                .equivalent(&source, &mut WorkLimit::new(4096))
                .unwrap()
        );
        assert!(matches!(
            schema(&key(), &hir, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn a_backedge_never_hides_later_dimensions_or_unknown_declarations() {
        let mut source = original();
        let StmtKind::Type(declaration) = &mut source.statements[0].kind else {
            panic!("source declaration")
        };
        let span = declaration.span;
        let TypeKind::Record { fields, .. } = &mut declaration.value.as_mut().unwrap().kind else {
            panic!("record declaration")
        };
        fields.push(TypeField {
            name: "after_backedge".into(),
            mutable: false,
            span,
            ty: TypeExpr {
                hir_id: None,
                text: String::new(),
                span,
                kind: TypeKind::Array {
                    length: None,
                    element: Box::new(TypeExpr {
                        hir_id: None,
                        text: String::new(),
                        span,
                        kind: TypeKind::Name {
                            path: vec!["int".into()],
                            arguments: vec![],
                        },
                    }),
                },
            },
        });
        let hir = HirProgram::lower(&source).unwrap();
        assert!(matches!(
            schema(&key(), &hir, &mut WorkLimit::new(4096))
                .unwrap()
                .sensitivity(&mut WorkLimit::new(4096)),
            SourceSensitivity::Sensitive { .. }
        ));
        for target in ["Node", "Missing"] {
            let mut source = original();
            let StmtKind::Type(declaration) = &mut source.statements[0].kind else {
                unreachable!()
            };
            declaration.value.as_mut().unwrap().kind = TypeKind::Name {
                path: vec![target.into()],
                arguments: vec![],
            };
            let hir = HirProgram::lower(&source).unwrap();
            assert!(matches!(
                schema(&key(), &hir, &mut WorkLimit::new(4096))
                    .unwrap()
                    .sensitivity(&mut WorkLimit::new(4096)),
                SourceSensitivity::Unknown { .. }
            ));
        }
    }

    #[test]
    fn legacy_names_cannot_borrow_global_evidence_across_a_local_shadow() {
        let mut source = original();
        let local = source.statements[0].clone();
        let StmtKind::Function(function) = &mut source.statements[1].kind else {
            panic!("original callable")
        };
        function.body.as_mut().unwrap().where_items.push(local);
        let hir = HirProgram::lower(&source).unwrap();
        assert!(matches!(
            schema(&key(), &hir, &mut WorkLimit::new(4096))
                .unwrap()
                .sensitivity(&mut WorkLimit::new(4096)),
            SourceSensitivity::Unknown { .. }
        ));
    }
}
