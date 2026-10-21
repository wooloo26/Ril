//! Resolve transparent global declarations into finite source graphs. Only
//! original HIR declaration edges can turn an opaque name into structural
//! evidence. Generic, opaque and captured interpretations stay unresolved.
use super::{LegacySourceExport, SourceSensitivity, SourceTypeQueries, graph::*, legacy};
use crate::hir::nodes::{self as hir, HirProgram};
use crate::sema::effect_identity::ArgumentKey;
use ril_compiler_core::ids::{StmtId, TypeExprId};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy)]
struct Alias {
    declaration: StmtId,
    value: TypeExprId,
}

struct Resolve<'a> {
    hir: &'a HirProgram,
    aliases: BTreeMap<String, Option<Alias>>,
    definitions: BTreeMap<StmtId, SourceTypeId>,
    syntax: BTreeMap<TypeExprId, SourceTypeId>,
    copied: BTreeMap<SourceTypeId, SourceTypeId>,
    builder: SourceBuilder,
}

pub(crate) fn sensitivity(
    key: &ArgumentKey,
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> SourceSensitivity {
    let result = resolve(key, hir, work).map(|graph| graph.types.sensitivity(graph.root, work));
    result.unwrap_or_else(|reason| SourceSensitivity::Unknown { reason })
}

struct DeclaredGraph {
    types: SourceTypes,
    root: SourceTypeId,
    declarations: BTreeSet<SourceTypeId>,
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
    work.charge(1)?;
    let Some(hir::Expr {
        kind: hir::ExprKind::Record { ty: Some(ty), .. },
        ..
    }) = hir.expression(source)
    else {
        return Ok(None);
    };
    let mut resolver = Resolve::new(hir, work)?;
    let root = resolver.ty(*ty, work, 0)?;
    let graph = resolver.freeze(root, work)?;
    if !matches!(
        graph.types.sensitivity(root, work),
        SourceSensitivity::Absent { .. }
    ) {
        return Ok(None);
    }
    graph
        .types
        .declared_key(root, &graph.declarations, work)
        .map(Some)
}

/// Projection uses the same graph as receiving. Backedges export only real
/// HIR declaration names; an arbitrary recursive graph cannot invent a name.
pub(crate) fn project(
    key: &ArgumentKey,
    path: &[crate::sema::facts::Slot],
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<ArgumentKey, SourceTypesError> {
    let path = super::index::steps_in(path, work)?;
    project_steps(key, &path, hir, work)
}

pub(crate) fn project_steps(
    key: &ArgumentKey,
    path: &[super::SourcePath],
    hir: &HirProgram,
    work: &mut WorkLimit,
) -> Result<ArgumentKey, SourceTypesError> {
    let graph = resolve(key, hir, work)?;
    let selected = graph.types.project(graph.root, path, work)?;
    graph
        .types
        .declared_key(selected, &graph.declarations, work)
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
        if let Some(&id) = self.definitions.get(&alias.declaration) {
            return Ok(Some(id));
        }
        work.text(name)?;
        let id = self.builder.reserve(work)?;
        self.definitions.insert(alias.declaration, id);
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
        if let Some(&output) = self.syntax.get(&id) {
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
                let arguments = arguments
                    .iter()
                    .map(|id| self.ty(*id, work, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                if arguments.is_empty() {
                    if let Some(scalar) = legacy::scalar(&name) {
                        return self.remember(id, SourceNode::Scalar(scalar), work);
                    }
                    if let Some(output) = self.alias(&name, work, depth + 1)? {
                        self.syntax.insert(id, output);
                        return Ok(output);
                    }
                }
                if let Some(kind) = legacy::container(&name) {
                    SourceNode::Container { kind, arguments }
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
                // The declaration graph cannot borrow a caller's constant
                // evaluator. Absence cannot be proved through this node.
                return self.unknown(
                    "fixed extent requires its frozen static interpretation",
                    work,
                );
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
            _ => return self.unknown("declaration requires a frozen type computation", work),
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
        self.syntax.insert(syntax, id);
        Ok(id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ril_syntax::ast::{StmtKind, TypeExpr, TypeField, TypeKind};

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
            sensitivity(&key(), &hir, &mut WorkLimit::new(4096)),
            SourceSensitivity::Absent { .. }
        ));
        let member = project(
            &key(),
            &[crate::sema::facts::Slot::Field("left".into())],
            &hir,
            &mut WorkLimit::new(4096),
        )
        .unwrap();
        assert!(
            matches!(member, ArgumentKey::Name { name, arguments } if name == "Option" && arguments == vec![key()])
        );
        assert!(matches!(
            sensitivity(&key(), &hir, &mut WorkLimit::new(0)),
            SourceSensitivity::Unknown {
                reason: SourceTypesError::BudgetExceeded
            }
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
            sensitivity(&key(), &hir, &mut WorkLimit::new(4096)),
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
                sensitivity(&key(), &hir, &mut WorkLimit::new(4096)),
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
            sensitivity(&key(), &hir, &mut WorkLimit::new(4096)),
            SourceSensitivity::Unknown { .. }
        ));
    }
}
