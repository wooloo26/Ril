//! Replay structural generic evidence from declarations and frozen observations.
//! No successful row equation creates a value, permission or resource proof.
use super::{
    SemanticFacts,
    copy_contract::{CopyInvocationStatus, CopyValueSnapshot},
    effect_identity::{ArgumentKey, StaticBinderSort},
    facts::{Publication, Slot},
    model::{
        FunctionInfo, Ty, Value,
        rows::{OpenTail, Row, RowIdentity, RowTail, Solver},
    },
    record_bounds::*,
};
use crate::hir::application::AstApplication;
use ril_compiler_core::{
    diagnostic::CauseId,
    ids::{CallableOwner, DefinitionId},
    source::Span,
};
use ril_syntax::ast::{
    Expr, ExprKind, Literal, Stmt, StmtKind, StringPart, TypeDeclaration, TypeExpr, TypeKind,
    Visibility,
};
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
mod call_input_source;
mod default_source_receiving;
mod dependencies;
mod explicit_named;
mod observation_index;
mod rigid;
mod scoped_identity;
mod scoped_members;
mod storage_sources;
mod writes;

type Failure = (Span, Option<CauseId>, String);
type Check<T = ()> = Result<T, String>;

pub(crate) fn validate_callable_inputs(facts: &SemanticFacts) -> Result<(), String> {
    if facts.closure_invocations.is_empty() && facts.copy_invocations.is_empty() {
        return Ok(());
    }
    Replay::new(facts)?.callable_inputs()
}

pub(crate) fn validate_storage_sources(facts: &SemanticFacts) -> Result<(), Failure> {
    let fallback = facts
        .source_program
        .as_ref()
        .and_then(|program| program.statements.first())
        .map(|statement| statement.span)
        .unwrap_or(Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        });
    let replay = Replay::new(facts).map_err(|message| (fallback, None, message))?;
    replay.storage_sources()
}

/// Original source only. Generated-source validation uses this entry point so
/// a proposed generated body cannot supply its own creation or call anchor.
pub(crate) fn ordinary_source_coordinates(
    facts: &SemanticFacts,
) -> Result<Vec<(CallableOwner, &Expr)>, String> {
    Ok(explicit_named::source_sites_base(facts)?
        .calls
        .into_iter()
        .map(|site| (site.owner, site.expression))
        .collect())
}

pub(crate) use call_input_source::OriginalOperandSources;

pub(crate) fn ordinary_lambda_coordinates(
    facts: &SemanticFacts,
) -> Result<Vec<(CallableOwner, &Expr)>, String> {
    Ok(explicit_named::source_sites_base(facts)?
        .lambdas
        .into_iter()
        .map(|site| (site.owner, site.expression))
        .collect())
}

const LIMIT: usize = 65_536;

struct Replay<'a> {
    facts: &'a SemanticFacts,
    observations: observation_index::ObservationIndex<'a>,
    blocks: Option<crate::hir::blocks::BlockIndex>,
    functions: BTreeMap<DefinitionId, &'a FunctionInfo>,
    bounds: BTreeMap<(DefinitionId, u32), &'a GenericRecordBound>,
}

fn require(condition: bool, description: &str) -> Check {
    condition
        .then_some(())
        .ok_or_else(|| description.to_owned())
}

impl<'a> Replay<'a> {
    fn new(facts: &'a SemanticFacts) -> Check<Self> {
        crate::sema::evaluation_identity::validate(facts)
            .map_err(|(_, _, message)| format!("application evaluation structure: {message}"))?;
        let observations = observation_index::ObservationIndex::new(facts)?;
        let blocks = facts
            .semantic_hir
            .as_deref()
            .map(crate::hir::blocks::BlockIndex::new)
            .transpose()
            .map_err(|error| format!("original block index: {error}"))?;
        require(
            facts.functions.len() <= LIMIT
                && facts.record_bounds.len() <= LIMIT
                && facts.bound_rows.len() <= LIMIT
                && facts.generic_bound_checks.len() <= LIMIT
                && facts.generic_bound_projections.len() <= LIMIT,
            "record-bound replay resource budget exhausted",
        )?;
        // Bound admission precedes recursive syntax equality or owned copies.
        // The source walk itself is iterative and has its own finite budget.
        projection_sites(facts)?;
        for function in &facts.functions {
            for syntax in function
                .syntax
                .generics
                .iter()
                .flat_map(|parameter| parameter.bound.iter().chain(&parameter.default))
                .chain(
                    function
                        .syntax
                        .parameters
                        .iter()
                        .filter_map(|parameter| parameter.ty.as_ref()),
                )
                .chain(function.syntax.return_type.iter())
            {
                require(
                    crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())
                        .is_some(),
                    "record declaration syntax exceeds independent replay admission",
                )?;
            }
        }
        let mut functions: BTreeMap<_, &FunctionInfo> = BTreeMap::new();
        for function in &facts.functions {
            if let Some(previous) = functions.insert(function.definition, function) {
                require(
                    previous.syntax.name == function.syntax.name
                        && previous.syntax.span == function.syntax.span
                        && previous.syntax.generics == function.syntax.generics
                        && previous.syntax.parameters.len() == function.syntax.parameters.len()
                        && previous
                            .syntax
                            .parameters
                            .iter()
                            .zip(&function.syntax.parameters)
                            .all(|(left, right)| left.mode == right.mode && left.ty == right.ty)
                        && previous.syntax.return_type == function.syntax.return_type
                        && previous.lexical_owner == function.lexical_owner
                        && previous.typing_environment.generic_context
                            == function.typing_environment.generic_context,
                    "one named declaration has inconsistent frozen lexical headers",
                )?;
            }
        }
        let mut bounds = BTreeMap::new();
        for (index, bound) in facts.record_bounds.iter().enumerate() {
            require(
                bound.id.0 as usize == index
                    && bounds
                        .insert((bound.definition, bound.generic_index), bound)
                        .is_none(),
                "record-bound registry has duplicate or misplaced declaration identities",
            )?;
        }
        Ok(Self {
            facts,
            observations,
            blocks,
            functions,
            bounds,
        })
    }

    fn function(&self, definition: DefinitionId) -> Check<&'a FunctionInfo> {
        self.functions
            .get(&definition)
            .copied()
            .ok_or_else(|| "record-bound owner is not a registered function".to_owned())
    }

    fn binder(&self, definition: DefinitionId, index: u32) -> Check<&'a super::GenericBinder> {
        let function = self.function(definition)?;
        let parameter = function
            .syntax
            .generics
            .get(index as usize)
            .ok_or_else(|| {
                "record-bound generic index is outside its source declaration".to_owned()
            })?;
        let mut matching = self
            .facts
            .generic_binders
            .iter()
            .filter(|(_, binder)| binder.definition == definition && binder.index == index);
        let (identity, binder) = matching
            .next()
            .ok_or_else(|| "record-bound generic has no genuine binder record".to_owned())?;
        require(
            matching.next().is_none()
                && &binder.identity == identity
                && binder.name == parameter.name,
            "record-bound generic identity disagrees with its owner and source index",
        )?;
        Ok(binder)
    }

    fn type_binder(&self, identity: &str) -> Check {
        let binder = self
            .facts
            .generic_binders
            .get(identity)
            .ok_or_else(|| "record field depends on an unregistered type binder".to_owned())?;
        let verified = self.binder(binder.definition, binder.index)?;
        let parameter = &self.function(binder.definition)?.syntax.generics[binder.index as usize];
        require(verified.identity == identity
            && parameter.name.chars().next().is_some_and(char::is_uppercase)
            && parameter.bound.as_ref().is_none_or(|bound|
                matches!(&bound.kind, TypeKind::Name {path,arguments} if path==&["Type"] && arguments.is_empty())
                || matches!(bound.kind, TypeKind::Record {..})),
            "a static coordinate or unknown sort cannot impersonate a Type binder")
    }

    fn owner_chain(&self, definition: DefinitionId) -> Check<Vec<DefinitionId>> {
        let mut result = vec![definition];
        let mut owners = BTreeSet::new();
        let mut current = self.function(definition)?.lexical_owner;
        while let Some(owner) = current {
            require(
                owners.len() < 256 && owners.insert(owner),
                "record-bound lexical owner graph is cyclic or too deep",
            )?;
            current = match owner {
                CallableOwner::Global => None,
                CallableOwner::Function(owner) => {
                    require(
                        !result.contains(&owner),
                        "record-bound named lexical ancestry is cyclic",
                    )?;
                    result.push(owner);
                    self.function(owner)?.lexical_owner
                }
                CallableOwner::Lambda(site) => Some(
                    self.facts
                        .closure_sites
                        .iter()
                        .find(|entry| entry.id == site)
                        .ok_or_else(|| {
                            "record-bound lexical lambda owner is unavailable".to_owned()
                        })?
                        .owner,
                ),
            };
        }
        result.reverse();
        Ok(result)
    }

    fn scope(&self, definition: DefinitionId) -> Check<BoundScope> {
        let mut types = BTreeMap::new();
        let mut rows = BTreeMap::new();
        for owner in self.owner_chain(definition)? {
            let function = self.function(owner)?;
            require(
                function.typing_environment.generic_context == types
                    && function.typing_environment.bound_row_context == rows,
                "captured structural scope does not match the nearest source lexical binders and residuals",
            )?;
            self.install_scope(owner, &mut types, &mut rows)?;
        }
        Ok(BoundScope { types, rows })
    }

    fn install_scope(
        &self,
        definition: DefinitionId,
        types: &mut BTreeMap<String, String>,
        rows: &mut BTreeMap<String, BoundRowId>,
    ) -> Check {
        let function = self.function(definition)?;
        for (index, parameter) in function.syntax.generics.iter().enumerate() {
            types.insert(
                parameter.name.clone(),
                self.binder(definition, index as u32)?.identity.clone(),
            );
            rows.remove(&parameter.name);
        }
        for parameter in &function.syntax.generics {
            let Some(TypeExpr {
                kind: TypeKind::Record {
                    row: Some(tail), ..
                },
                ..
            }) = &parameter.bound
            else {
                continue;
            };
            let TypeKind::Name { path, arguments } = &tail.kind else {
                continue;
            };
            if path.len() != 1 || !arguments.is_empty() {
                continue;
            }
            let name = &path[0];
            if self.facts.external_type_declarations.contains_key(name) && !types.contains_key(name)
            {
                continue;
            }
            let expected_role = if let Some(binder) = types.get(name) {
                self.type_binder(binder)?;
                BoundRowRole::DeclaredTypeParameter {
                    binder: binder.clone(),
                }
            } else {
                BoundRowRole::ImplicitResidual
            };
            let existing = rows
                .get(name)
                .copied()
                .filter(|id| self.row(*id).is_ok_and(|row| row.role == expected_role));
            if existing.is_none() {
                let candidates: Vec<_> = self
                    .facts
                    .bound_rows
                    .iter()
                    .filter(|row| {
                        row.definition == definition
                            && &row.name == name
                            && row.role == expected_role
                    })
                    .collect();
                require(
                    candidates.len() == 1,
                    "source residual has no unique declaration record",
                )?;
                rows.insert(name.clone(), candidates[0].id);
            }
        }
        Ok(())
    }

    fn row(&self, id: BoundRowId) -> Check<&'a BoundRowDeclaration> {
        self.facts
            .bound_rows
            .get(id.0 as usize)
            .filter(|row| row.id == id)
            .ok_or_else(|| "record-bound residual ID is not a registry member".to_owned())
    }

    fn key_scope(&self, scope: &BoundScope) -> Check<BTreeMap<String, String>> {
        let mut binders = scope.types.clone();
        for (name, id) in &scope.rows {
            let row = self.row(*id)?;
            let RowIdentity::Binder(identity) = &row.identity else {
                return Err("a declaration residual is not a rigid identity".into());
            };
            if let Some(existing) = binders.get(name) {
                require(
                    matches!(&row.role,BoundRowRole::DeclaredTypeParameter {binder} if binder==existing && binder==identity),
                    "implicit residual and declared Type namespaces were conflated",
                )?;
            } else {
                binders.insert(name.clone(), identity.clone());
            }
        }
        Ok(binders)
    }

    fn normalized_key(&self, syntax: &TypeExpr, scope: &BoundScope) -> Check<ArgumentKey> {
        let binders = self.key_scope(scope)?;
        crate::static_eval::effects::bounded_argument_key(syntax, &binders)
            .ok_or_else(|| "record field syntax exceeds the independent work budget".to_owned())?;
        if self.closed_dependencies(syntax, &binders).is_ok() {
            let normalized = self.closed_alias(syntax)?;
            return self.normalize(&normalized, &binders, 0, &mut 4096);
        }
        self.normalize(syntax, &binders, 0, &mut 4096)
    }

    fn normalize(
        &self,
        syntax: &TypeExpr,
        binders: &BTreeMap<String, String>,
        depth: usize,
        work: &mut usize,
    ) -> Check<ArgumentKey> {
        require(
            depth < 64 && *work > 0,
            "record field identity normalization budget exhausted",
        )?;
        *work -= 1;
        let mut child = |syntax: &TypeExpr| self.normalize(syntax, binders, depth + 1, work);
        Ok(match &syntax.kind {
            TypeKind::Name { path, arguments }
                if arguments.is_empty() && binders.contains_key(&path.join("::")) =>
            {
                let identity = &binders[&path.join("::")];
                if self.facts.generic_binders.contains_key(identity) {
                    self.type_binder(identity)?;
                }
                ArgumentKey::Binder {
                    identity: identity.clone(),
                    sort: StaticBinderSort::Type,
                }
            }
            TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                if arguments.is_empty() && super::checker::is_known_builtin_source_type(&name) {
                    let normalized = self.closed_alias(syntax)?;
                    if normalized.kind != syntax.kind {
                        return self.normalize(&normalized, binders, depth + 1, work);
                    }
                }
                if let Some(declaration) = self.facts.external_type_declarations.get(&name)
                    && !declaration.nominal
                    && !declaration.opaque
                    && declaration.variants.is_empty()
                {
                    self.closed_dependencies(syntax, binders)?;
                    let normalized = self.closed_alias(syntax)?;
                    require(
                        normalized.kind != syntax.kind,
                        "transparent alias did not normalize to an independently known type",
                    )?;
                    return self.normalize(&normalized, binders, depth + 1, work);
                }
                let named = name.strip_prefix("Prelude::").unwrap_or(&name).to_owned();
                let primitive = matches!(
                    named.as_str(),
                    "bool"
                        | "int"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                        | "u8"
                        | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                        | "bigint"
                        | "f32"
                        | "f64"
                        | "str"
                        | "bytes"
                        | "never"
                );
                let container = matches!(
                    named.as_str(),
                    "Immut" | "Option" | "Result" | "Set" | "Range" | "Heap::Heap" | "Deque::Deque"
                );
                let known = primitive
                    || container
                    || self
                        .facts
                        .external_type_declarations
                        .get(&name)
                        .is_some_and(|declaration| {
                            declaration.nominal
                                || declaration.opaque
                                || !declaration.variants.is_empty()
                        })
                    || (arguments.is_empty()
                        && super::checker::is_known_builtin_source_type(&name));
                require(known, "record field contains an unresolved type name")?;
                require(
                    !primitive || arguments.is_empty(),
                    "primitive field type has unexpected arguments",
                )?;
                ArgumentKey::Name {
                    name: named,
                    arguments: arguments.iter().map(&mut child).collect::<Check<_>>()?,
                }
            }
            TypeKind::Optional(inner) => ArgumentKey::Name {
                name: "Option".into(),
                arguments: vec![child(inner)?],
            },
            TypeKind::Array { element, length } => {
                let length = if length.is_some() {
                    let mut shell = syntax.clone();
                    if let TypeKind::Array { element, .. } = &mut shell.kind {
                        **element = TypeExpr {
                            hir_id: None,
                            text: String::new(),
                            span: syntax.span,
                            kind: TypeKind::Tuple(vec![]),
                        };
                    }
                    let shell = self.closed_alias(&shell)?;
                    let Some(ArgumentKey::Array {
                        length: Some(length),
                        ..
                    }) =
                        crate::static_eval::effects::bounded_argument_key(&shell, &BTreeMap::new())
                    else {
                        return Err("fixed field dimension has no frozen normalized integer".into());
                    };
                    Some(length)
                } else {
                    None
                };
                ArgumentKey::Array {
                    length,
                    element: Box::new(child(element)?),
                }
            }
            TypeKind::Map { key, value } => ArgumentKey::Map {
                key: Box::new(child(key)?),
                value: Box::new(child(value)?),
            },
            TypeKind::Tuple(items) => {
                ArgumentKey::Tuple(items.iter().map(&mut child).collect::<Check<_>>()?)
            }
            TypeKind::Record { fields, row } => {
                let mut result = fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), field.mutable, child(&field.ty)?)))
                    .collect::<Check<Vec<_>>>()?;
                result.sort_by(|a, b| a.0.cmp(&b.0));
                require(
                    result.windows(2).all(|pair| pair[0].0 != pair[1].0),
                    "record field type repeats a label",
                )?;
                ArgumentKey::Record {
                    fields: result,
                    row: row
                        .as_ref()
                        .map(|row| child(row).map(Box::new))
                        .transpose()?,
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                require(
                    parameters
                        .iter()
                        .all(|parameter| parameter.default.is_none())
                        && annotations.iter().all(|annotation| {
                            matches!(
                                annotation.text.replace(' ', "").as_str(),
                                "&mut" | "&^mut" | "&closure" | "&capture" | "@{}" | "&{}"
                            )
                        }),
                    "callable record field needs frozen lexical bounds or default-interface evidence",
                )?;
                ArgumentKey::Callable {
                    parameters: parameters
                        .iter()
                        .map(|parameter| {
                            Ok((
                                parameter.mode,
                                child(parameter.ty.as_ref().ok_or_else(|| {
                                    "record callable parameter has no type".to_owned()
                                })?)?,
                            ))
                        })
                        .collect::<Check<_>>()?,
                    result: Box::new(
                        result
                            .as_ref()
                            .map(|result| child(result))
                            .transpose()?
                            .unwrap_or(ArgumentKey::Tuple(vec![])),
                    ),
                    annotations: annotations
                        .iter()
                        .map(|annotation| annotation.text.replace(' ', ""))
                        .collect(),
                }
            }
            _ => return Err("record field identity has unsupported symbolic syntax".into()),
        })
    }

    fn closed_alias(&self, syntax: &TypeExpr) -> Check<TypeExpr> {
        crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())
            .ok_or_else(|| "record alias syntax exceeds the independent work budget".to_owned())?;
        let layout = self
            .facts
            .target_layout
            .ok_or_else(|| "record alias normalization has no frozen target layout".to_owned())?;
        if let Some(normalized) = super::checker::normalize_closed_source_syntax(
            syntax,
            &self.facts.external_type_declarations,
            layout,
        ) {
            return Ok(normalized);
        }
        let name = "\0record-bound-validation".to_owned();
        let declaration = TypeDeclaration {
            visibility: Visibility::Private,
            is_halt: false,
            name: name.clone(),
            generics: vec![],
            value: Some(syntax.clone()),
            variants: vec![],
            opaque: false,
            nominal: true,
            span: syntax.span,
        };
        crate::static_eval::normalize_constructor_arguments(
            &declaration,
            &[],
            &self.facts.external_type_declarations,
            layout,
        )
        .ok()
        .and_then(|normalized| normalized.payloads.get(&name).cloned().flatten())
        .and_then(|normalized| {
            super::checker::normalize_closed_source_syntax(
                &normalized,
                &self.facts.external_type_declarations,
                layout,
            )
        })
        .ok_or_else(|| "record alias needs unavailable symbolic normalization evidence".to_owned())
    }

    fn closed_dependencies(&self, syntax: &TypeExpr, binders: &BTreeMap<String, String>) -> Check {
        let mut pending = crate::static_eval::effects::type_dependencies(syntax);
        let mut seen = BTreeSet::new();
        while let Some(name) = pending.pop_first() {
            if !seen.insert(name.clone()) {
                continue;
            }
            require(
                seen.len() < 4096,
                "record alias dependency walk exceeds replay budget",
            )?;
            require(
                !binders.contains_key(&name),
                "symbolic alias field needs its frozen lexical normalization proof",
            )?;
            if let Some(declaration) = self.facts.external_type_declarations.get(&name) {
                let mut names = BTreeSet::new();
                if let Some(syntax) = &declaration.value {
                    crate::static_eval::effects::bounded_argument_key(syntax, &BTreeMap::new())
                        .ok_or_else(|| {
                            "record alias declaration exceeds replay admission".to_owned()
                        })?;
                    names.extend(crate::static_eval::effects::type_dependencies(syntax));
                }
                for parameter in &declaration.generics {
                    names.remove(&parameter.name);
                }
                pending.extend(names);
            }
        }
        Ok(())
    }
}

impl Replay<'_> {
    fn declared_type_paths(
        &self,
        definition: DefinitionId,
        binder: &str,
    ) -> Check<Vec<(usize, Vec<BoundTypeSelectionStep>)>> {
        fn walk(
            syntax: &TypeExpr,
            scope: &BoundScope,
            binder: &str,
            path: &mut Vec<BoundTypeSelectionStep>,
            output: &mut Vec<Vec<BoundTypeSelectionStep>>,
            depth: usize,
            work: &mut usize,
        ) -> Check {
            require(
                depth < 64 && *work > 0,
                "nested structural declaration path exceeds replay budget",
            )?;
            *work -= 1;
            match &syntax.kind {
                TypeKind::Name {
                    path: names,
                    arguments,
                } if arguments.is_empty()
                    && scope
                        .types
                        .get(&names.join("::"))
                        .is_some_and(|identity| identity == binder) =>
                {
                    output.push(path.clone())
                }
                TypeKind::Tuple(items) => {
                    for (index, item) in items.iter().enumerate() {
                        path.push(BoundTypeSelectionStep::Tuple(
                            u32::try_from(index)
                                .map_err(|_| "tuple type path index is too large")?,
                        ));
                        walk(item, scope, binder, path, output, depth + 1, work)?;
                        path.pop();
                    }
                }
                TypeKind::Record { fields, .. } => {
                    let mut sorted: Vec<_> = fields.iter().collect();
                    sorted.sort_by(|a, b| a.name.cmp(&b.name));
                    require(
                        sorted
                            .windows(2)
                            .all(|items| items[0].name != items[1].name),
                        "nested structural type repeats a field label",
                    )?;
                    for field in sorted {
                        path.push(BoundTypeSelectionStep::Field(field.name.clone()));
                        walk(&field.ty, scope, binder, path, output, depth + 1, work)?;
                        path.pop();
                    }
                }
                _ => {}
            }
            Ok(())
        }
        let scope = self.scope(definition)?;
        let mut result = Vec::new();
        let mut work = 4096;
        for (index, parameter) in self
            .function(definition)?
            .syntax
            .parameters
            .iter()
            .enumerate()
        {
            if let Some(syntax) = &parameter.ty {
                let mut paths = Vec::new();
                walk(
                    syntax,
                    &scope,
                    binder,
                    &mut Vec::new(),
                    &mut paths,
                    0,
                    &mut work,
                )?;
                result.extend(paths.into_iter().map(|path| (index, path)));
            }
        }
        Ok(result)
    }

    fn selected_value<'a>(
        &self,
        snapshot: &'a CopyValueSnapshot,
        path: &[BoundTypeSelectionStep],
    ) -> Check<&'a Value> {
        require(
            path.len() < 64,
            "nested structural selection exceeds replay depth",
        )?;
        let mut selected = &snapshot.value;
        for step in path {
            let slot = match step {
                BoundTypeSelectionStep::Tuple(index) => {
                    require(matches!(&selected.ty, Ty::Tuple(items) if (*index as usize) < items.len()),
                        "structural tuple path does not belong to its actual product type")?;
                    Slot::Tuple(*index)
                },
                BoundTypeSelectionStep::Field(name) => {
                    require(matches!(&selected.ty, Ty::Record(fields) | Ty::OpenRecord { fields, .. } if fields.contains_key(name)),
                        "structural field path does not belong to its actual product type")?;
                    Slot::Field(name.clone())
                },
                _ => return Err("structural selection needs a separate complete collection or type-only path proof".into()),
            };
            require(
                selected.origins.nodes.len() == 1,
                "nested structural selection needs its exact parent object",
            )?;
            let origin = *selected.origins.nodes.first().unwrap();
            selected = snapshot
                .nodes
                .iter()
                .find(|node| node.origin == origin)
                .and_then(|node| node.fields.iter().find(|(stored, _)| stored == &slot))
                .map(|(_, child)| child)
                .ok_or_else(|| {
                    "nested structural selection manufactured a missing stored edge".to_owned()
                })?;
        }
        Ok(selected)
    }

    fn declarations(&self) -> Result<(), (Span, String)> {
        for (&definition, function) in &self.functions {
            for (index, parameter) in function.syntax.generics.iter().enumerate() {
                let Some(
                    source @ TypeExpr {
                        kind: TypeKind::Record { fields, row },
                        ..
                    },
                ) = &parameter.bound
                else {
                    continue;
                };
                let verify = || -> Check {
                    let bound = self
                        .bounds
                        .get(&(definition, index as u32))
                        .ok_or_else(|| {
                            "source record constraint has no independent declaration coverage"
                                .to_owned()
                        })?;
                    let binder = self.binder(definition, index as u32)?;
                    self.type_binder(&binder.identity)?;
                    let scope = self.scope(definition)?;
                    require(
                        bound.binder == binder.identity && bound.scope == scope,
                        "record constraint borrows a different binder or lexical scope",
                    )?;
                    require(
                        self.normalized_key(&bound.syntax, &scope)?
                            == self.normalized_key(source, &scope)?,
                        "record constraint differs from the owning source bound",
                    )?;
                    require(
                        bound.fields.len() == fields.len(),
                        "record constraint lost or invented guaranteed fields",
                    )?;
                    let mut labels = BTreeSet::new();
                    for field in &bound.fields {
                        require(
                            labels.insert(&field.label),
                            "record constraint repeats a guaranteed label",
                        )?;
                        let declared = fields
                            .iter()
                            .find(|declared| declared.name == field.label)
                            .ok_or_else(|| {
                                "record constraint invented a guaranteed label".to_owned()
                            })?;
                        require(
                            field.mutable == declared.mutable
                                && field.key == self.normalized_key(&declared.ty, &scope)?
                                && field.key == self.normalized_key(&field.syntax, &scope)?,
                            "record field mode or complete identity differs from its declaration",
                        )?;
                        self.field_type(field, &scope)?;
                    }
                    match (&bound.tail, row) {
                        (DeclaredBoundTail::Closed, None) => {}
                        (DeclaredBoundTail::Row(id), Some(tail)) => {
                            let TypeKind::Name { path, arguments } = &tail.kind else {
                                return Err(
                                    "record constraint residual has no direct declaration path"
                                        .into(),
                                );
                            };
                            require(
                                path.len() == 1
                                    && arguments.is_empty()
                                    && scope.rows.get(&path[0]) == Some(id),
                                "record constraint residual refers to a different row declaration",
                            )?;
                        }
                        (DeclaredBoundTail::Concrete { .. }, _) => {
                            return Err(
                                "concrete record-bound tails need their independent row equation"
                                    .into(),
                            );
                        }
                        _ => {
                            return Err(
                                "record constraint closed or open tail differs from source".into(),
                            );
                        }
                    }
                    Ok(())
                };
                verify().map_err(|message| (source.span, message))?;
            }
        }
        for bound in &self.facts.record_bounds {
            let valid = self
                .function(bound.definition)
                .ok()
                .and_then(|function| function.syntax.generics.get(bound.generic_index as usize))
                .and_then(|parameter| parameter.bound.as_ref())
                .is_some_and(|bound| matches!(bound.kind, TypeKind::Record { .. }));
            if !valid {
                return Err((
                    bound.span,
                    "record constraint has no corresponding source declaration".into(),
                ));
            }
        }
        let mut identities = BTreeSet::new();
        let mut ordinals = BTreeSet::new();
        for (index, row) in self.facts.bound_rows.iter().enumerate() {
            let mut verify = || -> Check {
                require(
                    row.id.0 as usize == index
                        && identities.insert((row.definition, row.name.clone()))
                        && ordinals.insert((row.definition, row.ordinal)),
                    "residual declaration IDs, names or ordinals are duplicated",
                )?;
                let scope = self.scope(row.definition)?;
                require(
                    scope.rows.get(&row.name) == Some(&row.id),
                    "residual is not introduced by its source scope",
                )?;
                let mut paths = Vec::new();
                let mut lacks = BTreeSet::new();
                for bound in self
                    .facts
                    .record_bounds
                    .iter()
                    .filter(|bound| bound.definition == row.definition)
                {
                    if matches!(bound.tail,DeclaredBoundTail::Row(id) if id==row.id) {
                        paths.push(BoundDeclarationPath {
                            generic_index: bound.generic_index,
                            path: vec![BoundPathStep::Bound, BoundPathStep::RowTail],
                        });
                        let TypeKind::Record { fields, .. } =
                            &self.function(bound.definition)?.syntax.generics
                                [bound.generic_index as usize]
                                .bound
                                .as_ref()
                                .unwrap()
                                .kind
                        else {
                            unreachable!()
                        };
                        lacks.extend(fields.iter().map(|field| field.name.clone()));
                    }
                }
                require(
                    !paths.is_empty() && paths == row.declaration_paths && lacks == row.lacks,
                    "residual declaration paths or independently declared local absences differ",
                )?;
                match (&row.role, scope.types.get(&row.name)) {
                    (BoundRowRole::ImplicitResidual, None) => require(
                        row.identity
                            == RowIdentity::Binder(format!(
                                "function:{}:bound-row:{}",
                                row.definition.0, row.ordinal
                            )),
                        "implicit residual is not the stable declaration identity",
                    )?,
                    (BoundRowRole::DeclaredTypeParameter { binder }, Some(actual)) => {
                        self.type_binder(binder)?;
                        require(
                            binder == actual && row.identity == RowIdentity::Binder(binder.clone()),
                            "declared Type row does not retain its genuine binder identity",
                        )?;
                    }
                    _ => {
                        return Err(
                            "implicit residual was confused with a declared Type parameter".into(),
                        );
                    }
                }
                Ok(())
            };
            verify().map_err(|message| (row.span, message))?;
        }
        Ok(())
    }

    fn field_type(&self, field: &RecordBoundField, scope: &BoundScope) -> Check {
        self.ty_matches(&field.ty, &field.key, scope, 0)
    }

    fn ty_matches(&self, ty: &Ty, key: &ArgumentKey, scope: &BoundScope, depth: usize) -> Check {
        require(
            depth < 64,
            "record field semantic type exceeds replay depth",
        )?;
        let agrees = match (ty, key) {
            (Ty::Generic(actual), ArgumentKey::Binder { identity, .. }) => actual == identity,
            (Ty::Unit, ArgumentKey::Tuple(items)) => items.is_empty(),
            (Ty::Bool, ArgumentKey::Name { name, arguments }) => {
                name == "bool" && arguments.is_empty()
            }
            (Ty::Int(actual) | Ty::Float(actual), ArgumentKey::Name { name, arguments }) => {
                actual == name && arguments.is_empty()
            }
            (Ty::Str, ArgumentKey::Name { name, arguments }) => {
                name == "str" && arguments.is_empty()
            }
            (Ty::Bytes, ArgumentKey::Name { name, arguments }) => {
                name == "bytes" && arguments.is_empty()
            }
            (Ty::Never, ArgumentKey::Name { name, arguments }) => {
                name == "never" && arguments.is_empty()
            }
            (Ty::Named(actual), _) => {
                let syntax = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: self.function_scope_span(scope),
                    kind: TypeKind::Name {
                        path: actual.split("::").map(str::to_owned).collect(),
                        arguments: vec![],
                    },
                };
                let normalized = self.normalized_key(&syntax, scope)?;
                &normalized == key
            }
            (Ty::Array(inner), ArgumentKey::Array { element, .. }) => {
                self.ty_matches(inner, element, scope, depth + 1).is_ok()
            }
            (Ty::Immutable(inner), ArgumentKey::Name { name, arguments }) if name == "Immut" => {
                matches!(arguments.as_slice(),[key] if self.ty_matches(inner,key,scope,depth+1).is_ok())
            }
            (Ty::Optional(inner), ArgumentKey::Name { name, arguments }) if name == "Option" => {
                matches!(arguments.as_slice(),[key] if self.ty_matches(inner,key,scope,depth+1).is_ok())
            }
            (Ty::Set(inner), ArgumentKey::Name { name, arguments }) if name == "Set" => {
                matches!(arguments.as_slice(),[key] if self.ty_matches(inner,key,scope,depth+1).is_ok())
            }
            (Ty::Range(inner), ArgumentKey::Name { name, arguments }) if name == "Range" => {
                matches!(arguments.as_slice(),[key] if self.ty_matches(inner,key,scope,depth+1).is_ok())
            }
            (Ty::Result(ok, error), ArgumentKey::Name { name, arguments }) if name == "Result" => {
                matches!(arguments.as_slice(),[a,b] if self.ty_matches(ok,a,scope,depth+1).is_ok() && self.ty_matches(error,b,scope,depth+1).is_ok())
            }
            (Ty::Map(a, b), ArgumentKey::Map { key, value }) => {
                self.ty_matches(a, key, scope, depth + 1).is_ok()
                    && self.ty_matches(b, value, scope, depth + 1).is_ok()
            }
            (Ty::Tuple(items), ArgumentKey::Tuple(keys)) => {
                items.len() == keys.len()
                    && items
                        .iter()
                        .zip(keys)
                        .all(|(ty, key)| self.ty_matches(ty, key, scope, depth + 1).is_ok())
            }
            (
                Ty::Record(fields),
                ArgumentKey::Record {
                    fields: keys,
                    row: None,
                },
            ) => {
                fields.len() == keys.len()
                    && keys.iter().all(|(name, mutable, key)| {
                        fields.get(name).is_some_and(|(mode, ty)| {
                            mode == mutable && self.ty_matches(ty, key, scope, depth + 1).is_ok()
                        })
                    })
            }
            (
                Ty::Callable(parameters, result),
                ArgumentKey::Callable {
                    parameters: keys,
                    result: key,
                    ..
                },
            ) => {
                parameters.len() == keys.len()
                    && parameters
                        .iter()
                        .zip(keys)
                        .all(|(ty, (_, key))| self.ty_matches(ty, key, scope, depth + 1).is_ok())
                    && self.ty_matches(result, key, scope, depth + 1).is_ok()
            }
            _ => false,
        };
        require(
            agrees,
            "record field semantic type disagrees with its complete source identity",
        )
    }

    fn function_scope_span(&self, scope: &BoundScope) -> Span {
        scope
            .types
            .values()
            .find_map(|identity| {
                self.facts
                    .generic_binders
                    .get(identity)
                    .map(|binder| binder.owner)
            })
            .or_else(|| {
                self.facts.file.map(|file| Span {
                    file,
                    start: 0,
                    end: 0,
                })
            })
            .unwrap_or(Span {
                file: ril_compiler_core::source::FileId(0),
                start: 0,
                end: 0,
            })
    }
}

impl Replay<'_> {
    fn snapshot(&self, snapshot: &CopyValueSnapshot) -> Check {
        require(
            snapshot.nodes.len() <= LIMIT && snapshot.relations.len() <= LIMIT,
            "record-bound frozen graph exceeds replay budget",
        )?;
        let nodes: BTreeMap<_, _> = snapshot
            .nodes
            .iter()
            .map(|node| (node.origin, node))
            .collect();
        require(
            nodes.len() == snapshot.nodes.len(),
            "record-bound frozen graph repeats an origin",
        )?;
        let mut values = vec![(&snapshot.value, 0usize)];
        let mut visited = BTreeSet::new();
        let mut work = LIMIT;
        while let Some((value, depth)) = values.pop() {
            require(
                work > 0 && depth < 64,
                "record-bound frozen value exceeds replay budget",
            )?;
            work -= 1;
            require(
                (value.cause.0 as usize) < self.facts.explanations.causes.len(),
                "record-bound frozen value has no cause registry entry",
            )?;
            require(
                value
                    .origins
                    .nodes
                    .iter()
                    .all(|origin| nodes.contains_key(origin))
                    && value.origins.choices.values().all(|branches| {
                        branches
                            .iter()
                            .flatten()
                            .all(|origin| value.origins.nodes.contains(origin))
                    }),
                "record-bound frozen value has missing graph or choice membership",
            )?;
            if let Some(witness) = &value.source_type_witness {
                require(
                    witness.validate_closed()
                        && super::source_type_validation::resolved_names(
                            witness,
                            &self.facts.external_type_declarations,
                        ),
                    "record-bound frozen type identity is inconsistent or unresolved",
                )?;
            }
            for origin in &value.origins.nodes {
                if visited.insert(*origin) {
                    let node = nodes[origin];
                    values.extend(node.fields.iter().map(|(_, value)| (value, depth + 1)));
                }
            }
            for payload in [
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            {
                values.push((payload, depth + 1));
            }
        }
        require(
            visited.len() == nodes.len(),
            "record-bound frozen graph contains unobserved extra origins",
        )?;
        for node in &snapshot.nodes {
            require(
                (node.origin.0 as usize) < self.facts.heap.nodes.len()
                    && self.facts.allocated_scopes.contains(&node.fact.owner),
                "record-bound frozen origin has no registered identity or scope",
            )?;
            let fields: BTreeMap<_, _> = node
                .fields
                .iter()
                .map(|(slot, value)| (slot.clone(), value.origins.nodes.clone()))
                .collect();
            require(
                fields.len() == node.fields.len()
                    && fields == node.fact.fields
                    && fields
                        .values()
                        .flatten()
                        .all(|origin| nodes.contains_key(origin)),
                "record-bound frozen stored edges disagree with their constituent values",
            )?;
            for (_, value) in &node.fields {
                require(
                    value
                        .origins
                        .nodes
                        .iter()
                        .all(|origin| nodes.contains_key(origin)),
                    "record-bound frozen field points outside its graph",
                )?;
            }
        }
        let mut relations = BTreeSet::new();
        require(
            snapshot.relations.iter().all(|(a, b, relation)| {
                nodes.contains_key(a)
                    && nodes.contains_key(b)
                    && a <= b
                    && relations.insert((*a, *b))
                    && !(relation.equal == super::relations::Condition::TRUE
                        && relation.disjoint == super::relations::Condition::TRUE)
            }) && nodes.keys().enumerate().all(|(index, a)| {
                nodes
                    .keys()
                    .skip(index)
                    .all(|b| relations.contains(&(*a, *b)))
            }),
            "record-bound frozen relations are missing, repeated or contradictory",
        )
    }

    fn same_snapshot(&self, left: &CopyValueSnapshot, right: &CopyValueSnapshot) -> bool {
        left.value == right.value
            && left.nodes.len() == right.nodes.len()
            && left.relations == right.relations
            && left.nodes.iter().all(|node| {
                right.nodes.iter().any(|other| {
                    node.origin == other.origin
                        && node.fact == other.fact
                        && node.fields == other.fields
                        && node.length == other.length
                        && node.fixed == other.fixed
                })
            })
    }

    fn value_key(
        &self,
        snapshot: &CopyValueSnapshot,
        value: &Value,
        depth: usize,
    ) -> Check<ArgumentKey> {
        require(
            depth < 64,
            "complete actual record identity exceeds replay depth",
        )?;
        if let Some(witness) = &value.source_type_witness {
            require(
                witness.validate_closed()
                    && super::source_type_validation::resolved_names(
                        witness,
                        &self.facts.external_type_declarations,
                    ),
                "actual record source identity is not closed or resolved",
            )?;
            let key = self.normalized_key(&witness.syntax, &BoundScope::default())?;
            self.ty_matches(&value.ty, &key, &BoundScope::default(), 0)?;
            return Ok(key);
        }
        let name = match &value.ty {
            Ty::Unit => return Ok(ArgumentKey::Tuple(vec![])),
            Ty::Bool => Some("bool".to_owned()),
            Ty::Str => Some("str".to_owned()),
            Ty::Bytes => Some("bytes".to_owned()),
            Ty::Never => Some("never".to_owned()),
            Ty::Int(name) | Ty::Float(name) | Ty::Named(name) => Some(name.clone()),
            Ty::Record(fields) => {
                let mut result = Vec::new();
                require(
                    !value.origins.nodes.is_empty(),
                    "actual record has no stored whole-object evidence",
                )?;
                for (label, (mutable, _)) in fields {
                    let mut common = None;
                    for origin in &value.origins.nodes {
                        let child = snapshot
                            .nodes
                            .iter()
                            .find(|node| node.origin == *origin)
                            .and_then(|node| {
                                node.fields
                                    .iter()
                                    .find(|(slot, _)| slot == &Slot::Field(label.clone()))
                            })
                            .map(|(_, value)| value)
                            .ok_or_else(|| {
                                "actual record lost a declared stored constituent".to_owned()
                            })?;
                        let key = self.value_key(snapshot, child, depth + 1)?;
                        require(
                            common.as_ref().is_none_or(|previous| previous == &key),
                            "actual record alternatives have different complete field identities",
                        )?;
                        common = Some(key);
                    }
                    result.push((label.clone(), *mutable, common.unwrap()));
                }
                return Ok(ArgumentKey::Record {
                    fields: result,
                    row: None,
                });
            }
            _ => None,
        }
        .ok_or_else(|| {
            "actual record identity cannot be reconstructed from erased array/callable/open type"
                .to_owned()
        })?;
        self.normalized_key(
            &TypeExpr {
                hir_id: None,
                text: String::new(),
                span: self.function_scope_span(&BoundScope::default()),
                kind: TypeKind::Name {
                    path: name.split("::").map(str::to_owned).collect(),
                    arguments: vec![],
                },
            },
            &BoundScope::default(),
        )
    }

    fn fields(
        &self,
        fields: &[RecordBoundField],
        scope: &BoundScope,
    ) -> Check<BTreeMap<String, (bool, ArgumentKey)>> {
        let mut result = BTreeMap::new();
        for field in fields {
            require(
                result
                    .insert(field.label.clone(), (field.mutable, field.key.clone()))
                    .is_none()
                    && field.key == self.normalized_key(&field.syntax, scope)?,
                "structural schema repeats or misidentifies a field",
            )?;
            self.field_type(field, scope)?;
        }
        Ok(result)
    }

    fn schema(&self, check: &GenericBoundCheck) -> Check<Row<ArgumentKey>> {
        let schema = &check.actual_schema;
        let actual = self.selected_value(&check.actual, &check.selection_path)?;
        match &schema.source {
            StructuralSchemaSource::Closed(witness) => {
                require(
                    witness.validate_closed()
                        && super::source_type_validation::resolved_names(
                            witness,
                            &self.facts.external_type_declarations,
                        ),
                    "closed structural schema is not a resolved full type identity",
                )?;
                let key = self.normalized_key(&witness.syntax, &BoundScope::default())?;
                require(
                    key == self.value_key(&check.actual, actual, 0)?,
                    "closed structural schema belongs to another actual argument",
                )?;
                let ArgumentKey::Record { fields, row: None } = key else {
                    return Err(
                        "closed structural schema has no transparent closed record view".into(),
                    );
                };
                let fields: BTreeMap<_, _> = fields
                    .into_iter()
                    .map(|(name, mode, key)| (name, (mode, key)))
                    .collect();
                require(
                    schema.tail == RowTail::Closed
                        && self.fields(&schema.fields, &BoundScope::default())? == fields,
                    "closed structural schema fields or tail differ from the actual source identity",
                )?;
                self.stored_schema(
                    &check.actual,
                    actual,
                    &schema.fields,
                    &BoundScope::default(),
                    &RowTail::Closed,
                )?;
                for origin in &actual.origins.nodes {
                    let node = check
                        .actual
                        .nodes
                        .iter()
                        .find(|node| node.origin == *origin)
                        .unwrap();
                    require(node.fields.len()==fields.len() && node.fields.iter().all(|(slot,_)|
                        matches!(slot,Slot::Field(label) if fields.contains_key(label))),
                        "closed structural identity cannot hide an opaque row or extra stored member")?;
                }
                Ok(Row::closed(fields))
            }
            StructuralSchemaSource::CallerBound(id) => {
                let bound = self
                    .facts
                    .record_bounds
                    .get(id.0 as usize)
                    .filter(|bound| bound.id == *id)
                    .ok_or_else(|| "caller structural implication has no declaration".to_owned())?;
                require(
                    actual.ty == Ty::Generic(bound.binder.clone()),
                    "caller-bound schema does not belong to the actual generic value",
                )?;
                let fields = self.fields(&schema.fields, &bound.scope)?;
                require(
                    fields == self.fields(&bound.fields, &bound.scope)?,
                    "caller structural schema changed its independently guaranteed fields",
                )?;
                let tail = self.declared_tail(bound)?;
                require(
                    schema.tail == tail,
                    "caller structural schema closed or changed its rigid tail",
                )?;
                self.stored_schema(&check.actual, actual, &schema.fields, &bound.scope, &tail)?;
                Ok(Row { fields, tail })
            }
            StructuralSchemaSource::RigidParameter {
                definition,
                parameter_index,
                syntax,
                scope,
            } => {
                let ArgumentKey::Record {
                    fields,
                    row: Some(row),
                } = self.rigid_parameter_view(
                    *definition,
                    *parameter_index,
                    syntax,
                    scope,
                    actual,
                )?
                else {
                    return Err(
                        "rigid structural parameter is not a real open record annotation".into(),
                    );
                };
                let ArgumentKey::Binder { identity, .. } = *row else {
                    return Err("rigid structural parameter tail has no frozen binder".into());
                };
                let known: BTreeMap<_, _> = fields
                    .into_iter()
                    .map(|(name, mode, key)| (name, (mode, key)))
                    .collect();
                let tail = RowTail::Open(OpenTail {
                    identity: RowIdentity::Binder(identity.clone()),
                    lacks: known.keys().cloned().collect(),
                });
                let RowTail::Open(actual_tail) = &schema.tail else {
                    return Err("rigid structural schema was falsely marked closed".into());
                };
                require(
                    actual_tail.identity == RowIdentity::Binder(identity.clone())
                        && self.fields(&schema.fields, scope)? == known,
                    "rigid structural schema changed its field family or tail identity",
                )?;
                let proven = self.signature_lacks(*definition, scope, &identity)?;
                require(
                    actual_tail.lacks.is_subset(&proven),
                    "rigid structural schema invented an absence premise",
                )?;
                require(
                    matches!(&actual.ty,Ty::OpenRecord {row,..} if row.identity==actual_tail.identity),
                    "rigid structural schema does not describe the actual argument view",
                )?;
                let reception = self.scoped_reception_for_check(check)?;
                let mut members = Vec::new();
                if let Some(reception) = &reception {
                    for field in &schema.fields {
                        if scoped_members::symbolic_member_key(&field.key, scope) {
                            members.push(self.scoped_check_member(
                                reception,
                                check,
                                &field.label,
                            )?);
                        }
                    }
                }
                self.stored_schema_with_members(
                    &check.actual,
                    actual,
                    &schema.fields,
                    scope,
                    &tail,
                    &members,
                )?;
                Ok(Row {
                    fields: known,
                    tail: schema.tail.clone(),
                })
            }
        }
    }

    fn declared_tail(&self, bound: &GenericRecordBound) -> Check<RowTail> {
        Ok(match &bound.tail {
            DeclaredBoundTail::Closed => RowTail::Closed,
            DeclaredBoundTail::Row(id) => {
                let row = self.row(*id)?;
                let mut lacks = row.lacks.clone();
                lacks.extend(bound.fields.iter().map(|field| field.label.clone()));
                RowTail::Open(OpenTail {
                    identity: row.identity.clone(),
                    lacks,
                })
            }
            DeclaredBoundTail::Concrete { .. } => {
                return Err("concrete structural tails need an independent equation".into());
            }
        })
    }

    fn stored_schema(
        &self,
        snapshot: &CopyValueSnapshot,
        actual: &Value,
        fields: &[RecordBoundField],
        scope: &BoundScope,
        tail: &RowTail,
    ) -> Check {
        self.stored_schema_with_members(snapshot, actual, fields, scope, tail, &[])
    }

    fn stored_schema_with_members(
        &self,
        snapshot: &CopyValueSnapshot,
        actual: &Value,
        fields: &[RecordBoundField],
        scope: &BoundScope,
        tail: &RowTail,
        members: &[scoped_members::MemberIdentity<'_>],
    ) -> Check {
        require(
            !actual.origins.nodes.is_empty(),
            "structural schema has no actual stored receiver",
        )?;
        for origin in &actual.origins.nodes {
            let node = snapshot
                .nodes
                .iter()
                .find(|node| node.origin == *origin)
                .ok_or_else(|| {
                    "structural schema root is missing from its frozen graph".to_owned()
                })?;
            for field in fields {
                let child = node
                    .fields
                    .iter()
                    .find(|(slot, _)| slot == &Slot::Field(field.label.clone()))
                    .map(|(_, value)| value)
                    .ok_or_else(|| {
                        "structural schema manufactured a field without an existing edge".to_owned()
                    })?;
                self.ty_matches(&child.ty, &field.key, scope, 0)?;
                self.storage_shape(snapshot, child, &field.key, 0)?;
                if let Some(witness) = &child.source_type_witness {
                    require(
                        self.normalized_key(&witness.syntax, scope)? == field.key,
                        "stored structural field has another complete source identity",
                    )?;
                } else if matches!(
                    field.key,
                    ArgumentKey::Array { .. } | ArgumentKey::Callable { .. }
                ) {
                    self.verify_symbolic_field(members, snapshot, child, field, scope)?;
                }
            }
            if let RowTail::Open(tail) = tail {
                require(
                    node.fields
                        .iter()
                        .any(|(slot, _)| slot == &Slot::RowTail(tail.identity.clone())),
                    "open structural schema lost its opaque member-family edge",
                )?;
            }
        }
        Ok(())
    }

    fn signature_lacks(
        &self,
        definition: DefinitionId,
        scope: &BoundScope,
        identity: &str,
    ) -> Check<BTreeSet<String>> {
        let function = self.function(definition)?;
        let mut pending: Vec<_> = function
            .syntax
            .parameters
            .iter()
            .filter_map(|parameter| parameter.ty.as_ref())
            .chain(function.syntax.return_type.iter())
            .collect();
        let mut result = BTreeSet::new();
        let mut work = 4096;
        while let Some(syntax) = pending.pop() {
            require(work > 0, "rigid row declaration walk exceeds replay budget")?;
            work -= 1;
            match &syntax.kind {
                TypeKind::Record { fields, row } => {
                    if let Some(row) = row
                        && matches!(self.normalized_key(row,scope)?,ArgumentKey::Binder {identity:actual,..} if actual==identity)
                    {
                        result.extend(fields.iter().map(|field| field.name.clone()));
                    }
                    pending.extend(fields.iter().map(|field| &field.ty));
                    pending.extend(row.iter().map(Box::as_ref));
                }
                TypeKind::Name { arguments, .. } | TypeKind::Tuple(arguments) => {
                    pending.extend(arguments)
                }
                TypeKind::Array { element, .. } | TypeKind::Optional(element) => {
                    pending.push(element)
                }
                TypeKind::Map { key, value } => pending.extend([key.as_ref(), value.as_ref()]),
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    pending.extend(
                        parameters
                            .iter()
                            .filter_map(|parameter| parameter.ty.as_ref()),
                    );
                    pending.extend(result.iter().map(Box::as_ref));
                }
                _ => {}
            }
        }
        Ok(result)
    }
}

fn select_key(
    key: &ArgumentKey,
    substitutions: &BTreeMap<String, ArgumentKey>,
    depth: usize,
) -> Check<ArgumentKey> {
    require(
        depth < 64,
        "record-bound static substitution is cyclic or too deep",
    )?;
    let mut child = |key: &ArgumentKey| select_key(key, substitutions, depth + 1);
    Ok(match key {
        ArgumentKey::Binder { identity, .. } => match substitutions.get(identity) {
            Some(selected) if selected != key => child(selected)?,
            _ => key.clone(),
        },
        ArgumentKey::Closed(_) | ArgumentKey::GenericBuiltin(_) => key.clone(),
        ArgumentKey::Name { name, arguments } => ArgumentKey::Name {
            name: name.clone(),
            arguments: arguments.iter().map(&mut child).collect::<Check<_>>()?,
        },
        ArgumentKey::Array { length, element } => ArgumentKey::Array {
            length: length.clone(),
            element: Box::new(child(element)?),
        },
        ArgumentKey::Map { key, value } => ArgumentKey::Map {
            key: Box::new(child(key)?),
            value: Box::new(child(value)?),
        },
        ArgumentKey::Tuple(items) => {
            ArgumentKey::Tuple(items.iter().map(&mut child).collect::<Check<_>>()?)
        }
        ArgumentKey::Record { fields, row } => ArgumentKey::Record {
            fields: fields
                .iter()
                .map(|(name, mode, key)| Ok((name.clone(), *mode, child(key)?)))
                .collect::<Check<_>>()?,
            row: row
                .as_ref()
                .map(|row| child(row).map(Box::new))
                .transpose()?,
        },
        ArgumentKey::Callable {
            parameters,
            result,
            annotations,
        } => ArgumentKey::Callable {
            parameters: parameters
                .iter()
                .map(|(mode, key)| Ok((*mode, child(key)?)))
                .collect::<Check<_>>()?,
            result: Box::new(child(result)?),
            annotations: annotations.clone(),
        },
    })
}

#[derive(Clone)]
struct ProjectionSite<'a> {
    owner: CallableOwner,
    expression: &'a Expr,
    base: &'a Expr,
    field: Cow<'a, str>,
    supported: bool,
    assignment: Option<(&'a Expr, &'a str)>,
}

/// A literal coordinate is selected by its source syntax. The ordinary key
/// observation must still agree with it; a runtime string never selects a slot.
fn literal_field(key: &Expr) -> Option<String> {
    match &key.kind {
        ExprKind::Literal(Literal::String(text)) => {
            crate::lower::decode_text(text.get(1..text.len().checked_sub(1)?)?).ok()
        }
        ExprKind::Literal(Literal::RawString(text)) => {
            Some(text.get(1..text.len().checked_sub(1)?)?.to_owned())
        }
        ExprKind::Interpolated(parts)
            if parts.iter().all(|part| matches!(part, StringPart::Text(_))) =>
        {
            Some(
                parts
                    .iter()
                    .filter_map(|part| match part {
                        StringPart::Text(text) => Some(text.as_str()),
                        _ => None,
                    })
                    .collect(),
            )
        }
        _ => None,
    }
}

fn projection_sites(facts: &SemanticFacts) -> Check<Vec<ProjectionSite<'_>>> {
    enum Pending<'a> {
        Statement(CallableOwner, &'a Stmt, usize),
        Expression(CallableOwner, &'a Expr, usize),
    }
    let mut pending = Vec::new();
    for function in &facts.functions {
        let owner = CallableOwner::Function(function.definition);
        if let Some(body) = &function.syntax.body {
            pending.extend(
                body.statements
                    .iter()
                    .chain(&body.where_items)
                    .map(|statement| Pending::Statement(owner, statement, 0)),
            );
        }
    }
    let mut result = Vec::new();
    let mut assignments = Vec::new();
    let mut work = LIMIT;
    while let Some(current) = pending.pop() {
        require(
            work > 0,
            "record-bound source coverage walk exceeds replay budget",
        )?;
        work -= 1;
        match current {
            Pending::Statement(owner, statement, depth) => {
                require(depth < 128, "record-bound source coverage walk is too deep")?;
                let mut expression =
                    |expression| pending.push(Pending::Expression(owner, expression, depth + 1));
                match &statement.kind {
                    StmtKind::Binding(binding) => {
                        expression(&binding.value);
                        if let Some(fallback) = &binding.fallback {
                            expression(fallback)
                        }
                    }
                    StmtKind::Assignment {
                        target,
                        value,
                        operator,
                    } => {
                        assignments.push((owner, target, value, operator.as_str()));
                        expression(target);
                        expression(value)
                    }
                    StmtKind::Expr {
                        expression: value, ..
                    }
                    | StmtKind::HandlerApplication(value) => expression(value),
                    StmtKind::Handler(arms) => {
                        for arm in arms {
                            expression(&arm.operation);
                            expression(&arm.body)
                        }
                    }
                    // Named declarations have their own real DefinitionId roots.
                    StmtKind::Function(_)
                    | StmtKind::Type(_)
                    | StmtKind::Effect(_)
                    | StmtKind::Use(_) => {}
                }
            }
            Pending::Expression(owner, expression, depth) => {
                require(depth < 128, "record-bound source coverage walk is too deep")?;
                let mut children = Vec::new();
                let mut blocks = Vec::new();
                match &expression.kind {
                    ExprKind::Field {
                        base,
                        field,
                        safe: false,
                    } => {
                        result.push(ProjectionSite {
                            owner,
                            expression,
                            base,
                            field: Cow::Borrowed(field),
                            supported: true,
                            assignment: None,
                        });
                        children.push(base.as_ref());
                    }
                    ExprKind::Field { base, field, .. } => {
                        result.push(ProjectionSite {
                            owner,
                            expression,
                            base,
                            field: Cow::Borrowed(field),
                            supported: false,
                            assignment: None,
                        });
                        children.push(base);
                    }
                    ExprKind::ComputedField { base, key } => {
                        let field = literal_field(key);
                        result.push(ProjectionSite {
                            owner,
                            expression,
                            base,
                            supported: field.is_some(),
                            assignment: None,
                            field: field.map_or(Cow::Borrowed(""), Cow::Owned),
                        });
                        children.extend([base.as_ref(), key.as_ref()])
                    }
                    ExprKind::Index { base, index, .. } => {
                        result.push(ProjectionSite {
                            owner,
                            expression,
                            base,
                            field: Cow::Borrowed(""),
                            supported: false,
                            assignment: None,
                        });
                        children.extend([base.as_ref(), index.as_ref()])
                    }
                    ExprKind::Unary { operand, .. } => children.push(operand),
                    ExprKind::Generic { base, .. } => children.push(base),
                    ExprKind::Binary { left, right, .. } => {
                        children.extend([left.as_ref(), right.as_ref()])
                    }
                    ExprKind::Call { callee, arguments } => {
                        children.push(callee);
                        children.extend(arguments.iter().map(|argument| &argument.value));
                    }
                    ExprKind::Lambda { body, .. } => {
                        let site = facts
                            .closure_sites
                            .iter()
                            .find(|site| {
                                site.owner == owner && Some(site.source) == expression.hir_id
                            })
                            .ok_or_else(|| {
                                "record-bound coverage cannot identify a lexical lambda".to_owned()
                            })?;
                        pending.push(Pending::Expression(
                            CallableOwner::Lambda(site.id),
                            body,
                            depth + 1,
                        ));
                    }
                    ExprKind::Block(block) | ExprKind::Loop(block) => blocks.push(block),
                    ExprKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        children.extend([condition.as_ref(), then_branch.as_ref()]);
                        children.extend(else_branch.iter().map(Box::as_ref));
                    }
                    ExprKind::Match { value, arms, .. } => {
                        children.push(value);
                        for arm in arms {
                            children.push(&arm.body);
                            children.extend(arm.guard.iter());
                        }
                    }
                    ExprKind::Is { value, .. } => children.push(value),
                    ExprKind::While { condition, body } => {
                        children.push(condition);
                        blocks.push(body)
                    }
                    ExprKind::For { iterable, body, .. } => {
                        children.push(iterable);
                        blocks.push(body)
                    }
                    ExprKind::Control { value, .. } => {
                        children.extend(value.iter().map(Box::as_ref))
                    }
                    ExprKind::Derive { base, recipe } => {
                        children.extend(base.iter().map(Box::as_ref));
                        children.push(recipe)
                    }
                    ExprKind::Range { start, end, .. } => {
                        children.extend(start.iter().map(Box::as_ref));
                        children.extend(end.iter().map(Box::as_ref));
                    }
                    ExprKind::Tuple(items) | ExprKind::Array(items) => children.extend(items),
                    ExprKind::Map(items) => {
                        for (key, value) in items {
                            children.extend([key, value]);
                        }
                    }
                    ExprKind::Record { members, .. } => {
                        for member in members {
                            match member {
                                ril_syntax::ast::RecordMember::Field(field) => {
                                    children.push(&field.value)
                                }
                                ril_syntax::ast::RecordMember::Spread(value) => {
                                    children.push(value)
                                }
                            }
                        }
                    }
                    ExprKind::Interpolated(parts) => {
                        for part in parts {
                            if let ril_syntax::ast::StringPart::Interpolation {
                                expression, ..
                            } = part
                            {
                                children.push(expression)
                            }
                        }
                    }
                    ExprKind::Name(_)
                    | ExprKind::Path(_)
                    | ExprKind::Literal(_)
                    | ExprKind::Accessor(_)
                    | ExprKind::TypeValue(_)
                    | ExprKind::KeyOf(_)
                    | ExprKind::Ambient
                    | ExprKind::Error => {}
                }
                pending.extend(
                    children
                        .into_iter()
                        .map(|child| Pending::Expression(owner, child, depth + 1)),
                );
                for block in blocks {
                    pending.extend(
                        block
                            .statements
                            .iter()
                            .chain(&block.where_items)
                            .map(|statement| Pending::Statement(owner, statement, depth + 1)),
                    );
                }
            }
        }
    }
    for site in &mut result {
        site.assignment = assignments
            .iter()
            .find(|(owner, target, _, _)| {
                *owner == site.owner && std::ptr::eq(*target, site.expression)
            })
            .map(|(_, _, value, operator)| (*value, *operator));
    }
    Ok(result)
}

impl Replay<'_> {
    fn literal_coordinate_observation(
        &self,
        site: &ProjectionSite<'_>,
        context: super::effect_identity::InvocationContext,
    ) -> Check {
        let ExprKind::ComputedField { key, .. } = &site.expression.kind else {
            return Ok(());
        };
        let label = literal_field(key)
            .ok_or_else(|| "named projection has no genuine literal coordinate".to_owned())?;
        require(
            label == site.field,
            "computed projection selected a different source literal",
        )?;
        let mut observations = self
            .facts
            .invocation_expressions
            .iter()
            .filter_map(|observation| {
                (observation.context == context)
                    .then(|| self.facts.expressions.get(observation.expression))
                    .flatten()
                    .filter(|expression| expression.span == key.span)
            });
        let observed = observations
            .next()
            .ok_or_else(|| "literal coordinate has no actual key observation".to_owned())?;
        require(
            observations.next().is_none(),
            "literal coordinate has multiple actual key observations",
        )?;
        let value = &observed.value;
        require(
            value.ty == Ty::Str
                && value.static_coordinate.as_ref()
                    == Some(&super::model::StaticCoordinate::Label(label))
                && value.origins.nodes.is_empty()
                && value.sources.is_empty()
                && value.results.is_empty()
                && value.scoped.is_empty(),
            "literal coordinate observation disagrees with its source label or carries a runtime path",
        )?;
        let cause = self
            .facts
            .explanations
            .causes
            .get(value.cause.0 as usize)
            .ok_or_else(|| "literal coordinate has no source cause".to_owned())?;
        require(
            self.facts.explanations.kinds.get(value.cause.0 as usize)
                == Some(&super::facts::CauseKind::Source)
                && cause.span == Some(key.span)
                && cause.parents.is_empty(),
            "literal coordinate borrowed another expression's source cause",
        )
    }

    /// This is an opaque, readonly view of the whole receiver. It certifies no
    /// selected member, presence, inspection or writable path.
    fn symbolic_coordinate_projection(
        &self,
        site: &ProjectionSite<'_>,
        base: &super::effect_identity::InvocationExpression,
        result: &super::effect_identity::InvocationExpression,
    ) -> Check {
        let ExprKind::ComputedField { key, .. } = &site.expression.kind else {
            return Err(
                "safe or indexed generic projection has no independent path certificate".into(),
            );
        };
        let (ExprKind::Name(receiver_name), ExprKind::Name(key_name)) =
            (&site.base.kind, &key.kind)
        else {
            return Err("symbolic coordinate replay needs actual named parameter paths".into());
        };
        let Some(CallableOwner::Function(definition)) = base.context.owner else {
            return Err("symbolic coordinate replay has no named lexical owner".into());
        };
        require(
            base.context == result.context,
            "symbolic coordinate mixed invocation contexts",
        )?;
        let source = &self.facts.expressions[base.expression].value;
        let output = &self.facts.expressions[result.expression].value;
        let Ty::Generic(receiver) = &source.ty else {
            return Err("symbolic coordinate has no genuine generic receiver".into());
        };
        self.type_binder(receiver)?;
        let keys: Vec<_> = self
            .facts
            .invocation_expressions
            .iter()
            .filter(|observation| {
                observation.context == base.context
                    && self
                        .facts
                        .expressions
                        .get(observation.expression)
                        .is_some_and(|expression| expression.span == key.span)
            })
            .collect();
        require(
            keys.len() == 1,
            "symbolic coordinate has no unique actual key observation",
        )?;
        let key_value = &self.facts.expressions[keys[0].expression].value;
        let Ty::StaticKey(identity) = &key_value.ty else {
            return Err("computed generic projection needs its actual static-key binder".into());
        };
        let binder = self
            .facts
            .generic_binders
            .get(identity)
            .ok_or_else(|| "static coordinate binder is not registered".to_owned())?;
        require(
            self.binder(binder.definition, binder.index)?.identity == *identity,
            "static coordinate borrowed another declaration identity",
        )?;
        let function = self.function(binder.definition)?;
        let Some(TypeExpr {
            kind: TypeKind::KeyOf(bound),
            ..
        }) = &function.syntax.generics[binder.index as usize].bound
        else {
            return Err("static coordinate has no genuine source keyof constraint".into());
        };
        let TypeKind::Name { path, arguments } = &bound.kind else {
            return Err(
                "static coordinate receiver constraint needs a complete symbolic type proof".into(),
            );
        };
        let key_scope = self.scope(binder.definition)?;
        let scope = self.scope(definition)?;
        require(
            arguments.is_empty()
                && path.len() == 1
                && key_scope.types.get(&path[0]) == Some(receiver)
                && scope.types.get(&binder.name) == Some(identity),
            "static coordinate keyof constraint does not name this nearest receiver binder",
        )?;
        let summaries: Vec<_> = self
            .facts
            .invocations
            .iter()
            .filter(|summary| summary.context == Some(base.context))
            .collect();
        require(
            summaries.len() == 1,
            "symbolic coordinate has no unique actual invocation",
        )?;
        let activation = summaries[0]
            .activation
            .filter(|activation| self.facts.allocated_scopes.contains(activation))
            .ok_or_else(|| "symbolic coordinate has no actual activation".to_owned())?;
        let actual_function = self.function(definition)?;
        let direct_binder = key_value.sources.is_empty()
            && key_name == &binder.name
            && scope.types.get(key_name) == Some(identity);
        let parameter_key = key_value.sources.len() == 1 && key_value.sources.iter().all(|id|
            self.facts.bindings.get(*id).is_some_and(|binding|
                binding.parameter && binding.owner == activation && &binding.name == key_name))
            && actual_function.syntax.parameters.iter().any(|parameter|
                matches!(&parameter.pattern.kind, ril_syntax::ast::PatternKind::Name(name) if name == key_name)
                    && parameter.ty.as_ref().is_some_and(|syntax|
                        matches!(&syntax.kind, TypeKind::Name { path, arguments }
                            if arguments.is_empty() && path.len() == 1
                                && scope.types.get(&path[0]) == Some(identity))));
        require(
            (direct_binder || parameter_key)
                && source.sources.len() == 1
                && source.sources.iter().all(|id| {
                    self.facts.bindings.get(*id).is_some_and(|binding| {
                        binding.parameter
                            && binding.owner == activation
                            && &binding.name == receiver_name
                    })
                }),
            "symbolic coordinate operands are not their actual declared parameter paths",
        )?;
        let call = base
            .context
            .invocation
            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
            .filter(|call| {
                call.target == definition && call.status == CopyInvocationStatus::Completed
            })
            .ok_or_else(|| "symbolic coordinate has no genuine invocation entry".to_owned())?;
        self.read_parameter_reception(
            source,
            site.base,
            base.context,
            activation,
            call.entry.allocation_epoch,
        )?;
        let cause = self
            .facts
            .explanations
            .causes
            .get(output.cause.0 as usize)
            .ok_or_else(|| "symbolic coordinate has no immutable projection cause".to_owned())?;
        require(
            self.facts.explanations.kinds.get(output.cause.0 as usize)
                == Some(&super::facts::CauseKind::Projection)
                && cause.span == Some(site.expression.span)
                && cause.parents == [source.cause, key_value.cause],
            "symbolic coordinate borrowed another receiver or key evaluation",
        )?;
        let mut expected = source.clone();
        expected.ty = Ty::Projection {
            base: Box::new(source.ty.clone()),
            key: identity.clone(),
        };
        expected.permission = super::facts::Permission::Read;
        expected.construction = false;
        expected.marker = false;
        expected.retention_result = false;
        expected.constant = None;
        expected.static_coordinate = None;
        expected.unsuffixed_numeric = false;
        expected.literal_number = false;
        expected.callables.clear();
        expected.callable_bounds.clear();
        expected.callable_returns.clear();
        expected.signature = None;
        expected.variant_tag = None;
        expected.variant_payload = None;
        expected.variant_witnesses.clear();
        expected.option_tag = None;
        expected.option_payload = None;
        expected.result_tag = None;
        expected.result_payload = None;
        expected.result_success = None;
        expected.result_error = None;
        expected.outer_results.clear();
        expected.must_outer_results.clear();
        expected.must_results.clear();
        expected.cause = output.cause;
        require(
            *output == expected,
            "symbolic coordinate changed complete readonly origins, obligations or membership",
        )
    }

    fn projections(&self) -> Result<(), Failure> {
        let sites = projection_sites(self.facts).map_err(|message| {
            (
                self.function_scope_span(&BoundScope::default()),
                None,
                message,
            )
        })?;
        let mut causes = BTreeSet::new();
        for (projection_index, projection) in
            self.facts.generic_bound_projections.iter().enumerate()
        {
            let mut replay = || -> Check {
                let bound = self
                    .facts
                    .record_bounds
                    .get(projection.required.0 as usize)
                    .filter(|bound| bound.id == projection.required)
                    .ok_or_else(|| {
                        "record projection has no independently checked source constraint"
                            .to_owned()
                    })?;
                require(
                    causes.insert(projection.cause.0),
                    "record projection repeats another occurrence's cause",
                )?;
                let Slot::Field(label) = &projection.slot else {
                    return Err("record projection has no guaranteed named coordinate".into());
                };
                let field = bound
                    .fields
                    .iter()
                    .find(|field| &field.label == label)
                    .ok_or_else(|| {
                        "record projection uses an unlisted guaranteed field".to_owned()
                    })?;
                require(
                    projection.access != BoundAccess::Write,
                    "record Write observation needs its actual frozen assignment authorization anchor",
                )?;
                require(
                    projection.context.owner.is_some()
                        && self.facts.allocated_scopes.contains(&projection.activation)
                        && projection.allocation_epoch <= self.facts.allocation_history.len(),
                    "record projection has no registered context, activation or frozen epoch",
                )?;
                let summaries: Vec<_> = self
                    .facts
                    .invocations
                    .iter()
                    .filter(|summary| summary.context == Some(projection.context))
                    .collect();
                require(
                    summaries.len() == 1 && summaries[0].activation == Some(projection.activation),
                    "record projection does not belong to its actual invocation activation",
                )?;
                let matching: Vec<_> = sites
                    .iter()
                    .filter(|site| {
                        Some(site.owner) == projection.context.owner
                            && site.expression.span == projection.span
                            && site.field.as_ref() == label
                    })
                    .collect();
                require(
                    !matching.is_empty(),
                    "record projection has no matching ordinary source occurrence",
                )?;
                for site in &matching {
                    self.literal_coordinate_observation(site, projection.context)?;
                }
                let source_observations: Vec<_> = self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|observation| {
                        observation.context == projection.context
                            && self
                                .facts
                                .expressions
                                .get(observation.expression)
                                .is_some_and(|expression| {
                                    matching
                                        .iter()
                                        .any(|site| site.base.span == expression.span)
                                        && expression.value == projection.source.value
                                })
                    })
                    .collect();
                require(
                    source_observations.len() == 1,
                    "record projection source has no unique actual expression observation",
                )?;
                let output_observations: Vec<_> = self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|observation| {
                        observation.context == projection.context
                            && self
                                .facts
                                .expressions
                                .get(observation.expression)
                                .is_some_and(|expression| {
                                    expression.span == projection.span
                                        && expression.value == projection.output.value
                                })
                    })
                    .collect();
                require(
                    if projection.access == BoundAccess::ValueOnly {
                        self.write_for_projection(projection_index).is_some()
                            && output_observations.is_empty()
                    } else {
                        output_observations.len() == 1
                    },
                    "record projection result has no unique actual expression observation",
                )?;
                let cause = self
                    .facts
                    .explanations
                    .causes
                    .get(projection.cause.0 as usize)
                    .ok_or_else(|| {
                        "record projection has no immutable cause occurrence".to_owned()
                    })?;
                require(
                    self.facts
                        .explanations
                        .kinds
                        .get(projection.cause.0 as usize)
                        == Some(&super::facts::CauseKind::Projection)
                        && cause.span == Some(projection.span)
                        && projection.output.value.cause == projection.cause
                        && cause.parents.first() == Some(&projection.source.value.cause),
                    "record projection borrowed another evaluation's causal source",
                )?;
                if let Some(id) = projection.check {
                    let check = self
                        .facts
                        .generic_bound_checks
                        .get(id.0 as usize)
                        .filter(|check| check.id == id)
                        .ok_or_else(|| {
                            "record projection cites a missing actual shape check".to_owned()
                        })?;
                    require(
                        check.required == projection.required
                            && check.context == projection.context,
                        "record projection borrows another invocation's structural check",
                    )?;
                } else {
                    let own_declaration = projection.context.owner
                        == Some(CallableOwner::Function(bound.definition))
                        && projection
                            .context
                            .invocation
                            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                            .is_none_or(|call| call.declaration_probe);
                    let caller_implication=self.facts.generic_bound_checks.iter().any(|check|
                        check.context==projection.context && matches!(check.actual_schema.source,StructuralSchemaSource::CallerBound(id) if id==bound.id));
                    require(
                        own_declaration || caller_implication,
                        "record projection has neither its universal declaration nor an actual caller implication",
                    )?;
                }
                self.snapshot(&projection.source)?;
                self.snapshot(&projection.output)?;
                let source = &projection.source.value;
                let output = &projection.output.value;
                let loans: Vec<_> = self
                    .facts
                    .invocation_loan_starts
                    .iter()
                    .filter(|loan| {
                        loan.owner == projection.context.owner
                            && loan.named == projection.context.invocation
                            && loan.activation == projection.activation
                            && source
                                .participants
                                .contains(&super::facts::Participant::Loan(loan.loan))
                    })
                    .collect();
                if loans.is_empty() {
                    self.read_reception(projection, matching[0].base)?;
                } else {
                    require(
                        loans.len() == 1,
                        "record projection has no unique actual reception loan",
                    )?;
                    let loan = loans[0];
                    require(
                        projection.allocation_epoch == loan.allocation_epoch,
                        "record projection across recency needs its explicit historical path transport",
                    )?;
                    require(
                        source.origins == loan.origins
                            && source.permission <= loan.source.permission
                            && source.participants
                                == BTreeSet::from([super::facts::Participant::Loan(loan.loan)]),
                        "record projection changed its real received object or loan authority",
                    )?;
                }
                require(
                    source.origins.nodes.len() == 1,
                    "multiple-parent record projection requires its explicit branch replay",
                )?;
                let parent = *source.origins.nodes.iter().next().unwrap();
                let stored = projection
                    .source
                    .nodes
                    .iter()
                    .find(|node| node.origin == parent)
                    .and_then(|node| {
                        node.fields
                            .iter()
                            .find(|(slot, _)| slot == &projection.slot)
                    })
                    .map(|(_, value)| value)
                    .ok_or_else(|| {
                        "record projection manufactured a field without a frozen stored edge"
                            .to_owned()
                    })?;
                require(
                    cause.parents.get(1) == Some(&stored.cause),
                    "record projection borrowed another stored constituent's cause",
                )?;
                if stored.source_type_witness.is_none()
                    && scoped_members::symbolic_member_key(&field.key, &bound.scope)
                {
                    let reception = self.declared_bound_probe(projection, matching[0])?;
                    let member = self.declared_probe_member(&reception, label)?;
                    self.require_member_identity(
                        &member,
                        &projection.source,
                        stored,
                        field,
                        &bound.scope,
                    )?;
                }
                self.ty_matches(&output.ty, &field.key, &bound.scope, 0)?;
                self.storage_shape(&projection.source, stored, &field.key, 0)?;
                require(
                    output.origins.nodes == stored.origins.nodes
                        && output.permission == stored.permission.meet(source.permission)
                        && output.construction == (stored.construction && source.construction)
                        && output.stable == (stored.stable && source.stable),
                    "record projection minted origins or strengthened path authority",
                )?;
                let publication = if stored.publication == Publication::Immutable
                    || source.publication == Publication::Immutable
                {
                    Publication::Immutable
                } else if source.publication == Publication::Live {
                    Publication::Live
                } else {
                    stored.publication
                };
                require(
                    output.publication == publication,
                    "record projection changed publication through its access path",
                )?;
                let scalar = output.ty.scalar();
                let participants = if scalar {
                    BTreeSet::new()
                } else {
                    source.participants.clone()
                };
                let mut scoped = stored.scoped.clone();
                if !scalar {
                    scoped.extend(&source.scoped)
                } else {
                    scoped.clear()
                }
                require(
                    output.participants == participants
                        && output.scoped == scoped
                        && output.sources == source.sources
                        && output.temporary == (!scalar && (stored.temporary || source.temporary))
                        && output.through_return
                            == (stored.through_return || source.through_return),
                    "record projection changed loans, scoped authority or source-path identity",
                )?;
                require(
                    output.results == stored.results
                        && output.outer_results == stored.outer_results
                        && output.must_results == stored.must_results
                        && output.must_outer_results
                            == output
                                .outer_results
                                .intersection(&output.must_results)
                                .copied()
                                .collect(),
                    "record projection changed frozen Result membership or claimed unproved presence",
                )?;
                require(
                    output.callables == stored.callables
                        && output.signature == stored.signature
                        && output.callable_bounds == stored.callable_bounds
                        && output.callable_returns == stored.callable_returns
                        && output.pending_copies == stored.pending_copies,
                    "record projection replaced callable, capture or copy obligations",
                )?;
                for node in &projection.output.nodes {
                    require(
                        projection.source.nodes.iter().any(|source| {
                            source.origin == node.origin
                                && source.fact == node.fact
                                && source.fields == node.fields
                                && source.length == node.length
                                && source.fixed == node.fixed
                        }),
                        "record projection changed a frozen stored graph or cardinality proof",
                    )?;
                }
                require(
                    projection
                        .output
                        .relations
                        .iter()
                        .all(|relation| projection.source.relations.contains(relation)),
                    "record projection invented independence or alias relations",
                )?;
                let mut choices = stored.origins.choices.clone();
                for (choice, branches) in &source.origins.choices {
                    let branches = branches
                        .iter()
                        .map(|parents| {
                            if parents.contains(&parent) {
                                stored.origins.nodes.clone()
                            } else {
                                BTreeSet::new()
                            }
                        })
                        .collect();
                    choices.insert(*choice, branches);
                }
                require(
                    output.origins.choices == choices,
                    "record projection lost source alternative correlations",
                )?;
                Ok(())
            };
            replay().map_err(|message| (projection.span, Some(projection.cause), message))?;
        }
        // The independently recorded receiver and result expressions select the
        // actual occurrence. Shared source spans never merge separate calls.
        for site in &sites {
            let mut symbolic_results = BTreeSet::new();
            let bases:Vec<_>=self.facts.invocation_expressions.iter().filter(|observation|
                observation.context.owner==Some(site.owner)
                    && self.facts.expressions.get(observation.expression).is_some_and(|expression|expression.span==site.base.span
                        && matches!(&expression.value.ty,Ty::Generic(binder) if self.facts.record_bounds.iter().any(|bound|&bound.binder==binder)))).collect();
            for base in bases {
                let source = &self.facts.expressions[base.expression].value;
                let Ty::Generic(binder) = &source.ty else {
                    unreachable!()
                };
                let bound = self
                    .facts
                    .record_bounds
                    .iter()
                    .find(|bound| &bound.binder == binder)
                    .unwrap();
                if site.assignment.is_some() {
                    let covered = self
                        .facts
                        .bound_field_writes
                        .iter()
                        .filter(|write| {
                            self.facts
                                .generic_bound_projections
                                .get(write.projection_index)
                                .is_some_and(|projection| {
                                    projection.required == bound.id
                                        && projection.context == base.context
                                        && projection.span == site.expression.span
                                        && projection.source.value == *source
                                })
                                && self
                                    .observations
                                    .row(write.receiver_expression, &mut 4096)
                                    .is_ok_and(|receiver| std::ptr::eq(receiver, base))
                        })
                        .count();
                    if covered != 1 {
                        return Err((site.expression.span, Some(source.cause),
                            "generic record source assignment lacks exact independent write coverage".into()));
                    }
                    continue;
                }
                let results: Vec<_> = self
                    .facts
                    .invocation_expressions
                    .iter()
                    .filter(|observation| {
                        observation.context == base.context
                            && self
                                .facts
                                .expressions
                                .get(observation.expression)
                                .is_some_and(|expression| expression.span == site.expression.span)
                    })
                    .collect();
                if results.is_empty() {
                    return Err((
                        site.expression.span,
                        Some(source.cause),
                        "generic record source projection has no independent result observation"
                            .into(),
                    ));
                }
                for result in results {
                    let output = &self.facts.expressions[result.expression].value;
                    if !site.supported {
                        self.symbolic_coordinate_projection(site, base, result)
                            .map_err(|message| {
                                (site.expression.span, Some(output.cause), message)
                            })?;
                        if !symbolic_results.insert(result.expression) {
                            return Err((
                                site.expression.span,
                                Some(output.cause),
                                "symbolic coordinate repeats another receiver observation".into(),
                            ));
                        }
                        continue;
                    }
                    let covered = self
                        .facts
                        .generic_bound_projections
                        .iter()
                        .filter(|projection| {
                            projection.required == bound.id
                                && projection.context == base.context
                                && projection.slot == Slot::Field(site.field.to_string())
                                && projection.source.value == *source
                                && projection.output.value == *output
                        })
                        .count();
                    if covered != 1 {
                        return Err((
                            site.expression.span,
                            Some(output.cause),
                            "generic record source projection lacks exact independent coverage"
                                .into(),
                        ));
                    }
                }
            }
            if !site.supported {
                for result in self.facts.invocation_expressions.iter().filter(|observation|
                    observation.context.owner == Some(site.owner)
                        && self.facts.expressions.get(observation.expression).is_some_and(|expression|
                            expression.span == site.expression.span
                                && matches!(&expression.value.ty, Ty::Projection {base, ..}
                                    if matches!(base.as_ref(), Ty::Generic(binder)
                                        if self.facts.record_bounds.iter().any(|bound| &bound.binder == binder)))))
                {
                    if !symbolic_results.contains(&result.expression) {
                        return Err((site.expression.span, Some(self.facts.expressions[result.expression].value.cause),
                            "symbolic coordinate result lost its actual receiver observation".into()));
                    }
                }
            }
            if let ExprKind::Name(name)=&site.base.kind
                && let CallableOwner::Function(definition)=site.owner
                && let Ok(function)=self.function(definition)
                && let Some(parameter)=function.syntax.parameters.iter().find(|parameter|matches!(&parameter.pattern.kind,ril_syntax::ast::PatternKind::Name(actual) if actual==name))
                && parameter.ty.as_ref().is_some_and(|syntax|matches!(&syntax.kind,TypeKind::Name {path,arguments} if arguments.is_empty()
                    && self.facts.record_bounds.iter().any(|bound|bound.definition==definition && path==&[self.facts.generic_binders[&bound.binder].name.clone()])))
                && if site.supported {
                    !self.facts.generic_bound_projections.iter().any(|projection|projection.context.owner==Some(site.owner) && projection.span==site.expression.span)
                } else { symbolic_results.is_empty() }
            {
                return Err((site.expression.span,None,"source generic record projection was deleted from the evidence".into()));
            }
        }
        Ok(())
    }
}

impl Replay<'_> {
    fn storage_shape(
        &self,
        snapshot: &CopyValueSnapshot,
        value: &Value,
        key: &ArgumentKey,
        depth: usize,
    ) -> Check {
        require(depth < 64, "structural physical-shape replay is too deep")?;
        match key {
            ArgumentKey::Array { length, element } => {
                let required = length
                    .as_ref()
                    .map(|length| {
                        length
                            .strip_prefix("const(int:")
                            .and_then(|value| value.strip_suffix(')'))
                            .and_then(|value| value.parse::<u64>().ok())
                            .ok_or_else(|| {
                                "fixed structural field has no normalized target integer".to_owned()
                            })
                    })
                    .transpose()?;
                if let Some(required) = required {
                    let layout = self.facts.target_layout.ok_or_else(|| {
                        "fixed structural field has no frozen target layout".to_owned()
                    })?;
                    require(
                        matches!(layout.pointer_bits, 32 | 64),
                        "fixed structural field has an unsupported target layout",
                    )?;
                    require(
                        required < (1u64 << (layout.pointer_bits - 1)),
                        "fixed structural field exceeds its target integer range",
                    )?;
                    require(
                        !value.origins.nodes.is_empty(),
                        "fixed structural field has no actual array storage",
                    )?;
                }
                for origin in &value.origins.nodes {
                    let node = snapshot
                        .nodes
                        .iter()
                        .find(|node| node.origin == *origin)
                        .ok_or_else(|| "structural array storage is not frozen".to_owned())?;
                    if let Some(required) = required {
                        require(
                            node.fixed,
                            "structural fixed storage lost its declaration's resize invariant",
                        )?;
                        let actual = match node.length {
                            Some(Some(length)) => Some(length),
                            _ if matches!(node.fact.kind, super::facts::OriginKind::Fresh(_))
                                && node
                                    .fields
                                    .iter()
                                    .all(|(slot, _)| matches!(slot, Slot::Index(_))) =>
                            {
                                let indices: BTreeSet<_> = node
                                    .fields
                                    .iter()
                                    .filter_map(|(slot, _)| {
                                        if let Slot::Index(index) = slot {
                                            Some(*index)
                                        } else {
                                            None
                                        }
                                    })
                                    .collect();
                                indices
                                    .iter()
                                    .copied()
                                    .eq(0..indices.len() as i64)
                                    .then_some(indices.len() as u64)
                            }
                            _ => None,
                        };
                        require(
                            actual == Some(required),
                            "structural source identity lacks its independent actual fixed cardinality",
                        )?;
                        if required == 0 {
                            continue;
                        }
                    }
                    for (slot, child) in &node.fields {
                        if matches!(slot, Slot::Index(_) | Slot::AnyIndex) {
                            self.storage_shape(snapshot, child, element, depth + 1)?;
                        }
                    }
                }
            }
            ArgumentKey::Name { name, arguments } if name == "Immut" && arguments.len() == 1 => {
                self.storage_shape(snapshot, value, &arguments[0], depth + 1)?
            }
            ArgumentKey::Name { name, arguments } if name == "Option" && arguments.len() == 1 => {
                if let Some(payload) = &value.option_payload {
                    self.storage_shape(snapshot, payload, &arguments[0], depth + 1)?;
                } else if value.option_tag != Some(false) && has_fixed_shape(&arguments[0], 0)? {
                    return Err(
                        "optional fixed structural field lacks its frozen payload storage".into(),
                    );
                }
            }
            ArgumentKey::Name { name, arguments } if name == "Result" && arguments.len() == 2 => {
                for (index, payload) in [&value.result_success, &value.result_error]
                    .into_iter()
                    .enumerate()
                {
                    if let Some(payload) = payload {
                        self.storage_shape(snapshot, payload, &arguments[index], depth + 1)?;
                    } else if value.result_tag != Some(index == 1)
                        && has_fixed_shape(&arguments[index], 0)?
                    {
                        return Err(
                            "Result fixed structural field lacks its frozen tag-specific storage"
                                .into(),
                        );
                    }
                }
            }
            ArgumentKey::Record { fields, .. } => {
                for (label, _, key) in fields {
                    for origin in &value.origins.nodes {
                        let child = snapshot
                            .nodes
                            .iter()
                            .find(|node| node.origin == *origin)
                            .and_then(|node| {
                                node.fields
                                    .iter()
                                    .find(|(slot, _)| slot == &Slot::Field(label.clone()))
                            })
                            .map(|(_, child)| child)
                            .ok_or_else(|| {
                                "nested structural storage lost a guaranteed field".to_owned()
                            })?;
                        self.storage_shape(snapshot, child, key, depth + 1)?;
                    }
                }
            }
            ArgumentKey::Tuple(fields) => {
                for (index, key) in fields.iter().enumerate() {
                    for origin in &value.origins.nodes {
                        let child = snapshot
                            .nodes
                            .iter()
                            .find(|node| node.origin == *origin)
                            .and_then(|node| {
                                node.fields
                                    .iter()
                                    .find(|(slot, _)| slot == &Slot::Tuple(index as u32))
                            })
                            .map(|(_, child)| child)
                            .ok_or_else(|| {
                                "nested structural storage lost a tuple constituent".to_owned()
                            })?;
                        self.storage_shape(snapshot, child, key, depth + 1)?;
                    }
                }
            }
            _ if has_fixed_shape(key, 0)? => {
                return Err(
                    "wrapped fixed structural field needs its independent payload storage proof"
                        .into(),
                );
            }
            _ => {}
        }
        Ok(())
    }

    fn read_reception(&self, projection: &GenericBoundProjection, expression: &Expr) -> Check {
        self.read_parameter_reception(
            &projection.source.value,
            expression,
            projection.context,
            projection.activation,
            projection.allocation_epoch,
        )
    }

    fn read_parameter_reception(
        &self,
        source: &Value,
        expression: &Expr,
        context: super::effect_identity::InvocationContext,
        activation: super::facts::ScopeId,
        allocation_epoch: usize,
    ) -> Check {
        let Some(CallableOwner::Function(definition)) = context.owner else {
            return Err("record read receiver has no named parameter reception anchor".into());
        };
        let function = self.function(definition)?;
        let call = context
            .invocation
            .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
            .filter(|call| {
                call.target == definition && call.status == CopyInvocationStatus::Completed
            })
            .ok_or_else(|| {
                "record read receiver has no actual or declaration invocation entry".to_owned()
            })?;
        let mut matching = Vec::new();
        for binding in &source.sources {
            let Some(info) = self.facts.bindings.get(*binding) else {
                continue;
            };
            if !info.parameter || info.owner != activation {
                continue;
            }
            for (index, parameter) in function.syntax.parameters.iter().enumerate() {
                if info.pattern.is_some()
                    && parameter.pattern.hir_id == info.pattern
                    && matches!(&parameter.pattern.kind,ril_syntax::ast::PatternKind::Name(name) if name==&info.name)
                {
                    matching.push((*binding, index, info, parameter));
                }
            }
        }
        require(
            matching.len() == 1,
            "record read receiver has no unique genuine parameter binding",
        )?;
        let (binding_id, index, binding, parameter) = matching[0];
        require(
            u32::try_from(binding_id).ok() == Some(binding.root.0),
            "record read reception borrowed another binding's root identity",
        )?;
        let (mode, actual) = call.entry.arguments.get(index).ok_or_else(|| {
            "record read receiver has no whole argument at its real parameter index".to_owned()
        })?;
        let (root_expression, path) = product_expression_path(expression, &binding.name)?;
        let root = if path.is_empty() {
            source
        } else {
            self.observed_product_value(context, root_expression)?
        };
        let mut participants = actual.value.participants.clone();
        if participants.is_empty() {
            participants.insert(super::facts::Participant::Root(binding.root));
        }
        require(
            parameter.mode == ril_syntax::ast::ParameterMode::Read
                && *mode == super::model::Mode::Read
                && root.permission == super::facts::Permission::Read
                && root.publication == actual.value.publication
                && !root.construction
                && !root.marker
                && !root.retention_result
                && root.origins == actual.value.origins
                && root.sources == BTreeSet::from([binding_id])
                && root.participants == participants
                && binding.forwarded == actual.value.sources,
            "record read reception changed its actual object, root or readonly authority",
        )?;
        let mut parent = root;
        for (expression, step) in path {
            let slot = match &step {
                BoundTypeSelectionStep::Tuple(index) => Slot::Tuple(*index),
                BoundTypeSelectionStep::Field(name) => Slot::Field(name.clone()),
                _ => unreachable!(),
            };
            require(
                parent.origins.nodes.len() == 1,
                "nested read path has no exact received parent",
            )?;
            let origin = *parent.origins.nodes.first().unwrap();
            let stored = actual
                .nodes
                .iter()
                .find(|node| node.origin == origin)
                .and_then(|node| node.fields.iter().find(|(stored, _)| stored == &slot))
                .map(|(_, value)| value)
                .ok_or_else(|| "nested read path has no original frozen stored edge".to_owned())?;
            let output = self.observed_product_value(context, expression)?;
            self.product_key_observation(context, expression, &step)?;
            self.received_product_projection(parent, stored, output, origin, expression.span)?;
            parent = output;
        }
        require(
            parent == source,
            "nested read receiver belongs to another observed source path",
        )?;
        require(
            allocation_epoch == call.entry.allocation_epoch,
            "record read projection across recency needs explicit frozen source transport",
        )?;
        if let Some(parent) = call.caller_activation {
            require(
                self.facts.scope_parents.get(&activation) == Some(&parent),
                "record read activation differs from its actual caller scope",
            )?;
        } else {
            require(
                call.declaration_probe,
                "actual read reception cannot invent a missing caller activation",
            )?;
        }
        Ok(())
    }

    fn observed_product_value(
        &self,
        context: super::effect_identity::InvocationContext,
        expression: &Expr,
    ) -> Check<&Value> {
        let mut matching = self
            .facts
            .invocation_expressions
            .iter()
            .filter_map(|observation| {
                (observation.context == context)
                    .then(|| self.facts.expressions.get(observation.expression))
                    .flatten()
                    .filter(|observed| observed.span == expression.span)
            });
        let observed = matching.next().ok_or_else(|| {
            "received product path has no actual expression observation".to_owned()
        })?;
        require(
            matching.next().is_none(),
            "received product path has multiple actual expression observations",
        )?;
        Ok(&observed.value)
    }

    fn product_key_observation(
        &self,
        context: super::effect_identity::InvocationContext,
        expression: &Expr,
        step: &BoundTypeSelectionStep,
    ) -> Check {
        if let ExprKind::ComputedField { key, .. } = &expression.kind {
            let value = self.observed_product_value(context, key)?;
            let genuine = match step {
                BoundTypeSelectionStep::Tuple(index) => {
                    value.ty == Ty::Int("int".into())
                        && value.constant
                            == Some(super::model::Constant::Integer(i128::from(*index)))
                }
                BoundTypeSelectionStep::Field(label) => {
                    value.ty == Ty::Str
                        && value.static_coordinate
                            == Some(super::model::StaticCoordinate::Label(label.clone()))
                }
                _ => false,
            };
            require(
                genuine && value.origins.nodes.is_empty() && value.sources.is_empty(),
                "received product path borrowed a different coordinate or runtime key",
            )?;
        }
        Ok(())
    }

    fn received_product_projection(
        &self,
        parent: &Value,
        stored: &Value,
        output: &Value,
        origin: super::facts::NodeId,
        span: Span,
    ) -> Check {
        let cause = self
            .facts
            .explanations
            .causes
            .get(output.cause.0 as usize)
            .ok_or_else(|| "received product projection has no cause".to_owned())?;
        require(
            self.facts.explanations.kinds.get(output.cause.0 as usize)
                == Some(&super::facts::CauseKind::Projection)
                && cause.span == Some(span)
                && cause.parents == [parent.cause, stored.cause],
            "received product projection borrowed another stored constituent",
        )?;
        let mut expected = stored.clone();
        for (choice, branches) in &parent.origins.choices {
            expected.origins.choices.insert(
                *choice,
                branches
                    .iter()
                    .map(|parents| {
                        if parents.contains(&origin) {
                            stored.origins.nodes.clone()
                        } else {
                            BTreeSet::new()
                        }
                    })
                    .collect(),
            );
        }
        expected.permission = stored.permission.meet(parent.permission);
        expected.construction &= parent.construction;
        expected.publication = if stored.publication == Publication::Immutable
            || parent.publication == Publication::Immutable
        {
            Publication::Immutable
        } else if parent.publication == Publication::Live {
            Publication::Live
        } else {
            stored.publication
        };
        if !expected.origins.nodes.is_empty() {
            expected.temporary |= parent.temporary;
        }
        expected.stable &= parent.stable;
        expected.sources = parent.sources.clone();
        expected.static_coordinate = None;
        expected
            .callback_parameters
            .extend(&parent.callback_parameters);
        if !expected.ty.scalar() {
            expected.scoped.extend(&parent.scoped);
        }
        expected.participants = parent.participants.clone();
        expected.marker = parent.marker || (parent.construction && stored.marker);
        expected.retention_result =
            parent.retention_result || (parent.construction && stored.retention_result);
        expected.through_return |= parent.through_return;
        if expected.ty.scalar() {
            expected.unsuffixed_numeric = false;
            expected.participants.clear();
            expected.temporary = false;
            expected.scoped.clear();
        }
        expected.must_outer_results = expected
            .outer_results
            .intersection(&expected.must_results)
            .copied()
            .collect();
        expected.inherit_copy_dependencies(&parent.nested_copy_dependencies());
        expected.cause = output.cause;
        require(
            &expected == output,
            "received product path changed complete identity, readonly authority or obligations",
        )
    }
}

fn product_expression_path<'a>(
    expression: &'a Expr,
    parameter: &str,
) -> Check<(&'a Expr, Vec<(&'a Expr, BoundTypeSelectionStep)>)> {
    fn walk<'a>(
        expression: &'a Expr,
        parameter: &str,
        depth: usize,
        path: &mut Vec<(&'a Expr, BoundTypeSelectionStep)>,
    ) -> Check<&'a Expr> {
        require(
            depth < 64,
            "received product expression path exceeds replay depth",
        )?;
        let (base, step) = match &expression.kind {
            ExprKind::Name(name) if name == parameter => return Ok(expression),
            ExprKind::Field {
                base,
                field,
                safe: false,
            } => (base.as_ref(), BoundTypeSelectionStep::Field(field.clone())),
            ExprKind::ComputedField { base, key } => {
                let step = if let Some(label) = literal_field(key) {
                    BoundTypeSelectionStep::Field(label)
                } else if let ExprKind::Literal(Literal::Integer(text)) = &key.kind {
                    BoundTypeSelectionStep::Tuple(text.replace('_', "").parse::<u32>().map_err(
                        |_| "received tuple path requires a literal nonnegative integer",
                    )?)
                } else {
                    return Err("received product path needs an actual literal coordinate".into());
                };
                (base.as_ref(), step)
            }
            _ => return Err("record read receiver is not an exact received product path".into()),
        };
        let root = walk(base, parameter, depth + 1, path)?;
        path.push((expression, step));
        Ok(root)
    }
    let mut path = Vec::new();
    let root = walk(expression, parameter, 0, &mut path)?;
    Ok((root, path))
}

fn has_fixed_shape(key: &ArgumentKey, depth: usize) -> Check<bool> {
    require(depth < 64, "structural fixed-shape dependency is too deep")?;
    Ok(match key {
        ArgumentKey::Array {
            length: Some(_), ..
        } => true,
        ArgumentKey::Array { element, .. } => has_fixed_shape(element, depth + 1)?,
        ArgumentKey::Map { key, value } => {
            has_fixed_shape(key, depth + 1)? || has_fixed_shape(value, depth + 1)?
        }
        ArgumentKey::Name { arguments, .. } | ArgumentKey::Tuple(arguments) => arguments
            .iter()
            .map(|key| has_fixed_shape(key, depth + 1))
            .collect::<Check<Vec<_>>>()?
            .into_iter()
            .any(|found| found),
        ArgumentKey::Record { fields, .. } => fields
            .iter()
            .map(|(_, _, key)| has_fixed_shape(key, depth + 1))
            .collect::<Check<Vec<_>>>()?
            .into_iter()
            .any(|found| found),
        // A callable's parameter/result type never declares storage inside the
        // callable object. Its environment is checked by existing copy/loan rules.
        ArgumentKey::Callable { .. } => false,
        _ => false,
    })
}

impl Replay<'_> {
    fn applications(&self) -> Result<(), Failure> {
        for call in &self.facts.copy_invocations {
            let required: Vec<_> = self
                .facts
                .record_bounds
                .iter()
                .filter(|bound| bound.definition == call.target)
                .collect();
            if required.is_empty() || call.declaration_probe {
                continue;
            }
            let check_call = || -> Check {
                require(
                    call.status == CopyInvocationStatus::Completed,
                    "structural application has no completed ordinary invocation",
                )?;
                let checks: Vec<_> = self
                    .facts
                    .generic_bound_checks
                    .iter()
                    .filter(|check| check.context.invocation == Some(call.id))
                    .collect();
                require(
                    checks.len() == required.len(),
                    "actual structural invocation lacks complete check coverage",
                )?;
                let context = checks
                    .first()
                    .ok_or_else(|| "actual structural invocation has no check context".to_owned())?
                    .context;
                require(
                    context.owner == Some(CallableOwner::Function(call.target))
                        && checks.iter().all(|check| check.context == context),
                    "structural checks mix invocation or lexical owner identities",
                )?;
                let owned: BTreeSet<_> = required
                    .iter()
                    .filter_map(|bound| match bound.tail {
                        DeclaredBoundTail::Row(id) => Some(id),
                        _ => None,
                    })
                    .filter(|id| {
                        self.row(*id).is_ok_and(|row| {
                            row.definition == call.target
                                && match &row.role {
                                    BoundRowRole::ImplicitResidual => true,
                                    BoundRowRole::DeclaredTypeParameter { binder } => self
                                        .facts
                                        .generic_binders
                                        .get(binder)
                                        .is_some_and(|binder| binder.definition == call.target),
                                }
                        })
                    })
                    .collect();
                let fresh: BTreeMap<_, _> = owned
                    .iter()
                    .map(|id| {
                        (
                            *id,
                            RowIdentity::Fresh {
                                owner: format!("record-bound:{context:?}"),
                                ordinal: u64::from(id.0),
                            },
                        )
                    })
                    .collect();
                let mut solver = Solver::new(
                    "independent structural generic replay",
                    fresh.values().cloned(),
                );
                let mut selected: BTreeMap<BoundRowId, Row<ArgumentKey>> = BTreeMap::new();
                for bound in required {
                    let matching: Vec<_> = checks
                        .iter()
                        .filter(|check| check.required == bound.id)
                        .collect();
                    require(
                        matching.len() == 1,
                        "structural application repeats or drops a required declaration",
                    )?;
                    let check = *matching[0];
                    self.application_header(call, check, bound)?;
                    let actual = self.schema(check)?;
                    let expected = self
                        .fields(&bound.fields, &bound.scope)?
                        .into_iter()
                        .map(|(name, (mode, key))| {
                            Ok((name, (mode, select_key(&key, &check.substitutions, 0)?)))
                        })
                        .collect::<Check<BTreeMap<_, _>>>()?;
                    if let RowTail::Open(tail) = &actual.tail {
                        solver
                            .declare_rigid(tail.identity.clone(), tail.lacks.clone())
                            .map_err(|_| {
                                "caller residual has conflicting independently known roles"
                                    .to_owned()
                            })?;
                    }
                    let residual = match &bound.tail {
                        DeclaredBoundTail::Closed => None,
                        DeclaredBoundTail::Row(id) => {
                            let row = self.row(*id)?;
                            let mut lacks = row.lacks.clone();
                            lacks.extend(expected.keys().cloned());
                            let identity = fresh
                                .get(id)
                                .cloned()
                                .unwrap_or_else(|| row.identity.clone());
                            if !owned.contains(id) {
                                // A captured row's local requirement is not an independent
                                // absence proof. Only the caller schema supplies rigid facts.
                                let proven = match &actual.tail {
                                    RowTail::Open(tail) if tail.identity == identity => {
                                        tail.lacks.clone()
                                    }
                                    _ => BTreeSet::new(),
                                };
                                solver
                                    .declare_rigid(identity.clone(), proven)
                                    .map_err(|_| {
                                        "captured residual has conflicting roles".to_owned()
                                    })?;
                            }
                            Some(OpenTail { identity, lacks })
                        }
                        DeclaredBoundTail::Concrete { .. } => {
                            return Err(
                                "concrete structural tail has no complete replay equation".into()
                            );
                        }
                    };
                    let remainder = super::record_bound_shapes::entail(
                        &mut solver,
                        &expected,
                        residual.as_ref(),
                        &actual,
                    )
                    .map_err(|error| {
                        format!("structural application row equation is not proved: {error:?}")
                    })?;
                    match &bound.tail {
                        DeclaredBoundTail::Closed => require(
                            check.rows.is_empty(),
                            "closed structural application invented a residual selection",
                        )?,
                        DeclaredBoundTail::Row(id) => {
                            require(
                                check.rows.len() == 1 && check.rows[0].row == *id,
                                "structural application has a missing or unrelated residual selection",
                            )?;
                            let row = &check.rows[0];
                            let fields = self.fields(&row.fields, &self.schema_scope(check)?)?;
                            require(
                                fields == remainder.fields && row.remainder.tail == remainder.tail,
                                "recorded residual differs from the independently replayed equation",
                            )?;
                            let semantic: BTreeMap<_, _> = row
                                .fields
                                .iter()
                                .map(|field| {
                                    (field.label.clone(), (field.mutable, field.ty.clone()))
                                })
                                .collect();
                            require(
                                row.remainder.fields == semantic,
                                "recorded residual erased semantic field modes or types",
                            )?;
                            self.fixed_row_selection(call, *id, &remainder)?;
                            if let Some(previous) = selected.insert(*id, remainder.clone()) {
                                require(
                                    previous == remainder,
                                    "one shared residual was independently rebound per argument",
                                )?;
                            }
                            if let Some(witness) = &row.source_type_witness {
                                require(
                                    matches!(row.remainder.tail, RowTail::Closed)
                                        && witness.validate_closed()
                                        && self.normalized_key(
                                            &witness.syntax,
                                            &BoundScope::default(),
                                        )? == ArgumentKey::Record {
                                            fields: fields
                                                .into_iter()
                                                .map(|(name, (mode, key))| (name, mode, key))
                                                .collect(),
                                            row: None,
                                        },
                                    "an open or different residual borrowed a closed Type identity",
                                )?;
                            }
                        }
                        _ => {}
                    }
                }
                Ok(())
            };
            check_call().map_err(|message| (call.span, None, message))?;
        }
        for (index, check) in self.facts.generic_bound_checks.iter().enumerate() {
            let valid = check.id.0 as usize == index
                && check
                    .context
                    .invocation
                    .and_then(|id| self.facts.copy_invocations.get(id.0 as usize))
                    .is_some_and(|call| {
                        !call.declaration_probe
                            && call.target
                                == self
                                    .facts
                                    .record_bounds
                                    .get(check.required.0 as usize)
                                    .map_or(DefinitionId(u32::MAX), |bound| bound.definition)
                    });
            if !valid {
                return Err((
                    check.span,
                    Some(check.cause),
                    "structural check has no matching actual invocation".into(),
                ));
            }
        }
        Ok(())
    }

    fn schema_scope(&self, check: &GenericBoundCheck) -> Check<BoundScope> {
        match &check.actual_schema.source {
            StructuralSchemaSource::Closed(_) => Ok(BoundScope::default()),
            StructuralSchemaSource::CallerBound(id) => self
                .facts
                .record_bounds
                .get(id.0 as usize)
                .map(|bound| bound.scope.clone())
                .ok_or_else(|| "caller schema has no declaration scope".into()),
            StructuralSchemaSource::RigidParameter { scope, .. } => Ok(scope.clone()),
        }
    }

    fn fixed_row_selection(
        &self,
        call: &super::copy_contract::CopyInvocation,
        id: BoundRowId,
        remainder: &Row<ArgumentKey>,
    ) -> Check {
        let row = self.row(id)?;
        let owned = row.definition == call.target
            && match &row.role {
                BoundRowRole::ImplicitResidual => true,
                BoundRowRole::DeclaredTypeParameter { binder } => self
                    .facts
                    .generic_binders
                    .get(binder)
                    .is_some_and(|binder| binder.definition == call.target),
            };
        if !owned
            && self
                .facts
                .functions
                .iter()
                .filter(|function| function.definition == call.target)
                .any(|function| {
                    function
                        .typing_environment
                        .bound_row_selections
                        .contains_key(&id)
                })
        {
            return Err("fixed captured residual requires its exact creator invocation and callable capture anchor".into());
        }
        if let BoundRowRole::DeclaredTypeParameter { binder } = &row.role {
            let argument = self
                .facts
                .effect_invocations
                .iter()
                .filter(|invocation| {
                    invocation.invocation == Some(call.id) && invocation.function == call.target
                })
                .flat_map(|invocation| {
                    invocation
                        .arguments
                        .iter()
                        .chain(&invocation.captured_arguments)
                })
                .find(|argument| &argument.binder == binder);
            if let Some(key) = argument.and_then(|argument| argument.key.as_ref()) {
                let tail =
                    match &remainder.tail {
                        RowTail::Closed => None,
                        RowTail::Open(OpenTail {
                            identity: RowIdentity::Binder(identity),
                            ..
                        }) => Some(Box::new(ArgumentKey::Binder {
                            identity: identity.clone(),
                            sort: StaticBinderSort::Type,
                        })),
                        _ => return Err(
                            "declared Type residual has no closed or rigid selected row identity"
                                .into(),
                        ),
                    };
                let expected = ArgumentKey::Record {
                    fields: remainder
                        .fields
                        .iter()
                        .map(|(name, (mode, key))| (name.clone(), *mode, key.clone()))
                        .collect(),
                    row: tail,
                };
                require(
                    key == &expected,
                    "declared Type row was rebound instead of preserving its actual static argument",
                )?;
            }
        }
        Ok(())
    }

    fn application_header(
        &self,
        call: &super::copy_contract::CopyInvocation,
        check: &GenericBoundCheck,
        bound: &GenericRecordBound,
    ) -> Check {
        let paths = self.declared_type_paths(call.target, &bound.binder)?;
        require(
            paths.first().is_some_and(|(index, path)| {
                *index == check.argument_index as usize
                    && path.len() == check.selection_path.len()
                    && path.iter().zip(&check.selection_path).all(|(left, right)| {
                        match (left, right) {
                            (
                                BoundTypeSelectionStep::Tuple(a),
                                BoundTypeSelectionStep::Tuple(b),
                            ) => a == b,
                            (
                                BoundTypeSelectionStep::Field(a),
                                BoundTypeSelectionStep::Field(b),
                            ) => a == b,
                            _ => false,
                        }
                    })
            }),
            "structural check selected another source argument or invented a T object",
        )?;
        let (_, actual) = call
            .entry
            .arguments
            .get(check.argument_index as usize)
            .ok_or_else(|| {
                "structural application has no whole actual argument snapshot".to_owned()
            })?;
        self.snapshot(actual)?;
        self.snapshot(&check.actual)?;
        require(
            self.same_snapshot(actual, &check.actual),
            "structural check borrowed another call's actual source snapshot",
        )?;
        require(
            check.allocation_epoch == call.entry.allocation_epoch
                && call.caller_activation == Some(check.activation)
                && check.allocation_epoch <= self.facts.allocation_history.len()
                && self.facts.allocated_scopes.contains(&check.activation),
            "structural check differs from its invocation entry epoch or caller activation",
        )?;
        let actual_key = match &check.actual_schema.source {
            StructuralSchemaSource::Closed(_) => self.value_key(
                &check.actual,
                self.selected_value(&check.actual, &check.selection_path)?,
                0,
            )?,
            StructuralSchemaSource::CallerBound(id) => ArgumentKey::Binder {
                identity: self.facts.record_bounds[id.0 as usize].binder.clone(),
                sort: StaticBinderSort::Type,
            },
            StructuralSchemaSource::RigidParameter { scope, syntax, .. } => {
                self.normalized_key(syntax, scope)?
            }
        };
        let scope = self.schema_scope(check)?;
        let reception = self.scoped_reception_for_check(check)?;
        for (ordinal, (index, path)) in paths.iter().enumerate().skip(1) {
            let (_, whole) = call.entry.arguments.get(*index).ok_or_else(|| {
                "another structural occurrence has no whole actual argument".to_owned()
            })?;
            self.snapshot(whole)?;
            let selected = self.selected_value(whole, path)?;
            let key = match &selected.ty {
                Ty::Generic(identity)
                    if self
                        .facts
                        .record_bounds
                        .iter()
                        .any(|bound| &bound.binder == identity) =>
                {
                    ArgumentKey::Binder {
                        identity: identity.clone(),
                        sort: StaticBinderSort::Type,
                    }
                }
                Ty::OpenRecord { .. } => match &check.actual_schema.source {
                    StructuralSchemaSource::RigidParameter {
                        definition,
                        parameter_index,
                        syntax,
                        scope,
                    } => self.rigid_parameter_view(
                        *definition,
                        *parameter_index,
                        syntax,
                        scope,
                        selected,
                    )?,
                    _ => self.value_key(whole, selected, 0)?,
                },
                _ => self.value_key(whole, selected, 0)?,
            };
            require(
                key == actual_key,
                "another nested occurrence selected a different complete T identity",
            )?;
            let members = if let Some(reception) = &reception {
                self.scoped_member_tokens(
                    reception,
                    ordinal,
                    scoped_members::ReceptionSide::Actual,
                )?
            } else {
                Vec::new()
            };
            self.stored_schema_with_members(
                whole,
                selected,
                &check.actual_schema.fields,
                &scope,
                &check.actual_schema.tail,
                &members,
            )?;
        }
        let rigid_missing = matches!(
            check.actual_schema.source,
            StructuralSchemaSource::RigidParameter { .. }
        ) && !check.substitutions.contains_key(&bound.binder);
        require(
            rigid_missing || check.substitutions.get(&bound.binder) == Some(&actual_key),
            "structural application T substitution differs from its actual argument identity",
        )?;
        let observed: Vec<_> = self
            .facts
            .effect_invocations
            .iter()
            .filter(|invocation| {
                invocation.invocation == Some(call.id) && invocation.function == call.target
            })
            .collect();
        require(
            observed.len() == 1,
            "structural invocation lacks its actual static argument observation",
        )?;
        let observed = observed[0];
        if rigid_missing {
            let argument = observed
                .arguments
                .iter()
                .find(|argument| argument.binder == bound.binder)
                .ok_or_else(|| {
                    "rigid structural selection has no genuine actual Type argument observation"
                        .to_owned()
                })?;
            require(
                argument.key.is_none() && argument.syntax.is_none(),
                "an open structural proof was replaced by an unjustified static Type identity",
            )?;
        }
        let tokens = BoundScope {
            types: self
                .facts
                .generic_binders
                .keys()
                .map(|identity| (format!("\0effect-binder:{identity}"), identity.clone()))
                .collect(),
            rows: BTreeMap::new(),
        };
        for (binder, key) in &check.substitutions {
            let own = self
                .facts
                .generic_binders
                .get(binder)
                .filter(|declaration| declaration.definition == call.target);
            let mut argument = if let Some(own) = own {
                let actual = observed.arguments.get(own.index as usize).ok_or_else(|| {
                    "owned structural Type selection has no actual static argument row".to_owned()
                })?;
                require(
                    actual.definition == call.target
                        && actual.index == own.index
                        && actual.binder == own.identity
                        && observed
                            .arguments
                            .iter()
                            .filter(|argument| &argument.binder == binder)
                            .count()
                            == 1,
                    "owned structural Type selection borrowed another argument position or captured binder",
                )?;
                Some(actual)
            } else {
                observed
                    .arguments
                    .iter()
                    .chain(&observed.captured_arguments)
                    .find(|argument| &argument.binder == binder)
            };
            // The producer freezes its ambient substitution map too. Runtime
            // caller binders are not lexical captures of a global callee.
            // Follow only this actual invocation's parent chain to certify an
            // ambient selected value; never use another call's same-spelled T.
            let mut parent = call.parent;
            let mut seen = BTreeSet::new();
            while argument.is_none() {
                let Some(id) = parent else { break };
                require(
                    seen.insert(id) && seen.len() < 256,
                    "structural caller invocation ancestry is cyclic or too deep",
                )?;
                let entry = self
                    .facts
                    .copy_invocations
                    .get(id.0 as usize)
                    .filter(|entry| entry.id == id)
                    .ok_or_else(|| "structural caller invocation is not registered".to_owned())?;
                argument = self
                    .facts
                    .effect_invocations
                    .iter()
                    .filter(|invocation| {
                        invocation.invocation == Some(id) && invocation.function == entry.target
                    })
                    .flat_map(|invocation| {
                        invocation
                            .arguments
                            .iter()
                            .chain(&invocation.captured_arguments)
                    })
                    .find(|argument| {
                        &argument.binder == binder && argument.key.as_ref() == Some(key)
                    });
                parent = entry.parent;
            }
            let caller_scope = call.caller.map(|caller| self.scope(caller)).transpose()?;
            let genuine_symbolic = matches!(key,ArgumentKey::Binder {identity,..} if identity==binder
                && caller_scope.as_ref().is_some_and(|scope|scope.types.values().any(|actual|actual==identity)));
            let caller_implication = binder == &bound.binder
                && key == &actual_key
                && matches!(&check.actual_schema.source,StructuralSchemaSource::CallerBound(id)
                    if self.facts.record_bounds.get(id.0 as usize).is_some_and(|source|
                        matches!(key,ArgumentKey::Binder {identity,..} if identity==&source.binder)
                        && caller_scope.as_ref().is_some_and(|scope|scope.types.values().any(|identity|identity==&source.binder))));
            let dependent_input = own.is_some()
                && argument
                    .is_some_and(|argument| argument.key.is_none() && argument.syntax.is_none())
                && self.dependent_input_selection(check, bound, binder, key)?;
            if argument.is_none_or(|argument| argument.key.is_none() && argument.syntax.is_none())
                && (genuine_symbolic || caller_implication || dependent_input)
            {
                let ArgumentKey::Binder { identity, .. } = key else {
                    unreachable!()
                };
                self.type_binder(identity)?;
                continue;
            }
            let argument=argument.ok_or_else(||format!("structural substitution {binder} has no actual or captured argument observation"))?;
            require(
                argument.key.as_ref() == Some(key),
                "structural substitution differs from the frozen actual invocation",
            )?;
            let syntax = argument.syntax.as_ref().ok_or_else(|| {
                "structural substitution has no complete source syntax".to_owned()
            })?;
            require(
                self.normalized_key(syntax, &tokens)? == *key,
                "structural argument syntax and key disagree",
            )?;
        }
        Ok(())
    }
}

/// Called only at the independent solved-facts boundary. Missing source,
/// application or access proof remains an explicit NI obligation.
pub fn validate(facts: &SemanticFacts) -> Result<(), Failure> {
    let fallback = facts
        .functions
        .first()
        .map(|function| function.syntax.span)
        .or_else(|| facts.record_bounds.first().map(|bound| bound.span))
        .unwrap_or(Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        });
    let explicit_sources =
        explicit_named::has_sources(facts).map_err(|message| (fallback, None, message))?;
    let input_sources =
        call_input_source::has_sources(facts).map_err(|message| (fallback, None, message))?;
    let default_sources = default_source_receiving::has_sources(facts)
        .map_err(|message| (fallback, None, message))?;
    if facts.record_bounds.is_empty()
        && facts.bound_rows.is_empty()
        && facts.generic_bound_checks.is_empty()
        && facts.generic_bound_projections.is_empty()
        && facts.scoped_source_identities.is_empty()
        && facts.observed_accesses.is_empty()
        && facts.bound_field_writes.is_empty()
        && !explicit_sources
        && !input_sources
        && !default_sources
        && !facts.functions.iter().any(|function| {
            function.syntax.generics.iter().any(|parameter| {
                parameter
                    .bound
                    .as_ref()
                    .is_some_and(|bound| matches!(bound.kind, TypeKind::Record { .. }))
            })
        })
    {
        return Ok(());
    }
    let replay = Replay::new(facts).map_err(|message| (fallback, None, message))?;
    replay
        .declarations()
        .map_err(|(span, message)| (span, None, message))?;
    replay.scoped_source_coverage()?;
    replay.declaration_default_sources()?;
    replay.explicit_named_applications()?;
    replay.call_input_sources()?;
    replay.applications()?;
    replay.bound_writes()?;
    replay.projections()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::model::rows::RowIdentity;

    // These are declaration/header-only tests. They do not fabricate a
    // successful application or project a hypothetical runtime T object.
    fn headers(field: &str) -> SemanticFacts {
        let verified = crate::Session::new(b"fn identity<T>(value:T)->T{value}".to_vec())
            .verify()
            .unwrap();
        let mut facts = verified.facts().clone();
        let parsed = ril_syntax::parse(&format!(
            "fn identity<T:{{id:{field},..R}}>(value:T)->T{{value}}"
        ));
        assert!(parsed.is_ok());
        let StmtKind::Function(function) = &parsed.program.statements[0].kind else {
            unreachable!()
        };
        facts.functions[0].syntax = function.clone();
        let definition = facts.functions[0].definition;
        let binder = facts
            .generic_binders
            .values()
            .find(|binder| binder.definition == definition && binder.index == 0)
            .unwrap()
            .identity
            .clone();
        let syntax = function.generics[0].bound.clone().unwrap();
        let TypeKind::Record { fields, .. } = &syntax.kind else {
            unreachable!()
        };
        let id = GenericBoundId(0);
        let row = BoundRowId(0);
        let scope = BoundScope {
            types: BTreeMap::from([("T".into(), binder.clone())]),
            rows: BTreeMap::from([("R".into(), row)]),
        };
        let int = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: fields[0].ty.span,
            kind: TypeKind::Name {
                path: vec!["int".into()],
                arguments: vec![],
            },
        };
        facts.record_bounds.push(GenericRecordBound {
            id,
            definition,
            binder,
            generic_index: 0,
            syntax: syntax.clone(),
            scope,
            fields: vec![RecordBoundField {
                label: "id".into(),
                mutable: false,
                ty: Ty::Int("int".into()),
                syntax: int.clone(),
                key: crate::static_eval::effects::bounded_argument_key(&int, &BTreeMap::new())
                    .unwrap(),
            }],
            tail: DeclaredBoundTail::Row(row),
            span: syntax.span,
        });
        facts.bound_rows.push(BoundRowDeclaration {
            id: row,
            definition,
            ordinal: 0,
            name: "R".into(),
            role: BoundRowRole::ImplicitResidual,
            declaration_paths: vec![BoundDeclarationPath {
                generic_index: 0,
                path: vec![BoundPathStep::Bound, BoundPathStep::RowTail],
            }],
            identity: RowIdentity::Binder(format!("function:{}:bound-row:0", definition.0)),
            lacks: BTreeSet::from(["id".into()]),
            span: syntax.span,
        });
        facts
    }

    #[test]
    fn genuine_type_binder_and_implicit_residual_have_separate_source_roles() {
        let facts = headers("int");
        Replay::new(&facts).unwrap().declarations().unwrap();
        assert_eq!(facts.generic_binders.len(), 1);
        assert_eq!(facts.bound_rows.len(), 1);
    }

    #[test]
    fn missing_declaration_or_counterfeit_type_row_cannot_pass_by_empty_coverage() {
        let mut facts = headers("int");
        facts.record_bounds.clear();
        assert!(Replay::new(&facts).unwrap().declarations().is_err());
        let mut facts = headers("int");
        facts.bound_rows[0].role = BoundRowRole::DeclaredTypeParameter {
            binder: facts.record_bounds[0].binder.clone(),
        };
        assert!(Replay::new(&facts).unwrap().declarations().is_err());
    }

    #[test]
    fn independently_declared_absences_cannot_be_strengthened_or_dropped() {
        for lacks in [
            BTreeSet::new(),
            BTreeSet::from(["id".into(), "forged".into()]),
        ] {
            let mut facts = headers("int");
            facts.bound_rows[0].lacks = lacks;
            assert!(Replay::new(&facts).unwrap().declarations().is_err());
        }
    }

    #[test]
    fn captured_type_scope_uses_the_nearest_lexical_binder_not_an_outer_namesake() {
        let source = "fn outer<T>(value:T)->T{value\nwhere fn middle<T>(value:T)->T{value\nwhere fn leaf<U>(value:U)->U{value}}}";
        let verified = crate::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let mut facts = verified.facts().clone();
        let leaf = facts
            .functions
            .iter()
            .position(|function| function.syntax.name.ends_with("leaf"))
            .unwrap();
        let outer = facts
            .functions
            .iter()
            .find(|function| function.syntax.name.ends_with("outer"))
            .unwrap()
            .definition;
        let definition = facts.functions[leaf].definition;
        Replay::new(&facts).unwrap().scope(definition).unwrap();
        let wrong = facts
            .generic_binders
            .values()
            .find(|binder| binder.definition == outer && binder.name == "T")
            .unwrap()
            .identity
            .clone();
        let mut changed = facts.functions[leaf].typing_environment.thaw();
        changed.generic_context.insert("T".into(), wrong);
        facts.functions[leaf].typing_environment = changed.freeze();
        assert!(Replay::new(&facts).unwrap().scope(definition).is_err());
    }

    #[test]
    fn frozen_target_normalization_compares_alias_meaning_instead_of_ast_spelling() {
        let mut facts = headers("Count");
        let parsed = ril_syntax::parse("type Count=int");
        let StmtKind::Type(declaration) = &parsed.program.statements[0].kind else {
            unreachable!()
        };
        facts
            .external_type_declarations
            .insert("Count".into(), declaration.clone());
        Replay::new(&facts).unwrap().declarations().unwrap();
        facts.record_bounds[0].fields[0].key = ArgumentKey::Name {
            name: "str".into(),
            arguments: vec![],
        };
        assert!(Replay::new(&facts).unwrap().declarations().is_err());
    }

    #[test]
    fn one_application_cannot_rebind_a_shared_row_or_close_a_rigid_unknown_tail() {
        let required = BTreeMap::from([("id".into(), (false, "int"))]);
        let tail = OpenTail {
            identity: RowIdentity::Binder("callee:R".into()),
            lacks: BTreeSet::from(["id".into()]),
        };
        let mut solver = Solver::new("independent test", [tail.identity.clone()]);
        super::super::record_bound_shapes::entail(
            &mut solver,
            &required,
            Some(&tail),
            &Row::closed(BTreeMap::from([
                ("id".into(), (false, "int")),
                ("tag".into(), (false, "str")),
            ])),
        )
        .unwrap();
        assert!(
            super::super::record_bound_shapes::entail(
                &mut solver,
                &required,
                Some(&tail),
                &Row::closed(BTreeMap::from([
                    ("id".into(), (false, "int")),
                    ("tag".into(), (false, "int"))
                ]))
            )
            .is_err()
        );
        let caller = OpenTail {
            identity: RowIdentity::Binder("caller:S".into()),
            lacks: BTreeSet::from(["id".into()]),
        };
        let mut solver = Solver::new("independent open test", [tail.identity.clone()]);
        solver
            .declare_rigid(caller.identity.clone(), caller.lacks.clone())
            .unwrap();
        let selected = super::super::record_bound_shapes::entail(
            &mut solver,
            &required,
            Some(&tail),
            &Row::open(required.clone(), caller.clone()),
        )
        .unwrap();
        assert!(matches!(selected.tail,RowTail::Open(actual) if actual.identity==caller.identity));
    }
}
