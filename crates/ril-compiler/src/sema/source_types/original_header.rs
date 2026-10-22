//! One original-header ingress. Structural types remain a finite graph;
//! declaration sorts alone admit normalized Const coordinates.
use super::super::{
    SourceBuilder, SourceContainer, SourceField, SourceLength, SourceNode, SourceScalar,
    SourceSchema, SourceTypeId, SourceTypesError, WorkLimit,
};
use crate::{hir::nodes as hir, static_eval};
use ril_compiler_core::{ids::StmtId, target::TargetLayout};
use ril_syntax::ast::*;
use std::collections::BTreeMap;
#[path = "constructor_instance.rs"]
mod constructor_instance;
pub(crate) use constructor_instance::{DeclaredConstructorInstance, constructor_instance};

#[derive(Clone, Copy)]
pub(crate) struct HeaderContext<'a> {
    pub(crate) declarations: &'a BTreeMap<String, TypeDeclaration>,
    pub(crate) program: &'a Program,
    pub(crate) hir: &'a hir::HirProgram,
    pub(crate) binders: &'a BTreeMap<String, String>,
    pub(crate) layout: TargetLayout,
}

/// This is invoked only for an original header's typed elaboration request.
/// Actual observed Source graphs never enter the static interpreter here.
pub(crate) fn elaborate_original_header(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    charge_syntax(syntax, work)?;
    let header = Header {
        context,
        aliases: BTreeMap::new(),
        builder: SourceBuilder::new()?,
    };
    header.validate_syntax(syntax, work)?;
    let elaborated = header.elaborate(syntax, work)?;
    build(&elaborated, context, work, false).map(|schema| schema.with_original(syntax.hir_id))
}

pub(crate) fn original_header(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
) -> Result<SourceSchema, SourceTypesError> {
    build(syntax, context, work, true)
}

fn build(
    syntax: &TypeExpr,
    context: HeaderContext<'_>,
    work: &mut WorkLimit,
    authenticate: bool,
) -> Result<SourceSchema, SourceTypesError> {
    charge_syntax(syntax, work)?;
    work.charge(context.binders.len())?;
    for (name, identity) in context.binders {
        work.text(name)?;
        work.text(identity)?;
    }
    let mut binders = context.binders.clone();
    for identity in context.binders.values() {
        work.charge(1)?;
        work.text(identity)?;
        let token = format!("\0effect-binder:{identity}");
        if binders
            .insert(token, identity.clone())
            .is_some_and(|old| old != *identity)
        {
            return Err(SourceTypesError::Unresolved);
        }
    }
    let mut header = Header {
        context: HeaderContext {
            binders: &binders,
            ..context
        },
        aliases: BTreeMap::new(),
        builder: SourceBuilder::new()?,
    };
    if authenticate {
        header.validate_syntax(syntax, work)?;
    }
    let root = header.ty(syntax, true, work, 0)?;
    let types = header.builder.freeze(work)?;
    super::super::reception::complete(&types, root, work)?;
    SourceSchema::frozen_view(&types, root, syntax.hir_id, work)
}

fn charge_syntax(syntax: &TypeExpr, work: &mut WorkLimit) -> Result<(), SourceTypesError> {
    let mut remaining = work.remaining();
    let admitted = static_eval::charge_type_syntax_clone(syntax, &mut remaining);
    work.charge(work.remaining() - remaining)?;
    admitted.ok_or(SourceTypesError::BudgetExceeded)
}

struct Header<'a> {
    context: HeaderContext<'a>,
    aliases: BTreeMap<StmtId, SourceTypeId>,
    builder: SourceBuilder,
}

impl Header<'_> {
    fn validate_syntax(
        &self,
        syntax: &TypeExpr,
        work: &mut WorkLimit,
    ) -> Result<(), SourceTypesError> {
        let id = syntax.hir_id.ok_or(SourceTypesError::MissingNode)?;
        // One exhaustive admission pays the clone and one pays the canonical
        // pairing before either operation visits the original tree.
        charge_syntax(syntax, work)?;
        charge_syntax(syntax, work)?;
        let mut original = syntax.clone();
        self.context
            .hir
            .validate_type_syntax(&mut original, id, hir::HirLimits::default())
            .map_err(|error| match error {
                hir::LowerError::Budget(_) => SourceTypesError::BudgetExceeded,
                _ => SourceTypesError::Unresolved,
            })
    }
    /// Authenticate the map entry against both the original syntax declaration
    /// and its exact module HIR node. A same-spelled replacement is not a sort.
    fn declaration(
        &self,
        name: &str,
        work: &mut WorkLimit,
    ) -> Result<Option<(StmtId, TypeDeclaration)>, SourceTypesError> {
        let Some(declaration) = self.context.declarations.get(name) else {
            return Ok(None);
        };
        work.text(name)?;
        if declaration.name != name {
            return Err(SourceTypesError::Unresolved);
        }
        work.charge(self.context.program.statements.len())?;
        let mut originals = self.context.program.statements.iter().filter(|statement| {
            matches!(&statement.kind,
                StmtKind::Type(actual) if actual.name == name)
        });
        let actual = originals.next().ok_or(SourceTypesError::Unresolved)?;
        if originals.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        let id = actual.hir_id.ok_or(SourceTypesError::MissingNode)?;
        let statement = self
            .context
            .hir
            .statement(id)
            .ok_or(SourceTypesError::MissingNode)?;
        if statement.info.owner != hir::LexicalOwner::Module {
            return Err(SourceTypesError::Unresolved);
        }
        let StmtKind::Type(actual_declaration) = &actual.kind else {
            unreachable!()
        };
        // Pay clone and canonical pairing separately for both retained views.
        self.charge_declaration(actual_declaration, work)?;
        self.charge_declaration(actual_declaration, work)?;
        self.charge_declaration(declaration, work)?;
        self.charge_declaration(declaration, work)?;
        let mut original = actual.clone();
        let mut candidate = Stmt {
            hir_id: Some(id),
            span: declaration.span,
            kind: StmtKind::Type(declaration.clone()),
        };
        for syntax in [&mut original, &mut candidate] {
            self.context
                .hir
                .validate_statement_syntax(syntax, id, hir::HirLimits::default())
                .map_err(|error| match error {
                    hir::LowerError::Budget(_) => SourceTypesError::BudgetExceeded,
                    _ => SourceTypesError::Unresolved,
                })?;
        }
        let StmtKind::Type(declaration) = candidate.kind else {
            unreachable!()
        };
        Ok(Some((id, declaration)))
    }

    fn charge_declaration(
        &self,
        declaration: &TypeDeclaration,
        work: &mut WorkLimit,
    ) -> Result<(), SourceTypesError> {
        work.charge(1 + declaration.generics.len() + declaration.variants.len())?;
        work.text(&declaration.name)?;
        for generic in &declaration.generics {
            work.text(&generic.name)?;
            for ty in generic.bound.iter().chain(&generic.default) {
                charge_syntax(ty, work)?;
            }
        }
        if let Some(ty) = &declaration.value {
            charge_syntax(ty, work)?;
        }
        for variant in &declaration.variants {
            work.text(&variant.name)?;
            work.charge(variant.generics.len() + variant.annotations.len())?;
            for generic in &variant.generics {
                work.text(&generic.name)?;
                for ty in generic.bound.iter().chain(&generic.default) {
                    charge_syntax(ty, work)?;
                }
            }
            for ty in variant.payload.iter().chain(&variant.result) {
                charge_syntax(ty, work)?;
            }
            for annotation in &variant.annotations {
                work.text(&annotation.text)?;
            }
        }
        Ok(())
    }

    fn ty(
        &mut self,
        syntax: &TypeExpr,
        caller: bool,
        work: &mut WorkLimit,
        depth: usize,
    ) -> Result<SourceTypeId, SourceTypesError> {
        work.charge(1)?;
        if depth >= 64 {
            return Err(SourceTypesError::BudgetExceeded);
        }
        let node = match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                work.charge(path.len() + arguments.len())?;
                for part in path {
                    work.text(part)?;
                }
                let name = path.join("::");
                if caller
                    && arguments.is_empty()
                    && let Some(identity) = self.context.binders.get(&name)
                {
                    work.text(identity)?;
                    return self
                        .builder
                        .insert(SourceNode::Binder(identity.clone()), work);
                }
                if arguments.is_empty() {
                    if let Some(scalar) = super::super::legacy::scalar(&name) {
                        return self.builder.insert(SourceNode::Scalar(scalar), work);
                    }
                    if let Some(schema) = super::super::standard_data::schema(&name) {
                        return schema.insert(&mut self.builder, work);
                    }
                }
                let needs_declaration =
                    self.context
                        .declarations
                        .get(&name)
                        .is_some_and(|declaration| {
                            (!declaration.nominal
                                && !declaration.opaque
                                && declaration.variants.is_empty())
                                || declaration
                                    .generics
                                    .iter()
                                    .any(static_eval::const_nominal::static_parameter)
                        });
                if needs_declaration
                    && let Some((declaration_id, declaration)) = self.declaration(&name, work)?
                {
                    if !declaration.nominal
                        && !declaration.opaque
                        && declaration.variants.is_empty()
                    {
                        if !declaration.generics.is_empty() || !arguments.is_empty() {
                            return Err(SourceTypesError::NeedsStaticElaboration);
                        }
                        if let Some(&root) = self.aliases.get(&declaration_id) {
                            return Ok(root);
                        }
                        let value = declaration
                            .value
                            .as_ref()
                            .ok_or(SourceTypesError::Unresolved)?
                            .clone();
                        self.validate_syntax(&value, work)?;
                        let root = self.builder.reserve(work)?;
                        self.aliases.insert(declaration_id, root);
                        let target = self.ty(&value, false, work, depth + 1)?;
                        self.builder.define(
                            root,
                            SourceNode::Alias {
                                declaration: name,
                                target,
                            },
                            work,
                        )?;
                        return Ok(root);
                    }
                    if declaration.nominal && !declaration.generics.is_empty() {
                        let mut remaining = work.remaining();
                        let normalized = static_eval::const_nominal::closed_const_nominal_arguments(
                            &declaration,
                            arguments,
                            self.context.declarations,
                            self.context.layout,
                            &mut remaining,
                        );
                        work.charge(work.remaining() - remaining)?;
                        if let Some(arguments) =
                            normalized.map_err(|_| SourceTypesError::Unresolved)?
                        {
                            let schema = SourceSchema::certified_const_nominal(
                                &name,
                                &arguments,
                                syntax.hir_id,
                                work,
                            )?;
                            return schema.copy_into(&mut self.builder, work);
                        }
                        if declaration
                            .generics
                            .iter()
                            .any(static_eval::const_nominal::static_parameter)
                        {
                            return Err(SourceTypesError::NeedsStaticElaboration);
                        }
                    }
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| self.ty(argument, caller, work, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(root) = super::super::standard_views::instantiate(
                    &name,
                    &arguments,
                    &mut self.builder,
                    work,
                )? {
                    return Ok(root);
                }
                if let Some(kind) = super::super::legacy::container(&name) {
                    SourceNode::Container { kind, arguments }
                } else {
                    if !caller
                        && !self.context.declarations.contains_key(&name)
                        && !crate::sema::checker::is_known_builtin_source_type(&name)
                    {
                        return Err(SourceTypesError::Unresolved);
                    }
                    SourceNode::OpaqueName { name, arguments }
                }
            }
            TypeKind::Optional(inner) => SourceNode::Container {
                kind: SourceContainer::Option,
                arguments: vec![self.ty(inner, caller, work, depth + 1)?],
            },
            TypeKind::Array { length, element } => SourceNode::Array {
                length: match length {
                    None => SourceLength::Dynamic,
                    Some(_) => self.extent(syntax, work)?,
                },
                element: self.ty(element, caller, work, depth + 1)?,
            },
            TypeKind::Map { key, value } => SourceNode::Map {
                key: self.ty(key, caller, work, depth + 1)?,
                value: self.ty(value, caller, work, depth + 1)?,
            },
            TypeKind::Tuple(items) if items.is_empty() => SourceNode::Scalar(SourceScalar::Unit),
            TypeKind::Tuple(items) => {
                work.charge(items.len())?;
                SourceNode::Tuple(
                    items
                        .iter()
                        .map(|item| self.ty(item, caller, work, depth + 1))
                        .collect::<Result<_, _>>()?,
                )
            }
            TypeKind::Record { fields, row } => {
                work.charge(fields.len() + usize::from(row.is_some()))?;
                let fields = fields
                    .iter()
                    .map(|field| {
                        work.text(&field.name)?;
                        Ok(SourceField {
                            label: field.name.clone(),
                            mutable: field.mutable,
                            value: self.ty(&field.ty, caller, work, depth + 1)?,
                        })
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                SourceNode::Record {
                    fields,
                    row: row
                        .as_ref()
                        .map(|row| self.ty(row, caller, work, depth + 1))
                        .transpose()?,
                }
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                work.charge(parameters.len() + annotations.len() + 1)?;
                let parameters = parameters
                    .iter()
                    .map(|parameter| {
                        if parameter.default.is_some() {
                            return Err(SourceTypesError::Unresolved);
                        }
                        Ok((
                            parameter.mode,
                            self.ty(
                                parameter.ty.as_ref().ok_or(SourceTypesError::Unresolved)?,
                                caller,
                                work,
                                depth + 1,
                            )?,
                        ))
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                let result = match result {
                    Some(result) => self.ty(result, caller, work, depth + 1)?,
                    None => self
                        .builder
                        .insert(SourceNode::Scalar(SourceScalar::Unit), work)?,
                };
                let annotations = annotations
                    .iter()
                    .map(|annotation| {
                        work.text(&annotation.text)?;
                        Ok(annotation.text.replace(' ', ""))
                    })
                    .collect::<Result<_, SourceTypesError>>()?;
                SourceNode::Callable {
                    parameters,
                    result,
                    annotations,
                }
            }
            _ => return Err(SourceTypesError::NeedsStaticElaboration),
        };
        self.builder.insert(node, work)
    }

    fn extent(
        &self,
        syntax: &TypeExpr,
        work: &mut WorkLimit,
    ) -> Result<SourceLength, SourceTypesError> {
        use num_traits::ToPrimitive;
        work.charge(4)?;
        charge_syntax(syntax, work)?;
        let TypeKind::Array {
            length: Some(length),
            ..
        } = &syntax.kind
        else {
            return Err(SourceTypesError::Unresolved);
        };
        let shell = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: syntax.span,
            kind: TypeKind::Array {
                length: Some(length.clone()),
                element: Box::new(TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Tuple(vec![]),
                }),
            },
        };
        let normalized = self.elaborate(&shell, work)?;
        let TypeKind::Array {
            length: Some(length),
            ..
        } = normalized.kind
        else {
            return Err(SourceTypesError::Unresolved);
        };
        let ExprKind::Literal(Literal::Integer(text)) = &length.kind else {
            return Err(SourceTypesError::Unresolved);
        };
        work.text(text)?;
        let value = crate::numeric_literals::ExactLiteral::integer(
            text,
            false,
            crate::numeric_literals::ParseLimit { max_bytes: 4096 },
        )
        .map_err(|error| {
            if error == crate::numeric_literals::Error::ResourceLimit {
                SourceTypesError::BudgetExceeded
            } else {
                SourceTypesError::Unresolved
            }
        })?;
        Ok(SourceLength::Fixed(
            value
                .magnitude()
                .and_then(ToPrimitive::to_u64)
                .ok_or(SourceTypesError::Unresolved)?,
        ))
    }

    fn elaborate(
        &self,
        syntax: &TypeExpr,
        work: &mut WorkLimit,
    ) -> Result<TypeExpr, SourceTypesError> {
        work.charge(2)?;
        charge_syntax(syntax, work)?;
        let declaration = TypeDeclaration {
            visibility: Visibility::Private,
            is_halt: false,
            name: "\0source-header-elaboration".into(),
            generics: vec![],
            value: Some(syntax.clone()),
            variants: vec![],
            opaque: false,
            nominal: true,
            span: syntax.span,
        };
        let mut remaining = work.remaining();
        let normalized = static_eval::normalize_constructor_arguments_bounded(
            &declaration,
            &[],
            self.context.declarations,
            self.context.layout,
            &mut remaining,
        );
        work.charge(work.remaining() - remaining)?;
        normalized
            .map_err(|_| SourceTypesError::Unresolved)?
            .payloads
            .remove(&declaration.name)
            .flatten()
            .ok_or(SourceTypesError::Unresolved)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::source_types::SourceTypeQueries;

    fn fixture() -> (Program, hir::HirProgram, BTreeMap<String, TypeDeclaration>) {
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::nested-const-original-headers",
        );
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut program = parsed.program;
        let hir =
            hir::HirProgram::lower_identified(&mut program, hir::InputOrigin::Source).unwrap();
        let declarations = program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) => {
                    Some((declaration.name.clone(), declaration.clone()))
                }
                _ => None,
            })
            .collect();
        (program, hir, declarations)
    }

    fn parameter(program: &Program, name: &str) -> TypeExpr {
        program
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Function(function) if function.name == name => {
                    function.parameters[0].ty.clone()
                }
                _ => None,
            })
            .unwrap()
    }

    fn context<'a>(
        program: &'a Program,
        hir: &'a hir::HirProgram,
        declarations: &'a BTreeMap<String, TypeDeclaration>,
        binders: &'a BTreeMap<String, String>,
    ) -> HeaderContext<'a> {
        HeaderContext {
            program,
            hir,
            declarations,
            binders,
            layout: TargetLayout::POINTER64,
        }
    }

    #[test]
    fn original_headers_keep_nested_const_coordinates_and_regular_alias_backedges() {
        let (program, hir, declarations) = fixture();
        let binders = BTreeMap::from([("U".into(), "model:genuine:U".into())]);
        let context = context(&program, &hir, &declarations, &binders);
        let mut work = WorkLimit::new(65536);
        for name in [
            "keep_callback",
            "keep_array",
            "keep_record",
            "keep_node",
            "keep_generic",
        ] {
            let syntax = parameter(&program, name);
            let schema = original_header(&syntax, context, &mut work).unwrap();
            assert_eq!(schema.original(), syntax.hir_id);
            let (types, root) = schema.graph();
            assert!(
                types
                    .reachable([root], &mut work)
                    .unwrap()
                    .iter()
                    .any(|id| { matches!(types.get(*id).unwrap(), SourceNode::StaticValue(_)) })
            );
            if name == "keep_node" {
                assert!(schema.has_cycles(&mut work).unwrap());
                assert_eq!(
                    schema.key().unwrap_err(),
                    SourceTypesError::RecursiveLegacyKey
                );
            }
            if name == "keep_generic" {
                assert_eq!(
                    schema.binder_identities(&mut work).unwrap(),
                    std::collections::BTreeSet::from(["model:genuine:U".into()])
                );
            }
        }
        let first = original_header(&parameter(&program, "token_one"), context, &mut work).unwrap();
        let other = original_header(&parameter(&program, "token_two"), context, &mut work).unwrap();
        assert!(!first.equivalent(&other, &mut work).unwrap());
    }

    #[test]
    fn original_headers_reject_missing_or_replaced_declaration_identity_and_work() {
        let (program, hir, declarations) = fixture();
        let binders = BTreeMap::new();
        let syntax = parameter(&program, "token_one");
        assert!(matches!(
            original_header(
                &syntax,
                context(&program, &hir, &declarations, &binders),
                &mut WorkLimit::new(0)
            ),
            Err(SourceTypesError::BudgetExceeded)
        ));
        for mutation in 0..3 {
            let mut changed = program.clone();
            let mut changed_declarations = declarations.clone();
            match mutation {
                0 => changed_declarations.get_mut("Token").unwrap().name = "Other".into(),
                1 => changed.statements.retain(|statement| !matches!(&statement.kind, StmtKind::Type(declaration) if declaration.name == "Token")),
                _ => changed.statements.iter_mut().find(|statement| matches!(&statement.kind, StmtKind::Type(declaration) if declaration.name == "Token")).unwrap().hir_id = None,
            }
            assert!(
                original_header(
                    &syntax,
                    context(&changed, &hir, &changed_declarations, &binders),
                    &mut WorkLimit::new(16384)
                )
                .is_err()
            );
        }
        let other = parameter(&program, "token_two");
        for mutation in 0..4 {
            let mut changed = syntax.clone();
            let TypeKind::Name { arguments, .. } = &mut changed.kind else {
                unreachable!()
            };
            let TypeKind::Name {
                arguments: other_arguments,
                ..
            } = &other.kind
            else {
                unreachable!()
            };
            let TypeKind::Computation(expression) = &mut arguments[0].kind else {
                unreachable!()
            };
            let TypeKind::Computation(other_expression) = &other_arguments[0].kind else {
                unreachable!()
            };
            match mutation {
                0 => expression.kind = ExprKind::Literal(Literal::Integer("2".into())),
                1 => expression.hir_id = other_expression.hir_id,
                2 => arguments[0].hir_id = other_arguments[0].hir_id,
                _ => changed.hir_id = None,
            }
            assert!(
                original_header(
                    &changed,
                    context(&program, &hir, &declarations, &binders),
                    &mut WorkLimit::new(16384)
                )
                .is_err()
            );
        }
        let source = ril_test::case_source(
            "tests/regressions/source-transport.ril::nested-const-header-sort-conflict",
        );
        let mut bad = ril_syntax::parse(source).program;
        let bad_hir =
            hir::HirProgram::lower_identified(&mut bad, hir::InputOrigin::Source).unwrap();
        let bad_declarations = bad
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Type(declaration) => {
                    Some((declaration.name.clone(), declaration.clone()))
                }
                _ => None,
            })
            .collect();
        assert!(
            original_header(
                &parameter(&bad, "example"),
                context(&bad, &bad_hir, &bad_declarations, &binders),
                &mut WorkLimit::new(16384)
            )
            .is_err()
        );
    }

    #[test]
    fn constructor_instances_use_declared_sorts_and_keep_owner_and_payload_graphs() {
        let (program, hir, declarations) = fixture();
        let binders = BTreeMap::new();
        let context = context(&program, &hir, &declarations, &binders);
        let mut first = parameter(&program, "token_one");
        first.hir_id = None;
        let mut work = WorkLimit::new(65536);
        assert!(matches!(
            original_header(&first, context, &mut work),
            Err(SourceTypesError::MissingNode)
        ));
        let instance = constructor_instance(&first, context, &mut work).unwrap();
        let payload = instance.payloads["Token"].as_ref().unwrap();
        assert_eq!(instance.schema.original(), None);
        assert_eq!(
            payload.schema.original(),
            declarations["Token"].value.as_ref().unwrap().hir_id
        );
        assert!(
            payload
                .schema
                .equivalent_key(
                    &crate::sema::effect_identity::ArgumentKey::Name {
                        name: "int".into(),
                        arguments: vec![]
                    },
                    &mut work
                )
                .unwrap()
        );
        let other =
            constructor_instance(&parameter(&program, "token_two"), context, &mut work).unwrap();
        assert!(
            !instance
                .schema
                .equivalent(&other.schema, &mut work)
                .unwrap()
        );
        let mut changed = declarations.clone();
        changed.get_mut("Token").unwrap().name = "Other".into();
        assert!(
            constructor_instance(
                &first,
                super::tests::context(&program, &hir, &changed, &binders),
                &mut work
            )
            .is_err()
        );
        assert!(matches!(
            constructor_instance(&first, context, &mut WorkLimit::new(0)),
            Err(SourceTypesError::BudgetExceeded)
        ));
    }

    #[test]
    fn original_declaration_identity_does_not_depend_on_diagnostic_spans() {
        let (program, hir, declarations) = fixture();
        let binders = BTreeMap::new();
        let syntax = parameter(&program, "keep_node");
        let mut work = WorkLimit::new(65536);
        let original = original_header(
            &syntax,
            context(&program, &hir, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        let mut moved = declarations.clone();
        for declaration in moved.values_mut() {
            declaration.span.start = declaration.span.start.saturating_add(17);
            declaration.span.end = declaration.span.end.saturating_add(17);
            if let Some(value) = &mut declaration.value {
                value.span.start = value.span.start.saturating_add(29);
                value.span.end = value.span.end.saturating_add(29);
            }
        }
        let moved = original_header(
            &syntax,
            context(&program, &hir, &moved, &binders),
            &mut work,
        )
        .unwrap();
        assert!(original.equivalent(&moved, &mut work).unwrap());
        assert!(moved.has_cycles(&mut work).unwrap());
    }

    #[test]
    fn only_the_exact_standard_step_declaration_uses_the_catalog_instance_role() {
        let program = Program::default();
        let hir = hir::HirProgram::default();
        let declaration = crate::sema::model::iteration::step_declaration();
        let mut declarations = BTreeMap::from([(declaration.name.clone(), declaration.clone())]);
        let binders = BTreeMap::new();
        let scalar = |name: &str| TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Name {
                path: vec![name.into()],
                arguments: vec![],
            },
        };
        let syntax = TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Name {
                path: declaration.name.split("::").map(str::to_owned).collect(),
                arguments: vec![scalar("int"), scalar("str")],
            },
        };
        let mut work = WorkLimit::new(65536);
        let instance = constructor_instance(
            &syntax,
            context(&program, &hir, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        assert_eq!(
            instance
                .schema
                .opaque_arguments("Iter::Step", 2, &mut work)
                .unwrap()
                .unwrap()
                .len(),
            2
        );
        assert!(
            instance
                .payloads
                .values()
                .any(|payload| payload.as_ref().is_some_and(|payload| payload
                    .schema
                    .tuple_parts(&mut work)
                    .unwrap()
                    .is_some_and(|items| items.len() == 2)))
        );
        declarations.get_mut("Iter::Step").unwrap().span.start = 123;
        declarations.get_mut("Iter::Step").unwrap().span.end = 456;
        let relabeled = constructor_instance(
            &syntax,
            context(&program, &hir, &declarations, &binders),
            &mut work,
        )
        .unwrap();
        assert!(
            instance
                .schema
                .equivalent(&relabeled.schema, &mut work)
                .unwrap()
        );
        for mutation in 0..3 {
            let mut changed = declaration.clone();
            match mutation {
                0 => changed.generics[0].name = "Altered".into(),
                1 => changed.generics[0].bound = Some(scalar("int")),
                _ => changed.variants[1].payload = Some(scalar("int")),
            }
            declarations.insert("Iter::Step".into(), changed);
            assert!(
                constructor_instance(
                    &syntax,
                    context(&program, &hir, &declarations, &binders),
                    &mut work
                )
                .is_err()
            );
        }
        declarations.insert("Iter::Step".into(), declaration.clone());
        let source_owned = Program {
            statements: vec![Stmt {
                hir_id: None,
                span: declaration.span,
                kind: StmtKind::Type(declaration),
            }],
        };
        assert!(
            constructor_instance(
                &syntax,
                context(&source_owned, &hir, &declarations, &binders),
                &mut work
            )
            .is_err()
        );
    }
}
