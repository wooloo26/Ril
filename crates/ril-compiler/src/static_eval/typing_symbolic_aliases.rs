//! Pure alias expansion used only to expose inference structure. Synthetic
//! nominal declarations stand for registered lexical Type identities. The
//! result is symbolic syntax, never a closed source witness or permission fact.
use super::*;

pub(in crate::static_eval::typing) struct SymbolicAliasSyntax {
    pub(in crate::static_eval::typing) syntax: TypeExpr,
}

impl Typer<'_> {
    pub(in crate::static_eval::typing) fn symbolic_alias_syntax(
        &self,
        source: &TypeExpr,
        scope: &bounds::BoundEnvironment,
    ) -> Result<Option<SymbolicAliasSyntax>> {
        fn contains_alias(
            checker: &Typer<'_>,
            source: &TypeExpr,
            scope: &bounds::BoundEnvironment,
            depth: usize,
            nodes: &mut usize,
        ) -> Result<bool> {
            *nodes += 1;
            checker.schema_work.work(1)?;
            if depth >= 64 || *nodes > 4096 {
                return Err(Failure::Unsupported(
                    "static symbolic alias discovery exceeds its finite traversal allowance".into(),
                ));
            }
            let mut child = |source| contains_alias(checker, source, scope, depth + 1, nodes);
            match &source.kind {
                TypeKind::Name { path, arguments } => {
                    let is_binder = path.len() == 1
                        && (scope.type_binders.contains_key(&path[0])
                            || scope.type_ids.contains_key(&path[0]));
                    let full_name = path.join("::");
                    let name = normalized_path(path);
                    if !is_binder
                        && checker
                            .evaluator
                            .declarations
                            .get(&full_name)
                            .or_else(|| checker.evaluator.declarations.get(&name))
                            .is_some_and(|alias| {
                                !alias.nominal
                                    && !alias.opaque
                                    && alias.variants.is_empty()
                                    && alias.value.is_some()
                            })
                    {
                        return Ok(true);
                    }
                    for argument in arguments {
                        if child(argument)? {
                            return Ok(true);
                        }
                    }
                }
                TypeKind::Tuple(items) => {
                    for item in items {
                        if child(item)? {
                            return Ok(true);
                        }
                    }
                }
                TypeKind::Array { element, .. } | TypeKind::Optional(element) => {
                    return child(element);
                }
                TypeKind::Map { key, value } => return Ok(child(key)? || child(value)?),
                TypeKind::Record { fields, row } => {
                    for field in fields {
                        if child(&field.ty)? {
                            return Ok(true);
                        }
                    }
                    if let Some(row) = row {
                        return child(row);
                    }
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    for parameter in parameters {
                        if let Some(ty) = &parameter.ty
                            && child(ty)?
                        {
                            return Ok(true);
                        }
                    }
                    if let Some(result) = result {
                        return child(result);
                    }
                }
                _ => {}
            }
            Ok(false)
        }
        if !contains_alias(self, source, scope, 0, &mut 0)? {
            return Ok(None);
        }
        scope.admit_with_types(&self.schema_work, &[])?;
        // Expose the alias's structure under genuine lexical identities. Its
        // selected callable interface belongs to the application/value, not to
        // this normalization input. Substituting closed selections here can
        // accidentally feed invocation descriptors into pure type expansion.
        let mut symbols = scope.clone();
        symbols.selected_types.clear();
        symbols.selected_rows.clear();
        symbols.row_arguments.clear();
        symbols
            .type_arguments
            .retain(|_, selected| matches!(selected, Ty::Generic(_)));
        let source = self.scoped_source_syntax(source, &symbols)?;
        let mut declarations = BTreeMap::new();
        for (name, declaration) in &self.evaluator.declarations {
            self.schema_work.work(name.len() as u64 + 1)?;
            for syntax in declaration
                .value
                .iter()
                .chain(
                    declaration
                        .generics
                        .iter()
                        .flat_map(|parameter| parameter.bound.iter().chain(&parameter.default)),
                )
                .chain(
                    declaration
                        .variants
                        .iter()
                        .flat_map(|variant| variant.payload.iter().chain(&variant.result)),
                )
            {
                clone_work::type_syntax(&self.schema_work, syntax)?;
            }
            // A declaration's free names belong to its own lexical context.
            // Do not rewrite them using the currently applying callee's names.
            // Without a captured alias context the normalizer can only refuse
            // an otherwise unresolved free name.
            declarations.insert(name.clone(), declaration.clone());
        }
        let mut registered = BTreeSet::new();
        for id in scope.type_ids.values() {
            let identity = id.key();
            self.schema_work.work(identity.len() as u64 + 1)?;
            if !registered.insert(identity.clone()) {
                continue;
            }
            if declarations.contains_key(&identity) {
                return Err(Failure::Unsupported(
                    "a static symbolic Type identity collides with a source declaration".into(),
                ));
            }
            declarations.insert(
                identity.clone(),
                TypeDeclaration {
                    name: identity,
                    visibility: Visibility::Private,
                    is_halt: false,
                    generics: vec![],
                    value: None,
                    variants: vec![],
                    opaque: true,
                    nominal: true,
                    span: source.span,
                },
            );
        }
        let syntax = crate::sema::checker::normalize_closed_source_syntax(
            &source,
            &declarations,
            self.evaluator.layout,
        )
        .ok_or_else(|| {
            Failure::Unsupported(
                "static generic alias inference needs a pure lexical expansion".into(),
            )
        })?;
        Ok(Some(SymbolicAliasSyntax { syntax }))
    }
}
