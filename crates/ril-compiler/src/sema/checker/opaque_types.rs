//! Ordinary opacity limits source access, never the compiler's private graph.
use super::*;

impl Checker {
    /// Peel one public shell for private graph construction. Descendant opaque
    /// names stay intact so each recursively built value can retain its own
    /// public identity instead of exposing a nested representation to callers.
    pub(in crate::sema::checker) fn top_representation_type(&self, ty: &Ty) -> Option<Ty> {
        let (declaration, substitutions) = match ty {
            Ty::Named(name) => (self.types.get(name)?, BTreeMap::new()),
            Ty::Applied {
                constructor,
                arguments,
            } => {
                let declaration = self.types.get(constructor)?;
                if declaration.generics.len() != arguments.len() {
                    return None;
                }
                (
                    declaration,
                    declaration
                        .generics
                        .iter()
                        .zip(arguments)
                        .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
                        .collect(),
                )
            }
            _ => return None,
        };
        if declaration.nominal
            || !declaration.variants.is_empty()
            || (declaration.opaque && self.declaration_files.contains(&declaration.span.file.0))
        {
            return None;
        }
        Some(self.ty_substituted_shallow(declaration.value.as_ref()?, &substitutions))
    }

    /// A projection needs the receiver's outer shape, not normalized child
    /// types. A child keeps its own declared view and constructor identities.
    /// This is a runtime shape query; complete Source still comes from the
    /// original declaration and frozen environment.
    /// None means alias expansion exhausted its implementation allowance.
    pub(in crate::sema::checker) fn projection_shape_at(
        &self,
        ty: &Ty,
        file: FileId,
    ) -> Option<Ty> {
        let mut current = ty.clone();
        let mut seen = BTreeSet::new();
        for _ in 0..128 {
            if let Ty::Immutable(inner) = current {
                current = *inner;
                continue;
            }
            let name = match &current {
                Ty::Named(name) => name,
                Ty::Applied { constructor, .. } => constructor,
                _ => return Some(current),
            };
            if self
                .types
                .get(name)
                .is_some_and(|declaration| declaration.opaque && declaration.span.file != file)
                || !seen.insert(format!("{current:?}"))
            {
                return Some(current);
            }
            let Some(representation) = self.top_representation_type(&current) else {
                return Some(current);
            };
            current = representation;
        }
        match current {
            Ty::Named(_) | Ty::Applied { .. } | Ty::Immutable(_) => None,
            _ => Some(current),
        }
    }
    fn representation_in(
        &self,
        ty: &Ty,
        file: Option<FileId>,
        seen: &mut BTreeSet<String>,
        depth: usize,
    ) -> Ty {
        if depth >= 128 {
            return ty.clone();
        }
        let declaration = match ty {
            Ty::Named(name) => self
                .types
                .get(name)
                .map(|declaration| (declaration, BTreeMap::new())),
            Ty::Applied {
                constructor,
                arguments,
            } => self
                .types
                .get(constructor)
                .filter(|declaration| declaration.generics.len() == arguments.len())
                .map(|declaration| {
                    (
                        declaration,
                        declaration
                            .generics
                            .iter()
                            .zip(arguments)
                            .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
                            .collect(),
                    )
                }),
            _ => None,
        };
        if let Some((declaration, substitutions)) = declaration
            && !declaration.nominal
            && declaration.variants.is_empty()
            && (!declaration.opaque || !self.declaration_files.contains(&declaration.span.file.0))
            && (!declaration.opaque || file.is_none_or(|file| file == declaration.span.file))
            && let Some(body) = &declaration.value
            && seen.insert(format!("{ty:?}"))
        {
            let representation = self.ty_substituted(body, &mut BTreeSet::new(), &substitutions);
            return self.representation_in(&representation, file, seen, depth + 1);
        }
        let child =
            |ty: &Ty| Box::new(self.representation_in(ty, file, &mut seen.clone(), depth + 1));
        match ty {
            Ty::Immutable(inner) => Ty::Immutable(child(inner)),
            Ty::Optional(inner) => Ty::Optional(child(inner)),
            Ty::Array(inner) => Ty::Array(child(inner)),
            Ty::Set(inner) => Ty::Set(child(inner)),
            Ty::Range(inner) => Ty::Range(child(inner)),
            Ty::Result(a, b) => Ty::Result(child(a), child(b)),
            Ty::Map(a, b) => Ty::Map(child(a), child(b)),
            Ty::Tuple(items) => Ty::Tuple(items.iter().map(|ty| *child(ty)).collect()),
            Ty::Record(fields) => Ty::Record(
                fields
                    .iter()
                    .map(|(name, (mutable, ty))| (name.clone(), (*mutable, *child(ty))))
                    .collect(),
            ),
            Ty::OpenRecord { fields, row } => Ty::OpenRecord {
                fields: fields
                    .iter()
                    .map(|(name, (mutable, ty))| (name.clone(), (*mutable, *child(ty))))
                    .collect(),
                row: row.clone(),
            },
            Ty::Callable(parameters, result) => Ty::Callable(
                parameters.iter().map(|ty| *child(ty)).collect(),
                child(result),
            ),
            _ => ty.clone(),
        }
    }

    /// Only operations written in the defining source file see an ordinary
    /// opaque representation. Keep immutable qualifiers for authority checks.
    pub(in crate::sema::checker) fn representation_at(&self, ty: &Ty, file: FileId) -> Ty {
        self.representation_in(ty, Some(file), &mut BTreeSet::new(), 0)
    }

    /// This is compiler-private shape information, not source access permission.
    /// Foreign declarations retain their uninterpreted identities.
    pub(in crate::sema::checker) fn representation_graph_type(&self, ty: &Ty) -> Ty {
        self.representation_in(ty, None, &mut BTreeSet::new(), 0)
    }

    pub(in crate::sema::checker) fn expanded_at(&self, ty: &Ty, file: FileId) -> Ty {
        self.expanded(&self.representation_at(ty, file), &mut BTreeSet::new())
    }

    pub(in crate::sema::checker) fn compatible_at(
        &self,
        actual: &Ty,
        expected: &Ty,
        file: FileId,
    ) -> bool {
        self.compatible(
            &self.representation_at(actual, file),
            &self.representation_at(expected, file),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn shallow_row_aliases_expand_the_outer_fields_and_preserve_named_children() {
        let parsed = ril_syntax::parse(
            "type Packet={values:[0][2]int}\ntype Inner<R>={child:Packet,..R}\ntype Outer<R>={flag:bool,..Inner<R>}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        let row = Ty::Record([("label".into(), (true, Ty::Str))].into());
        let applied = Ty::Applied {
            constructor: "Outer".into(),
            arguments: vec![TypeArgument::Type(Box::new(row))],
        };
        assert_eq!(
            checker.top_representation_type(&applied),
            Some(Ty::Record(
                [
                    ("flag".into(), (false, Ty::Bool)),
                    ("child".into(), (false, Ty::Named("Packet".into()))),
                    ("label".into(), (true, Ty::Str)),
                ]
                .into()
            ))
        );
    }
    #[test]
    fn graph_peeling_preserves_nested_public_names_and_source_visibility() {
        let owner = FileId(7);
        let parsed = ril_syntax::parse_file(
            "opaque type Cell={mut count:int}\nopaque type Holder={child:Cell}\nopaque type Frozen=Immut<{mut count:int}>",
            owner,
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            let StmtKind::Type(declaration) = &statement.kind else {
                panic!()
            };
            checker
                .types
                .insert(declaration.name.clone(), declaration.clone());
        }
        let cell = Ty::Named("Cell".into());
        let holder = Ty::Named("Holder".into());
        let count = Ty::Record([("count".into(), (true, Ty::Int("int".into())))].into());
        assert_eq!(
            checker.top_representation_type(&holder),
            Some(Ty::Record([("child".into(), (false, cell.clone()))].into()))
        );
        assert_eq!(checker.representation_at(&cell, FileId(0)), cell);
        assert_eq!(
            checker.projection_shape_at(&holder, FileId(0)),
            Some(holder.clone())
        );
        assert_eq!(
            checker.projection_shape_at(&holder, owner),
            Some(Ty::Record([("child".into(), (false, cell.clone()))].into()))
        );
        assert_eq!(checker.representation_at(&cell, owner), count);
        assert!(!checker.compatible_at(&cell, &count, FileId(0)));
        assert!(checker.compatible_at(&cell, &count, owner));
        assert_eq!(
            checker.representation_graph_type(&holder),
            Ty::Record([("child".into(), (false, count.clone()))].into())
        );
        assert_eq!(
            checker.representation_at(&Ty::Named("Frozen".into()), owner),
            Ty::Immutable(Box::new(count))
        );
    }

    #[test]
    fn projection_shapes_keep_optional_alias_and_generic_child_views() {
        let owner = FileId(7);
        let source = ril_test::case_source(
            "tests/regressions/projection-views.ril::optional-child-views-pointer64",
        );
        let parsed = ril_syntax::parse_file(source, owner);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        let packet = Ty::Named("Packet".into());
        let optional = Ty::Optional(Box::new(packet.clone()));
        let envelope = Ty::Record([("packet".into(), (false, optional.clone()))].into());
        let pair = Ty::Tuple(vec![optional.clone(), Ty::Bool]);
        assert_eq!(
            checker.top_representation_type(&Ty::Named("Envelope".into())),
            Some(envelope.clone())
        );
        for (input, expected) in [
            (Ty::Named("Envelope".into()), envelope.clone()),
            (Ty::Named("Pair".into()), pair.clone()),
            (pair.clone(), pair),
            (
                Ty::Applied {
                    constructor: "Wrap".into(),
                    arguments: vec![TypeArgument::Type(Box::new(packet))],
                },
                envelope.clone(),
            ),
            (
                Ty::Immutable(Box::new(Ty::Named("Envelope".into()))),
                envelope,
            ),
            (
                Ty::Array(Box::new(optional.clone())),
                Ty::Array(Box::new(optional)),
            ),
        ] {
            assert_eq!(checker.projection_shape_at(&input, owner), Some(expected));
        }
        let template = checker.types["Packet"].clone();
        for index in 0..128 {
            let mut alias = template.clone();
            alias.name = format!("Alias{index}");
            alias.value = Some(TypeExpr {
                hir_id: None,
                text: String::new(),
                span: template.span,
                kind: TypeKind::Name {
                    path: vec![if index == 127 {
                        "Packet".into()
                    } else {
                        format!("Alias{}", index + 1)
                    }],
                    arguments: vec![],
                },
            });
            checker.types.insert(alias.name.clone(), alias);
        }
        assert_eq!(
            checker.projection_shape_at(&Ty::Named("Alias0".into()), owner),
            None,
            "exhausted expansion must remain an implementation limit"
        );
        assert_eq!(
            checker.projection_shape_at(&Ty::Named("Alias1".into()), owner),
            checker.top_representation_type(&Ty::Named("Packet".into()))
        );
        let Some(TypeExpr {
            kind: TypeKind::Name { path, .. },
            ..
        }) = &mut checker.types.get_mut("Alias127").unwrap().value
        else {
            panic!()
        };
        *path = vec!["Alias126".into()];
        assert_eq!(
            checker.projection_shape_at(&Ty::Named("Alias126".into()), owner),
            Some(Ty::Named("Alias126".into())),
            "an alias cycle must stop without inventing a structural shape"
        );
    }
}
