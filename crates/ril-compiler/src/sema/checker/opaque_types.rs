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
        Some(self.ty_substituted(
            declaration.value.as_ref()?,
            &mut BTreeSet::new(),
            &substitutions,
        ))
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
}
