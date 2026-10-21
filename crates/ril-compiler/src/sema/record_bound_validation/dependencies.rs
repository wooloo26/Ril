//! Independent reconstruction of an open dependent Type selection. The
//! producer's substitution is the proposition, never its own source proof.
use super::*;

fn equation(
    formal: &ArgumentKey,
    actual: &ArgumentKey,
    binder: &str,
    found: &mut Vec<ArgumentKey>,
    work: &mut usize,
    depth: usize,
) -> Check {
    require(
        *work > 0 && depth < 64,
        "bound input equation exceeds replay allowance",
    )?;
    *work -= 1;
    if matches!(formal, ArgumentKey::Binder { identity, sort: StaticBinderSort::Type }
        if identity == binder)
    {
        found.push(actual.clone());
        return Ok(());
    }
    if formal == actual {
        return Ok(());
    }
    let mut child = |formal, actual| equation(formal, actual, binder, found, work, depth + 1);
    match (formal, actual) {
        (
            ArgumentKey::Array {
                length: a,
                element: f,
            },
            ArgumentKey::Array {
                length: b,
                element: v,
            },
        ) if a == b => child(f, v),
        (ArgumentKey::Tuple(a), ArgumentKey::Tuple(b)) if a.len() == b.len() => {
            for (a, b) in a.iter().zip(b) {
                child(a, b)?;
            }
            Ok(())
        }
        (ArgumentKey::Map { key: a, value: b }, ArgumentKey::Map { key: c, value: d }) => {
            child(a, c)?;
            child(b, d)
        }
        (
            ArgumentKey::Name {
                name: a,
                arguments: f,
            },
            ArgumentKey::Name {
                name: b,
                arguments: v,
            },
        ) if a == b && f.len() == v.len() => {
            for (f, v) in f.iter().zip(v) {
                child(f, v)?;
            }
            Ok(())
        }
        (
            ArgumentKey::Callable {
                parameters: a,
                result: f,
                annotations: x,
            },
            ArgumentKey::Callable {
                parameters: b,
                result: v,
                annotations: y,
            },
        ) if a.len() == b.len() && x == y => {
            for ((am, f), (bm, v)) in a.iter().zip(b) {
                require(am == bm, "bound input equation erased a callable mode")?;
                child(f, v)?;
            }
            child(f, v)
        }
        (
            ArgumentKey::Record {
                fields: a,
                row: None,
            },
            ArgumentKey::Record {
                fields: b,
                row: None,
            },
        ) if a.len() == b.len() => {
            for (name, mode, f) in a {
                let (_, other_mode, v) = b
                    .iter()
                    .find(|(label, _, _)| label == name)
                    .ok_or_else(|| "bound input equation replaced a record label".to_owned())?;
                require(
                    mode == other_mode,
                    "bound input equation erased member mutability",
                )?;
                child(f, v)?;
            }
            Ok(())
        }
        _ => Err("bound input equation lacks matching complete source coordinates".into()),
    }
}

impl Replay<'_> {
    pub(super) fn dependent_input_selection(
        &self,
        check: &GenericBoundCheck,
        bound: &GenericRecordBound,
        binder: &str,
        selected: &ArgumentKey,
    ) -> Check<bool> {
        let ArgumentKey::Binder {
            identity: caller,
            sort: StaticBinderSort::Type,
        } = selected
        else {
            return Ok(false);
        };
        let Some(declaration) = self.facts.generic_binders.get(binder) else {
            return Ok(false);
        };
        if declaration.definition != bound.definition || binder == bound.binder {
            return Ok(false);
        }
        let generic = self
            .function(bound.definition)?
            .syntax
            .generics
            .get(declaration.index as usize)
            .ok_or_else(|| "dependent input binder has no real generic header".to_owned())?;
        if !generic.bound.as_ref().is_none_or(|bound| {
            matches!(&bound.kind, TypeKind::Name { path, arguments }
                if path == &["Type"] && arguments.is_empty())
        }) {
            return Ok(false);
        }
        if self.facts.bound_rows.iter().any(|row| row.definition == bound.definition
            && matches!(&row.role, BoundRowRole::DeclaredTypeParameter { binder: row } if row == binder)) {
            return Ok(false);
        }
        self.type_binder(binder)?;
        self.type_binder(caller)?;
        require(
            self.facts.generic_binders[caller].definition != bound.definition,
            "dependent input attempted to solve a caller with its own callee binder",
        )?;
        if !matches!(
            check.actual_schema.source,
            StructuralSchemaSource::RigidParameter { .. }
        ) {
            return Ok(false);
        }
        let identities: Vec<_> = self
            .facts
            .scoped_source_identities
            .iter()
            .filter(|source| source.required == bound.id && source.context == check.context)
            .collect();
        require(
            identities.len() == 1,
            "dependent input has no unique full original source",
        )?;
        // This stage checks real header/owner/ancestry, whole entry arity, every
        // material T path and exact epochs. It never calls schema/application
        // replay; the mandatory storage/shape check remains later in the pass.
        let _received = self.scoped_original_formal(identities[0])?;
        let source = identities[0];
        require(
            source
                .typing_environment
                .generic_context
                .values()
                .any(|id| id == caller),
            "dependent input selected a binder outside its original header namespace",
        )?;
        let ArgumentKey::Record { fields, .. } = &source.key else {
            return Err("dependent input has no complete original member family".into());
        };
        let substitutions: BTreeMap<_, _> = check
            .substitutions
            .iter()
            .filter(|(id, _)| id.as_str() != binder)
            .map(|(id, key)| (id.clone(), key.clone()))
            .collect();
        let mut found = Vec::new();
        let mut work = 4096;
        for field in &bound.fields {
            let (_, mutable, actual) = fields
                .iter()
                .find(|(name, _, _)| name == &field.label)
                .ok_or_else(|| "dependent input lost its original promised field".to_owned())?;
            require(
                *mutable == field.mutable,
                "dependent input changed a source member mode",
            )?;
            let formal = select_key(&field.key, &substitutions, 0)?;
            equation(&formal, actual, binder, &mut found, &mut work, 0)?;
        }
        require(
            !found.is_empty() && found.iter().all(|actual| actual == selected),
            "dependent input selected another real binder or inconsistent U occurrences",
        )?;
        for other in self
            .facts
            .generic_bound_checks
            .iter()
            .filter(|other| other.context == check.context)
        {
            if let Some(key) = other.substitutions.get(binder) {
                require(
                    key == selected,
                    "one actual invocation changed a shared dependent Type selection",
                )?;
            }
        }
        Ok(true)
    }
}
