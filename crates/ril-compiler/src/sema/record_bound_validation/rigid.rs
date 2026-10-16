//! Draft independent rigid declaration view. A source span can locate a type
//! subterm; its full key, real declaration/index, row and actual graph provide
//! the evidence.
use super::*;

impl Replay<'_> {
    pub(super) fn rigid_parameter_view(
        &self,
        definition: DefinitionId,
        parameter_index: u32,
        syntax: &TypeExpr,
        scope: &BoundScope,
        actual: &Value,
    ) -> Check<ArgumentKey> {
        let root = self
            .function(definition)?
            .syntax
            .parameters
            .get(parameter_index as usize)
            .and_then(|parameter| parameter.ty.as_ref())
            .ok_or_else(|| "rigid schema has no genuine source parameter".to_owned())?;
        require(
            scope == &self.scope(definition)?,
            "rigid schema borrowed another lexical type or residual scope",
        )?;
        let expected = self.normalized_key(syntax, scope)?;
        let ArgumentKey::Record {
            fields,
            row: Some(tail),
        } = &expected
        else {
            return Err("rigid schema source is not a real open record type".into());
        };
        let ArgumentKey::Binder {
            identity,
            sort: StaticBinderSort::Type,
        } = tail.as_ref()
        else {
            return Err("rigid schema tail has no genuine Type binder".into());
        };
        self.type_binder(identity)?;
        let mut pending = vec![(root, 0usize)];
        let mut work = 4096;
        let mut found = false;
        while let Some((source, depth)) = pending.pop() {
            require(
                depth < 64 && work > 0,
                "rigid source product walk exceeds replay budget",
            )?;
            work -= 1;
            match &source.kind {
                TypeKind::Tuple(items) => {
                    pending.extend(items.iter().map(|source| (source, depth + 1)))
                }
                TypeKind::Record { fields, row } => {
                    if row.is_some() && source.span == syntax.span {
                        require(
                            self.normalized_key(source, scope)? == expected,
                            "rigid declaration subterm has another complete field or row identity",
                        )?;
                        found = true;
                    }
                    pending.extend(fields.iter().map(|field| (&field.ty, depth + 1)));
                }
                _ => {}
            }
        }
        require(
            found,
            "rigid schema source is not an actual tuple/field subterm of its parameter",
        )?;
        let Ty::OpenRecord { fields: known, row } = &actual.ty else {
            return Err("rigid schema does not belong to an actual open record value".into());
        };
        require(
            known.len() == fields.len() && row.identity == RowIdentity::Binder(identity.clone()),
            "rigid schema changed the actual known field family or row identity",
        )?;
        for (name, mutable, key) in fields {
            let (actual_mutable, ty) = known.get(name).ok_or_else(|| {
                "rigid actual is missing an independently declared field".to_owned()
            })?;
            require(
                actual_mutable == mutable,
                "rigid actual changed a declared member's mutability",
            )?;
            self.ty_matches(ty, key, scope, 0)?;
        }
        Ok(expected)
    }
}
