//! Declaration promises guide fresh constructors. Stored expressions retain
//! their own types, slot declarations and numeric selections.
use super::*;

impl Typer<'_> {
    pub(super) fn application_argument_context(
        &self,
        source: &TypeExpr,
        ordinary: Ty,
        scope: &bounds::BoundEnvironment,
    ) -> Result<Ty> {
        if matches!(ordinary, Ty::Record(_)) {
            return Ok(ordinary);
        }
        let TypeKind::Name { path, arguments } = &source.kind else {
            return Ok(ordinary);
        };
        if path.len() != 1 || !arguments.is_empty() {
            return Ok(ordinary);
        }
        let Some(view) = scope
            .type_binders
            .get(&path[0])
            .and_then(|id| scope.views.get(id))
        else {
            return Ok(ordinary);
        };
        Ok(Ty::Record(
            view.fields
                .iter()
                .map(|(name, field)| {
                    Ok((
                        name.clone(),
                        (field.mutable, self.bound_type(&field.syntax, scope)?),
                    ))
                })
                .collect::<Result<_>>()?,
        ))
    }
}

pub(super) fn receive_fresh_record_modes(
    fields: &mut BTreeMap<String, (bool, Ty)>,
    context: Option<&Ty>,
) {
    if let Some(Ty::Record(required)) = context {
        for (name, (mutable, _)) in fields {
            if let Some((required, _)) = required.get(name) {
                *mutable = *required;
            }
        }
    }
}
