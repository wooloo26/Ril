//! Type variables occurring in a structural promise are ordinary constraints.
//! Selection discovers their complete member schemas; the shared row solver
//! still validates every promise before any application can be accepted.
use super::*;
use crate::sema::model::rows::{Row, RowTail};

impl Typer<'_> {
    pub(super) fn infer_bound_type_dependencies(
        &self,
        function: &Function,
        caller: &bounds::BoundEnvironment,
        scope: &mut bounds::BoundEnvironment,
    ) -> Result<()> {
        let parameters = function
            .generics
            .iter()
            .filter_map(|parameter| scope.type_binders.get(&parameter.name).cloned())
            .collect::<Vec<_>>();
        // Each productive round selects at least one previously unselected
        // declared binder. Existing selections are checked, never replaced.
        for _ in 0..=parameters.len() {
            let before = scope.type_arguments.len();
            for id in &parameters {
                self.schema_work.work(1)?;
                if !scope.type_arguments.contains_key(id) {
                    continue;
                }
                let Some(view) = scope.views.get(id).cloned() else {
                    continue;
                };
                let actual = self.actual_bound_shape(id, scope, caller)?;
                for (name, required) in &view.fields {
                    let (mutable, field) = actual.fields.get(name).ok_or_else(|| {
                        Failure::Diagnostic(
                            "E0301",
                            "static argument is missing a required bounded member".into(),
                        )
                    })?;
                    if *mutable != required.mutable {
                        return Err(Failure::Diagnostic(
                            "E0301",
                            "static argument has a different bounded member slot declaration"
                                .into(),
                        ));
                    }
                    let actual_type = self.bound_type(&field.syntax, caller)?;
                    let schema = self.complete_source_syntax(&field.syntax, caller)?;
                    self.infer_application_type(
                        &required.syntax,
                        &actual_type,
                        schema,
                        ApplicationInference {
                            caller,
                            declaration: &function.name,
                        },
                        scope,
                        0,
                    )?;
                }
                // A declared Type binder used as a residual is another type
                // constraint. Discovering a closed candidate here lets its own
                // promised members select further binders. Row entailment below
                // remains responsible for consistency and the shared lacks set.
                let Some(row_id) = &view.row else {
                    continue;
                };
                let Some(declared) = scope.rows[row_id].declared_type.clone() else {
                    continue;
                };
                if declared.declaration != function.name {
                    continue;
                }
                let residual = Row {
                    fields: actual
                        .fields
                        .into_iter()
                        .filter(|(name, _)| !view.fields.contains_key(name))
                        .collect(),
                    tail: actual.tail,
                };
                match &residual.tail {
                    RowTail::Closed => {
                        let syntax = row_syntax(&residual, function.span)?;
                        let schema = self.complete_source_syntax(&syntax, caller)?;
                        let ty = self.bound_type(&syntax, caller)?;
                        self.select_type_argument(&declared, &ty, schema, caller, scope)?;
                    }
                    RowTail::Open(tail) if residual.fields.is_empty() => {
                        // An exact caller residual can be forwarded under its
                        // registered Type identity. A composite open row has no
                        // such identity and must not masquerade as a closed T.
                        let Some(actual) = caller
                            .rows
                            .values()
                            .find(|row| row.identity == tail.identity)
                            .and_then(|row| row.declared_type.as_ref())
                        else {
                            continue;
                        };
                        let ty = Ty::Generic(actual.key());
                        let schema = caller.selected_types.get(actual).cloned();
                        self.select_type_argument(&declared, &ty, schema, caller, scope)?;
                    }
                    _ => {}
                }
            }
            if scope.type_arguments.len() == before {
                return Ok(());
            }
        }
        Err(Failure::Unsupported(
            "static bound dependency selection did not reach its finite fixed point".into(),
        ))
    }
}
