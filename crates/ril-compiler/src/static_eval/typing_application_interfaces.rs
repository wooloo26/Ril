//! Interface transport is a value summary, separate from canonical Type
//! selection. Rechecking a template with ordinary types derives callable label
//! and default alternatives without executing it or granting body obligations.
use super::*;

impl Typer<'_> {
    pub(super) fn application_return_interface(
        &self,
        function: &Function,
        scope: &bounds::BoundEnvironment,
        actual: &[Ty],
        plan: &application::StaticApplicationPlan,
        declared: &Ty,
    ) -> Result<Ty> {
        if !contains_callable_type(declared) {
            return Ok(declared.clone());
        }
        if !self
            .interface_applications
            .borrow_mut()
            .insert(function.name.clone())
        {
            return Err(Failure::Unsupported(
                "recursive static callable-interface summary needs a fixed point".into(),
            ));
        }
        let result = (|| {
            clone_work::function(&self.schema_work, function)?;
            let mut checker = self.child(Some(declared.clone()));
            checker.bound_environment = Some(std::sync::Arc::new(scope.clone()));
            checker.return_context = function
                .return_type
                .as_ref()
                .map(|syntax| checker.result_context(syntax, scope))
                .transpose()?;
            let mut env = scope.values.clone();
            for (parameter, slot) in function.parameters.iter().zip(&plan.slots) {
                let syntax = parameter.ty.as_ref().ok_or_else(|| {
                    Failure::Unsupported("static interface formal has no type".into())
                })?;
                let formal = checker.bound_type(syntax, scope)?;
                let actual = match slot {
                    application::ArgumentSlot::Explicit(index) => actual[*index].clone(),
                    application::ArgumentSlot::Default => parameter
                        .default
                        .as_ref()
                        .map(|expression| {
                            let context = checker.result_context(syntax, scope)?;
                            checker.expr_result_expected(
                                expression,
                                &mut env,
                                Some(&formal),
                                Some(&context),
                            )
                        })
                        .transpose()?
                        .unwrap_or_else(|| formal.clone()),
                };
                let received = checker.receive_type_interfaces(actual, syntax, &formal, scope)?;
                checker.bind(&parameter.pattern, erase_constants(received), &mut env)?;
                let schema = checker.complete_source_syntax(syntax, scope)?;
                checker.bind_source_schema(&parameter.pattern, schema)?;
            }
            let Some(body) = &function.body else {
                return Ok(declared.clone());
            };
            let body = record_contexts::block(body, function.return_type.as_ref());
            let actual = checker.block_result_expected(
                &body,
                &mut env,
                Some(declared),
                checker.return_context.as_ref(),
            )?;
            let actual = checker.callable_result(actual)?;
            let Some(source) = &function.return_type else {
                return Ok(declared.clone());
            };
            checker.receive_type_interfaces(actual, source, declared, scope)
        })();
        self.interface_applications
            .borrow_mut()
            .remove(&function.name);
        result
    }

    pub(super) fn receive_type_interfaces(
        &self,
        actual: Ty,
        source: &TypeExpr,
        declared: &Ty,
        scope: &bounds::BoundEnvironment,
    ) -> Result<Ty> {
        let mask = generic_receiving::for_types(
            source,
            &scope.type_binders,
            &self.evaluator.declarations,
            self.evaluator.layout,
            &self.schema_work,
        )?;
        Ok(receive(
            actual,
            declared,
            mask.as_ref().map(|mask| (&mask.syntax, &mask.markers)),
            0,
        ))
    }
}

fn receive(
    actual: Ty,
    declared: &Ty,
    mask: Option<(&TypeExpr, &BTreeSet<String>)>,
    depth: usize,
) -> Ty {
    if depth >= 64 {
        return declared.clone();
    }
    let mask = generic_receiving::transparent(mask);
    if let Some((
        TypeExpr {
            kind: TypeKind::Name { path, arguments },
            ..
        },
        markers,
    )) = mask
        && path.len() == 1
        && arguments.is_empty()
        && markers.contains(&path[0])
    {
        return with_interfaces(declared.clone(), &actual);
    }
    use generic_receiving::{Slot, child};
    match (actual, declared) {
        (Ty::Array(actual, _), Ty::Array(declared, length)) => Ty::Array(
            Box::new(receive(
                *actual,
                declared,
                child(mask, Slot::Element),
                depth + 1,
            )),
            *length,
        ),
        (Ty::Optional(actual), Ty::Optional(declared)) => Ty::Optional(Box::new(receive(
            *actual,
            declared,
            child(mask, Slot::Optional),
            depth + 1,
        ))),
        (Ty::Tuple(actual), Ty::Tuple(declared)) if actual.len() == declared.len() => Ty::Tuple(
            actual
                .into_iter()
                .zip(declared)
                .enumerate()
                .map(|(index, (a, d))| receive(a, d, child(mask, Slot::Tuple(index)), depth + 1))
                .collect(),
        ),
        (Ty::Record(mut actual), Ty::Record(declared)) => Ty::Record(
            declared
                .iter()
                .map(|(name, (mutable, declared))| {
                    let actual = actual
                        .remove(name)
                        .map_or_else(|| declared.clone(), |(_, ty)| ty);
                    (
                        name.clone(),
                        (
                            *mutable,
                            receive(actual, declared, child(mask, Slot::Field(name)), depth + 1),
                        ),
                    )
                })
                .collect(),
        ),
        (Ty::Map(ak, av), Ty::Map(dk, dv)) => Ty::Map(
            Box::new(receive(*ak, dk, child(mask, Slot::MapKey), depth + 1)),
            Box::new(receive(*av, dv, child(mask, Slot::MapValue), depth + 1)),
        ),
        (Ty::Result(ak, ae), Ty::Result(dk, de)) => Ty::Result(
            Box::new(receive(*ak, dk, child(mask, Slot::Success), depth + 1)),
            Box::new(receive(*ae, de, child(mask, Slot::Error), depth + 1)),
        ),
        _ => declared.clone(),
    }
}
