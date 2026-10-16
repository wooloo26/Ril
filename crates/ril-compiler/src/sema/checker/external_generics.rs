//! Concrete foreign instances still use ordinary named invocation checking.
//! Record static arguments even when absent from all run-time value types.
use super::*;

impl Checker {
    pub(super) fn external_generic(
        &mut self,
        value: &mut Value,
        arguments: &[TypeExpr],
        span: Span,
    ) -> bool {
        let [Callable::Named(id)] = value.callables.as_slice() else {
            return false;
        };
        let original = self.functions[*id].clone();
        let function = &original.syntax;
        if function.body.is_some() || !self.declaration_files.contains(&function.span.file.0) {
            return false;
        }
        if function.generics.is_empty() {
            self.error(
                "E0340",
                span,
                "foreign callable has no static parameters",
                [value.cause],
            );
            return true;
        }
        let scalar = |name: &str| {
            matches!(
                name,
                "int"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "u8"
                    | "u16"
                    | "u32"
                    | "u64"
                    | "bigint"
                    | "bool"
                    | "str"
                    | "bytes"
                    | "f32"
                    | "f64"
            )
        };
        if function.generics.iter().any(|parameter| {
                if parameter.name.chars().next().is_some_and(char::is_lowercase) {
                    !matches!(parameter.bound.as_ref().map(|bound|&bound.kind),Some(TypeKind::Name{path,arguments})if arguments.is_empty()&&scalar(&path.join("::")))
                } else {
                    parameter.bound.as_ref().is_some_and(|bound| !matches!(&bound.kind,TypeKind::Name{path,arguments}if path==&["Type"]&&arguments.is_empty()))
                }
            })
            || function.annotations.iter().any(|annotation|annotation.text.split(|character:char|!character.is_alphanumeric()&&character!='_').any(|token|function.generics.iter().any(|parameter|parameter.name==token)))
        {
            self.unsupported(span,"foreign effect/capability arguments or constrained type binders need a complete instantiated contract");
            return true;
        }
        let template = TypeDeclaration {
            visibility: function.visibility,
            is_halt: false,
            name: function.name.clone(),
            generics: function.generics.clone(),
            value: Some(TypeExpr {
                hir_id: None,
                text: String::new(),
                kind: TypeKind::Callable {
                    parameters: function.parameters.clone(),
                    result: function.return_type.clone().map(Box::new),
                    annotations: function.annotations.clone(),
                },
                span: function.span,
            }),
            variants: vec![],
            opaque: false,
            nominal: true,
            span: function.span,
        };
        let normalized = match crate::static_eval::normalize_constructor_arguments(
            &template,
            arguments,
            &self.types,
            self.layout,
        ) {
            Ok(normalized) => normalized,
            Err(crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message)) => {
                self.error(code, span, message, [value.cause]);
                return true;
            }
            Err(crate::static_eval::ArgumentNormalizationError::Unsupported(message)) => {
                self.unsupported(span, message);
                return true;
            }
        };
        for argument in &normalized.arguments {
            if matches!(argument.kind, TypeKind::Computation(_))
                && crate::static_eval::foreign::scalar(argument, &self.types, self.layout).is_err()
            {
                self.unsupported(
                    span,
                    "foreign static argument requires a concrete scalar value contract",
                );
                return true;
            }
        }
        let arguments: Vec<_> = function
            .generics
            .iter()
            .zip(normalized.arguments)
            .map(|(parameter, argument)| (parameter.name.clone(), argument))
            .collect();
        let key: Vec<_> = arguments
            .iter()
            .map(|(_, argument)| crate::static_eval::normalized_argument_key(argument))
            .collect();
        let existing = self.external_instances.iter().position(|instance| {
            instance.declaration_name == function.name
                && instance
                    .arguments
                    .iter()
                    .map(|(_, argument)| crate::static_eval::normalized_argument_key(argument))
                    .collect::<Vec<_>>()
                    == key
        });
        let instance = if let Some(index) = existing {
            index
        } else {
            let Some(Some(TypeExpr {
                kind:
                    TypeKind::Callable {
                        parameters, result, ..
                    },
                ..
            })) = normalized.payloads.get(&function.name)
            else {
                self.unsupported(
                    span,
                    "foreign static signature has no normalized callable witness",
                );
                return true;
            };
            let mut concrete = function.clone();
            concrete.name = format!(
                "{}\0foreign.instance.{}",
                function.name,
                self.external_instances.len()
            );
            concrete.generics.clear();
            concrete.parameters = parameters.clone();
            let static_arguments: Vec<_> = arguments
                .iter()
                .map(|(_, argument)| argument.clone())
                .collect();
            if let Err(error) = crate::static_eval::foreign::instantiate_defaults(
                function,
                &static_arguments,
                &mut concrete.parameters,
                &format!("ForeignDefault{}_", self.external_instances.len()),
                &self.types,
                self.layout,
            ) {
                match error {
                    crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message) => {
                        self.error(code, span, message, [value.cause])
                    }
                    crate::static_eval::ArgumentNormalizationError::Unsupported(message) => {
                        self.unsupported(span, message)
                    }
                }
                return true;
            }
            concrete.return_type = result.as_ref().map(|result| *result.clone());
            let callable_type = Ty::Callable(
                concrete
                    .parameters
                    .iter()
                    .map(|parameter| {
                        parameter
                            .ty
                            .as_ref()
                            .map(|ty| self.ty(ty))
                            .unwrap_or(Ty::Unknown)
                    })
                    .collect(),
                Box::new(
                    concrete
                        .return_type
                        .as_ref()
                        .map(|ty| self.ty(ty))
                        .unwrap_or(Ty::Unit),
                ),
            );
            let callable = self.functions.len();
            self.definitions.push(Definition {
                id: DefinitionId(callable as u32),
                span: concrete.span,
            });
            let mut info = original.clone();
            info.definition = DefinitionId(callable as u32);
            info.syntax = concrete.clone();
            self.functions.push(info);
            let index = self.external_instances.len();
            self.external_instances
                .push(super::super::ExternalInstance {
                    declaration_name: function.name.clone(),
                    syntax: concrete,
                    callable_type,
                    arguments,
                    sites: BTreeSet::new(),
                    callable,
                });
            index
        };
        let instance = &mut self.external_instances[instance];
        instance.sites.insert((span.file.0, span.start, span.end));
        value.callables = vec![Callable::Named(instance.callable)];
        value.ty = instance.callable_type.clone();
        value.signature = Some(instance.syntax.parameters.clone());
        true
    }
}
