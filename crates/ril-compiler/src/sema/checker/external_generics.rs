//! Concrete foreign instances still use ordinary named invocation checking.
//! Record static arguments even when absent from all run-time value types.
use super::*;

impl Checker {
    pub(super) fn external_static_callee_source(
        &self,
        value: &Value,
        syntax: &Expr,
        frame: &Frame,
        work: &mut crate::sema::source_types::WorkLimit,
    ) -> crate::sema::evaluated::CheckedSource {
        use crate::sema::source_types::{SourceSchema, SourceTypesError};
        if !matches!(syntax.kind, ExprKind::Generic { .. }) {
            return Ok(None);
        }
        let [Callable::Named(callable)] = value.callables.as_slice() else {
            return Ok(None);
        };
        work.charge(self.external_instances.len())?;
        let mut instances = self
            .external_instances
            .iter()
            .filter(|instance| instance.callable == *callable);
        let Some(instance) = instances.next() else {
            return Ok(None);
        };
        if instances.next().is_some() {
            return Err(SourceTypesError::Unresolved);
        }
        let context = self.invocation_context(frame.callable_owner);
        let occurrence = self.source_projection_occurrence(
            syntax.hir_id.ok_or(SourceTypesError::MissingNode)?,
            value,
            context,
            work,
        )?;
        work.charge(instance.applications.len())?;
        if !instance
            .applications
            .iter()
            .any(|application| application.occurrence == occurrence.identity)
        {
            return Err(SourceTypesError::MissingNode);
        }
        let info = self
            .functions
            .get(*callable)
            .ok_or(SourceTypesError::MissingNode)?;
        if info.hir_id != Some(instance.generated) || info.typing_environment.is_poisoned() {
            return Err(SourceTypesError::Unresolved);
        }
        let environment = info.typing_environment.clone();
        work.charge(info.syntax.parameters.len() + info.syntax.annotations.len())?;
        let mut parameters = Vec::with_capacity(info.syntax.parameters.len());
        for parameter in &info.syntax.parameters {
            let syntax = parameter.ty.as_ref().ok_or(SourceTypesError::MissingNode)?;
            let (schema, _) = self
                .input_original_header_schema(syntax, environment.clone(), work)?
                .ok_or(SourceTypesError::MissingNode)?;
            parameters.push((parameter.mode, schema));
        }
        let result = if let Some(syntax) = &info.syntax.return_type {
            self.input_original_header_schema(syntax, environment.clone(), work)?
                .ok_or(SourceTypesError::MissingNode)?
                .0
        } else {
            SourceSchema::tuple(&[], None, work)?
        };
        let annotations = info
            .syntax
            .annotations
            .iter()
            .map(|annotation| {
                work.text(&annotation.text)?;
                Ok(annotation.text.replace(' ', ""))
            })
            .collect::<Result<Vec<_>, SourceTypesError>>()?;
        Ok(Some((
            SourceSchema::callable(&parameters, &result, &annotations, None, work)?,
            environment,
        )))
    }

    fn external_static_application(
        &mut self,
        target: usize,
        arguments: &[TypeExpr],
    ) -> Result<super::super::ExternalApplication, &'static str> {
        use crate::sema::application_effect::{ActivationKind, OccurrenceIdentity};
        let activation = self
            .application_effect
            .current_activation()
            .ok_or("foreign static application has no current activation")?;
        let first_child = activation.0 as usize + 1;
        let children = self
            .application_effect
            .activations
            .len()
            .saturating_sub(first_child);
        if !self
            .application_effect
            .admit(8 + arguments.len() + children)
        {
            return Err("foreign static application identity query exceeds its work bound");
        }
        let parent = &self.application_effect.activations[activation.0 as usize];
        let source = parent
            .source
            .ok_or("foreign static application has no original HIR")?;
        let node = self
            .semantic_hir
            .expression(source)
            .ok_or("foreign static application HIR is absent")?;
        let crate::hir::nodes::ExprKind::Generic {
            base,
            arguments: original,
        } = &node.kind
        else {
            return Err("foreign static application is not the actual Generic expression");
        };
        if parent.kind != ActivationKind::Expression
            || original.len() != arguments.len()
            || original
                .iter()
                .zip(arguments)
                .any(|(id, syntax)| syntax.hir_id != Some(*id))
        {
            return Err("foreign static arguments changed their original HIR coordinates");
        }
        let mut child = self.application_effect.activations[first_child..]
            .iter()
            .filter(|child| {
                child.parent == Some(activation)
                    && child.source == Some(*base)
                    && child.kind == ActivationKind::Expression
            });
        let child = child
            .next()
            .filter(|_| child.next().is_none())
            .ok_or("foreign static application has no unique actual base evaluation")?;
        let token = child
            .result
            .ok_or("foreign static base evaluation is unfinished")?;
        let record = self
            .application_effect
            .evaluations
            .get(token.0 as usize)
            .ok_or("foreign static base observation is absent")?;
        let fact = self
            .application_effect
            .expressions
            .get(token.0 as usize)
            .ok_or("foreign static base value is absent")?;
        if record.id != token
            || record.identity
                != Some(OccurrenceIdentity {
                    source: *base,
                    activation: child.id,
                })
            || record.context != parent.context
            || child.context != parent.context
            || fact.source_id != Some(*base)
            || !matches!(fact.value.callables.as_slice(),[Callable::Named(actual)] if *actual == target)
        {
            return Err("foreign static base observation belongs to another target or context");
        }
        Ok(super::super::ExternalApplication {
            occurrence: OccurrenceIdentity { source, activation },
            base: token,
        })
    }

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
        let application = match self.external_static_application(*id, arguments) {
            Ok(application) => application,
            Err(message) => {
                self.unsupported(span, message);
                return true;
            }
        };
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
        let normalized = self.application_effect.with_work(|work| {
            crate::sema::external_instances::instantiate(
                &original,
                arguments,
                &self.types,
                &self.semantic_hir,
                self.layout,
                self.external_instances.len(),
                work,
            )
        });
        let normalized = match normalized {
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
        let mut concrete = normalized.syntax;
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
            instance.template == original.definition
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
            let generated = (|| {
                let mut statement = Stmt {
                    hir_id: None,
                    span: concrete.span,
                    kind: StmtKind::Function(concrete),
                };
                let admitted = self.application_effect.with_work(|work| {
                    let StmtKind::Function(function) = &statement.kind else {
                        unreachable!()
                    };
                    crate::static_eval::charge_function_syntax_clone(function, work)
                        .and_then(|_| {
                            crate::static_eval::charge_function_syntax_clone(function, work)
                        })
                        .and_then(|_| {
                            crate::static_eval::charge_function_syntax_clone(function, work)
                        })
                });
                admitted.ok_or("foreign generated declaration exceeds its work bound")?;
                let id = self
                    .semantic_hir
                    .mint_generated_identified_statement(
                        &mut statement,
                        crate::hir::nodes::NodeId::Expr(application.occurrence.source),
                        crate::hir::nodes::GeneratedKind::StaticSpecialization,
                        crate::hir::nodes::LexicalOwner::Module,
                        crate::hir::nodes::HirLimits::default(),
                    )
                    .map_err(
                        |_| "foreign generated declaration has no admitted original identity",
                    )?;
                let StmtKind::Function(function) = statement.kind else {
                    unreachable!()
                };
                Ok::<_, &str>((id, function))
            })();
            let (generated, syntax) = match generated {
                Ok(generated) => generated,
                Err(message) => {
                    self.unsupported(span, message);
                    return true;
                }
            };
            concrete = syntax;
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
            info.hir_id = Some(generated);
            info.definition = DefinitionId(callable as u32);
            info.syntax = concrete.clone();
            self.functions.push(info);
            let index = self.external_instances.len();
            self.external_instances
                .push(super::super::ExternalInstance {
                    template: original.definition,
                    declaration: original
                        .hir_id
                        .expect("authenticated original foreign declaration"),
                    generated,
                    declaration_name: function.name.clone(),
                    syntax: concrete,
                    callable_type,
                    arguments,
                    applications: Vec::new(),
                    callable,
                });
            index
        };
        self.external_instances[instance]
            .applications
            .push(application);
        let instance = &self.external_instances[instance];
        value.callables = vec![Callable::Named(instance.callable)];
        value.ty = instance.callable_type.clone();
        value.signature = Some(self.callable_signature(instance.syntax.parameters.clone()));
        true
    }
}
