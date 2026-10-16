//! Lower certified declaration types to representation-independent host schemas.
use super::*;
use crate::{
    hir::VerifiedProgram,
    modules::{ExternalDeclaration, ExternalDeclarationKind},
    sema::model::Ty,
};
use ril_ir::foreign as f;
use std::collections::BTreeMap;

pub(super) fn function(
    lower: &mut Lower<'_>,
    program: &VerifiedProgram,
    syntax: &ast::Function,
) -> Result<f::ExternalFunction, NotImplemented> {
    instance_function(lower, program, syntax, None)
}
pub(super) fn instances(
    lower: &mut Lower<'_>,
    program: &VerifiedProgram,
    syntax: &ast::Function,
) -> Result<Vec<f::ExternalFunction>, NotImplemented> {
    let instances: Vec<_> = program
        .facts()
        .external_instances
        .iter()
        .filter(|instance| instance.declaration_name == syntax.name)
        .collect();
    instances
        .into_iter()
        .map(|instance| instance_function(lower, program, &instance.syntax, Some(instance)))
        .collect()
}
fn instance_function(
    lower: &mut Lower<'_>,
    program: &VerifiedProgram,
    syntax: &ast::Function,
    instance: Option<&crate::sema::ExternalInstance>,
) -> Result<f::ExternalFunction, NotImplemented> {
    let declaration = declaration(
        program,
        instance.map_or(&syntax.name, |instance| &instance.declaration_name),
        ExternalDeclarationKind::Function,
    )?;
    if !syntax.generics.is_empty() {
        return Err(unsupported(
            "external generic declarations require instantiated exchange schemas",
        ));
    }
    let callable_type = if let Some(instance) = instance {
        &instance.callable_type
    } else {
        &program
            .facts()
            .bindings
            .iter()
            .find(|binding| binding.name == syntax.name && binding.span == syntax.span)
            .ok_or_else(|| unsupported("external function has no checked callable type"))?
            .value
            .ty
    };
    let Ty::Callable(parameters, result) = callable_type else {
        return Err(unsupported(
            "external declaration does not have a callable type",
        ));
    };
    let mut schema = Schema::new(program, lower.layout);
    let mut parameter_types = Vec::new();
    let mut callbacks = Vec::new();
    for (index, parameter) in parameters.iter().enumerate() {
        let expanded = schema.expanded(parameter);
        if let Ty::Callable(parameters, result) = expanded {
            let written = syntax.parameters[index].ty.as_ref().ok_or_else(|| {
                unsupported("external callback requires its checked source signature")
            })?;
            let written = schema.surface(written)?;
            let ast::TypeKind::Callable {
                parameters: written_parameters,
                result: written_result,
                ..
            } = &written.kind
            else {
                return Err(unsupported(
                    "external callback has no complete source parameter modes",
                ));
            };
            if written_parameters
                .iter()
                .any(|parameter| parameter.mode != ast::ParameterMode::Read)
            {
                return Err(unsupported(
                    "mutable callback arguments require a listed resource exchange contract",
                ));
            }
            if written_parameters.len() != parameters.len() {
                return Err(unsupported(
                    "external callback source and value signatures disagree",
                ));
            }
            let id = schema.arena.len() as u32;
            schema.arena.push(f::TypeNode::Callback);
            parameter_types.push(id);
            callbacks.push(f::CallbackSlot {
                argument: index as u32,
                path: vec![],
                mutable: syntax.parameters[index].mode == ast::ParameterMode::Mut,
                parameters: written_parameters
                    .iter()
                    .map(|parameter| {
                        schema.shape(parameter.ty.as_ref().ok_or_else(|| {
                            unsupported("external callback parameter type is not concrete")
                        })?)
                    })
                    .collect::<Result<_, _>>()?,
                result: if let Some(written) = written_result {
                    schema.shape(written)?
                } else {
                    schema.ty(&result)?
                },
            });
        } else {
            parameter_types.push(schema.shape(
                syntax.parameters[index].ty.as_ref().ok_or_else(|| {
                    unsupported("external parameter lacks its checked source shape")
                })?,
            )?);
        }
    }
    let result = if let Some(written) = &syntax.return_type {
        schema.shape(written)?
    } else {
        schema.ty(result)?
    };
    let definition = if let Some(instance) = instance {
        ril_compiler_core::ids::DefinitionId(instance.callable as u32)
    } else {
        program
            .definitions()
            .iter()
            .find(|definition| definition.span == syntax.span)
            .ok_or_else(|| unsupported("external function definition identity is missing"))?
            .id
    };
    let mut static_arguments = Vec::new();
    if let Some(instance) = instance {
        for (name, argument) in &instance.arguments {
            let identity = schema.wire_argument(argument)?;
            let value = if matches!(argument.kind, ast::TypeKind::Computation(_)) {
                f::StaticArgumentValue::Value {
                    identity,
                    value: crate::static_eval::foreign::scalar(
                        argument,
                        &program.facts().external_type_declarations,
                        lower.layout,
                    )
                    .map_err(|_| {
                        unsupported("external static scalar has no normalized value contract")
                    })?,
                }
            } else {
                // A phantom type need not be exchangeable. A failed optional
                // schema must not leave reserved/partial nodes in the arena.
                let checkpoint = (
                    schema.arena.clone(),
                    schema.source_seen.clone(),
                    schema.seen.clone(),
                );
                let shape = match schema.shape(argument) {
                    Ok(shape) => Some(shape),
                    Err(_) => {
                        (schema.arena, schema.source_seen, schema.seen) = checkpoint;
                        None
                    }
                };
                f::StaticArgumentValue::Type {
                    identity,
                    schema: shape,
                }
            };
            static_arguments.push(f::StaticArgument {
                name: name.clone(),
                value,
            });
        }
    }
    let previous_owner = lower
        .callable_owner
        .replace(CallableOwner::Function(definition));
    let parameters = syntax
        .parameters
        .iter()
        .map(|parameter| lower.parameter(parameter))
        .collect::<Result<_, _>>()?;
    lower.callable_owner = previous_owner;
    Ok(f::ExternalFunction {
        static_arguments,
        definition,
        internal_name: syntax.name.clone(),
        declaration: declaration.declaration.clone(),
        span: syntax.span,
        parameters,
        signature: f::Signature {
            arena: schema.arena,
            parameters: parameter_types,
            result,
            callbacks,
        },
    })
}

pub(super) fn constant(
    lower: &Lower<'_>,
    program: &VerifiedProgram,
    binding: &ast::Binding,
) -> Result<f::ExternalConstant, NotImplemented> {
    let ast::PatternKind::Name(name) = &binding.pattern.kind else {
        return Err(unsupported(
            "destructured external constants require whole-value exchange identity",
        ));
    };
    let declaration = declaration(program, name, ExternalDeclarationKind::Constant)?;
    let value = program
        .facts()
        .bindings
        .iter()
        .find(|info| info.name == *name && info.span.file == binding.pattern.span.file)
        .ok_or_else(|| unsupported("external constant has no checked type"))?;
    let mut schema = Schema::new(program, lower.layout);
    let written = binding
        .ty
        .as_ref()
        .ok_or_else(|| unsupported("external constant lacks its checked source shape"))?;
    let _ = value;
    let result = schema.shape(written)?;
    Ok(f::ExternalConstant {
        static_arguments: vec![],
        internal_name: name.clone(),
        declaration: declaration.declaration.clone(),
        span: binding.pattern.span,
        signature: f::Signature {
            arena: schema.arena,
            parameters: vec![],
            result,
            callbacks: vec![],
        },
    })
}
fn declaration<'a>(
    program: &'a VerifiedProgram,
    name: &str,
    kind: ExternalDeclarationKind,
) -> Result<&'a ExternalDeclaration, NotImplemented> {
    program
        .external_declarations()
        .iter()
        .find(|declaration| declaration.internal_name == name && declaration.kind == kind)
        .ok_or_else(|| unsupported("external declaration lacks a stable project identity"))
}

struct Schema<'a> {
    program: &'a VerifiedProgram,
    layout: TargetLayout,
    arena: Vec<f::TypeNode>,
    seen: Vec<(Ty, f::TypeRef)>,
    source_seen: BTreeMap<String, f::TypeRef>,
}
impl<'a> Schema<'a> {
    fn new(program: &'a VerifiedProgram, layout: TargetLayout) -> Self {
        Self {
            program,
            layout,
            arena: vec![],
            seen: vec![],
            source_seen: BTreeMap::new(),
        }
    }
    fn semantic(&self, syntax: &ast::TypeExpr) -> Result<Ty, NotImplemented> {
        let key = crate::static_eval::normalized_argument_key(syntax);
        self.program
            .facts()
            .external_type_witnesses
            .iter()
            .find(|witness| crate::static_eval::normalized_argument_key(&witness.syntax) == key)
            .map(|witness| witness.value_type.clone())
            .ok_or_else(|| unsupported("external type refinement lacks its checked syntax witness"))
    }
    fn representation(
        &self,
        declaration: &ast::TypeDeclaration,
        arguments: &[ast::TypeExpr],
    ) -> Result<ast::TypeExpr, NotImplemented> {
        if declaration.generics.is_empty() {
            return declaration
                .value
                .clone()
                .ok_or_else(|| unsupported("foreign type has no concrete representation"));
        }
        let mut payload = declaration.clone();
        payload.nominal = true;
        payload.variants.clear();
        crate::static_eval::normalize_constructor_arguments(
            &payload,
            arguments,
            &self.program.facts().external_type_declarations,
            self.layout,
        )
        .map_err(|_| unsupported("external type instance has no completed static representation"))?
        .payloads
        .remove(&declaration.name)
        .flatten()
        .ok_or_else(|| unsupported("foreign type instance has no concrete representation"))
    }
    fn surface(&self, syntax: &ast::TypeExpr) -> Result<ast::TypeExpr, NotImplemented> {
        let mut current = syntax.clone();
        let mut seen = std::collections::BTreeSet::new();
        while let ast::TypeKind::Name { path, arguments } = &current.kind {
            let Some(declaration) = self
                .program
                .facts()
                .external_type_declarations
                .get(&path.join("::"))
            else {
                break;
            };
            if declaration.nominal || declaration.opaque || !declaration.variants.is_empty() {
                break;
            }
            if !seen.insert(crate::static_eval::normalized_argument_key(&current)) {
                return Err(unsupported("cyclic external surface alias"));
            }
            current = self.representation(declaration, arguments)?;
        }
        Ok(current)
    }
    fn shape(&mut self, syntax: &ast::TypeExpr) -> Result<f::TypeRef, NotImplemented> {
        let key = crate::static_eval::normalized_argument_key(syntax);
        if let Some(id) = self.source_seen.get(&key) {
            return Ok(*id);
        }
        let checked = self.semantic(syntax)?;
        if self
            .program
            .facts()
            .external_resource_types
            .contains(&checked)
        {
            return Err(unsupported(
                "foreign type lacks a concrete ordinary representation or listed resource contract",
            ));
        }
        let id = u32::try_from(self.arena.len())
            .map_err(|_| unsupported("external schema identity domain exhausted"))?;
        self.source_seen.insert(key, id);
        self.arena.push(f::TypeNode::Unit);
        let node = match &syntax.kind {
            ast::TypeKind::Array { length, element } => f::TypeNode::Array {
                element: self.shape(element)?,
                length: if let Some(length) = length {
                    Some(crate::sema::checker::arrays::length_literal(length, self.layout.pointer_bits).map_err(|_| unsupported("foreign fixed array length violates the selected target's int domain"))?.ok_or_else(|| unsupported("foreign fixed array length was not statically materialized"))?)
                } else {
                    None
                },
            },
            ast::TypeKind::Map { key, value } => f::TypeNode::Map {
                key: self.shape(key)?,
                value: self.shape(value)?,
            },
            ast::TypeKind::Tuple(items) if items.is_empty() => f::TypeNode::Unit,
            ast::TypeKind::Tuple(items) => f::TypeNode::Tuple(
                items
                    .iter()
                    .map(|item| self.shape(item))
                    .collect::<Result<_, _>>()?,
            ),
            ast::TypeKind::Record { fields, row: None } => f::TypeNode::Record(
                fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), self.shape(&field.ty)?)))
                    .collect::<Result<_, NotImplemented>>()?,
            ),
            ast::TypeKind::Optional(inner) => f::TypeNode::Variant(vec![
                f::VariantShape {
                    wire_tag: "None".into(),
                    runtime_tag: "None".into(),
                    fields: vec![],
                },
                f::VariantShape {
                    wire_tag: "Some".into(),
                    runtime_tag: "Some".into(),
                    fields: vec![self.shape(inner)?],
                },
            ]),
            ast::TypeKind::Name { path, arguments } => {
                let name = path.join("::");
                if let Some(declaration) = self
                    .program
                    .facts()
                    .external_type_declarations
                    .get(&name)
                    .cloned()
                {
                    if declaration.nominal || !declaration.variants.is_empty() {
                        self.named_shape(&checked, &declaration, arguments)?
                    } else {
                        let representation = self.representation(&declaration, arguments)?;
                        let representation = self.shape(&representation)?;
                        if declaration.opaque {
                            f::TypeNode::OpaqueData {
                                wire_tag: self.instance_wire(&name, arguments)?,
                                runtime_tag: name,
                                representation,
                            }
                        } else {
                            self.arena[representation as usize].clone()
                        }
                    }
                } else {
                    match (
                        name.strip_prefix("Prelude::").unwrap_or(&name),
                        arguments.as_slice(),
                    ) {
                        ("Immut", [inner]) => f::TypeNode::Immutable(self.shape(inner)?),
                        ("Set", [inner]) => f::TypeNode::Set(self.shape(inner)?),
                        ("Range", [inner]) => f::TypeNode::Range(self.shape(inner)?),
                        ("Option", [inner]) => f::TypeNode::Variant(vec![
                            f::VariantShape {
                                wire_tag: "None".into(),
                                runtime_tag: "None".into(),
                                fields: vec![],
                            },
                            f::VariantShape {
                                wire_tag: "Some".into(),
                                runtime_tag: "Some".into(),
                                fields: vec![self.shape(inner)?],
                            },
                        ]),
                        ("Result", [ok, error]) => f::TypeNode::Variant(vec![
                            f::VariantShape {
                                wire_tag: "Ok".into(),
                                runtime_tag: "Ok".into(),
                                fields: vec![self.shape(ok)?],
                            },
                            f::VariantShape {
                                wire_tag: "Err".into(),
                                runtime_tag: "Err".into(),
                                fields: vec![self.shape(error)?],
                            },
                        ]),
                        _ => {
                            let primitive = self.ty(&checked)?;
                            self.arena[primitive as usize].clone()
                        }
                    }
                }
            }
            _ => {
                return Err(unsupported(
                    "external source type has an unresolved or non-exchange refinement",
                ));
            }
        };
        self.arena[id as usize] = node;
        Ok(id)
    }
    fn instance_wire(
        &self,
        name: &str,
        arguments: &[ast::TypeExpr],
    ) -> Result<String, NotImplemented> {
        let declaration = self
            .program
            .type_declarations()
            .get(name)
            .ok_or_else(|| unsupported("external type has no stable declaration identity"))?;
        let arguments = if let Some(syntax) =
            self.program.facts().external_type_declarations.get(name)
            && !syntax.generics.is_empty()
        {
            crate::static_eval::normalize_constructor_arguments(
                syntax,
                arguments,
                &self.program.facts().external_type_declarations,
                self.layout,
            )
            .map_err(|_| {
                unsupported(
                    "foreign instance identity lacks checked defaults or argument normalization",
                )
            })?
            .arguments
        } else {
            arguments.to_vec()
        };
        if arguments.is_empty() {
            return Ok(declaration.clone());
        }
        let arguments = arguments
            .iter()
            .map(|argument| self.wire_argument(argument))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{declaration}<{}>", arguments.join(",")))
    }
    fn wire_argument(&self, syntax: &ast::TypeExpr) -> Result<String, NotImplemented> {
        let mut syntax = syntax.clone();
        fn rewrite(schema: &Schema<'_>, syntax: &mut ast::TypeExpr) -> Result<(), NotImplemented> {
            match &mut syntax.kind {
                ast::TypeKind::Name { path, arguments } => {
                    let name = path.join("::");
                    if let Some(stable) = schema.program.type_declarations().get(&name) {
                        *path = vec![stable.clone()];
                    } else if schema
                        .program
                        .facts()
                        .external_type_declarations
                        .contains_key(&name)
                    {
                        return Err(unsupported(
                            "static argument refers to a type without a stable foreign identity",
                        ));
                    }
                    for argument in arguments {
                        rewrite(schema, argument)?;
                    }
                }
                ast::TypeKind::Array { element, .. } | ast::TypeKind::Optional(element) => {
                    rewrite(schema, element)?
                }
                ast::TypeKind::Map { key, value } => {
                    rewrite(schema, key)?;
                    rewrite(schema, value)?;
                }
                ast::TypeKind::Tuple(items) => {
                    for item in items {
                        rewrite(schema, item)?;
                    }
                }
                ast::TypeKind::Record { fields, row: None } => {
                    for field in fields {
                        rewrite(schema, &mut field.ty)?;
                    }
                }
                ast::TypeKind::Callable {
                    parameters,
                    result,
                    annotations,
                } if annotations.is_empty() => {
                    for parameter in parameters {
                        rewrite(
                            schema,
                            parameter.ty.as_mut().ok_or_else(|| {
                                unsupported("phantom callable type lacks a parameter type")
                            })?,
                        )?;
                    }
                    if let Some(result) = result {
                        rewrite(schema, result)?;
                    }
                }
                ast::TypeKind::Computation(_) => {
                    crate::static_eval::foreign::scalar(
                        syntax,
                        &schema.program.facts().external_type_declarations,
                        schema.layout,
                    )
                    .map_err(|_| {
                        unsupported("static foreign instance requires a concrete scalar identity")
                    })?;
                }
                _ => {
                    return Err(unsupported(
                        "static foreign instance identity is not concrete",
                    ));
                }
            }
            Ok(())
        }
        rewrite(self, &mut syntax)?;
        Ok(crate::static_eval::normalized_argument_key(&syntax))
    }
    fn named_shape(
        &mut self,
        ty: &Ty,
        declaration: &ast::TypeDeclaration,
        arguments: &[ast::TypeExpr],
    ) -> Result<f::TypeNode, NotImplemented> {
        let wire = self.instance_wire(&declaration.name, arguments)?;
        let constructors: Vec<_> = self
            .program
            .facts()
            .constructors
            .values()
            .filter(|constructor| &constructor.owner == ty)
            .cloned()
            .collect();
        let payload = |schema: &mut Self, constructor: &crate::sema::model::ConstructorInfo| {
            if let Some(syntax) = &constructor.payload_syntax {
                schema.shape(syntax)
            } else if !constructor.has_payload {
                schema.ty(&Ty::Unit)
            } else {
                Err(unsupported(
                    "external constructor payload has no checked refinement shape",
                ))
            }
        };
        if let [constructor] = constructors.as_slice()
            && constructor.nominal
        {
            return Ok(f::TypeNode::Nominal {
                wire_tag: wire,
                runtime_tag: constructor.tag.clone(),
                payload: payload(self, constructor)?,
            });
        }
        if constructors.is_empty() {
            return Err(unsupported(
                "external nominal instance has no verified constructor schema",
            ));
        }
        let variants = constructors
            .iter()
            .map(|constructor| {
                Ok(f::VariantShape {
                    wire_tag: format!(
                        "{wire}::{}",
                        constructor
                            .tag
                            .rsplit("::")
                            .next()
                            .unwrap_or(&constructor.tag)
                    ),
                    runtime_tag: constructor.tag.clone(),
                    fields: if constructor.has_payload {
                        vec![payload(self, constructor)?]
                    } else {
                        vec![]
                    },
                })
            })
            .collect::<Result<_, NotImplemented>>()?;
        Ok(f::TypeNode::Variant(variants))
    }
    fn expanded(&self, ty: &Ty) -> Ty {
        self.program
            .facts()
            .external_type_expansions
            .iter()
            .find(|(before, _)| before == ty)
            .map_or_else(|| ty.clone(), |(_, after)| after.clone())
    }
    fn ty(&mut self, ty: &Ty) -> Result<f::TypeRef, NotImplemented> {
        if let Some((_, id)) = self.seen.iter().find(|(previous, _)| previous == ty) {
            return Ok(*id);
        }
        if self.program.facts().external_resource_types.contains(ty) {
            return Err(unsupported(
                "external resource exchange requires a listed persistent provider contract",
            ));
        }
        let id = u32::try_from(self.arena.len())
            .map_err(|_| unsupported("external type schema exceeds its identity domain"))?;
        self.seen.push((ty.clone(), id));
        self.arena.push(f::TypeNode::Unit);
        let expanded = self.expanded(ty);
        let node = match &expanded {
            Ty::Never => f::TypeNode::Variant(vec![]),
            Ty::Unit => f::TypeNode::Unit,
            Ty::Bool => f::TypeNode::Bool,
            Ty::Str => f::TypeNode::String,
            Ty::Bytes => f::TypeNode::Bytes,
            Ty::Int(name) if name == "bigint" => f::TypeNode::BigInteger,
            Ty::Int(name) => {
                let (bits, signed) = match name.as_str() {
                    "int" => (self.layout.pointer_bits, true),
                    "isize" => (self.layout.pointer_bits, true),
                    "usize" => (self.layout.pointer_bits, false),
                    _ => (
                        name.get(1..)
                            .and_then(|bits| bits.parse::<u8>().ok())
                            .filter(|bits| matches!(bits, 8 | 16 | 32 | 64 | 128))
                            .ok_or_else(|| unsupported("external integer width"))?,
                        name.starts_with('i'),
                    ),
                };
                f::TypeNode::Integer { bits, signed }
            }
            Ty::Float(name) => f::TypeNode::Float {
                bits: match name.as_str() {
                    "float" | "f64" => 64,
                    "f32" => 32,
                    _ => return Err(unsupported("external float width")),
                },
            },
            Ty::Immutable(inner) => f::TypeNode::Immutable(self.ty(inner)?),
            Ty::Array(inner) => f::TypeNode::Array {
                element: self.ty(inner)?,
                length: None,
            },
            Ty::Map(key, value) => f::TypeNode::Map {
                key: self.ty(key)?,
                value: self.ty(value)?,
            },
            Ty::Set(inner) => f::TypeNode::Set(self.ty(inner)?),
            Ty::Range(inner) => f::TypeNode::Range(self.ty(inner)?),
            Ty::Tuple(items) => f::TypeNode::Tuple(
                items
                    .iter()
                    .map(|item| self.ty(item))
                    .collect::<Result<_, _>>()?,
            ),
            Ty::Record(fields) => f::TypeNode::Record(
                fields
                    .iter()
                    .map(|(name, (_, ty))| Ok((name.clone(), self.ty(ty)?)))
                    .collect::<Result<BTreeMap<_, _>, NotImplemented>>()?,
            ),
            Ty::Optional(inner) => f::TypeNode::Variant(vec![
                f::VariantShape {
                    wire_tag: "None".into(),
                    runtime_tag: "None".into(),
                    fields: vec![],
                },
                f::VariantShape {
                    wire_tag: "Some".into(),
                    runtime_tag: "Some".into(),
                    fields: vec![self.ty(inner)?],
                },
            ]),
            Ty::Result(ok, error) => f::TypeNode::Variant(vec![
                f::VariantShape {
                    wire_tag: "Ok".into(),
                    runtime_tag: "Ok".into(),
                    fields: vec![self.ty(ok)?],
                },
                f::VariantShape {
                    wire_tag: "Err".into(),
                    runtime_tag: "Err".into(),
                    fields: vec![self.ty(error)?],
                },
            ]),
            Ty::Named(name) => self.named(ty, name)?,
            Ty::Callable(..) => {
                return Err(unsupported(
                    "nested or returned callbacks require an explicit temporary exchange path",
                ));
            }
            _ => {
                return Err(unsupported(format!(
                    "external exchange schema is not concrete: {expanded:?}"
                )));
            }
        };
        self.arena[id as usize] = node;
        Ok(id)
    }
    fn named(&mut self, ty: &Ty, name: &str) -> Result<f::TypeNode, NotImplemented> {
        let wire = self
            .program
            .type_declarations()
            .get(name)
            .cloned()
            .ok_or_else(|| {
                unsupported(format!(
                    "external type has no stable declaration identity: {name}"
                ))
            })?;
        let constructors: Vec<_> = self
            .program
            .facts()
            .constructors
            .values()
            .filter(|info| &info.owner == ty)
            .cloned()
            .collect();
        if let [constructor] = constructors.as_slice()
            && constructor.nominal
        {
            let payload = self.ty(&constructor.payload)?;
            return Ok(f::TypeNode::Nominal {
                wire_tag: wire,
                runtime_tag: constructor.tag.clone(),
                payload,
            });
        }
        if !constructors.is_empty() {
            let variants = constructors
                .iter()
                .map(|constructor| {
                    let fields = if constructor.has_payload {
                        vec![self.ty(&constructor.payload)?]
                    } else {
                        vec![]
                    };
                    Ok(f::VariantShape {
                        wire_tag: format!(
                            "{wire}::{}",
                            constructor
                                .tag
                                .rsplit("::")
                                .next()
                                .unwrap_or(&constructor.tag)
                        ),
                        runtime_tag: constructor.tag.clone(),
                        fields,
                    })
                })
                .collect::<Result<_, NotImplemented>>()?;
            return Ok(f::TypeNode::Variant(variants));
        }
        Err(unsupported(format!(
            "opaque external type requires an explicit ordinary-data representation contract: {wire}"
        )))
    }
}
