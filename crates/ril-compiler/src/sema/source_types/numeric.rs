//! The numeric SDK's original declarations. Native defaults belong to the
//! declaration; callable ascription always retains its full fixed arity.
use super::*;
use builtins::Schema;
use ril_compiler_core::numeric_builtins::{NumericBuiltin, NumericPrimitive};
use ril_syntax::ast::ParameterMode;

pub(crate) fn scalar(kind: NumericPrimitive) -> SourceScalar {
    use NumericPrimitive as N;
    match kind {
        N::Int => SourceScalar::Int,
        N::I8 => SourceScalar::I8,
        N::I16 => SourceScalar::I16,
        N::I32 => SourceScalar::I32,
        N::I64 => SourceScalar::I64,
        N::U8 => SourceScalar::U8,
        N::U16 => SourceScalar::U16,
        N::U32 => SourceScalar::U32,
        N::U64 => SourceScalar::U64,
        N::BigInt => SourceScalar::BigInt,
        N::F32 => SourceScalar::F32,
        N::F64 => SourceScalar::F64,
    }
}

pub(crate) fn primitive(kind: SourceScalar) -> Option<NumericPrimitive> {
    NumericPrimitive::ALL
        .into_iter()
        .find(|candidate| scalar(*candidate) == kind)
}

fn number(kind: NumericPrimitive) -> &'static Schema {
    use NumericPrimitive as N;
    match kind {
        N::Int => &Schema::Scalar(SourceScalar::Int),
        N::I8 => &Schema::Scalar(SourceScalar::I8),
        N::I16 => &Schema::Scalar(SourceScalar::I16),
        N::I32 => &Schema::Scalar(SourceScalar::I32),
        N::I64 => &Schema::Scalar(SourceScalar::I64),
        N::U8 => &Schema::Scalar(SourceScalar::U8),
        N::U16 => &Schema::Scalar(SourceScalar::U16),
        N::U32 => &Schema::Scalar(SourceScalar::U32),
        N::U64 => &Schema::Scalar(SourceScalar::U64),
        N::BigInt => &Schema::Scalar(SourceScalar::BigInt),
        N::F32 => &Schema::Scalar(SourceScalar::F32),
        N::F64 => &Schema::Scalar(SourceScalar::F64),
    }
}

const TEXT: Schema = Schema::Scalar(SourceScalar::Str);
const INT: Schema = Schema::Scalar(SourceScalar::Int);
const ERROR: Schema = Schema::Nominal(standard_data::Nominal::NumError);

pub(crate) struct Definition {
    inputs: [Schema; 2],
    count: usize,
    pub(crate) minimum: usize,
    pub(crate) output: Schema,
}

pub(crate) fn definition(id: NumericBuiltin) -> Option<Definition> {
    Some(match id {
        NumericBuiltin::Parse(kind) => Definition {
            inputs: [TEXT, INT],
            count: if kind.floating() { 1 } else { 2 },
            minimum: 1,
            output: Schema::Result(number(kind), &ERROR),
        },
        NumericBuiltin::Format(kind) => Definition {
            inputs: [*number(kind), INT],
            count: if kind.floating() { 1 } else { 2 },
            minimum: 1,
            output: if kind.floating() {
                TEXT
            } else {
                Schema::Result(&TEXT, &ERROR)
            },
        },
        NumericBuiltin::Convert => return None,
    })
}

impl Definition {
    pub(crate) fn inputs(&self) -> &[Schema] {
        &self.inputs[..self.count]
    }

    pub(crate) fn schema(&self, work: &mut WorkLimit) -> Result<SourceSchema, SourceTypesError> {
        work.charge(self.count)?;
        let mut parameters = Vec::with_capacity(self.count);
        for input in self.inputs() {
            let (types, root) = input.graph(work)?;
            parameters.push((
                ParameterMode::Read,
                SourceSchema::frozen_view(&types, root, None, work)?,
            ));
        }
        let (types, root) = self.output.graph(work)?;
        let output = SourceSchema::frozen_view(&types, root, None, work)?;
        SourceSchema::callable(&parameters, &output, &[], None, work)
    }
}

pub(crate) fn conversion(
    source: &SourceSchema,
    destination: &SourceSchema,
    work: &mut WorkLimit,
) -> Result<Option<(SourceSchema, NumericPrimitive, NumericPrimitive)>, SourceTypesError> {
    let source_kind = source.scalar_representation(work)?.and_then(primitive);
    let destination_kind = destination.scalar_representation(work)?.and_then(primitive);
    let (Some(source_kind), Some(destination_kind)) = (source_kind, destination_kind) else {
        return Ok(None);
    };
    let (types, root) = ERROR.graph(work)?;
    let error = SourceSchema::frozen_view(&types, root, None, work)?;
    let output = SourceSchema::container(
        SourceContainer::Result,
        &[destination.clone(), error],
        None,
        work,
    )?;
    let signature = SourceSchema::callable(
        &[(ParameterMode::Read, source.clone())],
        &output,
        &[],
        None,
        work,
    )?;
    Ok(Some((signature, source_kind, destination_kind)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numeric_declarations_keep_native_defaults_separate_from_fixed_callable_arity() {
        for kind in NumericPrimitive::ALL {
            for id in [NumericBuiltin::Parse(kind), NumericBuiltin::Format(kind)] {
                let declaration = definition(id).unwrap();
                let mut work = WorkLimit::new(4096);
                let source = declaration.schema(&mut work).unwrap();
                let (parameters, result) = source.callable_parts(&mut work).unwrap().unwrap();
                assert_eq!(declaration.minimum, 1);
                assert_eq!(parameters.len(), if kind.floating() { 1 } else { 2 });
                assert!(
                    parameters
                        .iter()
                        .all(|(mode, _)| *mode == ParameterMode::Read)
                );
                assert!(declaration.schema(&mut WorkLimit::new(0)).is_err());
                if !kind.floating() {
                    let missing =
                        SourceSchema::callable(&parameters[..1], &result, &[], None, &mut work)
                            .unwrap();
                    assert!(!missing.receive_schema(&source, None, &mut work).unwrap());
                }
                let mut wrong_mode = parameters.clone();
                wrong_mode[0].0 = ParameterMode::Mut;
                let wrong_mode =
                    SourceSchema::callable(&wrong_mode, &result, &[], None, &mut work).unwrap();
                assert!(!wrong_mode.receive_schema(&source, None, &mut work).unwrap());
                assert!(source.receive_schema(&source, None, &mut work).unwrap());
            }
        }
        assert!(definition(NumericBuiltin::Convert).is_none());
    }
}
