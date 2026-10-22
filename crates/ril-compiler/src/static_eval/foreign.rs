//! Serialize only normalized scalar arguments. Compound static values need
//! their own graph identity contract and remain explicitly incomplete.
use super::*;
mod defaults;
pub(crate) use defaults::instantiate_defaults_bounded;

fn evaluator(declarations: &BTreeMap<String, TypeDeclaration>, layout: TargetLayout) -> Evaluator {
    Evaluator {
        type_environment: Default::default(),
        type_application_sequence: 0,
        layout,
        values: BTreeMap::new(),
        global_values: BTreeMap::new(),
        budget: Default::default(),
        declarations: declarations.clone(),
        effect_declarations: BTreeMap::new(),
        functions: BTreeMap::new(),
        function_environments: BTreeMap::new(),
        environments: vec![],
        alias_instances: BTreeMap::new(),
        static_signatures: BTreeMap::new(),
        active_functions: vec![],
        type_depth: 0,
        call_depth: 0,
        tail_returns: false,
        tail_types: false,
        numeric_return: None,
        results: Default::default(),
        result_site: None,
        expression_depth: 0,
        loop_frames: vec![],
        next_loop_target: 0,
        type_calls: BTreeSet::new(),
        next_collection: 0,
        publications: Default::default(),
        constants: Default::default(),
    }
}

fn failure(failure: Failure) -> ArgumentNormalizationError {
    match failure {
        Failure::Diagnostic(code, message) => ArgumentNormalizationError::Diagnostic(code, message),
        Failure::Unsupported(message) => ArgumentNormalizationError::Unsupported(message),
        Failure::Return(_) | Failure::TailCall(_) | Failure::TailType(_) | Failure::Loop(_) => {
            ArgumentNormalizationError::Unsupported(
                "foreign static argument cannot transfer control".into(),
            )
        }
    }
}

pub(crate) fn scalar(
    argument: &TypeExpr,
    declarations: &BTreeMap<String, TypeDeclaration>,
    layout: TargetLayout,
) -> std::result::Result<ril_ir::foreign::StaticValue, ArgumentNormalizationError> {
    let mut evaluator = evaluator(declarations, layout);
    use ril_ir::foreign::StaticValue as Wire;
    let value = evaluator.value_argument(argument).map_err(failure)?;
    Ok(match value {
        StaticValue::Integer(value) => Wire::Integer {
            decimal: value.to_string(),
            bits: layout.pointer_bits,
            signed: true,
        },
        StaticValue::TypedInteger(value, bits, signed) => Wire::Integer {
            decimal: value.to_string(),
            bits,
            signed,
        },
        StaticValue::BigInteger(value) => Wire::BigInteger(value.to_string()),
        StaticValue::Float(value, narrow) => Wire::Float {
            bits: if narrow { 32 } else { 64 },
            raw: if narrow {
                u64::from((value as f32).to_bits())
            } else {
                value.to_bits()
            },
        },
        StaticValue::Bool(value) => Wire::Bool(value),
        StaticValue::String(value) => Wire::String(value),
        StaticValue::Unit => Wire::Unit,
        StaticValue::Bytes(value) => Wire::Bytes(value),
        _ => {
            return Err(ArgumentNormalizationError::Unsupported(
                "non-scalar static foreign argument needs an explicit graph identity contract"
                    .into(),
            ));
        }
    })
}
