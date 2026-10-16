//! Static keys drive specialization while their syntax drives substitution.
//! Mutate real solved observations so agreement cannot be assumed from either.
use ril_compiler::{
    Session,
    sema::{
        SemanticFacts,
        effect_identity::{ArgumentKey, StaticArgumentWitness},
        validate::{ValidationIssueKind, solved_facts},
    },
};
use ril_syntax::ast::TypeKind;

const EFFECT: &str = include_str!("fixtures/source_type_witness/effect_instance.ril");
const MODES: &str = include_str!("fixtures/source_type_witness/modes.ril");
const CAPTURED: &str = r#"
fn outer<T>(value:T)->T{
    inner(value)
    where fn inner(item:T,other:T=item)->T{other}
}
fn example(){let input:[2]int=[1,2];let output=outer(input);assert(output[0]==1)}
"#;

fn facts(source: &str) -> SemanticFacts {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:#?}"))
        .facts()
        .clone()
}

fn inconsistent(facts: &SemanticFacts) {
    let issues = solved_facts(facts).expect_err("inconsistent frozen static argument was accepted");
    assert!(
        issues
            .iter()
            .any(|issue| matches!(&issue.kind, ValidationIssueKind::StaticArgument(_))),
        "{issues:#?}"
    );
}

fn actual_array(facts: &mut SemanticFacts) -> &mut StaticArgumentWitness {
    facts
        .effect_invocations
        .iter_mut()
        .filter(|event| !event.verifying)
        .flat_map(|event| &mut event.arguments)
        .find(|argument| matches!(&argument.key, Some(ArgumentKey::Array { .. })))
        .unwrap()
}

#[test]
fn syntax_and_specialization_keys_must_agree_on_empty_nested_array_dimensions() {
    let original = facts(EFFECT);
    assert!(solved_facts(&original).is_ok());
    let mut damaged = original.clone();
    let Some(ArgumentKey::Array { element, .. }) = &mut actual_array(&mut damaged).key else {
        unreachable!()
    };
    let ArgumentKey::Array { length, .. } = &mut **element else {
        unreachable!()
    };
    *length = Some("const(int:3)".into());
    inconsistent(&damaged);
    let mut damaged = original.clone();
    let TypeKind::Array { element, .. } =
        &mut actual_array(&mut damaged).syntax.as_mut().unwrap().kind
    else {
        unreachable!()
    };
    **element = ril_syntax::ast::TypeExpr {
        text: String::new(),
        span: element.span,
        kind: TypeKind::Name {
            path: vec!["str".into()],
            arguments: vec![],
        },
    };
    inconsistent(&damaged);
    // The key remains useful when only diagnostic positions change.
    let mut relocated = original;
    let span = &mut actual_array(&mut relocated).syntax.as_mut().unwrap().span;
    span.start = 0;
    span.end = 0;
    assert!(solved_facts(&relocated).is_ok());
}

#[test]
fn partial_static_arguments_cannot_claim_a_complete_substitution() {
    let original = facts(EFFECT);
    for drop_key in [false, true] {
        let mut damaged = original.clone();
        let argument = actual_array(&mut damaged);
        if drop_key {
            argument.key = None;
        } else {
            argument.syntax = None;
        }
        inconsistent(&damaged);
    }
    let mut incomplete = original;
    let argument = actual_array(&mut incomplete);
    argument.key = None;
    argument.syntax = None;
    assert!(
        solved_facts(&incomplete).is_ok(),
        "absence stays an obligation and grants no specialization"
    );
}

#[test]
fn symbolic_static_arguments_require_the_original_registered_binder() {
    let original = facts(EFFECT);
    let symbolic = original
        .effect_invocations
        .iter()
        .enumerate()
        .find_map(|(event, observation)| {
            observation
                .arguments
                .iter()
                .position(|argument| matches!(&argument.key, Some(ArgumentKey::Binder { .. })))
                .map(|index| (event, index))
        })
        .unwrap();
    let mut damaged = original.clone();
    let argument = &mut damaged.effect_invocations[symbolic.0].arguments[symbolic.1];
    let Some(ArgumentKey::Binder { identity, .. }) = &mut argument.key else {
        unreachable!()
    };
    identity.push_str(":wrong-activation");
    inconsistent(&damaged);
    let mut damaged = original.clone();
    let argument = &mut damaged.effect_invocations[symbolic.0].arguments[symbolic.1];
    argument.syntax.as_mut().unwrap().kind = TypeKind::Name {
        path: vec!["T".into()],
        arguments: vec![],
    };
    argument.key = Some(ArgumentKey::Name {
        name: "T".into(),
        arguments: vec![],
    });
    inconsistent(&damaged);
    let mut damaged = original.clone();
    let argument = &mut damaged.effect_invocations[symbolic.0].arguments[symbolic.1];
    argument.index += 1;
    inconsistent(&damaged);
    let mut damaged = original;
    let identity = damaged.effect_invocations[symbolic.0].arguments[symbolic.1]
        .binder
        .clone();
    damaged
        .generic_binders
        .get_mut(&identity)
        .unwrap()
        .identity
        .push_str(":forged");
    inconsistent(&damaged);
}

#[test]
fn defaults_and_captured_static_arguments_receive_the_same_independent_check() {
    let original = facts(CAPTURED);
    let selected = original
        .default_uses
        .iter()
        .position(|usage| {
            usage
                .captured_arguments
                .iter()
                .any(|argument| matches!(&argument.key, Some(ArgumentKey::Array { .. })))
        })
        .unwrap();
    let mut damaged = original.clone();
    let argument = damaged.default_uses[selected]
        .captured_arguments
        .iter_mut()
        .find(|argument| matches!(&argument.key, Some(ArgumentKey::Array { .. })))
        .unwrap();
    let Some(ArgumentKey::Array { length, .. }) = &mut argument.key else {
        unreachable!()
    };
    *length = Some("const(int:9)".into());
    inconsistent(&damaged);
    let selected = original
        .effect_invocations
        .iter()
        .position(|usage| {
            usage
                .captured_arguments
                .iter()
                .any(|argument| matches!(&argument.key, Some(ArgumentKey::Array { .. })))
        })
        .unwrap();
    let mut damaged = original;
    damaged.effect_invocations[selected]
        .captured_arguments
        .iter_mut()
        .find(|argument| matches!(&argument.key, Some(ArgumentKey::Array { .. })))
        .unwrap()
        .syntax = None;
    inconsistent(&damaged);
}

#[test]
fn observations_cover_their_exact_declaration_and_captured_environment() {
    let mut damaged = facts(EFFECT);
    let selected = damaged
        .effect_invocations
        .iter()
        .position(|event| !event.arguments.is_empty())
        .unwrap();
    damaged.effect_invocations[selected].arguments.clear();
    inconsistent(&damaged);
    let mut damaged = facts(CAPTURED);
    let selected = damaged
        .default_uses
        .iter()
        .position(|event| !event.captured_arguments.is_empty())
        .unwrap();
    damaged.default_uses[selected].captured_arguments.clear();
    inconsistent(&damaged);
    let mut damaged = facts(CAPTURED);
    let selected = damaged
        .effect_invocations
        .iter()
        .position(|event| !event.captured_arguments.is_empty())
        .unwrap();
    let repeated = damaged.effect_invocations[selected].captured_arguments[0].clone();
    damaged.effect_invocations[selected]
        .captured_arguments
        .push(repeated);
    inconsistent(&damaged);
}

#[test]
fn callable_parameter_modes_and_obligation_rows_cannot_disagree_with_substitution_syntax() {
    let original = facts(MODES);
    let selected = original.effect_invocations.iter().enumerate()
        .filter(|(_, event)| !event.verifying)
        .find_map(|(event, observation)| {
            observation.arguments.iter().position(|argument| {
                matches!(&argument.key, Some(ArgumentKey::Callable { parameters, annotations, .. })
                    if parameters.iter().any(|(mode, _)| *mode == ril_syntax::ast::ParameterMode::Mut)
                    && !annotations.is_empty())
            }).map(|index| (event, index))
        }).unwrap();
    let mut damaged = original.clone();
    let Some(ArgumentKey::Callable { parameters, .. }) =
        &mut damaged.effect_invocations[selected.0].arguments[selected.1].key
    else {
        unreachable!()
    };
    parameters[0].0 = ril_syntax::ast::ParameterMode::Read;
    inconsistent(&damaged);
    let mut damaged = original;
    let Some(ArgumentKey::Callable { annotations, .. }) =
        &mut damaged.effect_invocations[selected.0].arguments[selected.1].key
    else {
        unreachable!()
    };
    annotations.clear();
    inconsistent(&damaged);
}
