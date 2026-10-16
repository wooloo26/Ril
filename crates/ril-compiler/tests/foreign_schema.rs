use ril_compiler::{CheckOptions, CompilationOutcome, Session, session::ProjectSource};
use ril_ir::foreign::TypeNode;

fn project(declarations: &str) -> Session {
    project_with_options(declarations, CheckOptions::default())
}
fn project_with_options(declarations: &str, options: CheckOptions) -> Session {
    Session::with_project(
        "virtual/main.ril".into(),
        vec![
            ProjectSource {
                path: "virtual/main.ril".into(),
                bytes: b"use external/api\nfn entry(){}".to_vec(),
            },
            ProjectSource {
                path: "virtual/external/api.d.ril".into(),
                bytes: declarations.as_bytes().to_vec(),
            },
        ],
        options,
    )
    .unwrap()
}
fn schema(declarations: &str) -> ril_ir::core::Program {
    let verified = project(declarations).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap()
}

#[test]
fn fixed_cardinalities_survive_aliases_constants_and_callbacks() {
    let core = schema(
        "pub type Packet<n:int,T>={data:[n]T}\npub fn transform(data:Packet<2,u8>,callback:fn([2]u8)->[3]u8)->Packet<3,u8>\npub let HEADER:[4]u8",
    );
    let signature = &core.external_functions[0].signature;
    let lengths: std::collections::BTreeSet<_> = signature
        .arena
        .iter()
        .filter_map(|ty| {
            if let TypeNode::Array { length, .. } = ty {
                *length
            } else {
                None
            }
        })
        .collect();
    assert_eq!(lengths, [2, 3].into());
    let callback = &signature.callbacks[0];
    assert!(matches!(
        signature.arena[callback.parameters[0] as usize],
        TypeNode::Array {
            length: Some(2),
            ..
        }
    ));
    assert!(matches!(
        signature.arena[callback.result as usize],
        TypeNode::Array {
            length: Some(3),
            ..
        }
    ));
    let constant = &core.external_constants[0].signature;
    assert!(matches!(
        constant.arena[constant.result as usize],
        TypeNode::Array {
            length: Some(4),
            ..
        }
    ));
}

#[test]
fn exchange_qualifications_and_collection_shapes_remain_explicit() {
    let core = schema(
        "pub type Frozen=Immut<[4]u8>\npub fn echo(value:Frozen,counts:[str:int],labels:Set<str>)->Frozen",
    );
    let signature = &core.external_functions[0].signature;
    assert!(matches!(
        signature.arena[signature.result as usize],
        TypeNode::Immutable(_)
    ));
    assert!(matches!(
        signature.arena[signature.parameters[1] as usize],
        TypeNode::Map { .. }
    ));
    assert!(matches!(
        signature.arena[signature.parameters[2] as usize],
        TypeNode::Set(_)
    ));
}

#[test]
fn generic_nominal_and_recursive_sum_schema_keep_concrete_identity() {
    let core = schema(
        "pub type Box<T>([2]T)\npub type Chain<T>{Empty,Link((T,?Chain<T>))}\npub fn integer_box()->Box<int>\npub fn text_box()->Box<str>\npub fn chain()->Chain<int>",
    );
    let first = &core.external_functions[0].signature;
    let second = &core.external_functions[1].signature;
    let TypeNode::Nominal {
        wire_tag: a,
        payload,
        ..
    } = &first.arena[first.result as usize]
    else {
        panic!("{first:?}")
    };
    let TypeNode::Nominal { wire_tag: b, .. } = &second.arena[second.result as usize] else {
        panic!("{second:?}")
    };
    assert_ne!(a, b);
    assert!(matches!(
        first.arena[*payload as usize],
        TypeNode::Array {
            length: Some(2),
            ..
        }
    ));
    let recursive = &core.external_functions[2].signature;
    assert!(matches!(
        recursive.arena[recursive.result as usize],
        TypeNode::Variant(_)
    ));
    assert!(recursive.arena.len() < 16, "{recursive:?}");
}

#[test]
fn malformed_or_authority_bearing_signatures_are_not_weakened() {
    for (declaration, code) in [
        ("pub fn edit(mut data:[]int)", "E0908"),
        ("pub fn hidden()->{action:fn()->()}", "E0908"),
        ("pub fn wrong()->[-1]u8", "E0815"),
    ] {
        let outcome = project(declaration).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
            "{declaration}: {outcome:?}"
        );
    }
    let verified = project("pub type Handle\npub fn handle()->Handle")
        .verify()
        .unwrap();
    assert!(ril_compiler::lower::lower_core(&verified).is_err());
}

#[test]
fn ordinary_opaque_representation_and_static_defaults_are_preserved() {
    let core = schema(
        "pub opaque type Secret=[4]u8\npub type Integer=int\npub type Box<T=int>(T)\npub fn secret()->Secret\npub fn default_box()->Box\npub fn explicit_box()->Box<Integer>",
    );
    let secret = &core.external_functions[0].signature;
    let TypeNode::OpaqueData { representation, .. } = &secret.arena[secret.result as usize] else {
        panic!("{secret:?}")
    };
    assert!(matches!(
        secret.arena[*representation as usize],
        TypeNode::Array {
            length: Some(4),
            ..
        }
    ));
    let tag = |signature: &ril_ir::foreign::Signature| {
        let TypeNode::Nominal { wire_tag, .. } = &signature.arena[signature.result as usize] else {
            panic!("{signature:?}")
        };
        wire_tag.clone()
    };
    assert_eq!(
        tag(&core.external_functions[1].signature),
        tag(&core.external_functions[2].signature)
    );
}

#[test]
fn integer_schemas_and_cardinalities_follow_the_abstract_target() {
    let project = project_with_options(
        "pub fn value(data:[2147483647]u8)->int",
        CheckOptions {
            target: "pointer32".into(),
            ..Default::default()
        },
    );
    let verified = project.verify().unwrap();
    let core = ril_compiler::lower::lower_core_for(
        &verified,
        ril_compiler_core::target::TargetLayout::POINTER32,
    )
    .unwrap();
    let signature = &core.external_functions[0].signature;
    assert!(matches!(
        signature.arena[signature.result as usize],
        TypeNode::Integer {
            bits: 32,
            signed: true
        }
    ));
    assert!(matches!(
        signature.arena[signature.parameters[0] as usize],
        TypeNode::Array {
            length: Some(2147483647),
            ..
        }
    ));
}

#[test]
fn range_typeof_preserves_the_endpoint_integer_type() {
    let core = schema(
        "pub type ByteRange=typeof (0u8..0u8)\npub type IntRange=typeof (0..0)\npub fn ranges(value:ByteRange)->IntRange",
    );
    let signature = &core.external_functions[0].signature;
    let TypeNode::Range(byte) = signature.arena[signature.parameters[0] as usize] else {
        panic!("{signature:?}")
    };
    let TypeNode::Range(integer) = signature.arena[signature.result as usize] else {
        panic!("{signature:?}")
    };
    assert!(matches!(
        signature.arena[byte as usize],
        TypeNode::Integer {
            bits: 8,
            signed: false
        }
    ));
    assert!(matches!(
        signature.arena[integer as usize],
        TypeNode::Integer {
            bits: 64,
            signed: true
        }
    ));
}
