use ril_compiler::{
    ast::{
        TypeKind,
        walk::{Node, walk},
    },
    frontend::{Frontend, UnitKind, frontend},
    hir::{DefId, DefinitionKind},
    input::{DefinitionSource, IndexError, SourceIndex},
    library::{LibraryTypeId, OperationPhase},
    source::FileId,
    types::{
        AccessTerm, ParameterAccess, PrimitiveType, ReturnTerm, TypeHead, TypeTemplates,
        TypeTermKind,
    },
};
use ril_ir::{TargetSpec, layout::IntegerType};
use std::{io, path::Path};

fn compile(text: &str) -> Frontend {
    frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        if path == Path::new("root.ril") {
            Ok(text.as_bytes().to_vec())
        } else {
            Err(io::ErrorKind::NotFound.into())
        }
    })
    .unwrap()
}

fn definition(input: &SourceIndex<'_>, name: &str) -> DefId {
    input
        .hir
        .definitions
        .iter()
        .enumerate()
        .find_map(|(index, definition)| {
            (definition.name == name && definition.span.is_some_and(|span| span.file == FileId(0)))
                .then_some(DefId(index))
        })
        .unwrap()
}

#[test]
fn checking_inputs_preserve_default_scope_formals_and_source_body_identity() {
    let result = compile(
        r#"
type Cell = { var count: i64 }
type Slot<T> = { var via item: T }
fn fallback(first: i64, second: i64 = first) -> i64 { second }
fn observe(ref value: Cell) -> ref(value) Cell { value }
fn keep<T>(via value: T) -> infer T { value }
"#,
    );
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let input = SourceIndex::new(&result).unwrap();
    let templates = TypeTemplates::lower(&input).unwrap();
    let slot = definition(&input, "Slot");
    let Some(DefinitionSource::Type(slot_syntax)) = input.definition(slot) else {
        panic!("expected Slot");
    };
    let TypeTermKind::Record { fields, .. } = &templates
        .get(input.type_id(slot_syntax.value.as_ref().unwrap()).unwrap())
        .unwrap()
        .kind
    else {
        panic!("expected Slot schema");
    };
    let mode = fields[0].mode.unwrap();
    assert!(mode.replaceable);
    let AccessTerm::Inferred(mode) = mode.access else {
        panic!("expected member access binder");
    };
    assert_eq!(
        input.hir.mode_parameters[mode.0].owner,
        ril_compiler::hir::ModeOwner::Definition(slot)
    );
    let fallback = definition(&input, "fallback");
    let signature = &templates.signatures[&fallback];
    assert_eq!(signature.phase, OperationPhase::Runtime);
    assert_eq!(
        input.definition_scope(fallback),
        Some(signature.callable.scope)
    );
    assert!(matches!(
        input.definition(fallback),
        Some(DefinitionSource::Function(_))
    ));
    let default = input
        .expression(signature.callable.parameters[1].default.unwrap())
        .unwrap();
    let default_scope = input.expression_scope(default.span).unwrap();
    assert_ne!(default_scope, signature.callable.scope);
    assert_eq!(
        input.hir.scopes[default_scope.0].parent,
        Some(signature.callable.scope)
    );
    let first = signature.callable.parameters[0].binding.unwrap();
    assert!(
        input
            .references_at(default.span)
            .any(|reference| reference.definition == first)
    );

    let observed = &templates.signatures[&definition(&input, "observe")].callable;
    let ReturnTerm::Ref(sources) = &observed.result_access else {
        panic!("expected a resolved root source");
    };
    assert_eq!(sources, &[observed.parameters[0].binding.unwrap()]);
    let keep = &templates.signatures[&definition(&input, "keep")].callable;
    let ParameterAccess::Inferred(mode) = keep.parameters[0].access else {
        panic!("expected a mode binder");
    };
    assert_eq!(
        result
            .sources
            .slice(input.hir.mode_parameters[mode.0].span)
            .unwrap(),
        b"via"
    );
}

#[test]
fn overlapping_type_spans_keep_distinct_pattern_mode_and_data_binders() {
    let result = compile(
        r#"
type Select = \T -> match <T> {
    <{ let M item: let U, ..let Rest }> -> <U>,
    _ -> <never>,
}
"#,
    );
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let input = SourceIndex::new(&result).unwrap();
    let templates = TypeTemplates::lower(&input).unwrap();
    let wrapper = walk(&result.files[&FileId(0)].program)
        .find_map(|node| match node {
            Node::Type(ty) if matches!(ty.kind, TypeKind::PatternMode { .. }) => Some(ty),
            _ => None,
        })
        .unwrap();
    let TypeKind::PatternMode { ty: inner, .. } = &wrapper.kind else {
        unreachable!()
    };
    assert_eq!(wrapper.span, inner.span);
    let wrapper_id = input.type_id(wrapper).unwrap();
    let inner_id = input.type_id(inner).unwrap();
    assert_ne!(wrapper_id, inner_id);
    assert_eq!(input.types_at(wrapper.span).count(), 2);
    let TypeTermKind::PatternMode { binder, ty } = &templates.get(wrapper_id).unwrap().kind else {
        panic!("expected mode binder");
    };
    assert_eq!(input.hir.definitions[binder.0].name, "M");
    assert_eq!(*ty, inner_id);
    let TypeTermKind::PatternBinder(Some(binder)) = &templates.get(inner_id).unwrap().kind else {
        panic!("expected data binder");
    };
    assert_eq!(input.hir.definitions[binder.0].name, "U");
}

#[test]
fn optional_sugar_keeps_the_standard_identity_and_generic_arity_is_not_discarded() {
    let result = compile(
        r#"
type Option<T> = { value: T }
type Local = Option<i64>
type Standard = ?i64
type Unchecked = i64<str>
"#,
    );
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let input = SourceIndex::new(&result).unwrap();
    let templates = TypeTemplates::lower(&input).unwrap();
    let value = |name| {
        let Some(DefinitionSource::Type(declaration)) = input.definition(definition(&input, name))
        else {
            panic!("expected type declaration");
        };
        templates
            .get(input.type_id(declaration.value.as_ref().unwrap()).unwrap())
            .unwrap()
    };
    let TypeTermKind::Apply {
        head: TypeHead::Definition(local),
        ..
    } = value("Local").kind
    else {
        panic!("expected local alias");
    };
    let TypeTermKind::Apply {
        head: TypeHead::Definition(standard),
        ..
    } = value("Standard").kind
    else {
        panic!("expected standard optional");
    };
    assert_ne!(local, standard);
    assert_eq!(input.hir.library_types[&standard], LibraryTypeId::Option);
    let TypeTermKind::Apply {
        head: TypeHead::Primitive(PrimitiveType::Integer(IntegerType::I64)),
        arguments,
    } = &value("Unchecked").kind
    else {
        panic!("expected primitive application");
    };
    assert_eq!(arguments.len(), 1);
    for target in TargetSpec::ABSTRACT {
        assert_eq!(
            target
                .value_layout(PrimitiveType::Integer(IntegerType::I64).representation())
                .size(),
            8
        );
    }
}

#[test]
fn mapped_modes_and_values_use_the_coordinate_scope_and_keys_keep_the_outer_scope() {
    let result = compile(
        r#"
type Project = \T -> <{ modeof T.(K) [keyof T as K]: T.(K) }>
"#,
    );
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let input = SourceIndex::new(&result).unwrap();
    let templates = TypeTemplates::lower(&input).unwrap();
    let mapped = templates
        .nodes
        .iter()
        .find(|node| {
            node.span.file == FileId(0) && matches!(node.kind, TypeTermKind::Mapped { .. })
        })
        .unwrap();
    let TypeTermKind::Mapped {
        scope,
        binder,
        keys,
        value,
        ..
    } = &mapped.kind
    else {
        unreachable!()
    };
    let keys = input.expression(*keys).unwrap();
    assert_ne!(input.expression_scope(keys.span), Some(*scope));
    assert_eq!(templates.get(*value).unwrap().scope, *scope);
    assert_eq!(
        input.hir.definitions[binder.0].kind,
        DefinitionKind::Parameter
    );
    assert!(matches!(
        input.definition(*binder),
        Some(DefinitionSource::MappedCoordinate(_))
    ));
}

#[test]
fn rejected_sources_do_not_construct_checking_inputs() {
    let result = compile("fn invalid() -> i64 { missing }");
    assert!(matches!(
        SourceIndex::new(&result),
        Err(IndexError::FrontendRejected)
    ));
}
