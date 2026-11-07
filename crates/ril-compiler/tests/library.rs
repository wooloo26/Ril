use ril_compiler::{
    ast::{StmtKind, TypeKind},
    frontend::{UnitKind, frontend},
    hir::{CompilationUnitOrigin, DefinitionKind},
    library::{LibraryBodyId, LibraryTypeId, OperationPhase, PrimitiveId},
    source::FileId,
};
use std::{io, path::Path};

#[test]
fn collections_keep_source_bodies_and_one_identity_for_type_and_namespace_roles() {
    let input = r#"
use ril/array as Sequence
use ril/set as Unique
use ril/set::{from as make_unique}
type Ints = Unique<i64>
halt fn map(value: i64) -> i64 { value }
fn example() -> Set<i64> {
    let _ = map(1)
    let mut values: []i64 = []
    Array::push(mut values, 1)
    Sequence::push(mut values, 2)
    let frozen = clone(ref values)
    let _ = Sequence::map(frozen, \value -> value + 1)
    make_unique(frozen)
}
"#;
    let result = frontend(Path::new("root.ril"), UnitKind::Library, |path| {
        if path == Path::new("root.ril") {
            Ok(input.as_bytes().to_vec())
        } else {
            Err(io::Error::from(io::ErrorKind::NotFound))
        }
    })
    .unwrap();
    assert!(result.is_ok(), "{:?}", result.diagnostics);
    let hir = result.hir.as_ref().unwrap();
    let reference = |path: &[&str]| {
        hir.references
            .iter()
            .find(|reference| reference.span.file == FileId(0) && reference.path == path)
            .unwrap()
    };
    let ambient_push = reference(&["Array", "push"]);
    let explicit_push = reference(&["Sequence", "push"]);
    assert_eq!(ambient_push.definition, explicit_push.definition);
    assert_eq!(
        hir.primitives[&ambient_push.definition],
        PrimitiveId::ArrayPush
    );

    let map_definition = reference(&["Sequence", "map"]).definition;
    assert_eq!(hir.library_bodies[&map_definition], LibraryBodyId::ArrayMap);
    assert_eq!(
        hir.library_bodies[&map_definition].phase(),
        OperationPhase::Dual
    );
    assert!(!hir.primitives.contains_key(&map_definition));
    let local_map = reference(&["map"]).definition;
    assert!(!hir.library_bodies.contains_key(&local_map));
    assert!(!hir.primitives.contains_key(&local_map));
    assert_eq!(PrimitiveId::ByteSize.phase(), OperationPhase::Static);
    assert_eq!(PrimitiveId::Clone.phase(), OperationPhase::Runtime);
    assert_eq!(PrimitiveId::Len.phase(), OperationPhase::Dual);
    let map = &hir.definitions[map_definition.0];
    assert_eq!(map.kind, DefinitionKind::Function);
    let map_span = map.span.unwrap();
    let map_statement = result.files[&map_span.file]
        .program
        .statements
        .iter()
        .find(|stmt| stmt.span == map_span)
        .unwrap();
    let StmtKind::Function(map) = &map_statement.kind else {
        panic!("expected source function");
    };
    assert!(map.body.is_some());
    assert_eq!(
        hir.units[&map_span.file].origin,
        CompilationUnitOrigin::Bundled
    );

    let set = reference(&["Set"]).definition;
    assert_eq!(reference(&["Unique"]).definition, set);
    assert_eq!(hir.definitions[set.0].kind, DefinitionKind::OpaqueType);
    assert_eq!(hir.library_types[&set], LibraryTypeId::Set);
    assert!(hir.definitions[set.0].span.is_some());
    let from = &hir.definitions[reference(&["make_unique"]).definition.0];
    assert_eq!(from.kind, DefinitionKind::Function);
    assert_eq!(
        hir.library_bodies[&reference(&["make_unique"]).definition],
        LibraryBodyId::SetFrom
    );
    let set_unit = &hir.units[&from.span.unwrap().file];
    assert_eq!(set_unit.namespace, Some(set));
    assert_eq!(set_unit.origin, CompilationUnitOrigin::Bundled);

    let elem = hir
        .definitions
        .iter()
        .find(|definition| definition.name == "Elem" && definition.scope == set_unit.scope)
        .unwrap();
    let span = elem.span.unwrap();
    let StmtKind::Type(elem) = &result.files[&span.file]
        .program
        .statements
        .iter()
        .find(|stmt| stmt.span == span)
        .unwrap()
        .kind
    else {
        panic!("expected source type extractor");
    };
    assert!(matches!(
        elem.value.as_ref().unwrap().kind,
        TypeKind::TypeFunction { .. }
    ));
}
