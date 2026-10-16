use ril_compiler::sema::facts::Permission;
use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

#[test]
fn concrete_or_pattern_calls_type_inactive_tags_without_joining_their_payloads() {
    accepted(
        "type Choice{Left(int),Right(int)}\nfn choose(value:Choice)->int{match value{Choice::Left(number)|Choice::Right(number)->number}}\nfn example(){assert(choose(Choice::Left(11))==11);assert(choose(Choice::Right(22))==22)}",
    );
    accepted(
        "fn choose(value:Result<int,int>)->int{match value{Ok(number)|Err(number)->number}}\nfn example(){assert(choose(Ok(11))==11);assert(choose(Err(22))==22)}",
    );
}

#[test]
fn inactive_or_pattern_witnesses_do_not_add_origins_or_write_permissions() {
    for tag in ["Left", "Right"] {
        let source = format!(
            "type Cell={{mut count:int}}\ntype Choice{{Left(Cell),Right(Cell)}}\nfn example(){{let original=Cell.{{count:7}};let candidate=Choice::{tag}(original);let picked=match candidate{{Choice::Left(cell)|Choice::Right(cell)->cell}};assert(picked.count==7)}}"
        );
        let program = Session::new(source.into_bytes()).verify().unwrap();
        let facts = program.facts();
        let original = &facts
            .bindings
            .iter()
            .find(|binding| binding.name == "original")
            .unwrap()
            .value;
        let picked = &facts
            .bindings
            .iter()
            .find(|binding| binding.name == "picked")
            .unwrap()
            .value;
        assert_eq!(picked.origins, original.origins);
        assert_eq!(picked.permission, Permission::Read);
        assert!(!picked.construction);
    }
}

#[test]
fn inactive_or_pattern_schemas_still_require_matching_binders() {
    for source in [
        "type Choice{Left(int),Right(str)}\nfn example(){match Choice::Left(1){Choice::Left(value)|Choice::Right(value)->()}}",
        "type Choice{Left(int),Right(int)}\nfn example(){match Choice::Left(1){Choice::Left(left)|Choice::Right(right)->()}}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0346")),
            "{source}: {outcome:?}"
        );
    }
}
