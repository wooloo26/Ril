use super::*;
fn judgment(source: &str, function: &str) -> Judgment {
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    analyze(&parsed.program).judgments[function].clone()
}
#[test]
fn a_direct_affine_local_handler_has_a_finite_proof_without_assuming_its_own_arm() {
    let proof = judgment(
        "eff Read{get()->int}\nfn finite()->int{with Read::get()->resume 1;Read::get()}",
        "finite",
    );
    assert!(!proof.unresolved && !proof.may_diverge, "{proof:?}");
    let proof = judgment(
        "eff Read{get()->int}\nfn bad()->int{with Read::get()->resume Read::get();Read::get()}",
        "bad",
    );
    assert!(proof.unresolved);
    let proof = judgment(
        "eff Read{get()->int}\nfn bad()->int{with Read::get()->loop{};Read::get()}",
        "bad",
    );
    assert!(proof.may_diverge);
    let proof = judgment(
        "eff Invoke{run(fn()->int)->int}\nfn action()->int{1}\nfn bad()->int{with Invoke::run(action)->resume action();Invoke::run(\\->1)}",
        "bad",
    );
    assert!(proof.unresolved);
}
#[test]
fn lexical_shadowing_never_borrows_a_same_named_globals_finite_proof() {
    for source in [
        "fn work()->int{1}\nfn spin()->int{loop{}}\nfn bad()->int{let work=spin;work()}",
        "fn work()->int{1}\nfn spin()->int{loop{}}\nfn bad()->int{let (work,_other)=(spin,1);work()}",
        "fn work()->int{1}\nfn bad()->int{let f=\\work->work();f(\\->loop{})}",
        "fn work()->int{1}\nfn bad(){for [1] as work{work()}}",
        "fn work()->int{1}\nfn bad()->int{work() where fn work()->int{loop{}}}",
        "fn bad()->int{let recursive=\\->recursive();recursive()}",
    ] {
        let proof = judgment(source, "bad");
        assert!(proof.unresolved || proof.may_diverge, "{source}: {proof:?}");
    }
    let proof = judgment(
        "fn apply(action:fn()->int)->int{{let action=1};action()}",
        "apply",
    );
    assert_eq!(proof.callable_parameters, [0].into());
}
#[test]
fn expected_patterns_guarded_fallbacks_and_result_recovery_keep_invocation_obligations() {
    for source in [
        "fn spin()->int{loop{}}\nfn bad()->bool{1 is spin()}",
        "fn spin()->int{loop{}}\nfn bad()->int{let Some(value)=None else spin();value}",
        "fn spin()->int{loop{}}\nfn bad()->int{Err(1) ?? \\error->spin()}",
    ] {
        let proof = judgment(source, "bad");
        assert!(proof.unresolved || proof.may_diverge, "{source}: {proof:?}");
    }
    let proof = judgment("fn finite()->int{None ?? 1}", "finite");
    assert!(!proof.unresolved && !proof.may_diverge);
}
