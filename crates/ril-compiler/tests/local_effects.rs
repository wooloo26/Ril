use ril_compiler::{CompilationOutcome, Session};

fn accepted(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}

fn rejects(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
        "{source}: {outcome:?}"
    );
}

#[test]
fn local_effects_have_lexical_declaration_identity() {
    accepted(
        "fn example()->int{with Local::read()->resume 1;Local::read() where eff Local{read()->int}}",
    );
    accepted(
        "fn number()->int{with Local::read()->resume 1;Local::read() where eff Local{read()->int}}\nfn text()->str{with Local::read()->resume \"one\";Local::read() where eff Local{read()->str}}\nfn example(){assert(number()==1&&text()==\"one\")}",
    );
    accepted(
        "eff Read{get()->int}\nfn example(){with Read::get()->resume 7;let inner={with Read::get()->resume \"inner\";Read::get() where eff Read{get()->str}};assert(inner==\"inner\"&&Read::get()==7)}",
    );
    rejects(
        "fn example(){ {with Local::read()->resume 1;Local::read();where eff Local{read()->int}};Local::read()}",
        "E0204",
    );
}

#[test]
fn local_effects_can_be_forwarded_within_their_block() {
    accepted(
        "fn example()->int{let action=\\->Local::read();with Local::read()->resume 1;action() where eff Local{read()->int}}",
    );
    accepted(
        "fn example()->int{with Local::read()->resume 1;helper() where eff Local{read()->int};fn helper()->int @Local{Local::read()}}",
    );
}

#[test]
fn local_effects_cannot_escape_through_annotations_or_callable_graphs() {
    rejects(
        "fn example()->int @Local{Local::read() where eff Local{read()->int}}",
        "E0618",
    );
    rejects(
        "fn example()->fn()->int{\\->Local::read() where eff Local{read()->int}}",
        "E0618",
    );
    rejects(
        "fn example()->fn()->fn()->int{\\-> \\->Local::read() where eff Local{read()->int}}",
        "E0618",
    );
    rejects(
        "type Holder={mut read:fn()->int}\nfn example(){let mut target=Holder.{read:\\->0};{target.read=\\->Local::read();where eff Local{read()->int}}}",
        "E0618",
    );
}
