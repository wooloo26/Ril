use ril_compiler::{CompilationOutcome, Session, sema::resource_copy::CopyDischarge};

fn positive_fixture() -> &'static str {
    ril_test::case_source("tests/regressions/copy.ril::private-helpers")
}
const DUP: &str = "fn duplicate<T>(source:T)->T @Fiber{clone(source)}\n";
fn reject(source: &str, code: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|item|item.code==code)),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn private_helpers_use_the_actual_sender_contract_and_keep_ordinary_copies_separate() {
    let verified = Session::new(positive_fixture().as_bytes().to_vec())
        .verify()
        .unwrap();
    let facts = verified.facts();
    let closure = facts.copy_template_closure.as_ref().unwrap();
    assert!(
        closure
            .discharges
            .values()
            .any(|proof| matches!(proof, CopyDischarge::Ordinary(_)))
    );
    assert!(
        closure
            .discharges
            .values()
            .any(|proof| matches!(proof, CopyDischarge::Sender(_)))
    );
    assert!(
        facts
            .copy_boundaries
            .iter()
            .filter(|boundary| boundary.template)
            .all(|boundary| boundary.output.is_none())
    );
    for ((instance, _), proof) in &closure.discharges {
        if let CopyDischarge::Sender(id) = proof {
            let event = &facts.resource_clones[id.0 as usize];
            assert_eq!(event.invocation, Some(*instance));
            assert_eq!(
                event.source_descriptor.as_ref().unwrap().channel,
                event.output_descriptor.as_ref().unwrap().channel
            );
            assert!(
                !facts
                    .copy_boundaries
                    .iter()
                    .any(|boundary| boundary.invocation == Some(*instance)
                        && boundary.output.is_some())
            );
        }
    }
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    ril_codegen::lower::lower_native_with_entry(&core, "test_native").unwrap();
}

#[test]
fn every_actual_resource_instance_still_checks_effects_and_nonclonable_payloads() {
    reject(
        "use ril/concurrent/channel\nfn duplicate<T>(source:T)->T{clone(source)}\nfn example(tx:Channel::Sender<int>) @Fiber{let _=duplicate(tx)}",
        "E0612",
    );
    for bad in [
        "fn bad(tx:Channel::Sender<int>,file:File::Handle) @Fiber{let own=duplicate(tx);Channel::close(own);let _=duplicate(file)}",
        "fn bad(tx:Channel::Sender<int>,rx:Channel::Receiver<int>) @Fiber{let own=duplicate(tx);Channel::close(own);let _=duplicate(rx)}",
        "fn bad(tx:Channel::Sender<int>) @Fiber{let own=duplicate(tx);Channel::close(own);let _=duplicate(.{sender:tx})}",
        "fn bad(tx:Channel::Sender<int>) @Fiber{let own=duplicate(tx);Channel::close(own);var count=1;count+=1;let _=duplicate(\\->count)}",
    ] {
        reject(
            &format!("use ril/concurrent/channel\nuse ril/file\n{DUP}{bad}"),
            "E0530",
        );
    }
    reject(
        "use ril/concurrent/channel\nfn duplicate<T>(source:T)->Immut<T> @Fiber{clone_immut(source)}\nfn example(tx:Channel::Sender<int>) @Fiber{let _=duplicate(tx)}",
        "E0530",
    );
}

#[test]
fn consumed_authority_and_scope_escape_cannot_borrow_a_successful_sender_event() {
    reject(
        &format!(
            "use ril/concurrent/channel\n{DUP}fn example(tx:Channel::Sender<int>) @Fiber{{let own=duplicate(tx);Channel::close(own);Channel::close(tx);let _=duplicate(tx)}}"
        ),
        "E0603",
    );
    reject(
        &format!(
            "use ril/concurrent::{{scope,TaskFault}}\nuse ril/concurrent/channel\n{DUP}fn example() @Async{{let escaped=scope \\mut s ->{{let child=s.fork(\\->());child.join()?;let (tx,rx)=Channel::bounded<int>(1);Channel::close(rx);Ok(duplicate(tx))}};assert(escaped is Ok(_)|Err(_))}}"
        ),
        "E0606",
    );
}
