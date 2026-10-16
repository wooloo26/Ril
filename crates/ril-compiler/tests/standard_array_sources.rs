use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn check(source: &str, accepted: bool) {
    for layout in ["pointer32", "pointer64"] {
        let session = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        );
        if accepted {
            let program = session
                .verify()
                .unwrap_or_else(|outcome| panic!("{layout}: {source}\n{outcome:?}"));
            ril_compiler::lower::lower_core(&program).unwrap();
        } else {
            let outcome = session.check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                    if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
                "{layout}: {source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn actual_standard_array_producers_keep_the_declared_dynamic_shell() {
    for source in [
        "halt fn example()->[]int{Parallel::map([1,2],\\x->x+1)}",
        "fn example(){let mut queue=Deque::new<int>();Deque::push_back(mut queue,1);let values:[]int=Deque::values(queue);assert(len(values)==1)}",
    ] {
        check(source, true);
    }
}

#[test]
fn known_output_count_never_turns_a_standard_dynamic_shell_into_fixed_storage() {
    check(
        "halt fn example()->[2]int{Parallel::map([1,2],\\x->x+1)}",
        false,
    );
}

#[test]
fn actual_standard_result_members_keep_their_original_inner_dimensions() {
    check(
        "fn example(){let old:[0][3]int=[];let values:[][0][3]int=Parallel::map([1],\\_->old)}",
        true,
    );
    check(
        "fn example(){let old:[0][3]int=[];let values:[][0][2]int=Parallel::map([1],\\_->old)}",
        false,
    );
}
