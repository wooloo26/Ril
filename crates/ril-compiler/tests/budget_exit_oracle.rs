//! Independent finite execution model: no heap/proof implementation is reused.
//! Incomplete answers are never counted as accepted programs by this oracle.
use ril_compiler::{CompilationOutcome, Session};

#[derive(Clone, Copy, Debug)]
enum Limit {
    Zero,
    ExhaustBeforeInspection,
    Complete,
    Unknown,
}

impl Limit {
    fn syntax(self) -> &'static str {
        match self {
            Self::Zero => "0",
            Self::ExhaustBeforeInspection => "1",
            Self::Complete => "100",
            Self::Unknown => "quota",
        }
    }
    fn inspected_on_every_execution(self, before: bool, action: bool, recovery: bool) -> bool {
        before
            || match self {
                Self::Zero | Self::ExhaustBeforeInspection => recovery,
                Self::Complete => action,
                Self::Unknown => action && recovery,
            }
    }
}

fn program(limit: Limit, before: bool, action: bool, recovery: bool) -> String {
    let inspect = |yes| if yes { "assert(result is Err(_));" } else { "" };
    // The IIFE owns the business Result. Its read-only input capture is allowed
    // inside the budget. The helper call consumes a charge before any possible
    // action inspection, so quota 1 necessarily takes the recovery path.
    format!(
        r#"
fn dummy() {{}}
fn example(quota:int) {{
    (\ -> {{
        let result:Result<int,str>=Err("must inspect")
        {before}
        {{
            with Div::exhausted() -> {{{recovery} ()}}
            Div::budget({limit}, \ -> {{dummy(); {action} ()}})
        }}
    }})()
}}
"#,
        before = inspect(before),
        recovery = inspect(recovery),
        action = inspect(action),
        limit = limit.syntax()
    )
}

#[test]
fn accepted_budget_flows_cover_every_concrete_result_exit() {
    for limit in [
        Limit::Zero,
        Limit::ExhaustBeforeInspection,
        Limit::Complete,
        Limit::Unknown,
    ] {
        for bits in 0..8 {
            let before = bits & 1 != 0;
            let action = bits & 2 != 0;
            let recovery = bits & 4 != 0;
            let source = program(limit, before, action, recovery);
            let outcome = Session::new(source.as_bytes().to_vec()).check();
            if matches!(outcome, CompilationOutcome::Accepted { .. }) {
                assert!(
                    limit.inspected_on_every_execution(before, action, recovery),
                    "unsound acceptance for {limit:?}, before={before}, action={action}, recovery={recovery}:\n{source}"
                );
            }
            // Keep a positive control for every limit and every combination of
            // later checks: a conservative checker cannot pass by refusing all.
            if before || (action && recovery) || matches!(limit, Limit::Zero) && recovery {
                assert!(
                    matches!(outcome, CompilationOutcome::Accepted { .. }),
                    "entry inspection should remain covered for {limit:?}: {outcome:?}\n{source}"
                );
            }
        }
    }
}
