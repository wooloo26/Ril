//! Finite incoming Result graphs keep each conditional borrowed producer.
//! This describes unknown input contents; it creates no local allocation proof.
use super::*;

impl Checker {
    pub(in crate::sema::checker) fn formal_channel_result_graph(
        &mut self,
        ty: Ty,
        index: u32,
        span: Span,
        seen: &mut BTreeSet<String>,
    ) -> Value {
        let mut value = self.formal_result(ty.clone(), span);
        let Ty::Result(ok, error) = &ty else {
            return value;
        };
        if !ok.scalar() || !error.scalar() {
            let node = self.heap.symbolic(
                Pivot(self.heap.nodes.len() as u32),
                // Outside-producer duties use a sentinel until reception.
                // The object itself still belongs to a registered lexical
                // scope, just like every other symbolic formal heap node.
                ScopeId(0),
                value.cause,
            );
            value.origins = Origins::one(node);
            value.permission = Permission::Read;
            value.publication = Publication::Live;
        }
        fn charge(work: &mut usize, depth: usize) -> bool {
            let Some(next) = work.checked_sub(1) else {
                return false;
            };
            *work = next;
            depth <= 64
        }
        fn admitted(ty: &Ty, work: &mut usize, depth: usize) -> bool {
            if !charge(work, depth) {
                return false;
            }
            match ty {
                Ty::Result(ok, error) => {
                    admitted(ok, work, depth + 1) && admitted(error, work, depth + 1)
                }
                Ty::Immutable(inner) => admitted(inner, work, depth + 1),
                Ty::Optional(inner) => admitted(inner, work, depth + 1),
                _ => ty.scalar(),
            }
        }
        // The first incoming-graph contract covers finite ordinary Result
        // trees. Collections need quantified members, and nominal/recursive
        // leaves need separate shape evidence; they cannot borrow this bound.
        if !admitted(&ty, &mut 256, 0) {
            return value;
        }
        // Recursion and work exhaustion retain the outer duty and incomplete
        // graph. The message boundary will reject completeness, rather than
        // treating the unrepresented contents as absent.
        if seen.len() > 128 || !seen.insert(format!("incoming-result:{ty:?}")) {
            return value;
        }
        let success = self.formal_value(
            *ok.clone(),
            index.wrapping_mul(31).wrapping_add(1),
            span,
            &mut seen.clone(),
        );
        let failure = self.formal_value(
            *error.clone(),
            index.wrapping_mul(31).wrapping_add(2),
            span,
            &mut seen.clone(),
        );
        value.results.extend(&success.results);
        value.results.extend(&failure.results);
        value.must_results.extend(
            success
                .must_results
                .intersection(&failure.must_results)
                .copied(),
        );
        value.result_success = Some(Box::new(success));
        value.result_error = Some(Box::new(failure));
        value
    }
}
