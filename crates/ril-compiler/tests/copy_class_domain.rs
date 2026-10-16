//! Independent finite-class checks, alongside the production copy graph oracle.
use ril_compiler::sema::{facts::*, relations::*};
use ril_compiler_core::diagnostic::CauseId;
use std::collections::BTreeMap;

#[path = "../src/sema/checker/copy_classes.rs"]
mod copy_classes;

#[test]
fn a_batch_with_multiple_objects_or_a_historical_summary_is_not_singleton() {
    let mut heap = Heap::default();
    let (first, _) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
    assert!(!copy_classes::is_summary(&[first], |node| heap.relation(node, node)));
    let (second, _) = heap.fresh(SiteId(1), ScopeId(0), CauseId(0));
    assert!(copy_classes::is_summary(&[first, second], |node| heap.relation(node, node)));
    let (_, moved) = heap.fresh(SiteId(0), ScopeId(0), CauseId(0));
    let (_, older) = moved.unwrap();
    assert!(copy_classes::is_summary(&[older], |node| heap.relation(node, node)));
}
