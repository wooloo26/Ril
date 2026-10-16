//! Values held across later evaluation must follow allocation-site recency.
//! Each wrapper belongs to one Checker's monotonically growing move history.
//! It must not be transferred between checkers or reused with a rolled-back log.
use super::*;

#[derive(Clone)]
pub(super) struct EvaluatedValue {
    value: Value,
    recency: usize,
}
impl EvaluatedValue {
    /// Call after evaluation: the new result already belongs to this epoch.
    pub fn new(value: Value, recency: usize) -> Self {
        Self { value, recency }
    }

    pub fn current_mut(&mut self, moves: &[(NodeId, NodeId)]) -> &mut Value {
        // Only node references change. Permission, loan/root participants,
        // copy/Result/condition/numeric identities retain their existing duties.
        // remap_value_origins also transports every nested payload witness.
        for &(recent, older) in &moves[self.recency..] {
            copy::remap_value_origins(&mut self.value, recent, older);
        }
        self.recency = moves.len();
        &mut self.value
    }
    pub fn current(&mut self, moves: &[(NodeId, NodeId)]) -> Value {
        self.current_mut(moves).clone()
    }
    pub fn into_current(mut self, moves: &[(NodeId, NodeId)]) -> Value {
        self.current_mut(moves);
        self.value
    }
}
