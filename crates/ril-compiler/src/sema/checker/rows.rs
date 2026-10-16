//! Open rows retain one opaque member-family edge in the ordinary value graph.
//! Type equations only select labels; they never create origins or authority.
use super::*;
use crate::sema::model::rows::{OpenTail, Row, RowIdentity, RowTail, Solver};
#[path = "row_transport.rs"]
mod transport;

impl Checker {
    pub(super) fn declare_row_contract(&mut self, function: &Function) {
        fn collect(ty: &Ty, facts: &mut BTreeMap<RowIdentity, BTreeSet<String>>) {
            match ty {
                Ty::OpenRecord { fields, row } => {
                    facts
                        .entry(row.identity.clone())
                        .or_default()
                        .extend(row.lacks.clone());
                    for (_, ty) in fields.values() {
                        collect(ty, facts);
                    }
                }
                Ty::Record(fields) => {
                    for (_, ty) in fields.values() {
                        collect(ty, facts);
                    }
                }
                Ty::Optional(ty)
                | Ty::Immutable(ty)
                | Ty::Array(ty)
                | Ty::Set(ty)
                | Ty::Range(ty) => collect(ty, facts),
                Ty::Map(a, b) | Ty::Result(a, b) => {
                    collect(a, facts);
                    collect(b, facts);
                }
                Ty::Tuple(items) => {
                    for ty in items {
                        collect(ty, facts);
                    }
                }
                Ty::Callable(parameters, result) => {
                    for ty in parameters {
                        collect(ty, facts);
                    }
                    collect(result, facts);
                }
                _ => {}
            }
        }
        // Declaration absences are independent of an invocation's selections.
        let substitutions = std::mem::take(&mut self.generic_substitutions);
        let type_witnesses = std::mem::take(&mut self.generic_type_witnesses);
        let mut facts = BTreeMap::new();
        for syntax in function
            .parameters
            .iter()
            .filter_map(|p| p.ty.as_ref())
            .chain(function.return_type.iter())
        {
            let ty = self.ty_readonly(syntax, &mut BTreeSet::new());
            collect(&self.call_inference_type(&ty), &mut facts);
        }
        self.generic_substitutions = substitutions;
        self.generic_type_witnesses = type_witnesses;
        for (identity, lacks) in facts {
            self.generic_row_lacks
                .entry(identity)
                .or_default()
                .extend(lacks);
        }
    }

    pub(super) fn row_solver(&self) -> Solver<Ty> {
        let mut solver = Solver::new("declared value row", []);
        for (identity, lacks) in &self.generic_row_lacks {
            // No variables in this solver are flexible.
            solver
                .declare_rigid(identity.clone(), lacks.iter().cloned())
                .expect("rigid declaration");
        }
        solver
    }

    pub(super) fn value_row(&self, ty: &Ty) -> Option<Row<Ty>> {
        match self.expanded(ty, &mut BTreeSet::new()) {
            Ty::Record(fields) => Some(Row::closed(fields)),
            Ty::OpenRecord { fields, mut row } => {
                if let Some(lacks) = self.generic_row_lacks.get(&row.identity) {
                    row.lacks.extend(lacks.iter().cloned());
                }
                Some(Row::open(fields, row))
            }
            _ => None,
        }
    }

    pub(super) fn row_type(row: Row<Ty>) -> Ty {
        match row.tail {
            RowTail::Closed => Ty::Record(row.fields),
            RowTail::Open(tail) => Ty::OpenRecord {
                fields: row.fields,
                row: tail,
            },
        }
    }

    pub(super) fn formal_row_tail(&mut self, row: &OpenTail, span: Span) -> Value {
        // One opaque family stands for every potentially Result-bearing member.
        // It is never an outer Result and therefore cannot be inspected by a tag
        // test on the record. Concrete invocations use the caller's real duties.
        let mut tail = self.formal_result(
            Ty::OpenRecord {
                fields: BTreeMap::new(),
                row: row.clone(),
            },
            span,
        );
        tail.outer_results.clear();
        tail.must_outer_results.clear();
        let node = self
            .heap
            .symbolic(Pivot(self.heap.nodes.len() as u32), ScopeId(0), tail.cause);
        // A row tail denotes an arbitrary member family, not one selected
        // field object, even when its containing record is a singleton.
        self.heap.set_relation(node, node, Relation::UNKNOWN);
        tail.origins = Origins::one(node);
        tail.permission = Permission::Write;
        tail.publication = Publication::Live;
        tail.stable = true;
        tail
    }

    pub(super) fn has_unresolved_row(&self, value: &Value) -> bool {
        if self.call_inference_type(&value.ty).contains_open_row() {
            return true;
        }
        let reachable = self.heap.reachable(value.origins.nodes.iter().copied());
        self.fields.iter().any(|((node, slot), child)| {
            reachable.contains(node)
                && (matches!(slot, Slot::RowTail(_))
                    || self.call_inference_type(&child.ty).contains_open_row())
        })
    }

    pub(super) fn carried_row_tail(
        &mut self,
        source: &Value,
        row: &OpenTail,
        span: Span,
    ) -> Option<Value> {
        let slot = Slot::RowTail(row.identity.clone());
        let mut witnesses = Vec::new();
        for node in &source.origins.nodes {
            let Some(child) = self.fields.get(&(*node, slot.clone())) else {
                self.unsupported(span, "open row transport requires every source alternative's complete member-family witness");
                return None;
            };
            if child.origins.nodes.is_empty() || !child.results.is_subset(&source.results) {
                self.unsupported(
                    span,
                    "open row transport requires origins and Result membership coverage",
                );
                return None;
            }
            witnesses.push(child.clone());
        }
        let Some(mut tail) = witnesses.pop() else {
            self.unsupported(span, "open row transport has no source witness");
            return None;
        };
        for child in witnesses {
            tail = tail.join(&child, self.choice(), source.cause);
        }
        tail.permission = tail.permission.meet(source.permission);
        tail.publication = if tail.publication == Publication::Immutable
            || source.publication == Publication::Immutable
        {
            Publication::Immutable
        } else if source.publication == Publication::Live {
            Publication::Live
        } else {
            tail.publication
        };
        tail.construction &= source.construction;
        tail.temporary |= source.temporary;
        tail.stable &= source.stable;
        tail.sources.extend(&source.sources);
        tail.participants.extend(&source.participants);
        tail.scoped.extend(&source.scoped);
        tail.callback_parameters.extend(&source.callback_parameters);
        tail.must_results
            .retain(|duty| source.must_results.contains(duty));
        tail.marker = source.marker || (source.construction && tail.marker);
        tail.retention_result =
            source.retention_result || (source.construction && tail.retention_result);
        tail.through_return |= source.through_return;
        tail.readonly_spread = tail.permission == Permission::Read;
        Some(tail)
    }

    pub(super) fn require_row_transport(&mut self, value: &Value, expected: &Ty, span: Span) {
        self.constrain_collection_type(value, expected, span);
        self.require_nested_row_transport(value, expected, span);
    }
}
