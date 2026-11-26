use std::collections::BTreeMap;

use ril_hir::DefinitionId;
use ril_source::span::Span;

use super::{
    AdtKind, Member, Ty, TypedProgram, Value,
    check::{self, Checker, Env},
    render,
};

impl TypedProgram {
    /// A graph of formatting descriptors for the concrete type at the call site.
    pub fn inspection_plan(
        &self,
        call: Span,
        argument: Span,
        types: &BTreeMap<DefinitionId, Ty>,
    ) -> Option<Value> {
        let ty = self.types.get(&argument)?.specialize(types);
        let env = Env::new(call.file, *self.inspection_scopes.get(&call)?);
        let plan = Plan::build(&mut Checker::new(&self.hir, None), &env, &ty);
        plan.needs_plan().then(|| plan.encode())
    }
}

#[derive(Clone, Default)]
enum Node {
    #[default]
    Raw,
    Redacted(String),
    Elements(usize),
    Set(usize),
    Indexed(Vec<usize>),
    Fields(BTreeMap<String, usize>),
    Tags(BTreeMap<String, Vec<usize>>),
}

pub(super) struct Plan {
    nodes: Vec<Node>,
}

impl Plan {
    pub(super) fn build(checker: &mut Checker<'_>, env: &Env, ty: &Ty) -> Self {
        let ty = check::substitute(&checker.normalize(ty), &env.generics);
        let mut builder = Builder {
            checker,
            env,
            types: vec![Ty::Unknown],
            nodes: vec![Node::Raw],
        };
        builder.visit(&ty, 0);
        Self {
            nodes: builder.nodes,
        }
    }

    fn needs_plan(&self) -> bool {
        self.nodes
            .iter()
            .any(|node| matches!(node, Node::Redacted(_) | Node::Set(_)))
    }

    // The runtime reads these descriptors with the same indexing conventions
    // as the values they describe. Descriptor 0 permits structural formatting.
    fn encode(self) -> Value {
        let index = |id: usize| Value::Int(id.into());
        let indexed = |ids: Vec<usize>| Value::Tuple(ids.into_iter().map(index).collect());
        Value::Array(
            self.nodes
                .into_iter()
                .map(|node| match node {
                    Node::Raw => Value::Unit,
                    Node::Redacted(text) => Value::Str(text),
                    Node::Elements(item) => index(item),
                    Node::Set(item) => Value::Tag("Set".into(), vec![index(item)]),
                    Node::Indexed(items) => indexed(items),
                    Node::Fields(items) => Value::Record(
                        items
                            .into_iter()
                            .map(|(name, id)| (name, index(id)))
                            .collect(),
                    ),
                    Node::Tags(items) => Value::Record(
                        items
                            .into_iter()
                            .map(|(name, ids)| (name, indexed(ids)))
                            .collect(),
                    ),
                })
                .collect(),
        )
    }

    pub(super) fn render(&self, value: &Value) -> String {
        self.render_at(value, 1)
    }

    fn render_at(&self, value: &Value, index: usize) -> String {
        let list = |values: &[Value], ids: &[usize]| {
            values
                .iter()
                .enumerate()
                .map(|(i, value)| self.render_at(value, ids.get(i).copied().unwrap_or_default()))
                .collect::<Vec<_>>()
                .join(", ")
        };
        match (self.nodes.get(index), value) {
            (Some(Node::Redacted(text)), _) => text.clone(),
            (Some(Node::Elements(item)), Value::Array(values)) => {
                let parts = values
                    .iter()
                    .map(|value| self.render_at(value, *item))
                    .collect::<Vec<_>>();
                format!("[{}]", parts.join(", "))
            }
            (Some(Node::Set(item)), Value::Map(entries)) => {
                let parts = entries
                    .iter()
                    .map(|(key, _)| self.render_at(key, *item))
                    .collect::<Vec<_>>();
                format!("Set([{}])", parts.join(", "))
            }
            (Some(Node::Indexed(ids)), Value::Tuple(values)) => format!("({})", list(values, ids)),
            (Some(Node::Indexed(ids)), Value::Map(values)) => {
                let parts = values
                    .iter()
                    .map(|(key, value)| {
                        let key = self.render_at(key, ids.first().copied().unwrap_or_default());
                        let value = self.render_at(value, ids.get(1).copied().unwrap_or_default());
                        format!("{key}: {value}")
                    })
                    .collect::<Vec<_>>();
                format!("[{}]", parts.join(", "))
            }
            (Some(Node::Fields(ids)), Value::Record(fields)) => {
                let parts = fields
                    .iter()
                    .map(|(name, value)| {
                        let value =
                            self.render_at(value, ids.get(name).copied().unwrap_or_default());
                        format!("{name}: {value}")
                    })
                    .collect::<Vec<_>>();
                format!(".{{ {} }}", parts.join(", "))
            }
            (Some(Node::Tags(tags)), Value::Tag(tag, values)) if !values.is_empty() => {
                let ids = tags.get(tag).map_or(&[][..], Vec::as_slice);
                format!("{tag}({})", list(values, ids))
            }
            _ => render(value),
        }
    }
}

struct Builder<'a, 'hir> {
    checker: &'a mut Checker<'hir>,
    env: &'a Env,
    types: Vec<Ty>,
    nodes: Vec<Node>,
}

impl Builder<'_, '_> {
    fn visit(&mut self, ty: &Ty, depth: usize) -> usize {
        if let Some(index) = self.types.iter().position(|seen| seen == ty) {
            return index;
        }
        let index = self.nodes.len();
        self.types.push(ty.clone());
        self.nodes.push(Node::Raw);
        let node = if depth > 96 {
            // A recursively expanding generic type need not have a finite shape graph.
            Node::Redacted("...".into())
        } else {
            self.describe(ty, depth + 1)
        };
        if let Some(slot) = self.nodes.get_mut(index) {
            *slot = node;
        }
        index
    }

    fn describe(&mut self, ty: &Ty, depth: usize) -> Node {
        match ty {
            Ty::Array(item) => Node::Elements(self.visit(&item.ty, depth)),
            Ty::Map(key, item) => {
                Node::Indexed(vec![self.visit(key, depth), self.visit(&item.ty, depth)])
            }
            Ty::Tuple(items) => Node::Indexed(
                items
                    .iter()
                    .map(|item| self.visit(&item.ty, depth))
                    .collect(),
            ),
            Ty::Record(fields, _) => self.record(fields, depth),
            Ty::Adt(adt) => {
                if self.checker.hir.std_type(adt.definition) == Some(ril_hir::StdType::Set)
                    && let [super::GenericValue::Type(elem)] = adt.arguments.as_slice()
                {
                    return Node::Set(self.visit(elem, depth));
                }
                let name = self
                    .checker
                    .hir
                    .definition(adt.definition)
                    .name
                    .value
                    .clone();
                match adt.kind {
                    AdtKind::Foreign => Node::Redacted(format!("<{name}>")),
                    AdtKind::Opaque | AdtKind::OpaqueSum
                        if adt.defining_scope != self.env.scope =>
                    {
                        Node::Redacted(format!("<{name}>"))
                    }
                    AdtKind::Sum | AdtKind::OpaqueSum => Node::Tags(
                        self.checker
                            .sum_variants(adt)
                            .into_iter()
                            .map(|(tag, items)| {
                                (
                                    tag,
                                    items.iter().map(|item| self.visit(item, depth)).collect(),
                                )
                            })
                            .collect(),
                    ),
                    AdtKind::Nominal | AdtKind::Opaque => {
                        match self.checker.representation(self.env, adt) {
                            Some(rep) => {
                                let index = self.visit(&rep, depth);
                                self.nodes.get(index).cloned().unwrap_or_default()
                            }
                            None => Node::Raw,
                        }
                    }
                }
            }
            _ => Node::Raw,
        }
    }

    fn record(&mut self, fields: &BTreeMap<String, Member>, depth: usize) -> Node {
        Node::Fields(
            fields
                .iter()
                .map(|(name, field)| (name.clone(), self.visit(&field.ty, depth)))
                .collect(),
        )
    }
}
