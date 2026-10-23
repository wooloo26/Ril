//! Actual static producers and tag observations. Universal path proof is separate.
use super::*;

pub(super) fn tag(path: &[String]) -> Option<bool> {
    match path {
        [name] if name == "Ok" => Some(true),
        [name] if name == "Err" => Some(false),
        [prelude, name] if prelude == "Prelude" && name == "Ok" => Some(true),
        [prelude, name] if prelude == "Prelude" && name == "Err" => Some(false),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ProducerId(pub u32);

#[derive(Clone, Debug, PartialEq)]
pub(super) struct Produced {
    pub id: ProducerId,
    pub success: bool,
    pub payload: StaticValue,
    pub ty: Option<Box<TypeExpr>>,
    pub source_type: Option<std::sync::Arc<crate::sema::model::SourceTypeWitness>>,
}

#[derive(Clone, Debug)]
struct Production {
    span: Span,
    inspections: Vec<Span>,
}

#[derive(Default)]
pub(super) struct Ledger {
    productions: Vec<Production>,
}

#[derive(Clone, Debug)]
pub(crate) struct Receipt {
    pub producer: ProducerId,
    pub production: Span,
    pub inspections: Vec<Span>,
}

impl Ledger {
    pub fn has_producers(&self) -> bool {
        !self.productions.is_empty()
    }
    pub fn receipt(&self, id: ProducerId) -> Option<Receipt> {
        let production = self.productions.get(id.0 as usize)?;
        (!production.inspections.is_empty()).then(|| Receipt {
            producer: id,
            production: production.span,
            inspections: production.inspections.clone(),
        })
    }
}

impl Evaluator {
    pub(super) fn produce_result(
        &mut self,
        success: bool,
        payload: StaticValue,
    ) -> Result<StaticValue> {
        let span = self.result_site.ok_or_else(|| {
            Failure::Unsupported("static Result producer has no evaluated call site".into())
        })?;
        let id = ProducerId(u32::try_from(self.results.productions.len()).map_err(|_| {
            Failure::Unsupported("static Result producer identity allowance".into())
        })?);
        self.results.productions.push(Production {
            span,
            inspections: vec![],
        });
        Ok(StaticValue::Result(Box::new(Produced {
            id,
            success,
            payload,
            ty: None,
            source_type: None,
        })))
    }
    pub(super) fn inspect_static_result(&mut self, id: ProducerId, span: Span) -> Result<()> {
        let production = self
            .results
            .productions
            .get_mut(id.0 as usize)
            .ok_or_else(|| {
                Failure::Unsupported("static Result inspection has no producer".into())
            })?;
        if !production.inspections.contains(&span) {
            production.inspections.push(span);
        }
        Ok(())
    }
}
