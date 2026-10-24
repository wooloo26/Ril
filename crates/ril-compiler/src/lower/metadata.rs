//! Select only the frontend results required to compile executable code.
use crate::sema::{SemanticFacts, model::Callable};
use ril_compiler_core::ids::CallableOwner;
use ril_ir::metadata::{ClosureSite, ProgramMetadata, RetainedHandler};

pub(super) fn lower(facts: &SemanticFacts) -> ProgramMetadata {
    ProgramMetadata {
        target_layout: facts.target_layout,
        generic_templates: facts
            .copy_template_closure
            .as_ref()
            .map(|closure| closure.templates.keys().copied().collect())
            .unwrap_or_default(),
        closure_sites: facts
            .closure_sites
            .iter()
            .map(|site| ClosureSite {
                id: site.id,
                owner: site.owner,
                source: site.source,
                span: site.span,
            })
            .collect(),
        retained_handlers: facts
            .retained_handlers
            .iter()
            .map(|handler| RetainedHandler {
                callable: match handler.callable {
                    Callable::Named(id, _) => {
                        Some(CallableOwner::Function(facts.functions[id].definition))
                    }
                    Callable::Closure(id) => facts.closures[id].site.map(CallableOwner::Lambda),
                    _ => None,
                },
                span: handler.span,
                definitions: handler
                    .handlers
                    .iter()
                    .map(|id| facts.handlers[*id].site)
                    .collect(),
            })
            .collect(),
        ..Default::default()
    }
}
