//! Invocation proofs preserve the actual callback's creation environment while
//! evaluating a helper's handler scope. This never grants finiteness from an
//! effect row alone or replaces an already selected lexical handler.
use super::*;

#[derive(Clone)]
pub(super) struct ArgumentContext {
    expression: Expr,
    aliases: BTreeMap<String, Expr>,
    parameters: BTreeMap<String, usize>,
    handlers: BTreeMap<String, Judgment>,
    arguments: std::sync::Arc<BTreeMap<String, ArgumentContext>>,
}

impl Visitor<'_> {
    pub(super) fn actual_callback(
        &mut self,
        name: &str,
        seen: &mut BTreeSet<String>,
    ) -> Option<Judgment> {
        let context = self.callback_arguments.get(name)?.clone();
        let aliases = std::mem::replace(&mut self.aliases, context.aliases);
        let parameters = std::mem::replace(&mut self.parameters, context.parameters);
        let arguments = std::mem::replace(&mut self.callback_arguments, context.arguments);
        let handlers = self.handlers.clone();
        // Uncovered callback operations still forward to the helper. Captured
        // lexical selections take precedence over its invocation handlers.
        self.handlers.extend(context.handlers);
        let result = self.callable(&context.expression, seen);
        self.aliases = aliases;
        self.parameters = parameters;
        self.callback_arguments = arguments;
        self.handlers = handlers;
        Some(result)
    }

    pub(super) fn contextual_call(
        &mut self,
        name: &str,
        arguments: &[Argument],
    ) -> Option<Judgment> {
        // Recursive edges use the independently established summary. Replaying
        // their captured environments recursively cannot establish finiteness.
        if self.contextual_calls.contains(name) {
            return None;
        }
        if self.depth >= 96 {
            return Some(Judgment::unresolved());
        }
        let function = self.functions.get(name)?.clone();
        let body = function.body.as_ref()?;
        if arguments.len() != function.parameters.len() {
            return None;
        }
        let mut callback_arguments = BTreeMap::new();
        for (parameter, argument) in function.parameters.iter().zip(arguments) {
            let PatternKind::Name(name) = &parameter.pattern.kind else {
                return None;
            };
            callback_arguments.insert(
                name.clone(),
                ArgumentContext {
                    expression: argument.value.clone(),
                    aliases: self.aliases.clone(),
                    parameters: self.parameters.clone(),
                    handlers: self.handlers.clone(),
                    arguments: self.callback_arguments.clone(),
                },
            );
        }
        let mut contextual_calls = self.contextual_calls.clone();
        contextual_calls.insert(name.into());
        let mut child = Visitor {
            functions: self.functions,
            summaries: self.summaries,
            budget_proofs: self.budget_proofs,
            budget_witnesses: vec![],
            parameters: BTreeMap::new(),
            aliases: BTreeMap::new(),
            handlers: self.handlers.clone(),
            callback_arguments: std::sync::Arc::new(callback_arguments),
            contextual_calls,
            depth: self.depth + 1,
            diagnostics: vec![],
            unsupported: vec![],
        };
        let result = child.block(body);
        self.diagnostics.extend(child.diagnostics);
        self.unsupported.extend(child.unsupported);
        self.budget_witnesses.extend(child.budget_witnesses);
        Some(result)
    }
}
