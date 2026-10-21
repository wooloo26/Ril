//! Independent constructor payload replay from the genuine type header and
//! each actual supplied operand. No named invocation is invented for a tag.
use super::*;
use crate::sema::{
    copy_contract::CopyCallEvent,
    model::{Callable, ConstructorInfo},
};
use ril_syntax::ast::PatternKind;

impl Replay<'_> {
    fn original_constructor_payload(
        &self,
        constructor: &ConstructorInfo,
        callee_syntax: &Expr,
    ) -> Check<TypeExpr> {
        let family = match &constructor.owner {
            Ty::Named(name)
            | Ty::Applied {
                constructor: name, ..
            } => name,
            _ => return Err("constructor source has no nominal declaration family".into()),
        };
        if let Some((declaration, payload)) =
            crate::sema::source_types::standard_data::constructor_payload(&constructor.tag)
        {
            require(
                family == declaration.name() && !constructor.nominal && constructor.has_payload,
                "standard constructor changed its canonical family or kind",
            )?;
            let canonical = payload
                .syntax(
                    constructor.span,
                    &mut crate::sema::source_types::WorkLimit::new(4096),
                )
                .map_err(|error| error.to_string())?;
            let actual = constructor
                .payload_syntax
                .as_ref()
                .ok_or("standard constructor lost its source payload")?;
            let key =
                crate::static_eval::effects::bounded_argument_key(&canonical, &BTreeMap::new())
                    .ok_or("standard constructor payload exceeds its source bound")?;
            require(
                crate::static_eval::effects::bounded_argument_key(actual, &BTreeMap::new())
                    == Some(key),
                "standard constructor changed its original source declaration",
            )?;
            return Ok(canonical);
        }
        let declaration = self
            .facts
            .external_type_declarations
            .get(family)
            .ok_or_else(|| "constructor source lost its genuine type declaration".to_owned())?;
        let program = self
            .facts
            .source_program
            .as_ref()
            .ok_or_else(|| "constructor source has no actual frozen Program".to_owned())?;
        // Nested/captured declaration instances need a lexical declaration
        // receipt. The built-in Step has one exact owned canonical header;
        // its namespace, synthetic span or current metadata alone is no proof.
        require(program.statements.iter().any(|statement|
            matches!(&statement.kind, StmtKind::Type(actual) if actual == declaration))
            || declaration == &crate::sema::model::iteration::step_declaration(),
            "constructor payload header lacks its actual Source or exact canonical declaration")?;
        let (raw, variant_parameters) = if declaration.nominal {
            require(
                constructor.nominal
                    && constructor.tag == declaration.name
                    && constructor.span == declaration.span,
                "constructor payload changed its genuine nominal declaration",
            )?;
            (declaration.value.as_ref(), &[][..])
        } else {
            require(
                !declaration.opaque && !constructor.nominal,
                "constructor payload borrowed an opaque or nominal representation",
            )?;
            let variant = declaration
                .variants
                .iter()
                .find(|variant| {
                    format!("{}::{}", declaration.name, variant.name) == constructor.tag
                })
                .ok_or_else(|| "constructor payload has no genuine variant header".to_owned())?;
            require(
                constructor.span == variant.span,
                "constructor payload changed its genuine variant declaration",
            )?;
            (variant.payload.as_ref(), variant.generics.as_slice())
        };
        let raw = raw.ok_or_else(|| "nullary data tag claims a callable payload".to_owned())?;
        crate::static_eval::effects::bounded_argument_key(raw, &BTreeMap::new())
            .ok_or_else(|| "constructor payload source exceeds its replay admission".to_owned())?;
        if declaration.generics.is_empty() && variant_parameters.is_empty() {
            return self.closed_alias(raw);
        }
        // A closed declaration payload independent of its nominal value/type
        // indices does not borrow those indices from a receiving annotation.
        if crate::static_eval::effects::type_dependencies(raw)
            .iter()
            .all(|name| {
                declaration
                    .generics
                    .iter()
                    .chain(variant_parameters)
                    .all(|parameter| &parameter.name != name)
            })
        {
            return self.closed_alias(raw);
        }
        let ExprKind::Generic { base, arguments } = &callee_syntax.kind else {
            return Err(
                "constructor payload requires its original explicit instance source".into(),
            );
        };
        let name = match &base.kind {
            ExprKind::Name(name) => name.clone(),
            ExprKind::Path(path) => path.join("::"),
            _ => return Err("constructor instance lost its original declaration Source".into()),
        };
        require(
            name == constructor.tag,
            "constructor instance source targets another declaration",
        )?;
        let layout = self
            .facts
            .target_layout
            .ok_or_else(|| "constructor instance has no frozen static layout".to_owned())?;
        let normalized = crate::static_eval::normalize_constructor_arguments(
            declaration,
            arguments,
            &self.facts.external_type_declarations,
            layout,
        )
        .map_err(|_| {
            "constructor instance source cannot independently normalize its true arguments"
                .to_owned()
        })?;
        normalized
            .payloads
            .get(&constructor.tag)
            .cloned()
            .flatten()
            .ok_or_else(|| {
                "constructor instance equation excludes the actual source tag".to_owned()
            })
    }

    pub(super) fn constructor_input_sources(
        &self,
        event: &CopyCallEvent,
        syntax: &Expr,
        callee: &Value,
        context: InvocationContext,
        sites: &super::super::explicit_named::SourceSites<'_>,
    ) -> Check {
        let application = AstApplication::from_ast(syntax)
            .ok_or_else(|| "constructor source has no genuine application".to_owned())?;
        let callee_syntax = application.callee;
        let arguments = &application.operands;
        for callable in &callee.callables {
            let Callable::Constructor(name) = callable else {
                continue;
            };
            let constructor =
                self.facts.constructors.get(name).ok_or_else(|| {
                    "constructor source lost its actual registered tag".to_owned()
                })?;
            let payload = self.original_constructor_payload(constructor, callee_syntax)?;
            let payload_key = self.normalized_key(&payload, &BoundScope::default())?;
            if source_reception::sensitive(&payload_key, &mut 4096) == Some(false) {
                continue;
            }
            let declared = constructor.payload_syntax.as_ref().ok_or_else(|| {
                "constructor source erased its sensitive payload syntax".to_owned()
            })?;
            require(
                self.normalized_key(declared, &BoundScope::default())? == payload_key,
                "constructor payload differs from its original declaration/instance source",
            )?;
            let expected: Vec<_> = match (&payload_key, arguments.len()) {
                (_, 1) => vec![payload_key],
                (ArgumentKey::Tuple(items), count) if count == items.len() => items.clone(),
                _ => {
                    return Err(
                        "constructor source changed its single tuple payload boundary".into(),
                    );
                }
            };
            let preparations: Vec<_> = self
                .facts
                .call_arguments
                .iter()
                .filter(|row| row.source_event == event.id)
                .collect();
            let [preparation] = preparations.as_slice() else {
                return Err(
                    "constructor source lost its unique actual argument preparation".into(),
                );
            };
            require(
                preparation.target.is_none()
                    && preparation.evaluation_complete
                    && preparation.slots.len() == expected.len()
                    && preparation.supplied.len() == arguments.len(),
                "constructor source preparation changed its real target, arity or completion",
            )?;
            let mut written = BTreeMap::new();
            for argument in arguments {
                let slot = if let Some(label) = argument.label {
                    callee.signature.as_ref().and_then(|parameters| {
                        parameters.iter().position(|parameter|
                        matches!(&parameter.pattern.kind, PatternKind::Name(name) if name.as_str() == label))
                    })
                } else {
                    (0..expected.len()).find(|slot| !written.contains_key(slot))
                }
                .ok_or_else(|| {
                    "constructor source argument has no actual label/position slot".to_owned()
                })?;
                require(
                    written.insert(slot, argument.expression).is_none(),
                    "constructor source supplies one actual slot twice",
                )?;
            }
            for (slot, expected) in expected.iter().enumerate() {
                if source_reception::sensitive(expected, &mut 4096) == Some(false) {
                    continue;
                }
                require(
                    preparation.slots.get(slot) == Some(&ArgumentSource::Supplied),
                    "constructor source payload is missing its real supplied operand",
                )?;
                let actual_syntax = written.get(&slot).ok_or_else(|| {
                    "constructor source operand has no genuine argument AST".to_owned()
                })?;
                let token = preparation
                    .supplied
                    .get(&(slot as u32))
                    .ok_or_else(|| "constructor source lost its actual operand token".to_owned())?;
                let actual = self
                    .facts
                    .expressions
                    .get(token.expression)
                    .ok_or_else(|| {
                        "constructor source operand token is outside its arena".to_owned()
                    })?;
                require(
                    actual.source_id.is_some()
                        && actual.source_id == actual_syntax.hir_id
                        && token.allocation_epoch <= self.facts.allocation_history.len()
                        && self
                            .facts
                            .invocation_expressions
                            .iter()
                            .filter(|row| {
                                row.expression == token.expression
                                    && row.context == context
                                    && row.argument_of == Some((event.id, slot as u32))
                            })
                            .count()
                            == 1,
                    "constructor source operand belongs to another event, slot or Source occurrence",
                )?;
                self.input_operand_interval(event, slot, token.expression, context, sites)?;
                let key = self.original_observed_source_key(
                    actual_syntax,
                    token.expression,
                    context,
                    sites,
                );
                let fresh =
                    source_reception::construction(actual_syntax, &mut 4096).ok_or_else(|| {
                        "constructor source construction exceeds its replay budget".to_owned()
                    })?;
                let answer = match key {
                    Ok(key) => {
                        source_reception::compatible(expected, &key, Some(&fresh), &mut 4096)
                    }
                    Err(_) => source_reception::empty_context(expected, &fresh, &mut 4096),
                };
                require(
                    answer == Some(true),
                    "constructor original whole input source does not prove its declared payload coordinates",
                )?;
            }
        }
        Ok(())
    }
}
