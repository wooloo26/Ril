//! Independent constructor payload replay from the genuine type header and
//! each actual supplied operand. No named invocation is invented for a tag.
use super::*;
use crate::sema::{
    copy_contract::CopyCallEvent,
    model::{Callable, ConstructorInfo},
};
use ril_syntax::ast::PatternKind;

impl Replay<'_> {
    fn declared_constructor_instance_schema(
        &self,
        syntax: &TypeExpr,
        environment: &FrozenEnvironment,
        work: &mut usize,
    ) -> Check<crate::sema::source_types::declarations::DeclaredConstructorInstance> {
        use crate::sema::source_types::declarations::{HeaderContext, constructor_instance};
        require(
            !environment.is_poisoned(),
            "constructor instance has a poisoned interpretation",
        )?;
        let hir = self
            .facts
            .semantic_hir
            .as_deref()
            .ok_or("constructor instance has no original HIR")?;
        let context = HeaderContext {
            declarations: &self.facts.external_type_declarations,
            program: self
                .facts
                .source_program
                .as_deref()
                .ok_or("constructor instance has no original Program")?,
            hir,
            lexical: self
                .lexical
                .as_ref()
                .ok_or("constructor instance has no lexical index")?,
            binders: &environment.generic_context,
            functions: &self.facts.functions,
            generic_binders: &self.facts.generic_binders,
            layout: self
                .facts
                .target_layout
                .ok_or("constructor instance has no frozen layout")?,
        };
        super::graph_sources::schema_work(work, |budget| {
            constructor_instance(syntax, context, budget)
        })
    }

    fn registered_constructor_result_source(
        &self,
        constructor: &ConstructorInfo,
        callee_syntax: &Expr,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        require(
            !constructor.typing_environment.is_poisoned(),
            "constructor result has a poisoned declaration interpretation",
        )?;
        let mut generic_names = BTreeSet::new();
        constructor.owner.generic_names(&mut generic_names);
        if !generic_names.is_empty() {
            require(
                constructor.source.is_none(),
                "constructor template claims a complete instance Source",
            )?;
            return Ok(None);
        }
        let Some(written) = constructor.source_syntax.as_deref() else {
            let program = self
                .facts
                .source_program
                .as_ref()
                .ok_or("constructor result has no frozen Source program")?;
            *work = work
                .checked_sub(program.statements.len())
                .ok_or("constructor declaration classification exceeds its work bound")?;
            let mut declared = false;
            for statement in &program.statements {
                let StmtKind::Type(declaration) = &statement.kind else {
                    continue;
                };
                *work = work
                    .checked_sub(declaration.variants.len())
                    .ok_or("constructor variant classification exceeds its work bound")?;
                declared |= declaration.nominal && declaration.name == constructor.tag
                    || declaration.variants.iter().any(|variant| {
                        format!("{}::{}", declaration.name, variant.name) == constructor.tag
                    });
            }
            let step = crate::sema::model::iteration::step_declaration();
            *work = work
                .checked_sub(step.variants.len())
                .ok_or("canonical constructor classification exceeds its work bound")?;
            declared |= step
                .variants
                .iter()
                .any(|variant| format!("{}::{}", step.name, variant.name) == constructor.tag);
            // Source-owned declarations and the exact built-in Step header
            // register result views. Standard catalog entities without a
            // source header keep their existing separate payload validation.
            require(
                !declared
                    && constructor.source.is_none()
                    && constructor.source_type_witness.is_none(),
                "constructor erased its required declaration and instance Source",
            )?;
            return Ok(None);
        };
        let TypeKind::Name { path, .. } = &written.kind else {
            return Err("constructor result is not its nominal declaration header".into());
        };
        let family = path.join("::");
        let declaration = self
            .facts
            .external_type_declarations
            .get(&family)
            .ok_or("constructor result lost its genuine type declaration")?;
        let program = self
            .facts
            .source_program
            .as_ref()
            .ok_or("constructor result has no frozen Source program")?;
        *work = work
            .checked_sub(program.statements.len())
            .ok_or("constructor declaration coverage exceeds its work bound")?;
        require(program.statements.iter().any(|statement|
            matches!(&statement.kind, StmtKind::Type(actual) if actual == declaration))
            || declaration == &crate::sema::model::iteration::step_declaration(),
            "constructor result header lacks its actual declaration")?;
        let fixed_result = if declaration.nominal {
            require(
                constructor.nominal
                    && constructor.tag == declaration.name
                    && constructor.span == declaration.span,
                "constructor result changed its nominal declaration",
            )?;
            None
        } else {
            let variant = declaration.variants.iter().find(|variant| {
                format!("{}::{}", declaration.name, variant.name) == constructor.tag
                    && variant.span == constructor.span
            });
            require(
                !constructor.nominal && !declaration.opaque && variant.is_some(),
                "constructor result changed its variant declaration",
            )?;
            let variant = variant.unwrap();
            if let Some(result) = &variant.result {
                crate::static_eval::effects::bounded_argument_key(result, &BTreeMap::new())
                    .ok_or("constructor result equation exceeds its Source admission")?;
            }
            variant.result.as_ref().filter(|result| {
                let dependencies = crate::static_eval::effects::type_dependencies(result);
                declaration
                    .generics
                    .iter()
                    .chain(&variant.generics)
                    .all(|parameter| !dependencies.contains(&parameter.name))
            })
        };
        // A GADT tag may itself state a closed result equation. The actual
        // declaration then supplies that Source even without written generic
        // arguments, independently of any receiving annotation.
        let declaration_result = if declaration.generics.is_empty()
            || matches!(callee_syntax.kind, ExprKind::Generic { .. })
        {
            None
        } else {
            Some(self.closed_alias(fixed_result
                .ok_or("constructor result has no original explicit instance Source or closed declaration equation")?)?)
        };
        let arguments = if declaration.generics.is_empty() || declaration_result.is_some() {
            vec![]
        } else {
            let ExprKind::Generic { base, arguments } = &callee_syntax.kind else {
                return Err("constructor result has no original explicit instance Source".into());
            };
            let name = match &base.kind {
                ExprKind::Name(name) => name.clone(),
                ExprKind::Path(path) => path.join("::"),
                _ => return Err("constructor result lost its original instance declaration".into()),
            };
            require(
                name == constructor.tag,
                "constructor result instance targets another declaration",
            )?;
            for argument in arguments {
                crate::static_eval::charge_type_syntax_clone(argument, work)
                    .ok_or("constructor instance arguments exceed their syntax bound")?;
            }
            arguments.clone()
        };
        let expected = declaration_result.unwrap_or_else(|| TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Name {
                path: declaration.name.split("::").map(str::to_owned).collect(),
                arguments,
            },
        });
        let environment = constructor.typing_environment.clone();
        require(
            !environment.is_poisoned(),
            "constructor result has a poisoned interpretation",
        )?;
        let view = constructor
            .source
            .ok_or("constructor result erased its admitted instance Source")?;
        require(
            view.environment == environment.id(),
            "constructor result changed its original interpretation",
        )?;
        let (actual, admitted_environment) = super::graph_sources::schema_work(work, |budget| {
            self.facts.source_types.view_schema(view, budget)
        })?;
        require(
            admitted_environment.id() == environment.id(),
            "constructor result borrowed another Source environment",
        )?;
        let expected = self.declared_constructor_instance_schema(&expected, &environment, work)?;
        require(
            expected.payloads.contains_key(&constructor.tag),
            "constructor result instance excludes the actual variant",
        )?;
        let expected = expected.schema;
        let cached = self
            .declared_constructor_instance_schema(written, &environment, work)?
            .schema;
        require(
            super::graph_sources::schema_work(work, |budget| expected.equivalent(&actual, budget))?
                && super::graph_sources::schema_work(work, |budget| {
                    expected.equivalent(&cached, budget)
                })?,
            "constructor result Source differs from its actual declaration and instance",
        )?;
        Ok(Some((actual, admitted_environment)))
    }

    pub(super) fn original_constructor_result_schema(
        &self,
        expression: &Expr,
        value: &Value,
        context: InvocationContext,
        observation: Option<usize>,
        work: &mut usize,
    ) -> Check<Option<OriginalSource>> {
        let Some(application) = AstApplication::from_ast(expression) else {
            return Ok(None);
        };
        let root = self.original_source_root(expression, value, context, observation, work)?;
        *work = work
            .checked_sub(self.facts.copy_call_events.len())
            .ok_or("constructor result event work exhausted")?;
        let mut events = self
            .facts
            .copy_call_events
            .iter()
            .filter(|event| event.result_expression == Some(root));
        let Some(event) = events.next() else {
            return Ok(None);
        };
        require(
            events.next().is_none()
                && event.matches_source(expression)
                && event.owner == context.owner
                && event.parent == context.invocation,
            "constructor result borrowed another actual call occurrence",
        )?;
        let callee = event
            .callee_expression
            .ok_or("constructor result lost its actual callee observation")?;
        let fact = self
            .facts
            .expressions
            .get(callee)
            .ok_or("constructor result callee is outside its arena")?;
        require(
            fact.source_id.is_some()
                && fact.source_id == application.callee.hir_id
                && self.observations.row(callee, work)?.context == context,
            "constructor result borrowed another callee Source",
        )?;
        let [Callable::Constructor(name)] = fact.value.callables.as_slice() else {
            return Ok(None);
        };
        let constructor = self
            .facts
            .constructors
            .get(name)
            .ok_or("constructor result lost its registered declaration")?;
        require(
            value.variant_tag.as_ref() == Some(&constructor.tag),
            "constructor result changed its actual tag",
        )?;
        self.registered_constructor_result_source(constructor, application.callee, work)
    }

    fn original_constructor_payload(
        &self,
        constructor: &ConstructorInfo,
        callee_syntax: &Expr,
        work: &mut usize,
    ) -> Check<TypeExpr> {
        if let Some(written) = constructor.source_syntax.as_deref() {
            let mut instance = self.declared_constructor_instance_schema(
                written,
                &constructor.typing_environment,
                work,
            )?;
            return instance
                .payloads
                .remove(&constructor.tag)
                .ok_or("constructor declaration instance excludes the selected payload tag")?
                .map(|payload| payload.syntax)
                .ok_or_else(|| "nullary constructor has no declared payload".into());
        }
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
        let normalized = crate::static_eval::normalize_constructor_arguments_bounded(
            declaration,
            arguments,
            &self.facts.external_type_declarations,
            layout,
            work,
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
        let mut input_work = 16384;
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
            self.registered_constructor_result_source(constructor, callee_syntax, &mut 16384)?;
            let payload =
                self.original_constructor_payload(constructor, callee_syntax, &mut 16384)?;
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
            let expected = if let Some(written) = constructor.source_syntax.as_deref() {
                let mut instance = self.declared_constructor_instance_schema(
                    written,
                    &constructor.typing_environment,
                    &mut 16384,
                )?;
                let payload = instance
                    .payloads
                    .remove(&constructor.tag)
                    .ok_or("constructor payload instance excludes its actual tag")?
                    .ok_or("nullary declaration claims an input payload")?;
                if arguments.len() == 1 {
                    vec![payload.schema]
                } else {
                    let parts = payload
                        .schema
                        .tuple_parts(&mut WorkLimit::new(16384))
                        .map_err(|error| error.to_string())?
                        .ok_or("constructor payload has no original tuple boundary")?;
                    require(
                        parts.len() == arguments.len(),
                        "constructor payload changed its original tuple arity",
                    )?;
                    parts
                }
            } else {
                expected
                    .iter()
                    .map(|key| {
                        self.source_header_schema(key, FrozenEnvironment::default(), &mut 16384)
                            .map(|(schema, _)| schema)
                    })
                    .collect::<Check<Vec<_>>>()?
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
                let required = match expected.sensitivity(&mut WorkLimit::new(16384)) {
                    crate::sema::source_types::SourceSensitivity::Absent { .. } => false,
                    crate::sema::source_types::SourceSensitivity::Sensitive { .. }
                    | crate::sema::source_types::SourceSensitivity::Unknown {
                        reason: crate::sema::source_types::SourceTypesError::Unresolved,
                    } => true,
                    crate::sema::source_types::SourceSensitivity::Unknown { reason } => {
                        return Err(format!("constructor Source query failed: {reason}"));
                    }
                };
                if !required {
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
                self.input_operand_interval(
                    event,
                    slot,
                    token.expression,
                    context,
                    &mut input_work,
                )?;
                let actual = self.original_observed_source_schema_with_work(
                    actual_syntax,
                    token.expression,
                    context,
                    sites,
                    &mut 16384,
                )?;
                let fresh =
                    source_reception::construction(actual_syntax, &mut 4096).ok_or_else(|| {
                        "constructor source construction exceeds its replay budget".to_owned()
                    })?;
                let answer = if let Some(answer) = expected
                    .empty_context(&fresh, &mut WorkLimit::new(4096))
                    .map_err(|error| error.to_string())?
                {
                    answer
                } else {
                    let (actual, environment) =
                        actual.ok_or("constructor operand has no original Source graph")?;
                    require(
                        !environment.is_poisoned(),
                        "constructor operand Source environment is poisoned",
                    )?;
                    expected
                        .receive_schema(&actual, Some(&fresh), &mut WorkLimit::new(16384))
                        .map_err(|error| error.to_string())?
                };
                require(
                    answer,
                    "constructor original whole input source does not prove its declared payload coordinates",
                )?;
            }
        }
        Ok(())
    }
}
