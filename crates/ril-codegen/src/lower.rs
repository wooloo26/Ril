//! Native representations are selected after the shared Core IR boundary.
use ril_compiler_core::phase::{NotImplemented, Stage};

pub fn lower_native(
    program: &ril_ir::core::Program,
) -> Result<ril_ir::native::Module, NotImplemented> {
    lower_native_with_entry(program, "main")
}

pub fn lower_native_with_entry(
    program: &ril_ir::core::Program,
    entry: &str,
) -> Result<ril_ir::native::Module, NotImplemented> {
    use ril_ir::{core, native};
    if program
        .provenance
        .target_layout
        .is_some_and(|layout| layout.pointer_bits != 64)
    {
        return Err(NotImplemented::new(
            Stage::Lowering,
            "native execution requires a program verified with a 64-bit target layout",
        ));
    }
    if program
        .functions
        .iter()
        .find(|function| function.name == entry)
        .is_some_and(|selected| {
            program
                .provenance
                .copy_template_closure
                .as_ref()
                .is_some_and(|closure| {
                    closure
                        .templates
                        .iter()
                        .any(|template| template.owner == selected.definition)
                })
        })
    {
        return Err(NotImplemented::new(
            Stage::Provenance,
            "native entry requires its own copy-template substitution proof",
        ));
    }
    let mut lowered = crate::hof::lower(program)?;
    let metering = crate::cps::contains_budget(&lowered);
    if metering {
        for function in &mut lowered.functions {
            *function = crate::cps::normalize(function)?;
        }
    }
    let program = &lowered;
    let selected = program
        .functions
        .iter()
        .find(|function| function.name == entry)
        .ok_or_else(|| {
            NotImplemented::new(
                Stage::Lowering,
                format!("entry function {entry} was not found"),
            )
        })?;
    if !selected.parameters.is_empty() {
        return Err(NotImplemented::new(
            Stage::Lowering,
            "native entry must take no arguments",
        ));
    }
    // Managed values use one boxed representation. Verified generic bodies
    // retain their symbolic metadata and share this ABI. Type computations
    // requiring specialization must already have been lowered by the frontend.
    let symbol = |function: &core::Function| format!("__ril_fn_{}", function.definition.0);
    let suspending = crate::cps::suspending_functions(program);
    let mut functions: Vec<_> = program
        .functions
        .iter()
        .map(|function| {
            Ok(native::Function {
                symbol: symbol(function),
                body: if suspending.contains(&function.name) {
                    native::Body::Cps(std::sync::Arc::new(crate::cps::lower(function)?))
                } else {
                    native::Body::Managed(function.clone())
                },
            })
        })
        .collect::<Result<_, NotImplemented>>()?;
    let mut budget_entries = std::collections::BTreeMap::new();
    functions.extend(
        program
            .external_functions
            .iter()
            .map(|function| native::Function {
                symbol: format!("__ril_foreign_{}", function.definition.0),
                body: native::Body::Foreign(function.clone()),
            }),
    );
    if metering {
        for function in &program.functions {
            let mut graph = crate::cps::lower_metered(function)?;
            let name = native::budget_entry_name(&function.name);
            graph.name = name.clone();
            budget_entries.insert(function.name.clone(), name);
            functions.push(native::Function {
                symbol: format!("{}__budget", symbol(function)),
                body: native::Body::Cps(std::sync::Arc::new(graph)),
            });
        }
    }
    let initializer = core::Function {
        role: core::FunctionRole::Synthetic,
        definition: ril_compiler_core::ids::DefinitionId(u32::MAX),
        name: native::GLOBAL_INITIALIZER.into(),
        generic_parameters: vec![],
        parameters: vec![],
        body: program.globals.clone(),
        span: selected.span,
    };
    let mut global_bindings = std::collections::BTreeSet::new();
    for statement in &program.globals.statements {
        if let core::Statement::Bind { pattern, .. } = statement {
            global_names(pattern, &mut global_bindings);
        }
    }
    functions.push(native::Function {
        symbol: "__ril_globals".into(),
        body: native::Body::Cps(std::sync::Arc::new(crate::cps::lower(&initializer)?)),
    });
    if metering {
        let mut graph = crate::cps::lower_metered(&initializer)?;
        let name = native::budget_entry_name(native::GLOBAL_INITIALIZER);
        graph.name = name.clone();
        budget_entries.insert(native::GLOBAL_INITIALIZER.into(), name);
        functions.push(native::Function {
            symbol: "__ril_globals__budget".into(),
            body: native::Body::Cps(std::sync::Arc::new(graph)),
        });
    }
    functions.push(native::Function {
        symbol: "main".into(),
        body: native::Body::Entry {
            initializer: "__ril_globals".into(),
            entry: symbol(selected),
        },
    });
    Ok(native::Module {
        specializations: program.provenance.specializations.clone(),
        constant_graphs: program.constant_graphs.clone(),
        global_bindings,
        external_functions: program.external_functions.clone(),
        external_constants: program.external_constants.clone(),
        foreign_bindings: vec![],
        retained_handlers: program.provenance.retained_handlers.clone(),
        closure_sites: program.provenance.closure_sites.clone(),
        nonretaining_adapters: program.provenance.nonretaining_adapters.clone(),
        budget_entries,
        functions,
        constructors: program.constructors.clone(),
        operations: program.operations.clone(),
        call_signatures: program.call_signatures.clone(),
    })
}

fn global_names(pattern: &ril_ir::core::Pattern, names: &mut std::collections::BTreeSet<String>) {
    use ril_ir::core::Pattern;
    match pattern {
        Pattern::Name(name) | Pattern::Rest(Some(name)) => {
            names.insert(name.clone());
        }
        Pattern::Tuple(items)
        | Pattern::Array(items)
        | Pattern::Alternative(items)
        | Pattern::Constructor {
            arguments: items, ..
        } => {
            for item in items {
                global_names(item, names);
            }
        }
        Pattern::Record(fields) => {
            for (_, pattern) in fields {
                global_names(pattern, names);
            }
        }
        Pattern::RecordRest { fields, rest } => {
            names.insert(rest.clone());
            for (_, pattern) in fields {
                global_names(pattern, names);
            }
        }
        _ => {}
    }
}
