//! A foreign instance is derived from an authenticated written declaration.
//! Normalized syntax receives generated HIR identities only after this query.
use super::model::FunctionInfo;
use crate::{hir, static_eval};
use ril_compiler_core::target::TargetLayout;
use ril_syntax::ast::*;
use static_eval::ArgumentNormalizationError as Error;
use std::collections::BTreeMap;

fn unsupported(message: &str) -> Error {
    Error::Unsupported(message.into())
}

fn admit(function: &Function, work: &mut usize) -> Result<(), Error> {
    static_eval::charge_function_syntax_clone(function, work)
        .ok_or_else(|| unsupported("foreign declaration syntax exceeds its work bound"))
}

pub(crate) struct InstantiatedFunction {
    pub(crate) syntax: Function,
    pub(crate) arguments: Vec<TypeExpr>,
}

/// The original template and static arguments jointly determine all instance
/// headers and defaults. This query grants no run-time evaluation occurrence.
pub(crate) fn instantiate(
    template: &FunctionInfo,
    arguments: &[TypeExpr],
    declarations: &BTreeMap<String, TypeDeclaration>,
    hir: &hir::HirProgram,
    layout: TargetLayout,
    instance: usize,
    work: &mut usize,
) -> Result<InstantiatedFunction, Error> {
    *work = work
        .checked_sub(3)
        .ok_or_else(|| unsupported("foreign instance work bound exhausted"))?;
    if template.typing_environment.is_poisoned() || template.syntax.body.is_some() {
        return Err(unsupported(
            "foreign instance has no original declaration interpretation",
        ));
    }
    let id = template.hir_id.ok_or_else(|| {
        unsupported("foreign instance template has no original declaration identity")
    })?;
    let original = hir
        .statement(id)
        .ok_or_else(|| unsupported("foreign instance template declaration is absent"))?;
    if !matches!(
        original.info.origin,
        hir::nodes::NodeOrigin::Source | hir::nodes::NodeOrigin::Transformed { .. }
    ) {
        return Err(unsupported(
            "foreign instance template must be an original declaration",
        ));
    }
    admit(&template.syntax, work)?;
    admit(&template.syntax, work)?;
    let mut statement = Stmt {
        hir_id: Some(id),
        span: template.syntax.span,
        kind: StmtKind::Function(template.syntax.clone()),
    };
    hir.validate_statement_syntax(&mut statement, id, hir::nodes::HirLimits::default())
        .map_err(|_| {
            unsupported("foreign instance template differs from its original HIR declaration")
        })?;
    *work = work
        .checked_sub(arguments.len())
        .ok_or_else(|| unsupported("foreign static argument work bound exhausted"))?;
    for argument in arguments {
        let id = argument
            .hir_id
            .ok_or_else(|| unsupported("foreign static argument has no actual HIR coordinate"))?;
        for _ in 0..2 {
            static_eval::charge_type_syntax_clone(argument, work).ok_or_else(|| {
                unsupported("foreign static argument syntax exceeds its work bound")
            })?;
        }
        let mut syntax = argument.clone();
        hir.validate_type_syntax(&mut syntax, id, hir::nodes::HirLimits::default())
            .map_err(|_| {
                unsupported("foreign static argument differs from the actual HIR application")
            })?;
    }
    admit(&template.syntax, work)?;
    let function = &template.syntax;
    let callable = TypeDeclaration {
        visibility: function.visibility,
        is_halt: false,
        name: function.name.clone(),
        generics: function.generics.clone(),
        value: Some(TypeExpr {
            hir_id: None,
            text: String::new(),
            span: function.span,
            kind: TypeKind::Callable {
                parameters: function.parameters.clone(),
                result: function.return_type.clone().map(Box::new),
                annotations: function.annotations.clone(),
            },
        }),
        variants: vec![],
        opaque: false,
        nominal: true,
        span: function.span,
    };
    let mut normalized = static_eval::normalize_constructor_arguments_bounded(
        &callable,
        arguments,
        declarations,
        layout,
        work,
    )?;
    let Some(Some(TypeExpr {
        kind: TypeKind::Callable {
            parameters, result, ..
        },
        ..
    })) = normalized.payloads.remove(&function.name)
    else {
        return Err(unsupported(
            "foreign static instance has no complete callable signature",
        ));
    };
    admit(function, work)?;
    let mut concrete = function.clone();
    concrete.name = format!("{}\0foreign.instance.{instance}", function.name);
    concrete.generics.clear();
    concrete.parameters = parameters;
    concrete.return_type = result.map(|result| *result);
    static_eval::foreign::instantiate_defaults_bounded(
        function,
        &normalized.arguments,
        &mut concrete.parameters,
        &format!("ForeignDefault{instance}_"),
        declarations,
        layout,
        work,
    )?;
    Ok(InstantiatedFunction {
        syntax: concrete,
        arguments: normalized.arguments,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::context::FrozenEnvironment;
    use ril_compiler_core::ids::DefinitionId;

    fn fixture() -> (Program, hir::HirProgram, FunctionInfo, Vec<TypeExpr>) {
        let case =
            ril_test::case_by_id("tests/conformance/numeric.ril::external-const-floating-defaults");
        let mut program = Program::default();
        for file in &case.files {
            let parsed = ril_syntax::parse(std::str::from_utf8(&file.bytes).unwrap());
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            program.statements.extend(parsed.program.statements);
        }
        let hir =
            hir::HirProgram::lower_identified(&mut program, crate::hir::nodes::InputOrigin::Source)
                .unwrap();
        let (statement, function) = program
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Function(function) if function.name == "fixed" => {
                    Some((statement, function))
                }
                _ => None,
            })
            .unwrap();
        let arguments=program.statements.iter().find_map(|statement| match &statement.kind {
            StmtKind::Function(function) if function.name == "example"=>function.body.as_ref(),
            _=>None,
        }).unwrap().statements.iter().find_map(|statement| match &statement.kind {
            StmtKind::Binding(binding) if matches!(&binding.pattern.kind,PatternKind::Name(name) if name == "rounded")=> {
                let ExprKind::Call { callee,.. }=&binding.value.kind else { return None; };
                let ExprKind::Generic { arguments,.. }=&callee.kind else { return None; };
                Some(arguments.clone())
            }
            _=>None,
        }).unwrap();
        let template = FunctionInfo {
            hir_id: statement.hir_id,
            definition: DefinitionId(0),
            lexical_owner: None,
            typing_environment: FrozenEnvironment::default(),
            syntax: function.clone(),
            lexical: Default::default(),
            owner: None,
            handler_context: vec![],
            lexical_scope: 0,
            environment: None,
            captures: Default::default(),
            writes: Default::default(),
            environment_published: false,
        };
        (program, hir, template, arguments)
    }

    fn accepted(result: Result<InstantiatedFunction, Error>) -> InstantiatedFunction {
        match result {
            Ok(result) => result,
            Err(Error::Diagnostic(code, message)) => panic!("{code}: {message}"),
            Err(Error::Unsupported(message)) => panic!("{message}"),
        }
    }

    #[test]
    fn original_foreign_instances_derive_closed_headers_and_static_defaults_together() {
        let (_, hir, template, arguments) = fixture();
        let normalized = accepted(instantiate(
            &template,
            &arguments,
            &BTreeMap::new(),
            &hir,
            TargetLayout::POINTER64,
            0,
            &mut 65536,
        ));
        assert!(normalized.syntax.generics.is_empty());
        assert!(
            matches!(&normalized.syntax.parameters[0].ty.as_ref().unwrap().kind,TypeKind::Name { path,arguments } if path == &["f32"] && arguments.is_empty())
        );
        let default = normalized.syntax.parameters[0].default.as_ref().unwrap();
        let ExprKind::Literal(Literal::Float(text)) = &default.kind else {
            panic!("the actual static value must specialize the default");
        };
        let value = static_eval::committed_float::decode(text).unwrap().unwrap();
        assert_eq!(value.width, 32);
        assert_eq!(value.bits, u64::from(16777216.0f32.to_bits()));
        assert_eq!(
            normalized.syntax.parameters[0].ty.as_ref().unwrap().hir_id,
            None
        );
        assert_eq!(normalized.syntax.return_type.as_ref().unwrap().hir_id, None);
    }

    #[test]
    fn foreign_instance_normalization_requires_both_original_syntax_identities_and_work() {
        let (_, hir, template, arguments) = fixture();
        let declarations = BTreeMap::new();
        for change in 0..3 {
            let mut changed = template.clone();
            match change {
                0 => changed.hir_id = None,
                1 => changed.syntax.parameters[0].ty.as_mut().unwrap().hir_id = None,
                _ => changed.syntax.return_type.as_mut().unwrap().kind = TypeKind::Tuple(vec![]),
            }
            assert!(
                instantiate(
                    &changed,
                    &arguments,
                    &declarations,
                    &hir,
                    TargetLayout::POINTER64,
                    0,
                    &mut 65536
                )
                .is_err()
            );
        }
        let mut changed = arguments.clone();
        changed[0].hir_id = None;
        assert!(
            instantiate(
                &template,
                &changed,
                &declarations,
                &hir,
                TargetLayout::POINTER64,
                0,
                &mut 65536
            )
            .is_err()
        );
        let mut changed = arguments.clone();
        let TypeKind::Computation(value) = &mut changed[0].kind else {
            panic!("static value argument");
        };
        value.kind = ExprKind::Literal(Literal::Bool(true));
        assert!(
            instantiate(
                &template,
                &changed,
                &declarations,
                &hir,
                TargetLayout::POINTER64,
                0,
                &mut 65536
            )
            .is_err()
        );
        assert!(
            instantiate(
                &template,
                &arguments,
                &declarations,
                &hir,
                TargetLayout::POINTER64,
                0,
                &mut 0
            )
            .is_err()
        );
    }
}
