//! Export already checked type expansions for the host exchange boundary.
//! This snapshot creates no new semantic permission and does not reparse types.
use super::*;

impl Checker {
    /// A declaration-only shape template adds no run-time behavior. Its int
    /// binders may occur in fixed cardinalities, never as ordinary data types;
    /// every concrete use still passes static substitution and shape checking.
    pub(super) fn external_shape_template(&self, declaration: &TypeDeclaration) -> bool {
        if !self.declaration_files.contains(&declaration.span.file.0)
            || declaration.nominal
            || !declaration.variants.is_empty()
        {
            return false;
        }
        let Some(value) = &declaration.value else {
            return false;
        };
        let mut integers = BTreeSet::new();
        for parameter in &declaration.generics {
            if parameter.name.chars().next().is_some_and(char::is_lowercase) {
                if !matches!(parameter.bound.as_ref().map(|bound| &bound.kind), Some(TypeKind::Name { path, arguments }) if path == &["int"] && arguments.is_empty()) { return false; }
                integers.insert(parameter.name.clone());
            } else if parameter.bound.as_ref().is_some_and(|bound| !matches!(&bound.kind, TypeKind::Name { path, arguments } if path == &["Type"] && arguments.is_empty())) { return false; }
        }
        fn length(expression: &Expr, integers: &BTreeSet<String>) -> bool {
            match &expression.kind {
                ExprKind::Literal(Literal::Integer(_)) => true,
                ExprKind::Name(name) => integers.contains(name),
                ExprKind::Unary { operator, operand } if operator == "-" => {
                    length(operand, integers)
                }
                ExprKind::Binary {
                    operator,
                    left,
                    right,
                } if matches!(operator.as_str(), "+" | "-" | "*" | "/" | "%") => {
                    length(left, integers) && length(right, integers)
                }
                _ => false,
            }
        }
        fn shape(ty: &TypeExpr, integers: &BTreeSet<String>) -> bool {
            match &ty.kind {
                TypeKind::Name { path, arguments } => {
                    !integers.contains(&path.join("::"))
                        && arguments.iter().all(|argument| shape(argument, integers))
                }
                TypeKind::Array {
                    length: count,
                    element,
                } => {
                    count.as_ref().is_none_or(|count| length(count, integers))
                        && shape(element, integers)
                }
                TypeKind::Optional(inner) => shape(inner, integers),
                TypeKind::Map { key, value } => shape(key, integers) && shape(value, integers),
                TypeKind::Tuple(items) => items.iter().all(|item| shape(item, integers)),
                TypeKind::Record { fields, row: None } => {
                    fields.iter().all(|field| shape(&field.ty, integers))
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    parameters.iter().all(|parameter| {
                        parameter.ty.as_ref().is_some_and(|ty| shape(ty, integers))
                    }) && result.as_ref().is_none_or(|result| shape(result, integers))
                }
                _ => false,
            }
        }
        shape(value, &integers)
    }
    pub(super) fn external_type_witnesses(
        &self,
        program: &Program,
    ) -> Vec<super::super::ExternalTypeWitness> {
        let mut pending = Vec::new();
        for instance in &self.external_instances {
            pending.extend(
                instance
                    .syntax
                    .parameters
                    .iter()
                    .filter_map(|parameter| parameter.ty.clone()),
            );
            pending.extend(instance.syntax.return_type.iter().cloned());
            pending.extend(
                instance
                    .arguments
                    .iter()
                    .map(|(_, argument)| argument.clone())
                    .filter(|argument| !matches!(argument.kind, TypeKind::Computation(_))),
            );
        }
        for statement in &program.statements {
            match &statement.kind {
                StmtKind::Function(function)
                    if function.body.is_none()
                        && self.declaration_files.contains(&function.span.file.0) =>
                {
                    pending.extend(
                        function
                            .parameters
                            .iter()
                            .filter_map(|parameter| parameter.ty.clone()),
                    );
                    pending.extend(function.return_type.iter().cloned());
                }
                StmtKind::Binding(binding) if matches!(binding.value.kind, ExprKind::Ambient) => {
                    pending.extend(binding.ty.iter().cloned())
                }
                _ => {}
            }
        }
        pending.extend(
            self.constructors
                .values()
                .filter_map(|constructor| constructor.payload_syntax.clone()),
        );
        let mut seen = BTreeSet::new();
        let mut output = Vec::new();
        while let Some(syntax) = pending.pop() {
            let key = crate::static_eval::normalized_argument_key(&syntax);
            if !seen.insert(key) {
                continue;
            }
            let value_type = self.ty_readonly(&syntax, &mut BTreeSet::new());
            match &syntax.kind {
                TypeKind::Name { path, arguments } => {
                    pending.extend(arguments.iter().cloned());
                    if let Some(declaration) = self.types.get(&path.join("::")) {
                        if declaration.generics.is_empty() {
                            pending.extend(declaration.value.iter().cloned());
                            pending.extend(
                                declaration
                                    .variants
                                    .iter()
                                    .filter_map(|variant| variant.payload.clone()),
                            );
                        } else {
                            // Static materialization has already checked these
                            // actuals. Reuse the same substitution/equivalence
                            // path to retain refinements in the private witness.
                            let mut payload = declaration.clone();
                            if payload.variants.is_empty() {
                                payload.nominal = true;
                            }
                            if let Ok(instance) =
                                crate::static_eval::normalize_constructor_arguments(
                                    &payload,
                                    arguments,
                                    &self.types,
                                    self.layout,
                                )
                            {
                                pending.extend(instance.arguments);
                                pending.extend(instance.payloads.into_values().flatten());
                            }
                        }
                    }
                }
                TypeKind::Array { element, .. }
                | TypeKind::Optional(element)
                | TypeKind::Rest(element)
                | TypeKind::KeyOf(element) => pending.push(*element.clone()),
                TypeKind::Map { key, value } => {
                    pending.push(*key.clone());
                    pending.push(*value.clone());
                }
                TypeKind::Tuple(items) => pending.extend(items.iter().cloned()),
                TypeKind::Record { fields, row } => {
                    pending.extend(fields.iter().map(|field| field.ty.clone()));
                    pending.extend(row.iter().map(|row| *row.clone()));
                }
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    pending.extend(
                        parameters
                            .iter()
                            .filter_map(|parameter| parameter.ty.clone()),
                    );
                    pending.extend(result.iter().map(|result| *result.clone()));
                }
                _ => {}
            }
            output.push(super::super::ExternalTypeWitness { syntax, value_type });
        }
        output
    }
    pub(super) fn external_type_expansions(&self) -> Vec<(Ty, Ty)> {
        let mut pending: Vec<_> = self
            .bindings
            .iter()
            .filter(|binding| self.declaration_files.contains(&binding.span.file.0))
            .map(|binding| binding.value.ty.clone())
            .collect();
        let mut output: Vec<(Ty, Ty)> = Vec::new();
        while let Some(ty) = pending.pop() {
            if output.iter().any(|(before, _)| before == &ty) {
                continue;
            }
            let expanded = if matches!(ty, Ty::Immutable(_)) {
                ty.clone()
            } else {
                self.expanded(&ty, &mut BTreeSet::new())
            };
            output.push((ty.clone(), expanded.clone()));
            for constructor in self
                .constructors
                .values()
                .filter(|constructor| constructor.owner == ty && constructor.has_payload)
            {
                pending.push(constructor.payload.clone());
            }
            match expanded {
                Ty::Immutable(inner)
                | Ty::Optional(inner)
                | Ty::Array(inner)
                | Ty::Set(inner)
                | Ty::Range(inner) => pending.push(*inner),
                Ty::Result(left, right) | Ty::Map(left, right) => pending.extend([*left, *right]),
                Ty::Tuple(items) => pending.extend(items),
                Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
                    pending.extend(fields.into_values().map(|(_, ty)| ty))
                }
                Ty::Callable(parameters, result) => {
                    pending.extend(parameters);
                    pending.push(*result);
                }
                _ => {}
            }
        }
        output
    }
}
