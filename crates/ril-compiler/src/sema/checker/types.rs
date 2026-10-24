use super::io_types as io;
use super::*;
#[path = "contextual_inference.rs"]
mod contextual;
#[path = "opaque_types.rs"]
mod opaque;
pub(super) use contextual::substitute_inferred_type;
fn contains_static_key(ty: &Ty) -> bool {
    match ty {
        Ty::StaticKey(_) => true,
        Ty::Immutable(inner)
        | Ty::Optional(inner)
        | Ty::Array(inner)
        | Ty::Set(inner)
        | Ty::Range(inner) => contains_static_key(inner),
        Ty::Map(a, b) | Ty::Result(a, b) => contains_static_key(a) || contains_static_key(b),
        Ty::Tuple(items) => items.iter().any(contains_static_key),
        Ty::Record(fields) | Ty::OpenRecord { fields, .. } => {
            fields.values().any(|(_, ty)| contains_static_key(ty))
        }
        _ => false,
    }
}

/// Infer only this call's binders. Generic symbols supplied by the caller are
/// rigid, even when they occur inside an aggregate or an instantiated type.
/// An unsuccessful argument does not leave partial substitutions behind.
pub(super) fn unify_call_types(
    expected: &Ty,
    actual: &Ty,
    binders: &BTreeSet<String>,
    substitutions: &mut BTreeMap<String, Ty>,
) -> bool {
    fn merge(left: &Ty, right: &Ty, depth: usize) -> Option<Ty> {
        if depth > 128 {
            return None;
        }
        if left == right {
            return Some(left.clone());
        }
        if matches!(left, Ty::Unknown | Ty::Never) {
            return Some(right.clone());
        }
        if matches!(right, Ty::Unknown | Ty::Never) {
            return Some(left.clone());
        }
        let unary = |a: &Ty, b: &Ty| merge(a, b, depth + 1).map(Box::new);
        Some(match (left, right) {
            (Ty::Immutable(a), Ty::Immutable(b)) => Ty::Immutable(unary(a, b)?),
            (Ty::Optional(a), Ty::Optional(b)) => Ty::Optional(unary(a, b)?),
            (Ty::Array(a), Ty::Array(b)) => Ty::Array(unary(a, b)?),
            (Ty::Set(a), Ty::Set(b)) => Ty::Set(unary(a, b)?),
            (Ty::Range(a), Ty::Range(b)) => Ty::Range(unary(a, b)?),
            (Ty::Result(a, b), Ty::Result(c, d)) => Ty::Result(unary(a, c)?, unary(b, d)?),
            (Ty::Map(a, b), Ty::Map(c, d)) => Ty::Map(unary(a, c)?, unary(b, d)?),
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => Ty::Tuple(
                a.iter()
                    .zip(b)
                    .map(|(a, b)| merge(a, b, depth + 1))
                    .collect::<Option<_>>()?,
            ),
            (Ty::Record(a), Ty::Record(b)) if a.keys().eq(b.keys()) => Ty::Record(
                a.iter()
                    .map(|(name, (mutable, ty))| {
                        let (other_mutable, other_ty) = &b[name];
                        (*mutable == *other_mutable)
                            .then(|| merge(ty, other_ty, depth + 1))
                            .flatten()
                            .map(|ty| (name.clone(), (*mutable, ty)))
                    })
                    .collect::<Option<_>>()?,
            ),
            (Ty::Callable(a, b), Ty::Callable(c, d)) if a.len() == c.len() => Ty::Callable(
                a.iter()
                    .zip(c)
                    .map(|(a, c)| merge(a, c, depth + 1))
                    .collect::<Option<_>>()?,
                unary(b, d)?,
            ),
            (
                Ty::Applied {
                    constructor: a,
                    arguments: b,
                },
                Ty::Applied {
                    constructor: c,
                    arguments: d,
                },
            ) if a == c && b.len() == d.len() => {
                let arguments = b
                    .iter()
                    .zip(d)
                    .map(|(a, b)| match (a, b) {
                        (TypeArgument::Type(a), TypeArgument::Type(b)) => {
                            merge(a, b, depth + 1).map(|ty| TypeArgument::Type(Box::new(ty)))
                        }
                        (
                            TypeArgument::CanonicalType { ty: a, key: left },
                            TypeArgument::CanonicalType { ty: b, key: right },
                        ) if left == right => {
                            merge(a, b, depth + 1).map(|ty| TypeArgument::CanonicalType {
                                ty: Box::new(ty),
                                key: left.clone(),
                            })
                        }
                        _ if a == b => Some(a.clone()),
                        _ => None,
                    })
                    .collect::<Option<_>>()?;
                Ty::Applied {
                    constructor: a.clone(),
                    arguments,
                }
            }
            _ => return None,
        })
    }
    fn infer(
        expected: &Ty,
        actual: &Ty,
        binders: &BTreeSet<String>,
        substitutions: &mut BTreeMap<String, Ty>,
        depth: usize,
    ) -> bool {
        if depth > 128 {
            return false;
        }
        // A missing sum payload or a diverging expression gives no evidence
        // about a binder. The caller must reject binders left unsolved.
        if matches!(actual, Ty::Unknown | Ty::Never) {
            return true;
        }
        if let Ty::Generic(identity) = expected
            && binders.contains(identity)
        {
            let selected = match substitutions.get(identity) {
                Some(previous) => merge(previous, actual, depth + 1),
                None => Some(actual.clone()),
            };
            if let Some(selected) = selected {
                substitutions.insert(identity.clone(), selected);
                return true;
            }
            return false;
        }
        if expected == actual || matches!(expected, Ty::Unknown) {
            return true;
        }
        if let Ty::OpenRecord { fields, row } = expected
            && matches!(actual, Ty::Record(_) | Ty::OpenRecord { .. })
        {
            use crate::sema::model::rows::{Row, RowIdentity, RowTail, Solver};
            let actual_row = match actual {
                Ty::Record(fields) => Row::closed(fields.clone()),
                Ty::OpenRecord { fields, row } => Row::open(fields.clone(), row.clone()),
                _ => unreachable!(),
            };
            let actual_fields = &actual_row.fields;
            let RowIdentity::Binder(identity) = &row.identity else {
                return false;
            };
            // Only the callee's declared inference variables are flexible.
            // A caller's rigid unknown tail cannot become an empty record.
            if !binders.contains(identity) {
                return false;
            }
            for (label, (mutable, field_type)) in fields {
                let Some((actual_mutable, actual_type)) = actual_fields.get(label) else {
                    return false;
                };
                if mutable != actual_mutable
                    || !infer(field_type, actual_type, binders, substitutions, depth + 1)
                {
                    return false;
                }
            }
            let expected_fields = fields
                .iter()
                .map(|(label, (mutable, ty))| {
                    (
                        label.clone(),
                        (*mutable, substitute_inferred_type(ty, substitutions)),
                    )
                })
                .collect();
            let expected_row = Row::open(expected_fields, row.clone());
            let mut solver = Solver::new("source row call", [row.identity.clone()]);
            if let RowTail::Open(actual_tail) = &actual_row.tail {
                if actual_tail.identity == row.identity {
                    return false;
                }
                if solver
                    .declare_rigid(
                        actual_tail.identity.clone(),
                        actual_tail.lacks.iter().cloned(),
                    )
                    .is_err()
                {
                    return false;
                }
            }
            if let Some(previous) = substitutions.get(identity) {
                let previous = match previous {
                    Ty::Record(fields) => Row::closed(fields.clone()),
                    Ty::OpenRecord { fields, row } => Row::open(fields.clone(), row.clone()),
                    Ty::Generic(identity) => {
                        let RowTail::Open(tail) = &actual_row.tail else {
                            return false;
                        };
                        if tail.identity != RowIdentity::Binder(identity.clone()) {
                            return false;
                        }
                        // An explicit Type prefix may name the caller's rigid
                        // residual. Its row interpretation comes from this
                        // actual argument, including the declared absences.
                        Row::open(BTreeMap::new(), tail.clone())
                    }
                    _ => return false,
                };
                if solver
                    .unify(&Row::open(BTreeMap::new(), row.clone()), &previous)
                    .is_err()
                {
                    return false;
                }
            }
            if solver.unify(&expected_row, &actual_row).is_err() {
                return false;
            }
            let Some(selected) = solver.binding(&row.identity) else {
                return false;
            };
            let Ok(selected) = solver.normalize(selected) else {
                return false;
            };
            if let Some(Ty::Generic(previous)) = substitutions.get(identity) {
                // The row equation checks a view of this explicit Type. Keep
                // the original Type identity instead of replacing it with its
                // structural row interpretation.
                return selected.fields.is_empty()
                    && matches!(&selected.tail, RowTail::Open(tail)
                        if tail.identity == RowIdentity::Binder(previous.clone()));
            }
            substitutions.insert(identity.clone(), Checker::row_type(selected));
            return true;
        }
        let mut child = |a: &Ty, b: &Ty| infer(a, b, binders, substitutions, depth + 1);
        match (expected, actual) {
            (Ty::Immutable(a), Ty::Immutable(b))
            | (Ty::Optional(a), Ty::Optional(b))
            | (Ty::Array(a), Ty::Array(b))
            | (Ty::Set(a), Ty::Set(b))
            | (Ty::Range(a), Ty::Range(b)) => child(a, b),
            (Ty::Result(a, b), Ty::Result(c, d)) | (Ty::Map(a, b), Ty::Map(c, d)) => {
                child(a, c) && child(b, d)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) if a.len() == b.len() => {
                a.iter().zip(b).all(|(a, b)| child(a, b))
            }
            (Ty::Record(a), Ty::Record(b)) if a.keys().eq(b.keys()) => {
                a.iter().all(|(name, (mutable, ty))| {
                    let (other_mutable, other_ty) = &b[name];
                    mutable == other_mutable && child(ty, other_ty)
                })
            }
            (Ty::Callable(a, b), Ty::Callable(c, d)) if a.len() == c.len() => {
                a.iter().zip(c).all(|(a, c)| child(a, c)) && child(b, d)
            }
            (
                Ty::Applied {
                    constructor: a,
                    arguments: b,
                },
                Ty::Applied {
                    constructor: c,
                    arguments: d,
                },
            ) if a == c && b.len() == d.len() => b.iter().zip(d).all(|(a, b)| match (a, b) {
                (TypeArgument::Type(a), TypeArgument::Type(b)) => child(a, b),
                (
                    TypeArgument::CanonicalType { ty: a, key: left },
                    TypeArgument::CanonicalType { ty: b, key: right },
                ) => left == right && child(a, b),
                (TypeArgument::Type(a), TypeArgument::CanonicalType { ty: b, .. }) => {
                    let mut names = BTreeSet::new();
                    a.generic_names(&mut names);
                    !names.is_disjoint(binders) && child(a, b)
                }
                _ => a == b,
            }),
            _ => false,
        }
    }
    let mut inferred = substitutions.clone();
    if infer(expected, actual, binders, &mut inferred, 0) {
        *substitutions = inferred;
        true
    } else {
        false
    }
}
fn static_parameter(parameter: &GenericParameter) -> bool {
    parameter
        .name
        .chars()
        .next()
        .is_some_and(char::is_lowercase)
        || matches!(
            parameter.bound.as_ref().map(|bound| &bound.kind),
            Some(TypeKind::KeyOf(_))
        )
}
fn normalized_static_argument(argument: &TypeExpr) -> bool {
    fn expression(value: &Expr) -> bool {
        match &value.kind {
            ExprKind::Literal(_) => true,
            ExprKind::Unary { operator, operand } if operator == "-" => expression(operand),
            ExprKind::Array(items) | ExprKind::Tuple(items) => items.iter().all(expression),
            ExprKind::Map(entries) => entries
                .iter()
                .all(|(key, value)| expression(key) && expression(value)),
            ExprKind::Record { members, .. } => members.iter().all(
                |member| matches!(member,RecordMember::Field(field) if expression(&field.value)),
            ),
            ExprKind::Call { callee, arguments } if matches!(&callee.kind,ExprKind::Name(name) if name == "Some" || name == "Prelude::Some") => {
                arguments.iter().all(|argument| expression(&argument.value))
            }
            ExprKind::Name(name) => name == "None" || name == "Prelude::None",
            _ => false,
        }
    }
    match &argument.kind {
        TypeKind::Computation(value) => expression(value),
        TypeKind::Tuple(items) => items.iter().all(normalized_static_argument),
        _ => false,
    }
}
impl Checker {
    fn record_with_row(
        &self,
        fields: BTreeMap<String, (bool, Ty)>,
        syntax: &TypeExpr,
        tail: Ty,
    ) -> Ty {
        self.try_record_with_row(fields, syntax, tail)
            .unwrap_or(Ty::Unknown)
    }
    fn try_record_with_row(
        &self,
        mut fields: BTreeMap<String, (bool, Ty)>,
        syntax: &TypeExpr,
        tail: Ty,
    ) -> Result<Ty, BTreeSet<String>> {
        let (extra, mut row) = match tail {
            Ty::Record(extra) => {
                use crate::sema::model::rows::{Row, Solver};
                let solver = Solver::new("closed record composition", []);
                let plan =
                    solver.union(&Row::closed(fields), &Row::closed(extra), &BTreeMap::new());
                return match plan {
                    Ok(plan) => Ok(Ty::Record(
                        plan.exact()
                            .expect("two closed rows have no unresolved tail")
                            .fields,
                    )),
                    Err(crate::sema::model::rows::RowError::Overlap(labels)) => Err(labels),
                    Err(_) => Ok(Ty::Unknown),
                };
            }
            Ty::OpenRecord { fields, row } => (fields, row),
            Ty::Generic(identity) => (
                BTreeMap::new(),
                super::super::model::rows::OpenTail {
                    identity: super::super::model::rows::RowIdentity::Binder(identity),
                    lacks: BTreeSet::new(),
                },
            ),
            Ty::Named(name)
                if !self.types.contains_key(&name)
                    && !crate::modules::known_standard_identity(&name) =>
            {
                (
                    BTreeMap::new(),
                    super::super::model::rows::OpenTail {
                        identity: super::super::model::rows::RowIdentity::Binder(format!(
                            "unresolved-row:{}:{}:{}:{name}",
                            syntax.span.file.0, syntax.span.start, syntax.span.end
                        )),
                        lacks: BTreeSet::new(),
                    },
                )
            }
            _ => return Ok(Ty::Unknown),
        };
        let overlap: BTreeSet<_> = extra
            .keys()
            .filter(|name| fields.contains_key(*name))
            .cloned()
            .collect();
        if !overlap.is_empty() {
            return Err(overlap);
        }
        fields.extend(extra);
        row.lacks.extend(fields.keys().cloned());
        Ok(Ty::OpenRecord { fields, row })
    }
    fn require_data_component(&mut self, ty: &Ty, span: Span) {
        if contains_static_key(&self.call_inference_type(ty)) {
            self.error(
                "E0301",
                span,
                "a static key parameter is not an ordinary constituent data type",
                [],
            );
        }
    }
    pub(super) fn structural_alias_contract(&mut self, declaration: &TypeDeclaration) -> bool {
        if declaration.nominal
            || declaration.opaque
            || !declaration.variants.is_empty()
            || declaration.value.is_none()
        {
            return false;
        }
        if declaration.generics.iter().any(|parameter|static_parameter(parameter)
            || parameter.bound.as_ref().is_some_and(|bound| !matches!(&bound.kind,TypeKind::Name{path,arguments} if path==&["Type"]&&arguments.is_empty()))) {
            return false;
        }
        fn mentions(ty: &TypeExpr, names: &BTreeSet<String>) -> bool {
            match &ty.kind {
                TypeKind::Name { path, arguments } => {
                    names.contains(&path.join("::"))
                        || arguments.iter().any(|ty| mentions(ty, names))
                }
                TypeKind::Array { element, .. }
                | TypeKind::Optional(element)
                | TypeKind::KeyOf(element)
                | TypeKind::Rest(element) => mentions(element, names),
                TypeKind::Tuple(items) => items.iter().any(|ty| mentions(ty, names)),
                TypeKind::Record { fields, row } => {
                    fields.iter().any(|field| mentions(&field.ty, names))
                        || row.as_ref().is_some_and(|ty| mentions(ty, names))
                }
                TypeKind::Map { key, value } => mentions(key, names) || mentions(value, names),
                TypeKind::Callable {
                    parameters, result, ..
                } => {
                    parameters.iter().any(|parameter| {
                        parameter.ty.as_ref().is_some_and(|ty| mentions(ty, names))
                    }) || result.as_ref().is_some_and(|ty| mentions(ty, names))
                }
                _ => false,
            }
        }
        let previous = self.type_source.environment.generic_context.clone();
        for (index, parameter) in declaration.generics.iter().enumerate() {
            self.type_source.environment.generic_context.insert(
                parameter.name.clone(),
                format!(
                    "{}:{}:type:{index}:{}",
                    declaration.span.file.0, declaration.span.start, parameter.name
                ),
            );
        }
        let mut default_seen = false;
        for (index, parameter) in declaration.generics.iter().enumerate() {
            if let Some(default) = &parameter.default {
                default_seen = true;
                let later = declaration.generics[index..]
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect();
                if mentions(default, &later) {
                    self.error(
                        "E0320",
                        default.span,
                        "generic default cannot reference itself or a later parameter",
                        [],
                    );
                }
                if matches!(default.kind, TypeKind::Computation(_)) {
                    self.error(
                        "E0323",
                        default.span,
                        "type parameter default requires a type",
                        [],
                    );
                } else {
                    self.require_type_argument_identity(default);
                    let _ = self.ty(default);
                }
            } else if default_seen {
                self.error(
                    "E0316",
                    parameter.span,
                    "generic defaults must be trailing",
                    [],
                );
            }
        }
        self.type_source.environment.generic_context = previous;
        true
    }
    pub(super) fn canonical_type_argument(&self, syntax: &TypeExpr, ty: Ty) -> TypeArgument {
        if ty.contains_open_row() {
            return TypeArgument::Type(Box::new(ty));
        }
        let mut names = BTreeSet::new();
        ty.generic_names(&mut names);
        if names.is_empty() {
            if let Some(syntax) = self.closed_source_syntax(syntax) {
                return TypeArgument::CanonicalType {
                    ty: Box::new(ty),
                    key: crate::static_eval::normalized_argument_key(&syntax),
                };
            }
            if self.argument_has_selected_generic(syntax) {
                return match self.selected_type_key(&ty) {
                    Some(key) => TypeArgument::CanonicalType {
                        ty: Box::new(ty),
                        key,
                    },
                    // Incomplete semantic shapes cannot fabricate a source
                    // identity from the old binder's spelling.
                    None => TypeArgument::Type(Box::new(ty)),
                };
            }
            // A failed closed normalization is an outstanding source identity
            // obligation, including finite traversal exhaustion. Its old raw
            // spelling is not a second canonical proof of the same type.
            TypeArgument::Type(Box::new(ty))
        } else {
            TypeArgument::Type(Box::new(ty))
        }
    }
    pub(super) fn argument_has_selected_generic(&self, syntax: &TypeExpr) -> bool {
        let child = |ty: &TypeExpr| self.argument_has_selected_generic(ty);
        match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                (arguments.is_empty()
                    && self
                        .type_source
                        .environment
                        .generic_context
                        .get(&path.join("::"))
                        .is_some_and(|identity| {
                            self.type_source
                                .environment
                                .generic_substitutions
                                .contains_key(identity)
                        }))
                    || arguments.iter().any(child)
            }
            TypeKind::Optional(inner)
            | TypeKind::Rest(inner)
            | TypeKind::KeyOf(inner)
            | TypeKind::Array { element: inner, .. } => child(inner),
            TypeKind::Tuple(items) => items.iter().any(child),
            TypeKind::Record { fields, row } => {
                fields.iter().any(|field| child(&field.ty))
                    || row.as_ref().is_some_and(|row| child(row))
            }
            TypeKind::Map { key, value } => child(key) || child(value),
            TypeKind::Callable {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| parameter.ty.as_ref().is_some_and(child))
                    || result.as_ref().is_some_and(|result| child(result))
            }
            _ => false,
        }
    }
    pub(super) fn selected_type_key(&self, ty: &Ty) -> Option<String> {
        fn complete(ty: &Ty) -> bool {
            match ty {
                Ty::Array(_)
                | Ty::Callable(..)
                | Ty::Unknown
                | Ty::Generic(_)
                | Ty::Projection { .. }
                | Ty::StaticKey(_)
                | Ty::Range(_) => false,
                Ty::Optional(inner) | Ty::Immutable(inner) | Ty::Set(inner) => complete(inner),
                Ty::Result(a, b) | Ty::Map(a, b) => complete(a) && complete(b),
                Ty::Tuple(items) => items.iter().all(complete),
                Ty::Record(fields) => fields.values().all(|(_, ty)| complete(ty)),
                Ty::Applied { .. } | Ty::OpenRecord { .. } => false,
                _ => true,
            }
        }
        let ty = self.call_inference_type(ty);
        if complete(&ty)
            && let Some(syntax) = io::data_type(
                &ty,
                Span {
                    file: self.file,
                    start: 0,
                    end: 0,
                },
            )
        {
            return Some(crate::static_eval::normalized_argument_key(&syntax));
        }
        match &ty {
            Ty::Applied {
                constructor,
                arguments,
            } => {
                let keys = arguments
                    .iter()
                    .map(|argument| match argument {
                        TypeArgument::CanonicalType { key, .. } | TypeArgument::Static(key) => {
                            Some(key.clone())
                        }
                        TypeArgument::Type(ty) => self.selected_type_key(ty),
                        TypeArgument::Symbolic(_) => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(format!("{}<{}>", constructor, keys.join(",")))
            }
            Ty::Immutable(inner) => Some(format!("Immut<{}>", self.selected_type_key(inner)?)),
            Ty::Optional(inner) => Some(format!("Option<{}>", self.selected_type_key(inner)?)),
            Ty::Result(ok, error) => Some(format!(
                "Result<{},{}>",
                self.selected_type_key(ok)?,
                self.selected_type_key(error)?
            )),
            Ty::Tuple(items) => Some(format!(
                "({})",
                items
                    .iter()
                    .map(|ty| self.selected_type_key(ty))
                    .collect::<Option<Vec<_>>>()?
                    .join(",")
            )),
            Ty::Record(fields) => {
                let mut fields = fields
                    .iter()
                    .map(|(name, (mutable, ty))| {
                        Some(format!(
                            "{}{}:{}",
                            if *mutable { "mut " } else { "" },
                            name,
                            self.selected_type_key(ty)?
                        ))
                    })
                    .collect::<Option<Vec<_>>>()?;
                fields.sort();
                Some(format!("{{{};}}", fields.join(",")))
            }
            _ => None,
        }
    }
    pub(super) fn canonical_argument_syntax(
        &self,
        syntax: &TypeExpr,
        depth: usize,
    ) -> Option<TypeExpr> {
        super::source_types::expand_builtin_source_syntax(&self.types, syntax, depth)
    }
    pub(super) fn applied_type(
        &mut self,
        declaration: &TypeDeclaration,
        arguments: &[TypeExpr],
        span: Span,
    ) -> Ty {
        if arguments.len() != declaration.generics.len() {
            self.error(
                "E0340",
                span,
                "type instance must supply its normalized generic argument list",
                [],
            );
            return Ty::Unknown;
        }
        let mut actual = vec![];
        for (parameter, argument) in declaration.generics.iter().zip(arguments) {
            if static_parameter(parameter) {
                let symbolic = match &argument.kind {
                    TypeKind::Name { path, arguments } if arguments.is_empty() => self
                        .type_source
                        .environment
                        .generic_context
                        .get(&path.join("::"))
                        .cloned(),
                    TypeKind::Computation(expression) => match &expression.kind {
                        ExprKind::Name(name) => self
                            .type_source
                            .environment
                            .generic_context
                            .get(name)
                            .cloned(),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(identity) = symbolic {
                    actual.push(TypeArgument::Symbolic(identity));
                } else if normalized_static_argument(argument) {
                    actual.push(TypeArgument::Static(
                        crate::static_eval::normalized_argument_key(argument),
                    ));
                } else {
                    self.unsupported(
                        argument.span,
                        "static instance argument has no normalized constant or binder identity",
                    );
                    actual.push(TypeArgument::Symbolic(format!(
                        "unproved:{}:{}",
                        span.file.0, argument.span.start
                    )));
                }
            } else {
                self.require_type_argument_identity(argument);
                let ty = self.ty(argument);
                self.require_data_component(&ty, argument.span);
                actual.push(self.canonical_type_argument(argument, ty));
            }
        }
        let owner = Ty::Applied {
            constructor: declaration.name.clone(),
            arguments: actual,
        };
        self.register_constructor_instance(declaration, arguments, &owner, span);
        owner
    }
    pub(super) fn ty(&mut self, syntax: &TypeExpr) -> Ty {
        if let Some(value) = self.source_typeof_value(syntax)
            && value.source_type_witness.is_some()
        {
            return value.ty.clone();
        }
        match &syntax.kind {
            TypeKind::Name { path, arguments } => {
                let full_name = path.join("::");
                if arguments.is_empty()
                    && let Some(identity) = self.effect_type_binders.get(&full_name)
                {
                    return Ty::Generic(identity.clone());
                }
                let name = full_name
                    .strip_prefix("Prelude::")
                    .unwrap_or(&full_name)
                    .to_owned();
                if full_name == name
                    && let Some(identity) = self.type_source.environment.generic_context.get(&name)
                {
                    if !arguments.is_empty() {
                        self.unsupported(
                            syntax.span,
                            "higher-kinded generic application needs its declared kind proof",
                        );
                        return Ty::Unknown;
                    }
                    if self.generic_key_bounds.contains_key(identity) {
                        return Ty::StaticKey(identity.clone());
                    }
                    return self
                        .type_source
                        .environment
                        .generic_substitutions
                        .get(identity)
                        .cloned()
                        .unwrap_or_else(|| Ty::Generic(identity.clone()));
                }
                if full_name == name
                    && arguments.is_empty()
                    && let Some(row) = self.bound_row_type(&name)
                {
                    return row;
                }
                if matches!(full_name.as_str(), "Iter::Source" | "Iter::Cursor") {
                    if let Some(schema) = super::iter_types::schema(syntax) {
                        return self.ty(&schema);
                    }
                    self.error(
                        "E0340",
                        syntax.span,
                        "iteration type has a different generic arity",
                        [],
                    );
                    return Ty::Unknown;
                }
                if let Some(declaration) = self.types.get(&full_name).cloned() {
                    if !declaration.generics.is_empty() || !arguments.is_empty() {
                        return self.applied_type(&declaration, arguments, syntax.span);
                    }
                    return Ty::Named(declaration.name);
                }
                if matches!(full_name.as_str(), "Io::ReadOps" | "Io::WriteOps") {
                    if let Some(schema) = io::operation_type(syntax) {
                        let argument = self.ty(&arguments[0]);
                        self.require_data_component(&argument, arguments[0].span);
                        return self.ty(&schema);
                    }
                    self.error(
                        "E0340",
                        syntax.span,
                        "stream operation record requires one receiver type",
                        [],
                    );
                    return Ty::Unknown;
                }
                if let Some(ty) = standard::file_type(&name) {
                    if !arguments.is_empty() {
                        self.error(
                            "E0340",
                            syntax.span,
                            "this standard type has no generic arguments",
                            [],
                        );
                    }
                    return ty;
                }
                if matches!(name.as_str(), "Deque::Deque" | "Heap::Heap") {
                    if arguments.len() != 1 {
                        self.error(
                            "E0340",
                            syntax.span,
                            "collection instance requires one element type",
                            [],
                        );
                        return Ty::Unknown;
                    }
                    self.require_type_argument_identity(&arguments[0]);
                    let element = self.ty(&arguments[0]);
                    return Ty::Applied {
                        constructor: name,
                        arguments: vec![self.canonical_type_argument(&arguments[0], element)],
                    };
                }
                if name == "Order::Ops" {
                    if arguments.len() != 1 {
                        self.error(
                            "E0340",
                            syntax.span,
                            "Order::Ops requires one element type",
                            [],
                        );
                        return Ty::Unknown;
                    }
                    let element = self.ty(&arguments[0]);
                    return Ty::Record(
                        [(
                            "compare".into(),
                            (
                                false,
                                Ty::Callable(
                                    vec![element.clone(), element],
                                    Box::new(Ty::Named("Order::Ordering".into())),
                                ),
                            ),
                        )]
                        .into(),
                    );
                }
                if name == "Immut" && arguments.len() != 1 {
                    self.error("E0340", syntax.span, "Immut requires one type argument", []);
                    return Ty::Unknown;
                }
                if name == "Immut" && arguments.len() == 1 {
                    let inner = self.ty(&arguments[0]);
                    self.require_data_component(&inner, arguments[0].span);
                    return if matches!(inner, Ty::Immutable(_)) {
                        inner
                    } else {
                        Ty::Immutable(Box::new(inner))
                    };
                }
                if name == "Option" {
                    if arguments.len() != 1 {
                        self.error(
                            "E0340",
                            syntax.span,
                            "Option requires one type argument",
                            [],
                        );
                        return Ty::Unknown;
                    }
                    let inner = self.ty(&arguments[0]);
                    self.require_data_component(&inner, arguments[0].span);
                    return Ty::Optional(Box::new(inner));
                }
                if name == "Result" {
                    if arguments.len() != 2 {
                        self.error(
                            "E0340",
                            syntax.span,
                            "Result requires two type arguments",
                            [],
                        );
                        return Ty::Unknown;
                    }
                    let ok = self.ty(&arguments[0]);
                    let error = self.ty(&arguments[1]);
                    self.require_data_component(&ok, arguments[0].span);
                    self.require_data_component(&error, arguments[1].span);
                    return Ty::Result(Box::new(ok), Box::new(error));
                }
                if name == "Range" {
                    if arguments.len() != 1 {
                        self.error(
                            "E0340",
                            syntax.span,
                            "integer range requires one endpoint type",
                            [],
                        );
                        return Ty::Unknown;
                    }
                    let element = self.ty(&arguments[0]);
                    if !matches!(element, Ty::Int(_)) {
                        self.error(
                            "E0327",
                            syntax.span,
                            "range endpoint type must be an integer",
                            [],
                        );
                    }
                    return Ty::Range(Box::new(element));
                }
                if name == "Set" {
                    if arguments.len() != 1 {
                        self.error("E0340", syntax.span, "Set requires one type argument", []);
                        return Ty::Unknown;
                    }
                    let element = self.ty(&arguments[0]);
                    self.require_data_component(&element, arguments[0].span);
                    self.require_key_type(&element, syntax.span);
                    return Ty::Set(Box::new(element));
                }
                if !arguments.is_empty()
                    && matches!(
                        name.as_str(),
                        "int"
                            | "i8"
                            | "i16"
                            | "i32"
                            | "i64"
                            | "u8"
                            | "u16"
                            | "u32"
                            | "u64"
                            | "bigint"
                            | "f32"
                            | "f64"
                            | "bool"
                            | "str"
                            | "bytes"
                            | "never"
                            | "Random::Rng"
                            | "Time::Duration"
                            | "Time::Instant"
                            | "Time::TimeError"
                            | "Time::Timestamp"
                            | "Io::ErrorKind"
                            | "Io::IoError"
                            | "StringBuilder::Builder"
                            | "Num::NumError"
                            | "Binary::ByteOrder"
                            | "Binary::BinaryError"
                            | "Binary::Cursor"
                            | "Unicode::DecodeError"
                            | "Unicode::ScalarError"
                            | "Hex::HexError"
                    )
                {
                    self.error(
                        "E0340",
                        syntax.span,
                        "this type has no generic parameters",
                        [],
                    );
                    return Ty::Unknown;
                }
                match name.as_str() {
                    "int" | "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
                    | "bigint" => Ty::Int(name),
                    "f32" | "f64" => Ty::Float(name),
                    "bool" => Ty::Bool,
                    "str" => Ty::Str,
                    "bytes" => Ty::Bytes,
                    "never" => Ty::Never,
                    "Random::Rng"
                    | "Time::Duration"
                    | "Time::Instant"
                    | "Time::TimeError"
                    | "Io::ErrorKind"
                    | "StringBuilder::Builder"
                    | "Num::NumError"
                    | "Binary::ByteOrder"
                    | "Binary::BinaryError" => Ty::Named(name),
                    "Unicode::DecodeError" | "Hex::HexError" => {
                        Ty::Record([("offset".into(), (false, Ty::Int("int".into())))].into())
                    }
                    "Unicode::ScalarError" => {
                        Ty::Record([("value".into(), (false, Ty::Int("u32".into())))].into())
                    }
                    "Time::Timestamp" => Ty::Record(
                        [
                            ("seconds".into(), (false, Ty::Int("i64".into()))),
                            ("nanos".into(), (false, Ty::Int("u32".into()))),
                        ]
                        .into(),
                    ),
                    "Io::IoError" => Ty::Record(
                        [
                            ("kind".into(), (false, Ty::Named("Io::ErrorKind".into()))),
                            (
                                "native_code".into(),
                                (false, Ty::Optional(Box::new(Ty::Int("i64".into())))),
                            ),
                            ("message".into(), (false, Ty::Str)),
                        ]
                        .into(),
                    ),
                    "Binary::Cursor" => Ty::Record(
                        [
                            ("data".into(), (false, Ty::Bytes)),
                            ("offset".into(), (true, Ty::Int("int".into()))),
                        ]
                        .into(),
                    ),
                    _ if self.types.contains_key(&name) => Ty::Named(name),
                    _ => {
                        self.error("E0204", syntax.span, format!("unknown type {name}"), []);
                        Ty::Unknown
                    }
                }
            }
            TypeKind::Array { element, .. } => {
                let element_type = self.ty(element);
                if contains_static_key(&element_type) {
                    self.error(
                        "E0301",
                        element.span,
                        "a static key is not an ordinary array element type",
                        [],
                    );
                }
                Ty::Array(Box::new(element_type))
            }
            TypeKind::Optional(inner) => {
                let ty = self.ty(inner);
                self.require_data_component(&ty, inner.span);
                Ty::Optional(Box::new(ty))
            }
            TypeKind::Tuple(items) => {
                if items.is_empty() {
                    Ty::Unit
                } else {
                    Ty::Tuple(
                        items
                            .iter()
                            .map(|t| {
                                let ty = self.ty(t);
                                self.require_data_component(&ty, t.span);
                                ty
                            })
                            .collect(),
                    )
                }
            }
            TypeKind::Record { fields, row } => {
                let fields = fields
                    .iter()
                    .map(|f| {
                        let ty = self.ty(&f.ty);
                        self.require_data_component(&ty, f.ty.span);
                        (f.name.clone(), (f.mutable, ty))
                    })
                    .collect();
                if let Some(row) = row {
                    let tail = self.ty_readonly(row, &mut BTreeSet::new());
                    match self.try_record_with_row(fields, row, tail) {
                        Ok(Ty::Unknown) => {
                            self.unsupported(syntax.span,"record row composition requires a record or an identified symbolic tail");
                            Ty::Unknown
                        }
                        Ok(ty) => ty,
                        Err(labels) => {
                            self.error(
                                "E0212",
                                row.span,
                                format!(
                                    "explicit record fields overlap their named row: {}",
                                    labels.into_iter().collect::<Vec<_>>().join(", ")
                                ),
                                [],
                            );
                            Ty::Unknown
                        }
                    }
                } else {
                    Ty::Record(fields)
                }
            }
            TypeKind::Map { key, value } => {
                let key_ty = self.ty(key);
                self.require_data_component(&key_ty, key.span);
                self.require_key_type(&key_ty, key.span);
                let value_ty = self.ty(value);
                self.require_data_component(&value_ty, value.span);
                Ty::Map(Box::new(key_ty), Box::new(value_ty))
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                for ann in annotations {
                    if ann.kind == AnnotationKind::Effect {
                        let _ = self.effect_row(ann);
                    }
                    if ann.kind == AnnotationKind::Capability
                        && ann.text != "&mut"
                        && ann.text != "&^mut"
                        && ann.text != "&closure"
                        && ann.text != "&capture"
                        && !ann.text.starts_with("&{")
                    {
                        self.error(
                            "E0539",
                            ann.span,
                            "state provider reference is only permitted on named definitions",
                            [],
                        );
                    }
                }
                let callable = Ty::Callable(
                    parameters
                        .iter()
                        .map(|p| p.ty.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unknown))
                        .collect(),
                    Box::new(result.as_ref().map(|t| self.ty(t)).unwrap_or(Ty::Unit)),
                );
                self.validate_empty_callable_rows(&callable, annotations, syntax.span);
                callable
            }
            TypeKind::Projection { base, .. } => {
                let ty = self.ty(base);
                if matches!(
                    self.expanded(&ty, &mut BTreeSet::new()),
                    Ty::Array(_) | Ty::Set(_) | Ty::Map(..) | Ty::Tuple(_)
                ) {
                    self.error(
                        "E0337",
                        syntax.span,
                        "collection types have no structural member projection",
                        [],
                    );
                } else {
                    self.unsupported(syntax.span, "type member projection");
                }
                Ty::Unknown
            }
            TypeKind::ComputedProjection { base, key } => {
                let base_type = self.ty(base);
                let identity = if let ExprKind::Name(name) = &key.kind {
                    self.type_source
                        .environment
                        .generic_context
                        .get(name)
                        .filter(|identity| self.generic_key_bounds.contains_key(*identity))
                        .cloned()
                } else {
                    None
                };
                if let Some(identity) = identity {
                    if let Some(coordinate) = self
                        .type_source
                        .environment
                        .static_key_arguments
                        .get(&identity)
                        .cloned()
                    {
                        if let Some(projected) =
                            self.static_type_projection(&base_type, &coordinate)
                        {
                            projected
                        } else {
                            self.error(
                                "E0323",
                                key.span,
                                "static key is not a member of the projected type",
                                [],
                            );
                            Ty::Unknown
                        }
                    } else {
                        Ty::Projection {
                            base: Box::new(base_type),
                            key: identity,
                        }
                    }
                } else {
                    self.unsupported(
                        syntax.span,
                        "computed type projection requires a static coordinate proof",
                    );
                    Ty::Unknown
                }
            }
            _ => {
                self.unsupported(syntax.span, "computed type verification");
                Ty::Unknown
            }
        }
    }
    pub(super) fn require_type_argument_identity(&mut self, syntax: &TypeExpr) {
        if !self.complete_argument_identity(syntax, &mut BTreeSet::new()) {
            self.unsupported(
                syntax.span,
                "type argument identity needs fixed array or callable qualification metadata",
            );
        }
    }
    fn complete_argument_identity(&self, syntax: &TypeExpr, seen: &mut BTreeSet<String>) -> bool {
        if self.closed_source_syntax(syntax).is_some() {
            return true;
        }
        match &syntax.kind {
            TypeKind::Array {
                length: Some(_), ..
            } => false,
            TypeKind::Array { element, .. } | TypeKind::Optional(element) => {
                self.complete_argument_identity(element, seen)
            }
            TypeKind::Name { path, arguments } => {
                if !arguments
                    .iter()
                    .all(|argument| self.complete_argument_identity(argument, &mut seen.clone()))
                {
                    return false;
                }
                let name = path.join("::");
                if !seen.insert(name.clone()) {
                    return true;
                }
                self.types
                    .get(&name)
                    .filter(|declaration| {
                        !declaration.nominal
                            && !declaration.opaque
                            && declaration.variants.is_empty()
                    })
                    .and_then(|declaration| declaration.value.as_ref())
                    .is_none_or(|value| self.complete_argument_identity(value, seen))
            }
            TypeKind::Tuple(items) => items
                .iter()
                .all(|item| self.complete_argument_identity(item, &mut seen.clone())),
            TypeKind::Record { fields, row } => {
                row.is_none()
                    && fields
                        .iter()
                        .all(|field| self.complete_argument_identity(&field.ty, &mut seen.clone()))
            }
            TypeKind::Map { key, value } => {
                self.complete_argument_identity(key, &mut seen.clone())
                    && self.complete_argument_identity(value, &mut seen.clone())
            }
            TypeKind::Callable {
                parameters,
                result,
                annotations,
            } => {
                annotations.is_empty()
                    && parameters.iter().all(|parameter| {
                        parameter.mode == ParameterMode::Read
                            && parameter.ty.as_ref().is_some_and(|ty| {
                                self.complete_argument_identity(ty, &mut seen.clone())
                            })
                    })
                    && result.as_ref().is_none_or(|result| {
                        self.complete_argument_identity(result, &mut seen.clone())
                    })
            }
            TypeKind::Computation(_) => true,
            _ => false,
        }
    }
    pub(super) fn expanded(&self, ty: &Ty, seen: &mut BTreeSet<String>) -> Ty {
        if let Ty::Immutable(inner) = ty {
            return self.expanded(inner, seen);
        }
        if let Ty::Named(name) = ty
            && seen.insert(name.clone())
            && let Some(decl) = self.types.get(name)
            && !decl.nominal
            && !decl.opaque
            && decl.variants.is_empty()
            && let Some(value) = &decl.value
        {
            return self.ty_readonly(value, seen);
        }
        if let Ty::Applied {
            constructor,
            arguments,
        } = ty
            && seen.insert(format!("{ty:?}"))
            && let Some(declaration) = self.types.get(constructor)
            && !declaration.nominal
            && !declaration.opaque
            && declaration.variants.is_empty()
            && let Some(value) = &declaration.value
        {
            let substitutions = declaration
                .generics
                .iter()
                .zip(arguments)
                .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
                .collect();
            return self.ty_substituted(value, seen, &substitutions);
        }
        ty.clone()
    }
    /// Normalize transparent aliases at every inference position. Immutable
    /// qualification and nominal/opaque instance identities remain explicit.
    pub(super) fn call_inference_type(&self, ty: &Ty) -> Ty {
        fn normalize(checker: &Checker, ty: &Ty, seen: &mut BTreeSet<String>, depth: usize) -> Ty {
            if depth > 128 {
                return ty.clone();
            }
            if let Ty::Immutable(inner) = ty {
                return Ty::Immutable(Box::new(normalize(
                    checker,
                    inner,
                    &mut seen.clone(),
                    depth + 1,
                )));
            }
            if matches!(ty, Ty::Named(_) | Ty::Applied { .. }) {
                let expanded = checker.expanded(ty, seen);
                if expanded != *ty {
                    return normalize(checker, &expanded, seen, depth + 1);
                }
            }
            let child = |ty: &Ty| Box::new(normalize(checker, ty, &mut seen.clone(), depth + 1));
            match ty {
                Ty::Optional(inner) => Ty::Optional(child(inner)),
                Ty::Array(inner) => Ty::Array(child(inner)),
                Ty::Set(inner) => Ty::Set(child(inner)),
                Ty::Range(inner) => Ty::Range(child(inner)),
                Ty::Result(ok, error) => Ty::Result(child(ok), child(error)),
                Ty::Map(key, value) => Ty::Map(child(key), child(value)),
                Ty::Tuple(items) => Ty::Tuple(items.iter().map(|ty| *child(ty)).collect()),
                Ty::Record(fields) => Ty::Record(
                    fields
                        .iter()
                        .map(|(name, (mutable, ty))| (name.clone(), (*mutable, *child(ty))))
                        .collect(),
                ),
                Ty::OpenRecord { fields, row } => Ty::OpenRecord {
                    fields: fields
                        .iter()
                        .map(|(name, (mutable, ty))| (name.clone(), (*mutable, *child(ty))))
                        .collect(),
                    row: {
                        let mut row = row.clone();
                        if let Some(lacks) = checker.generic_row_lacks.get(&row.identity) {
                            row.lacks.extend(lacks.iter().cloned());
                        }
                        row
                    },
                },
                Ty::Callable(parameters, result) => Ty::Callable(
                    parameters.iter().map(|ty| *child(ty)).collect(),
                    child(result),
                ),
                Ty::Applied {
                    constructor,
                    arguments,
                } => Ty::Applied {
                    constructor: constructor.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| match argument {
                            TypeArgument::Type(ty) => TypeArgument::Type(child(ty)),
                            TypeArgument::CanonicalType { ty, key } => {
                                TypeArgument::CanonicalType {
                                    ty: child(ty),
                                    key: key.clone(),
                                }
                            }
                            _ => argument.clone(),
                        })
                        .collect(),
                },
                _ => ty.clone(),
            }
        }
        normalize(self, ty, &mut BTreeSet::new(), 0)
    }
    pub(super) fn ty_readonly(&self, ty: &TypeExpr, seen: &mut BTreeSet<String>) -> Ty {
        self.ty_substituted(ty, seen, &BTreeMap::new())
    }
    pub(super) fn ty_substituted(
        &self,
        ty: &TypeExpr,
        seen: &mut BTreeSet<String>,
        substitutions: &BTreeMap<String, TypeArgument>,
    ) -> Ty {
        self.ty_substituted_mode(ty, seen, substitutions, true)
    }
    /// Read only this syntax layer. Named descendants keep their identity so
    /// finite capability scans can budget each alias before expanding it.
    pub(super) fn ty_substituted_shallow(
        &self,
        ty: &TypeExpr,
        substitutions: &BTreeMap<String, TypeArgument>,
    ) -> Ty {
        self.ty_substituted_mode(ty, &mut BTreeSet::new(), substitutions, false)
    }

    /// A record's row is part of its outer shape, not a stored child view.
    /// Expand transparent row aliases while retaining every member's declared
    /// type. Carry the same ancestry through nested compositions and cycles.
    fn shallow_row_shape(&self, tail: Ty, seen: &mut BTreeSet<String>) -> Ty {
        let (name, arguments) = match &tail {
            Ty::Named(name) => (name, &[][..]),
            Ty::Applied {
                constructor,
                arguments,
            } => (constructor, arguments.as_slice()),
            _ => return tail,
        };
        let Some(declaration) = self.types.get(name) else {
            return tail;
        };
        if declaration.nominal
            || declaration.opaque
            || !declaration.variants.is_empty()
            || declaration.generics.len() != arguments.len()
            || seen.len() >= 128
            || !seen.insert(format!("row-shape:{name}"))
        {
            return tail;
        }
        let Some(body) = &declaration.value else {
            return tail;
        };
        let substitutions = declaration
            .generics
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| (parameter.name.clone(), argument.clone()))
            .collect();
        let shape = self.ty_substituted_mode(body, seen, &substitutions, false);
        self.shallow_row_shape(shape, seen)
    }

    fn ty_substituted_mode(
        &self,
        ty: &TypeExpr,
        seen: &mut BTreeSet<String>,
        substitutions: &BTreeMap<String, TypeArgument>,
        expand_aliases: bool,
    ) -> Ty {
        let substitute = |ty: &TypeExpr,
                          seen: &mut BTreeSet<String>,
                          substitutions: &BTreeMap<String, TypeArgument>| {
            self.ty_substituted_mode(ty, seen, substitutions, expand_aliases)
        };
        match &ty.kind {
            TypeKind::Name { path, arguments } => {
                let full_name = path.join("::");
                let name = full_name
                    .strip_prefix("Prelude::")
                    .unwrap_or(&full_name)
                    .to_owned();
                if full_name == name
                    && let Some(argument) = substitutions.get(&name)
                {
                    return match argument {
                        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. }
                            if arguments.is_empty() =>
                        {
                            *ty.clone()
                        }
                        TypeArgument::Symbolic(identity) if arguments.is_empty() => {
                            Ty::Generic(identity.clone())
                        }
                        _ => Ty::Unknown,
                    };
                }
                if full_name == name
                    && let Some(identity) = self.type_source.environment.generic_context.get(&name)
                {
                    if self.generic_key_bounds.contains_key(identity) {
                        return Ty::StaticKey(identity.clone());
                    }
                    return self
                        .type_source
                        .environment
                        .generic_substitutions
                        .get(identity)
                        .cloned()
                        .unwrap_or_else(|| Ty::Generic(identity.clone()));
                }
                if full_name == name
                    && arguments.is_empty()
                    && let Some(row) = self.bound_row_type(&name)
                {
                    return row;
                }
                if !self.types.contains_key(&full_name)
                    && let Some(schema) =
                        io::operation_type(ty).or_else(|| super::iter_types::schema(ty))
                {
                    return substitute(&schema, seen, substitutions);
                }
                if !self.types.contains_key(&full_name)
                    && let Some(ty) = standard::file_type(&name)
                {
                    return if arguments.is_empty() {
                        ty
                    } else {
                        Ty::Unknown
                    };
                }
                if name == "Immut" && arguments.len() == 1 {
                    return Ty::Immutable(Box::new(substitute(&arguments[0], seen, substitutions)));
                }
                if name == "Option" && arguments.len() == 1 {
                    return Ty::Optional(Box::new(substitute(&arguments[0], seen, substitutions)));
                }
                if name == "Result" && arguments.len() == 2 {
                    return Ty::Result(
                        Box::new(substitute(&arguments[0], seen, substitutions)),
                        Box::new(substitute(&arguments[1], seen, substitutions)),
                    );
                }
                if name == "Range" && arguments.len() == 1 {
                    return Ty::Range(Box::new(substitute(&arguments[0], seen, substitutions)));
                }
                if name == "Set" && arguments.len() == 1 {
                    return Ty::Set(Box::new(substitute(&arguments[0], seen, substitutions)));
                }
                if let Some(declaration) = self.types.get(&full_name)
                    && !declaration.generics.is_empty()
                {
                    if arguments.len() != declaration.generics.len() {
                        return Ty::Unknown;
                    }
                    let arguments = declaration
                        .generics
                        .iter()
                        .zip(arguments)
                        .map(|(parameter, argument)| {
                            if !expand_aliases
                                && let TypeKind::Name { path, arguments } = &argument.kind
                                && arguments.is_empty()
                                && let Some(argument) = substitutions.get(&path.join("::"))
                            {
                                return argument.clone();
                            }
                            if static_parameter(parameter) {
                                if let TypeKind::Name { path, arguments } = &argument.kind
                                    && arguments.is_empty()
                                    && let Some(argument) = substitutions.get(&path.join("::"))
                                {
                                    return argument.clone();
                                }
                                if !expand_aliases && !normalized_static_argument(argument) {
                                    return TypeArgument::Symbolic(format!(
                                        "unresolved-static:{}",
                                        crate::static_eval::normalized_argument_key(argument)
                                    ));
                                }
                                TypeArgument::Static(crate::static_eval::normalized_argument_key(
                                    argument,
                                ))
                            } else {
                                let ty = substitute(argument, &mut seen.clone(), substitutions);
                                if expand_aliases {
                                    self.canonical_type_argument(argument, ty)
                                } else {
                                    self.shallow_type_argument(argument, ty, substitutions)
                                }
                            }
                        })
                        .collect();
                    let applied = Ty::Applied {
                        constructor: if expand_aliases {
                            name
                        } else {
                            declaration.name.clone()
                        },
                        arguments,
                    };
                    return if expand_aliases {
                        self.expanded(&applied, seen)
                    } else {
                        applied
                    };
                }
                if matches!(name.as_str(), "Deque::Deque" | "Heap::Heap") && arguments.len() == 1 {
                    return Ty::Applied {
                        constructor: name,
                        arguments: vec![self.canonical_type_argument(
                            &arguments[0],
                            substitute(&arguments[0], seen, substitutions),
                        )],
                    };
                }
                let result = match name.as_str() {
                    "bool" => Ty::Bool,
                    "str" => Ty::Str,
                    "bytes" => Ty::Bytes,
                    "never" => Ty::Never,
                    "f32" | "f64" => Ty::Float(name.clone()),
                    "int" | "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
                    | "bigint" => Ty::Int(name.clone()),
                    _ => Ty::Named(name.clone()),
                };
                if expand_aliases {
                    self.expanded(&result, seen)
                } else {
                    result
                }
            }
            TypeKind::Record { fields, row } => {
                let fields = fields
                    .iter()
                    .map(|f| {
                        (
                            f.name.clone(),
                            (
                                f.mutable,
                                substitute(&f.ty, &mut seen.clone(), substitutions),
                            ),
                        )
                    })
                    .collect();
                if let Some(row) = row {
                    let mut ancestry = seen.clone();
                    let tail = substitute(row, &mut ancestry, substitutions);
                    let tail = if expand_aliases {
                        tail
                    } else {
                        self.shallow_row_shape(tail, &mut ancestry)
                    };
                    self.record_with_row(fields, row, tail)
                } else {
                    Ty::Record(fields)
                }
            }
            TypeKind::Tuple(items) => {
                if items.is_empty() {
                    Ty::Unit
                } else {
                    Ty::Tuple(
                        items
                            .iter()
                            .map(|t| substitute(t, &mut seen.clone(), substitutions))
                            .collect(),
                    )
                }
            }
            TypeKind::Array { element, .. } => {
                Ty::Array(Box::new(substitute(element, seen, substitutions)))
            }
            TypeKind::Optional(inner) => {
                Ty::Optional(Box::new(substitute(inner, seen, substitutions)))
            }
            TypeKind::ComputedProjection { base, key } => {
                let base = substitute(base, seen, substitutions);
                if let ExprKind::Name(name) = &key.kind
                    && let Some(identity) = self.type_source.environment.generic_context.get(name)
                    && self.generic_key_bounds.contains_key(identity)
                {
                    if let Some(coordinate) = self
                        .type_source
                        .environment
                        .static_key_arguments
                        .get(identity)
                    {
                        self.static_type_projection(&base, coordinate)
                            .unwrap_or(Ty::Unknown)
                    } else {
                        Ty::Projection {
                            base: Box::new(base),
                            key: identity.clone(),
                        }
                    }
                } else {
                    Ty::Unknown
                }
            }
            TypeKind::Map { key, value } => Ty::Map(
                Box::new(substitute(key, &mut seen.clone(), substitutions)),
                Box::new(substitute(value, &mut seen.clone(), substitutions)),
            ),
            TypeKind::Callable {
                parameters, result, ..
            } => Ty::Callable(
                parameters
                    .iter()
                    .map(|p| {
                        p.ty.as_ref()
                            .map(|t| substitute(t, &mut seen.clone(), substitutions))
                            .unwrap_or(Ty::Unknown)
                    })
                    .collect(),
                Box::new(
                    result
                        .as_ref()
                        .map(|t| substitute(t, seen, substitutions))
                        .unwrap_or(Ty::Unit),
                ),
            ),
            _ => Ty::Unknown,
        }
    }
    /// Shallow substitution must also substitute identity metadata. Reusing
    /// the literal key of `T` or `[]T` would merge different alias instances.
    fn shallow_type_argument(
        &self,
        syntax: &TypeExpr,
        ty: Ty,
        substitutions: &BTreeMap<String, TypeArgument>,
    ) -> TypeArgument {
        fn key(
            syntax: &TypeExpr,
            substitutions: &BTreeMap<String, TypeArgument>,
        ) -> Option<String> {
            let child = |syntax: &TypeExpr| key(syntax, substitutions);
            Some(match &syntax.kind {
                TypeKind::Name { path, arguments } => {
                    let name = path.join("::");
                    if arguments.is_empty()
                        && let Some(argument) = substitutions.get(&name)
                    {
                        return match argument {
                            TypeArgument::CanonicalType { key, .. } | TypeArgument::Static(key) => {
                                Some(key.clone())
                            }
                            _ => None,
                        };
                    }
                    format!(
                        "{}<{}>",
                        name.strip_prefix("Prelude::").unwrap_or(&name),
                        arguments
                            .iter()
                            .map(child)
                            .collect::<Option<Vec<_>>>()?
                            .join(",")
                    )
                }
                TypeKind::Optional(inner) => format!("Option<{}>", child(inner)?),
                TypeKind::Array { element, .. } => {
                    // Read the normalized length expression without inventing
                    // an expression-level static substitution policy here.
                    let mut shell = syntax.clone();
                    let TypeKind::Array {
                        element: shell_element,
                        length,
                        ..
                    } = &mut shell.kind
                    else {
                        unreachable!()
                    };
                    if let Some(length) = length
                        && !normalized_static_argument(&TypeExpr {
                            hir_id: None,
                            kind: TypeKind::Computation(length.clone()),
                            text: String::new(),
                            span: length.span,
                        })
                    {
                        return None;
                    }
                    shell_element.kind = TypeKind::Tuple(vec![]);
                    let shell = crate::static_eval::normalized_argument_key(&shell);
                    format!("{}{}", shell.strip_suffix("()")?, child(element)?)
                }
                TypeKind::Map { key, value } => format!("[{}:{}]", child(key)?, child(value)?),
                TypeKind::Tuple(items) => format!(
                    "({})",
                    items
                        .iter()
                        .map(child)
                        .collect::<Option<Vec<_>>>()?
                        .join(",")
                ),
                TypeKind::Record { fields, row } => {
                    let mut fields = fields
                        .iter()
                        .map(|field| {
                            Some(format!(
                                "{}{}:{}",
                                if field.mutable { "mut " } else { "" },
                                field.name,
                                child(&field.ty)?
                            ))
                        })
                        .collect::<Option<Vec<_>>>()?;
                    fields.sort();
                    format!(
                        "{{{};{}}}",
                        fields.join(","),
                        match row {
                            Some(row) => child(row)?,
                            None => String::new(),
                        }
                    )
                }
                TypeKind::Callable {
                    parameters,
                    result,
                    annotations,
                } => format!(
                    "fn({})->{}{}",
                    parameters
                        .iter()
                        .map(|parameter| Some(format!(
                            "{:?}:{}",
                            parameter.mode,
                            match &parameter.ty {
                                Some(ty) => child(ty)?,
                                None => String::new(),
                            }
                        )))
                        .collect::<Option<Vec<_>>>()?
                        .join(","),
                    match result {
                        Some(result) => child(result)?,
                        None => String::new(),
                    },
                    annotations
                        .iter()
                        .map(|annotation| annotation.text.replace(' ', ""))
                        .collect::<String>()
                ),
                _ => crate::static_eval::normalized_argument_key(syntax),
            })
        }
        let Some(syntax) = self.canonical_argument_syntax(syntax, 0) else {
            return TypeArgument::Type(Box::new(ty));
        };
        match key(&syntax, substitutions) {
            Some(key) if !ty.contains_open_row() => TypeArgument::CanonicalType {
                ty: Box::new(ty),
                key,
            },
            _ => TypeArgument::Type(Box::new(ty)),
        }
    }
    pub(super) fn compatible(&self, actual: &Ty, expected: &Ty) -> bool {
        self.compatible_recursive(actual, expected, &mut BTreeSet::new(), 0)
    }
    fn compatible_recursive(
        &self,
        actual: &Ty,
        expected: &Ty,
        seen: &mut BTreeSet<(String, String)>,
        depth: usize,
    ) -> bool {
        if actual == expected || matches!(actual, Ty::Never) {
            return true;
        }
        if matches!(actual, Ty::Unknown) || matches!(expected, Ty::Unknown) {
            return true;
        }
        if depth >= 128 {
            return false;
        }
        if !seen.insert((format!("{actual:?}"), format!("{expected:?}"))) {
            return true;
        }
        let a = self.expanded(actual, &mut BTreeSet::new());
        let b = self.expanded(expected, &mut BTreeSet::new());
        match (&a, &b) {
            (Ty::Int(a), Ty::Int(b)) | (Ty::Float(a), Ty::Float(b)) => a == b,
            (Ty::Array(a), Ty::Array(b))
            | (Ty::Set(a), Ty::Set(b))
            | (Ty::Optional(a), Ty::Optional(b)) => {
                self.compatible_recursive(a, b, seen, depth + 1)
            }
            (Ty::Result(a, b), Ty::Result(c, d)) | (Ty::Map(a, b), Ty::Map(c, d)) => {
                self.compatible_recursive(a, c, seen, depth + 1)
                    && self.compatible_recursive(b, d, seen, depth + 1)
            }
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|(a, b)| self.compatible_recursive(a, b, seen, depth + 1))
            }
            (Ty::Record(a), Ty::Record(b)) => {
                a.len() == b.len()
                    && a.iter().all(|(name, (m, t))| {
                        b.get(name).is_some_and(|(n, u)| {
                            m == n && self.compatible_recursive(t, u, seen, depth + 1)
                        })
                    })
            }
            (Ty::Callable(a, r), Ty::Callable(b, s)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b)
                        .all(|(a, b)| self.compatible_recursive(a, b, seen, depth + 1))
                    && self.compatible_recursive(r, s, seen, depth + 1)
            }
            _ => a == b,
        }
    }
    pub(super) fn require_type(&mut self, value: &Value, ty: &Ty, span: Span) {
        self.check_retained_callable_answer(value, ty, span);
        if self.call_inference_type(&value.ty).contains_open_row()
            || self.call_inference_type(ty).contains_open_row()
        {
            if value.ty == Ty::Never {
                return;
            }
            if matches!(self.representation_at(ty, span.file), Ty::Immutable(_))
                && (value.publication != Publication::Immutable
                    || self.has_writer(value)
                    || value.mutable_environment
                    || value.observer_environment)
            {
                self.error(
                    "E0535",
                    span,
                    "immutable qualification requires proof for the complete record tail",
                    [value.cause],
                );
                return;
            }
            self.require_row_transport(value, ty, span);
            return;
        }
        self.constrain_collection_type(value, ty, span);
        let visible_ty = self.representation_at(ty, span.file);
        let expected = self.expanded_at(ty, span.file);
        if !value.callables.is_empty()
            && !matches!(expected, Ty::Callable(..) | Ty::Generic(_) | Ty::Unknown)
        {
            self.error(
                "E0301",
                span,
                "a callable descriptor cannot be ascribed a data type",
                [value.cause],
            );
            return;
        }
        if value.ty == Ty::Unknown
            && matches!(expected, Ty::Callable(..))
            && value
                .callables
                .iter()
                .any(|callable| matches!(callable, Callable::Builtin(_)))
        {
            self.unsupported(
                span,
                "first-class builtin callable requires a complete checked signature",
            );
            return;
        }
        if (value.construction || value.unsuffixed_numeric)
            && let Some(alternatives) = self.type_alternatives.get(&value.cause.0).cloned()
        {
            for alternative in alternatives {
                self.require_type(&alternative, ty, span);
            }
        }
        self.literal_shape_context(value, &visible_ty, span);
        if matches!(visible_ty, Ty::Immutable(_))
            && (self.has_writer(value)
                || value.mutable_environment
                || value.observer_environment
                || (value.publication != Publication::Immutable && !value.construction))
        {
            self.error(
                "E0535",
                span,
                "Immut qualification requires an immutable reachable graph",
                [value.cause],
            );
        }
        if let Ty::Int(name) = ty {
            if let Some(Constant::Integer(number)) = value.constant
                && value.literal_number
            {
                self.integer_range(number, name, span, value.cause);
            }
            if let Ty::Int(actual) = &value.ty
                && actual != name
                && !value.unsuffixed_numeric
            {
                self.error(
                    "E0301",
                    span,
                    "integer types do not implicitly promote",
                    [value.cause],
                );
            }
        }
        if !self.compatible_at(&value.ty, ty, span.file)
            && !self.literal_shape_compatible(value, &visible_ty)
            && !self.constructor_callable_compatible(value, ty)
        {
            if let (Ty::Record(actual), Ty::Record(expected)) = (
                self.expanded_at(&value.ty, span.file),
                self.expanded_at(ty, span.file),
            ) {
                let unexpected: Vec<_> = actual
                    .keys()
                    .filter(|name| !expected.contains_key(*name))
                    .cloned()
                    .collect();
                let missing: Vec<_> = expected
                    .keys()
                    .filter(|name| !actual.contains_key(*name))
                    .cloned()
                    .collect();
                if !unexpected.is_empty() || !missing.is_empty() {
                    if !unexpected.is_empty() {
                        self.error(
                            "E0302",
                            span,
                            format!("unexpected record fields: {}", unexpected.join(", ")),
                            [value.cause],
                        );
                    }
                    if !missing.is_empty() {
                        self.error(
                            "E0307",
                            span,
                            format!("missing record fields: {}", missing.join(", ")),
                            [value.cause],
                        );
                    }
                    return;
                }
            }
            let mut handler = false;
            let mut pending = vec![value.cause];
            let mut seen = BTreeSet::new();
            while let Some(id) = pending.pop() {
                if seen.insert(id.0) {
                    handler |= self.explanations.kinds[id.0 as usize] == CauseKind::Handler;
                    pending.extend(&self.explanations.causes[id.0 as usize].parents);
                }
            }
            self.error(
                if handler { "E0625" } else { "E0301" },
                span,
                format!("expected {ty:?}, found {:?}", value.ty),
                [value.cause],
            );
        }
    }
    pub(super) fn require_branch_types(&mut self, left: &mut Value, right: &mut Value, span: Span) {
        if left.ty == Ty::Never || right.ty == Ty::Never {
            return;
        }
        let before = self.diagnostics.len();
        self.require_type(right, &left.ty, span);
        for diagnostic in &mut self.diagnostics[before..] {
            if matches!(diagnostic.code.as_str(), "E0301" | "E0302" | "E0307") {
                diagnostic.code = "E0351".into();
            }
        }
    }
    pub(super) fn literal_shape_compatible(&self, value: &Value, expected: &Ty) -> bool {
        if !value.construction {
            return false;
        }
        let expected = self.expanded(expected, &mut BTreeSet::new());
        match (&value.ty, &expected) {
            (Ty::Optional(_), Ty::Optional(expected)) => {
                value.option_payload.as_ref().is_some_and(|payload| {
                    self.compatible(&payload.ty, expected)
                        || self.literal_shape_compatible(payload, expected)
                })
            }
            (Ty::Array(_), Ty::Array(element)) => value.origins.nodes.iter().all(|node| {
                self.fields
                    .iter()
                    .filter(|((parent, slot), _)| {
                        parent == node && matches!(slot, Slot::Index(_) | Slot::AnyIndex)
                    })
                    .all(|(_, child)| {
                        self.compatible(&child.ty, element)
                            || self.literal_shape_compatible(child, element)
                    })
            }),
            (Ty::Map(..), Ty::Map(key, element)) => value.origins.nodes.iter().all(|node| {
                self.fields
                    .iter()
                    .filter(|((parent, _), _)| parent == node)
                    .all(|((_, slot), child)| {
                        let expected = if matches!(slot,Slot::Field(name)if name=="key") {
                            &**key
                        } else {
                            &**element
                        };
                        self.compatible(&child.ty, expected)
                            || self.literal_shape_compatible(child, expected)
                    })
            }),
            (Ty::Tuple(items), Ty::Tuple(expected)) if items.len() == expected.len() => {
                value.origins.nodes.iter().all(|node| {
                    expected.iter().enumerate().all(|(index, ty)| {
                        self.fields
                            .get(&(*node, Slot::Tuple(index as u32)))
                            .is_some_and(|child| {
                                self.compatible(&child.ty, ty)
                                    || self.literal_shape_compatible(child, ty)
                            })
                    })
                })
            }
            (Ty::Record(fields), Ty::Record(expected)) if fields.len() == expected.len() => {
                value.origins.nodes.iter().all(|node| {
                    expected.iter().all(|(name, (_, ty))| {
                        self.fields
                            .get(&(*node, Slot::Field(name.clone())))
                            .is_some_and(|child| {
                                self.compatible(&child.ty, ty)
                                    || self.literal_shape_compatible(child, ty)
                            })
                    })
                })
            }
            _ => false,
        }
    }
    fn literal_shape_context(&mut self, value: &Value, expected: &Ty, span: Span) {
        if !value.construction {
            return;
        }
        let expected = self.expanded(expected, &mut BTreeSet::new());
        let mut checks = Vec::new();
        for node in &value.origins.nodes {
            for ((parent, slot), child) in &self.fields {
                if parent != node {
                    continue;
                }
                let ty = match (&expected, slot) {
                    (Ty::Array(ty), Slot::Index(_) | Slot::AnyIndex) => Some(*ty.clone()),
                    (Ty::Map(key, _), Slot::Field(name)) if name == "key" => Some(*key.clone()),
                    (Ty::Map(_, value), Slot::Index(_) | Slot::AnyIndex) => Some(*value.clone()),
                    (Ty::Tuple(items), Slot::Tuple(index)) => items.get(*index as usize).cloned(),
                    (Ty::Record(fields), Slot::Field(name)) => {
                        fields.get(name).map(|(_, ty)| ty.clone())
                    }
                    _ => None,
                };
                if let Some(ty) = ty {
                    checks.push(((*parent, slot.clone()), child.clone(), ty));
                }
            }
        }
        for (key, child, ty) in checks {
            self.require_type(&child, &ty, span);
            if self.literal_shape_compatible(&child, &ty)
                && let Some(stored) = self.fields.get_mut(&key)
            {
                stored.ty = ty;
            }
        }
    }
    pub(super) fn require_key_type(&mut self, ty: &Ty, span: Span) {
        let expanded = self.expanded(ty, &mut BTreeSet::new());
        let admitted = matches!(
            expanded,
            Ty::Bool | Ty::Int(_) | Ty::Str | Ty::Bytes | Ty::Unit | Ty::Generic(_)
        ) || matches!(&expanded,Ty::Named(name) if matches!(name.as_str(),"Os::NativeString"|"Path::Path"));
        if !admitted {
            self.error(
                "E0328",
                span,
                "map keys and set elements require an admitted equality key type",
                [],
            );
        }
    }
    pub(super) fn known_empty_map(&self, value: &Value) -> bool {
        matches!(self.call_inference_type(&value.ty), Ty::Map(..))
            && !value.origins.nodes.is_empty()
            && value.origins.nodes.iter().all(|node| {
                matches!(self.heap.nodes[node.0 as usize].kind, OriginKind::Fresh(_))
                    && !self
                        .uncertain_slots
                        .iter()
                        .any(|(parent, _)| parent == node)
                    && !self.fields.keys().any(|(parent, slot)| {
                        parent == node
                            && matches!(slot, Slot::Index(_) | Slot::AnyIndex | Slot::Field(_))
                    })
            })
    }
    pub(super) fn unresolved_empty_map_keys(&self, value: &Value) -> bool {
        fn visit(checker: &Checker, value: &Value, seen: &mut BTreeSet<NodeId>) -> bool {
            if value.requires_inference
                && matches!(value.ty, Ty::Map(..))
                && matches!(checker.collection_type(value),Ty::Map(key,element) if *key==Ty::Unknown||*element==Ty::Unknown)
            {
                return true;
            }
            if [
                &value.variant_payload,
                &value.option_payload,
                &value.result_payload,
                &value.result_success,
                &value.result_error,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            .any(|value| visit(checker, value, seen))
            {
                return true;
            }
            for node in &value.origins.nodes {
                if seen.insert(*node)
                    && checker
                        .fields
                        .iter()
                        .any(|((parent, _), value)| parent == node && visit(checker, value, seen))
                {
                    return true;
                }
            }
            false
        }
        visit(self, value, &mut BTreeSet::new())
    }
    fn contextual_empty_map(&mut self, value: &mut Value, syntax: &TypeExpr) {
        let Ty::Map(key, element) = self.call_inference_type(&value.ty) else {
            return;
        };
        if (*key != Ty::Unknown && *element != Ty::Unknown) || !self.known_empty_map(value) {
            return;
        }
        let expected = self.ty(syntax);
        let Ty::Map(key, element) = self.call_inference_type(&expected) else {
            return;
        };
        if *key == Ty::Unknown || *element == Ty::Unknown {
            return;
        }
        self.require_key_type(&key, syntax.span);
        self.constrain_collection_type(value, &expected, syntax.span);
        value.ty = expected;
        value.requires_inference = !self.pending_result_binders(value).is_empty();
    }
    pub(super) fn callable_syntax(
        &self,
        syntax: &TypeExpr,
        seen: &mut BTreeSet<String>,
    ) -> Option<(Vec<Parameter>, Vec<Annotation>)> {
        match &syntax.kind {
            TypeKind::Callable {
                parameters,
                annotations,
                ..
            } => Some((parameters.clone(), annotations.clone())),
            TypeKind::Name { path, .. } => {
                let name = path.join("::");
                if !seen.insert(name.clone()) {
                    return None;
                }
                self.types
                    .get(&name)
                    .and_then(|decl| decl.value.as_ref())
                    .and_then(|ty| self.callable_syntax(ty, seen))
            }
            _ => None,
        }
    }
    /// Compare modes without replacing the actual invocation descriptor.
    pub(super) fn check_signature_modes(&mut self, value: &Value, syntax: &TypeExpr) {
        if let Some((parameters, _)) = self.callable_syntax(syntax, &mut BTreeSet::new())
            && let Some(source) = &value.signature
            && source.parameters.len() == parameters.len()
            && source
                .parameters
                .iter()
                .zip(&parameters)
                .any(|(a, b)| a.mode != b.mode)
        {
            self.error(
                "E0407",
                syntax.span,
                "callable parameter modes must match exactly",
                [value.cause],
            );
        }
    }

    pub(super) fn ascribe_signature(&mut self, value: &mut Value, syntax: &TypeExpr) {
        let source = self.signature_source(syntax);
        self.ascribe_signature_from(value, syntax, &source);
    }

    pub(super) fn ascribe_signature_from(
        &mut self,
        value: &mut Value,
        syntax: &TypeExpr,
        source: &super::contracts::SignatureSource<'_>,
    ) {
        if let TypeKind::Name { path, arguments } = &syntax.kind
            && arguments.is_empty()
            && self
                .type_source
                .environment
                .generic_context
                .get(&path.join("::"))
                .is_some_and(|binder| {
                    self.type_source
                        .environment
                        .generic_sources
                        .contains_key(binder)
                })
        {
            // T transports the actual callable interface (including defaults
            // and labels). Its identity schema does not replace that descriptor.
            self.ascribe_source_type(value, syntax);
            return;
        }
        if let Some(instantiated) = self.instantiated_callable_alias(syntax) {
            self.ascribe_signature_from(value, &instantiated, source);
            return;
        }
        self.instantiate_builtin_signature(value, syntax);
        self.contextual_empty_map(value, syntax);
        if !self.pending_result_binders(value).is_empty() {
            if !self.complete_argument_identity(syntax, &mut BTreeSet::new()) {
                self.unsupported(syntax.span,"contextual generic result requires complete dimensions and callable qualification identity");
            } else {
                let expected = self.ty(syntax);
                self.contextual_result_inference(value, &expected, syntax.span);
            }
        }
        if let Some(schema) =
            io::operation_type(syntax).or_else(|| super::iter_types::schema(syntax))
        {
            self.ascribe_signature_from(value, &schema, source);
            return;
        }
        if let Some((parameters, annotations)) = self.callable_syntax(syntax, &mut BTreeSet::new())
        {
            self.check_signature_modes(value, syntax);
            value.signature = Some(self.callable_signature(parameters));
            self.ascribe_callable_return(value, syntax, source);
            self.ascribe_callable_bounds_from(value, syntax, &annotations, source);
        }
        self.ascribe_nested_callable_bounds_from(value, syntax, source);
        self.ascribe_source_type(value, syntax);
    }
    pub(super) fn check_storage_shape(
        &mut self,
        value: &Value,
        syntax: &TypeExpr,
        frame: &mut Frame,
    ) {
        let instantiated = self.instantiated_source_syntax(syntax);
        let syntax = instantiated.as_ref().unwrap_or(syntax);
        self.array_shape(value, syntax, frame);
        if let TypeKind::Array { element, .. } = &syntax.kind {
            let expected = self.ty(element);
            let children: Vec<_> = value
                .origins
                .nodes
                .iter()
                .flat_map(|node| {
                    self.fields
                        .iter()
                        .filter_map(move |((parent, slot), value)| {
                            (*parent == *node && matches!(slot, Slot::Index(_) | Slot::AnyIndex))
                                .then_some(value.clone())
                        })
                })
                .collect();
            for child in children {
                self.require_type(&child, &expected, element.span);
            }
        }
    }
    pub(super) fn integer_range(&mut self, number: i128, name: &str, span: Span, cause: CauseId) {
        let (signed, bits) = match name {
            "i8" => (true, 8),
            "i16" => (true, 16),
            "i32" => (true, 32),
            "i64" => (true, 64),
            "int" | "isize" => (true, self.layout.pointer_bits),
            "i128" => (true, 128),
            "u8" => (false, 8),
            "u16" => (false, 16),
            "u32" => (false, 32),
            "u64" => (false, 64),
            "usize" => (false, self.layout.pointer_bits),
            "u128" => (false, 128),
            _ => return,
        };
        let valid = if signed {
            bits == 128 || (number >= -(1i128 << (bits - 1)) && number < (1i128 << (bits - 1)))
        } else {
            number >= 0 && (bits == 128 || number < (1i128 << bits))
        };
        if !valid {
            self.error(
                "E0326",
                span,
                format!("integer literal is outside {name}'s range"),
                [cause],
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn closed_source_records_solve_rows_without_losing_remainders_or_field_modes() {
        let parsed = ril_syntax::parse(
            "fn choose<R,T>(value:{id:T,..R})->{id:T,..R}{value}\ntype Actual={id:int,mut payload:[]int}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let StmtKind::Function(function) = &parsed.program.statements[0].kind else {
            panic!()
        };
        let StmtKind::Type(actual) = &parsed.program.statements[1].kind else {
            panic!()
        };
        let mut checker = Checker::new(FileId(0));
        checker.type_source.environment.generic_context.extend([
            ("R".into(), "callee:R".into()),
            ("T".into(), "callee:T".into()),
        ]);
        let template = checker.ty(function.parameters[0].ty.as_ref().unwrap());
        let actual = checker.ty(actual.value.as_ref().unwrap());
        let binders = BTreeSet::from(["callee:R".into(), "callee:T".into()]);
        let mut selected = BTreeMap::new();
        assert!(unify_call_types(
            &template,
            &actual,
            &binders,
            &mut selected
        ));
        assert_eq!(selected["callee:T"], Ty::Int("int".into()));
        assert_eq!(
            selected["callee:R"],
            Ty::Record(
                [(
                    "payload".into(),
                    (true, Ty::Array(Box::new(Ty::Int("int".into()))))
                )]
                .into()
            )
        );
        assert_eq!(substitute_inferred_type(&template, &selected), actual);
        let previous = selected.clone();
        for different in [
            Ty::Record(
                [
                    ("id".into(), (false, Ty::Int("int".into()))),
                    (
                        "payload".into(),
                        (false, Ty::Array(Box::new(Ty::Int("int".into())))),
                    ),
                ]
                .into(),
            ),
            Ty::Record(
                [
                    ("id".into(), (false, Ty::Int("int".into()))),
                    ("payload".into(), (true, Ty::Array(Box::new(Ty::Str)))),
                ]
                .into(),
            ),
            Ty::Record(
                [
                    ("id".into(), (false, Ty::Str)),
                    (
                        "payload".into(),
                        (true, Ty::Array(Box::new(Ty::Int("int".into())))),
                    ),
                ]
                .into(),
            ),
        ] {
            assert!(!unify_call_types(
                &template,
                &different,
                &binders,
                &mut selected
            ));
            assert_eq!(
                selected, previous,
                "a failed row equation leaked partial selections"
            );
        }
    }
    #[test]
    fn source_row_inference_keeps_lacks_and_never_solves_a_rigid_unknown_tail() {
        use crate::sema::model::rows::{OpenTail, RowIdentity};
        let template = Ty::OpenRecord {
            fields: [("id".into(), (false, Ty::Int("int".into())))].into(),
            row: OpenTail {
                identity: RowIdentity::Binder("callee:R".into()),
                lacks: ["id".into(), "reserved".into()].into(),
            },
        };
        let binders = BTreeSet::from(["callee:R".into()]);
        let mut selected = BTreeMap::new();
        let forbidden = Ty::Record(
            [
                ("id".into(), (false, Ty::Int("int".into()))),
                ("reserved".into(), (false, Ty::Str)),
            ]
            .into(),
        );
        assert!(!unify_call_types(
            &template,
            &forbidden,
            &binders,
            &mut selected
        ));
        assert!(selected.is_empty());
        let complete = Ty::Record([("id".into(), (false, Ty::Int("int".into())))].into());
        assert!(!unify_call_types(
            &template,
            &complete,
            &BTreeSet::new(),
            &mut selected
        ));
        assert!(selected.is_empty());
        assert!(unify_call_types(
            &template,
            &Ty::Unknown,
            &binders,
            &mut selected
        ));
        assert!(
            selected.is_empty(),
            "absence of evidence cannot select an empty row"
        );
        assert_eq!(substitute_inferred_type(&template, &selected), template);
        assert!(unify_call_types(
            &template,
            &complete,
            &binders,
            &mut selected
        ));
        assert_eq!(selected["callee:R"], Ty::Record(BTreeMap::new()));
        let corrupted = [(
            "callee:R".into(),
            Ty::Record([("reserved".into(), (false, Ty::Str))].into()),
        )]
        .into();
        assert!(matches!(
            substitute_inferred_type(&template, &corrupted),
            Ty::OpenRecord { .. }
        ));
    }
    #[test]
    fn an_explicit_symbolic_type_keeps_its_identity_when_used_as_a_rigid_row() {
        use crate::sema::model::rows::{OpenTail, RowIdentity};
        let template = Ty::OpenRecord {
            fields: [("item".into(), (false, Ty::Generic("callee:T".into())))].into(),
            row: OpenTail {
                identity: RowIdentity::Binder("callee:R".into()),
                lacks: ["item".into(), "reserved".into()].into(),
            },
        };
        let actual = Ty::OpenRecord {
            fields: [("item".into(), (false, Ty::Generic("caller:T".into())))].into(),
            row: OpenTail {
                identity: RowIdentity::Binder("caller:R".into()),
                lacks: ["item".into(), "reserved".into()].into(),
            },
        };
        let binders = ["callee:T".into(), "callee:R".into()].into();
        let explicit = BTreeMap::from([
            ("callee:T".into(), Ty::Generic("caller:T".into())),
            ("callee:R".into(), Ty::Generic("caller:R".into())),
        ]);
        let mut selected = explicit.clone();
        assert!(unify_call_types(
            &template,
            &actual,
            &binders,
            &mut selected
        ));
        assert_eq!(selected, explicit);

        let mut other = explicit.clone();
        other.insert("callee:R".into(), Ty::Generic("other:R".into()));
        let before = other.clone();
        assert!(!unify_call_types(&template, &actual, &binders, &mut other));
        assert_eq!(other, before);

        let Ty::OpenRecord {
            mut fields,
            mut row,
        } = actual
        else {
            unreachable!()
        };
        row.lacks.remove("reserved");
        assert!(!unify_call_types(
            &template,
            &Ty::OpenRecord {
                fields: fields.clone(),
                row: row.clone()
            },
            &binders,
            &mut selected,
        ));
        assert_eq!(selected, explicit);
        row.lacks.insert("reserved".into());
        fields.insert("extra".into(), (false, Ty::Str));
        row.lacks.insert("extra".into());
        assert!(!unify_call_types(
            &template,
            &Ty::OpenRecord { fields, row },
            &binders,
            &mut selected,
        ));
        assert_eq!(selected, explicit);
    }
    #[test]
    fn call_unification_uses_one_strict_binding_per_parameter() {
        let binders = BTreeSet::from(["callee:T".to_owned()]);
        let variable = Ty::Generic("callee:T".into());
        let mut inferred = BTreeMap::new();
        assert!(unify_call_types(
            &variable,
            &Ty::Int("int".into()),
            &binders,
            &mut inferred
        ));
        assert!(!unify_call_types(
            &variable,
            &Ty::Str,
            &binders,
            &mut inferred
        ));
        assert_eq!(inferred["callee:T"], Ty::Int("int".into()));

        inferred.clear();
        assert!(unify_call_types(
            &variable,
            &Ty::Generic("caller:T".into()),
            &binders,
            &mut inferred
        ));
        assert!(!unify_call_types(
            &variable,
            &Ty::Generic("caller:U".into()),
            &binders,
            &mut inferred
        ));
        assert!(!unify_call_types(
            &variable,
            &Ty::Int("int".into()),
            &binders,
            &mut inferred
        ));
    }
    #[test]
    fn call_unification_fills_nested_holes_without_losing_instance_identity() {
        let binders = BTreeSet::from(["callee:T".to_owned()]);
        let variable = Ty::Generic("callee:T".into());
        let mut inferred = BTreeMap::new();
        let optional = |ty| Ty::Optional(Box::new(ty));
        assert!(unify_call_types(
            &variable,
            &optional(Ty::Unknown),
            &binders,
            &mut inferred
        ));
        assert!(unify_call_types(
            &variable,
            &optional(Ty::Str),
            &binders,
            &mut inferred
        ));
        assert_eq!(inferred["callee:T"], optional(Ty::Str));
        assert!(!unify_call_types(
            &variable,
            &optional(Ty::Bool),
            &binders,
            &mut inferred
        ));
        let instance = |key: &str| Ty::Applied {
            constructor: "private:Token".into(),
            arguments: vec![TypeArgument::Static(key.into())],
        };
        inferred.clear();
        assert!(unify_call_types(
            &variable,
            &instance("f64:+0"),
            &binders,
            &mut inferred
        ));
        assert!(!unify_call_types(
            &variable,
            &instance("f64:-0"),
            &binders,
            &mut inferred
        ));

        // Failed later tuple members must not leak earlier inferred choices.
        inferred.clear();
        assert!(!unify_call_types(
            &Ty::Tuple(vec![variable.clone(), Ty::Bool]),
            &Ty::Tuple(vec![Ty::Str, Ty::Int("int".into())]),
            &binders,
            &mut inferred,
        ));
        assert!(inferred.is_empty());
        assert!(unify_call_types(
            &variable,
            &Ty::Unknown,
            &binders,
            &mut inferred
        ));
        assert!(inferred.is_empty());
    }
    #[test]
    fn applied_types_keep_static_arguments_and_unfold_only_structural_aliases() {
        let parsed = ril_syntax::parse(
            "type Token<value: f64>(int)\ntype Positive = Token<0.0>\ntype Negative = Token<-0.0>\ntype Alias<T> = (T, []T)\ntype Concrete = Alias<int>",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        let ty = |name: &str, checker: &mut Checker| {
            let declaration = checker.types[name].clone();
            checker.ty(declaration.value.as_ref().unwrap())
        };
        let positive = ty("Positive", &mut checker);
        let negative = ty("Negative", &mut checker);
        assert!(matches!(positive,Ty::Applied {ref constructor,..} if constructor=="Token"));
        assert_ne!(positive, negative);
        assert!(!checker.compatible(&positive, &negative));
        assert_eq!(checker.expanded(&positive, &mut BTreeSet::new()), positive);
        let concrete = ty("Concrete", &mut checker);
        assert_eq!(
            checker.expanded(&concrete, &mut BTreeSet::new()),
            Ty::Tuple(vec![
                Ty::Int("int".into()),
                Ty::Array(Box::new(Ty::Int("int".into())))
            ])
        );
    }
    #[test]
    fn applied_arguments_keep_dimensions_and_callable_qualifications_in_their_keys() {
        let parsed = ril_syntax::parse(
            "type Token<T>(int)\ntype Two=Token<[2]int>\ntype Three=Token<[3]int>\ntype Reader=Token<fn(int)->int>\ntype Writer=Token<fn(mut int)->int>\ntype Capture=Token<fn(int)->int &capture>",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        let mut instance = |name: &str| {
            let syntax = checker.types[name].value.clone().unwrap();
            checker.ty(&syntax)
        };
        let two = instance("Two");
        let three = instance("Three");
        let reader = instance("Reader");
        let writer = instance("Writer");
        let capture = instance("Capture");
        assert_ne!(two, three);
        assert_ne!(reader, writer);
        assert_ne!(reader, capture);
        for value in [two, three, reader, writer, capture] {
            assert!(
                matches!(value,Ty::Applied{arguments,..} if matches!(arguments.as_slice(),[TypeArgument::CanonicalType{..}]))
            );
        }
        // These closed descriptors now retain all dimensions and modes. They
        // still carry no permission or storage-cardinality proof.
        assert!(checker.unsupported.is_empty(), "{:?}", checker.unsupported);
    }
    #[test]
    fn callable_context_checks_do_not_grant_data_types_or_inspect_captured_results() {
        for source in [
            "fn example(){let number:int=len;let value=number+1}",
            "fn example(){let value:{item:int}=.{item:len}}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let outcome = crate::sema::analyze(&parsed.program, FileId(0));
            assert!(
                outcome
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{:?} {:?}",
                outcome.diagnostics,
                outcome.unsupported
            );
        }
        let parsed =
            ril_syntax::parse("fn ignore(action:fn(bool)->()){}\nfn example(){ignore(len)}");
        let outcome = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(!outcome.unsupported.is_empty(), "{:?}", outcome.diagnostics);
        let parsed = ril_syntax::parse(
            "fn bad(){let result:Result<int,str>=Err(\"lost\");let callback:fn(int)->bool=\\_ -> result is Err(_)}",
        );
        let outcome = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            outcome
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{:?} {:?}",
            outcome.diagnostics,
            outcome.unsupported
        );
        let parsed = ril_syntax::parse(
            "type Option {Item(int)}\nfn own(value:Option)->Option{value}\nfn standard(value:Prelude::Option<int>)->Prelude::Option<int>{value}",
        );
        let outcome = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            outcome.program.is_some(),
            "{:?} {:?}",
            outcome.diagnostics,
            outcome.unsupported
        );
    }
    #[test]
    fn closed_record_shape_mismatches_keep_their_specific_diagnostics() {
        for (source, code) in [
            (
                "type User={id:int,name:str}\nfn example(){let value:User=.{id:1,name:\"Ada\",age:3}}",
                "E0302",
            ),
            (
                "type User={id:int,name:str}\nfn example(){let value:User=.{id:1}}",
                "E0307",
            ),
            (
                "fn take(value:{id:int}){}\nfn example(){take(.{id:1,name:\"Ada\"})}",
                "E0302",
            ),
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let outcome = crate::sema::analyze(&parsed.program, FileId(0));
            assert!(
                outcome
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{source}: {:?} {:?}",
                outcome.diagnostics,
                outcome.unsupported
            );
            assert!(
                !outcome
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "specific record error was accompanied by a general error: {:?}",
                outcome.diagnostics
            );
        }
    }
    #[test]
    fn nongeneric_standard_types_do_not_discard_written_type_arguments() {
        for source in [
            "fn bad(value:int<str>)->int{value}",
            "fn bad(value:Path::Path<int>){}",
            "fn bad(value:Immut<int,str>){}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let result = crate::sema::analyze(&parsed.program, FileId(0));
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0340"),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn stream_operation_records_preserve_callable_modes_rows_and_type_identity() {
        let parsed = ril_syntax::parse(
            "type Reader={mut position:int}\nfn read(mut reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader.position+=1;Ok(.{data:b\"\",end:true})}\nfn write(mut writer:Reader,data:bytes)->Io::WriteProgress&mut{writer.position+=1;.{written:0,error:None}}\nfn example(){let input:Io::ReadOps<Reader>=.{read:read};let output:Io::WriteOps<Reader>=.{write:write}}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        for source in [
            "type Reader={position:int}\nfn read(reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError>{Ok(.{data:b\"\",end:true})}\nfn example(){let input:Io::ReadOps<Reader>=.{read:read}}",
            "type Reader={position:int}\nfn read(reader:Reader,maximum:int)->Result<Io::ReadChunk,Io::IoError>{Ok(.{data:b\"\",end:true})}\nfn example(){let input=Io::ReadOps<Reader>.{read:read}}",
            "fn example(input:Io::ReadOps<int,str>){}",
        ] {
            let parsed = ril_syntax::parse(source);
            assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
            let result = crate::sema::analyze(&parsed.program, FileId(0));
            assert!(
                result.program.is_none(),
                "{:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| matches!(diagnostic.code.as_str(), "E0407" | "E0340")),
                "{:?}",
                result.diagnostics
            );
        }
        let parsed = ril_syntax::parse(
            "fn read(mut reader:[3]int,maximum:int)->Result<Io::ReadChunk,Io::IoError>&mut{reader[0]+=1;Ok(.{data:b\"\",end:true})}\nfn example(){let input=Io::ReadOps<[2]int>.{read:read}}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let parsed = ril_syntax::parse(
            "type Carrier<T>(T)\ntype Reader={mut position:int}\ntype Alias=Carrier<Io::ReadOps<Reader>>\ntype Explicit=Carrier<{read:fn(mut Reader,int)->Result<Io::ReadChunk,Io::IoError>&mut}>\ntype WrongMode=Carrier<{read:fn(Reader,int)->Result<Io::ReadChunk,Io::IoError>&mut}>\ntype WrongRow=Carrier<{read:fn(mut Reader,int)->Result<Io::ReadChunk,Io::IoError>}>\ntype Two=Carrier<Io::ReadOps<[2]int>>\ntype Three=Carrier<Io::ReadOps<[3]int>>",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        let mut instance = |name: &str| {
            let syntax = checker.types[name].value.clone().unwrap();
            checker.ty(&syntax)
        };
        let alias = instance("Alias");
        let explicit = instance("Explicit");
        let mode = instance("WrongMode");
        let row = instance("WrongRow");
        let two = instance("Two");
        let three = instance("Three");
        assert_eq!(alias, explicit);
        assert_ne!(alias, mode);
        assert_ne!(alias, row);
        assert_ne!(two, three);
    }
    #[test]
    fn transparent_record_aliases_share_the_complete_source_normal_form() {
        let parsed = ril_syntax::parse(
            "type Reader={mut position:int}\ntype Alias=Io::ReadOps<Reader>\ntype Explicit={read:fn(mut Reader,int)->Result<Io::ReadChunk,Io::IoError>&mut}\ntype Nested=Alias\ntype Chunk=Io::ReadChunk\ntype ChunkRecord={data:bytes,end:bool}\ntype Handle=File::Handle",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in &parsed.program.statements {
            if let StmtKind::Type(declaration) = &statement.kind {
                checker
                    .types
                    .insert(declaration.name.clone(), declaration.clone());
            }
        }
        let mut witness = |name: &str| {
            let syntax = checker.types[name].value.clone().unwrap();
            checker
                .source_type_from_syntax(&syntax)
                .unwrap_or_else(|| panic!("{name} has no complete source schema"))
        };
        let alias = witness("Alias");
        let explicit = witness("Explicit");
        let nested = witness("Nested");
        assert_eq!(alias.key, explicit.key);
        assert_eq!(alias.key, nested.key);
        assert_eq!(witness("Chunk").key, witness("ChunkRecord").key);
        let TypeKind::Record { fields, row: None } = &alias.syntax.kind else {
            panic!("{:?}", alias.syntax)
        };
        let TypeKind::Callable {
            parameters,
            annotations,
            ..
        } = &fields[0].ty.kind
        else {
            panic!()
        };
        assert_eq!(parameters[0].mode, ParameterMode::Mut);
        assert!(matches!(
            parameters[0].ty.as_ref().unwrap().kind,
            TypeKind::Record { .. }
        ));
        assert!(
            annotations
                .iter()
                .any(|annotation| annotation.text == "&mut")
        );
        let handle = witness("Handle");
        assert!(
            matches!(&handle.syntax.kind, TypeKind::Name { path, arguments } if path == &["File", "Handle"] && arguments.is_empty())
        );
    }

    #[test]
    fn incomplete_source_normalization_never_publishes_a_canonical_key() {
        let checker = Checker::new(FileId(0));
        let mut syntax = TypeExpr {
            hir_id: None,
            kind: TypeKind::Name {
                path: vec!["int".into()],
                arguments: vec![],
            },
            text: String::new(),
            span: Span {
                file: FileId(0),
                start: 0,
                end: 1,
            },
        };
        for _ in 0..130 {
            syntax = TypeExpr {
                hir_id: None,
                kind: TypeKind::Array {
                    length: None,
                    element: Box::new(syntax),
                },
                text: String::new(),
                span: Span {
                    file: FileId(0),
                    start: 0,
                    end: 1,
                },
            };
        }
        assert!(checker.closed_source_syntax(&syntax).is_none());
        assert!(matches!(
            checker.canonical_type_argument(&syntax, Ty::Array(Box::new(Ty::Int("int".into())))),
            TypeArgument::Type(_)
        ));
        let unknown = TypeExpr {
            kind: TypeKind::Name {
                path: vec!["Unresolved".into()],
                arguments: vec![],
            },
            ..syntax
        };
        assert!(checker.closed_source_syntax(&unknown).is_none());
        assert!(matches!(
            checker.canonical_type_argument(&unknown, Ty::Named("Unresolved".into())),
            TypeArgument::Type(_)
        ));
    }
    #[test]
    fn first_class_resource_operations_keep_mut_modes_and_latent_fiber_effects() {
        let parsed = ril_syntax::parse(
            "fn example(){let input:Io::ReadOps<File::Handle>=.{read:File::read_chunk};let output:Io::WriteOps<File::Handle>=.{write:File::write};let wait:fn(mut Process::Child)->Result<Process::ExitStatus,Process::ProcessError>=Process::wait;let terminate:fn(mut Process::Child)->Result<(),Process::ProcessError>=Process::terminate}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let parsed = ril_syntax::parse(
            "fn example(){let read:fn(mut File::Handle,int)->Result<Io::ReadChunk,Io::IoError>@{}&mut=File::read_chunk}",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result.program.is_none(),
            "first-class IO was granted a closed pure effect row"
        );
        assert!(!result.diagnostics.is_empty(), "{:?}", result.unsupported);
        let parsed = ril_syntax::parse(
            "fn example(){let write:fn(File::Handle,bytes)->Io::WriteProgress=File::write}",
        );
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0407"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn result_contexts_solve_only_the_producing_calls_missing_binders() {
        for source in [
            "fn empty<T>()->[]T{[]}\nfn example(){let first:[]int=empty();let second:[]str=empty()}",
            "fn empty<T>()->[]T{[]}\nfn example<T,U>(){let first:[]T=empty();let second:[]U=empty()}",
            "fn empty_pair<T>()->([]T,[]T){([],[])}\nfn example(){let pair:([]int,[]int)=empty_pair()}",
            "fn empty<T>()->[]T{[]}\nfn example(){let pair:([]int,int)=(empty(),1)}",
            "fn empty<T>()->[]T{[]}\nfn example(){let pair:([]int,[]str)=(empty(),empty())}",
            "fn empty<T>()->[]T{[]}\nfn example(){let optional:?[]int=Some(empty());let result:Result<[]str,str>=Ok(empty());assert(result is Ok(_))}",
            "fn empty<T>()->[]T{[]}\nfn identity<T>(values:[]T)->[]T{values}\nfn example(){let values:[]int=identity(empty())}",
            "fn empty<T>()->[]T{let values:[]T=[];values}\nfn example(){let values:[]int=empty()}",
        ] {
            let outcome = crate::session::Session::new(source.as_bytes().to_vec()).verify();
            assert!(outcome.is_ok(), "{source}: {outcome:?}");
        }
        for (source, code) in [
            (
                "fn empty<T>()->[]T{[]}\nfn bad(){let values=empty()}",
                "E0344",
            ),
            (
                "fn empty<T>()->[]T{[]}\nfn bad(){let pair=(empty(),1)}",
                "E0344",
            ),
            (
                "fn empty<T>()->[]T{[]}\nfn ignore<T>(value:[]T){}\nfn bad(){ignore(empty())}",
                "E0344",
            ),
            (
                "fn empty<T>()->[]T{[]}\nfn identity<T>(values:[]T)->[]T{values}\nfn bad(){let mut values:[]int=identity(empty())}",
                "E0528",
            ),
            (
                "fn empty<T>()->[]T{let values:[]T=[];values}\nfn bad(){let mut values:[]int=empty()}",
                "E0528",
            ),
            (
                "fn empty_pair<T>()->([]T,[]T){([],[])}\nfn bad(){let pair:([]int,[]str)=empty_pair()}",
                "E0301",
            ),
            (
                "fn empty_pair<T>()->([]T,[]T){([],[])}\nfn bad<T,U>(){let pair:([]T,[]U)=empty_pair()}",
                "E0301",
            ),
            (
                "fn empty<T>()->[]T{[]}\nfn bad(){let mut values:[]int=empty();values !> Array::push(\"wrong\")}",
                "E0301",
            ),
        ] {
            let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
            let crate::session::CompilationOutcome::Rejected { diagnostics } = outcome else {
                panic!("{source}: {outcome:?}");
            };
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic.code == code),
                "{source}: {diagnostics:?}"
            );
        }
        let source = "fn empty<T>()->[]T{[]}\nfn example(){let first:[]int=empty();let second:[]str=empty()}";
        let verified = crate::session::Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap();
        let selected = &verified.facts().inference_resolutions;
        let integer = selected
            .iter()
            .find(|resolution| resolution.selected == Ty::Int("int".into()))
            .unwrap();
        let string = selected
            .iter()
            .find(|resolution| resolution.selected == Ty::Str)
            .unwrap();
        assert_ne!(
            integer.binder, string.binder,
            "independent invocation inference shared a type variable"
        );
        for resolution in [integer, string] {
            assert!(
                verified
                    .facts()
                    .explanations
                    .chain(resolution.cause)
                    .iter()
                    .any(|cause| cause.id == resolution.origin)
            );
        }
    }
    #[test]
    fn empty_maps_require_a_real_key_context_before_any_key_operation() {
        for source in [
            "fn example(){let mut values:[int:int]=[:];Map::set(mut values,1,2);assert(values[1]==Some(2))}",
            "fn empty()->[str:int]{[:]}\nfn example(){let values=empty();assert(Map::get(values,\"missing\")==None)}",
            "fn read(values:[int:int]){assert(Map::get(values,1)==None)}\nfn example(){read([:])}",
            "fn example(){let record:{values:[int:int]}=.{values:[:]};let values=record.values;assert(Map::get(values,1)==None)}",
        ] {
            let verified = crate::session::Session::new(source.as_bytes().to_vec()).verify();
            assert!(verified.is_ok(), "{source}: {verified:?}");
        }
        for (source, code) in [
            ("fn bad(){let values=[:]}", "E0344"),
            ("fn bad(){let record=.{values:[:]}}", "E0344"),
            ("fn bad(){[:];}", "E0344"),
            ("fn bad(){let values:[f64:int]=[:]}", "E0328"),
            (
                "fn read(values:[int:int]){}\nfn bad<T>(values:[T:int]){read(values)}",
                "E0301",
            ),
        ] {
            let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
            let crate::session::CompilationOutcome::Rejected { diagnostics } = outcome else {
                panic!("{source}: {outcome:?}");
            };
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic.code == code),
                "{source}: {diagnostics:?}"
            );
        }
    }
}
