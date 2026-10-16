//! Conditional GADT payload schemas belong to a tested value. They are never
//! registered as constructor callables or ambient generic substitutions.
use super::*;

struct Conditional {
    info: ConstructorInfo,
    equations: BTreeMap<String, Ty>,
}
enum Match {
    Compatible(Box<Conditional>),
    Excluded,
    Unresolved,
}
fn closed_shape(ty: &Ty) -> bool {
    fn visit(ty: &Ty, depth: usize) -> bool {
        if depth >= 128 {
            return false;
        }
        match ty {
            Ty::Unit | Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Str | Ty::Bytes => true,
            Ty::Immutable(inner) | Ty::Optional(inner) => visit(inner, depth + 1),
            Ty::Result(ok, error) => visit(ok, depth + 1) && visit(error, depth + 1),
            Ty::Tuple(items) => items.iter().all(|item| visit(item, depth + 1)),
            Ty::Record(fields) => fields.values().all(|(_, ty)| visit(ty, depth + 1)),
            // Bare Ty does not certify array dimensions, callable rows, an
            // opaque representation or any unknown member of a row.
            _ => false,
        }
    }
    visit(ty, 0)
}
fn argument_type(argument: &TypeArgument) -> Option<&Ty> {
    match argument {
        TypeArgument::Type(ty) | TypeArgument::CanonicalType { ty, .. } => Some(ty),
        _ => None,
    }
}
fn insert_equation(map: &mut BTreeMap<String, Ty>, identity: &str, ty: &Ty) -> bool {
    if let Some(previous) = map.get(identity) {
        previous == ty
    } else {
        map.insert(identity.into(), ty.clone());
        true
    }
}
fn substitute(ty: &Ty, substitutions: &BTreeMap<String, Ty>) -> Option<Ty> {
    Some(match ty {
        Ty::Generic(identity) => substitutions.get(identity)?.clone(),
        Ty::Unit | Ty::Bool | Ty::Int(_) | Ty::Float(_) | Ty::Str | Ty::Bytes | Ty::Never => {
            ty.clone()
        }
        Ty::Immutable(inner) => Ty::Immutable(Box::new(substitute(inner, substitutions)?)),
        Ty::Optional(inner) => Ty::Optional(Box::new(substitute(inner, substitutions)?)),
        Ty::Result(ok, error) => Ty::Result(
            Box::new(substitute(ok, substitutions)?),
            Box::new(substitute(error, substitutions)?),
        ),
        Ty::Tuple(items) => Ty::Tuple(
            items
                .iter()
                .map(|ty| substitute(ty, substitutions))
                .collect::<Option<_>>()?,
        ),
        Ty::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|(name, (mutable, ty))| {
                    Some((name.clone(), (*mutable, substitute(ty, substitutions)?)))
                })
                .collect::<Option<_>>()?,
        ),
        // Array lengths and callable rows are not represented by bare Ty.
        // A conditional schema must not silently discard those identities.
        Ty::Array(_)
        | Ty::Callable(..)
        | Ty::Map(..)
        | Ty::Set(_)
        | Ty::Range(_)
        | Ty::Named(_)
        | Ty::Applied { .. }
        | Ty::Projection { .. }
        | Ty::StaticKey(_)
        | Ty::Unknown => return None,
        Ty::OpenRecord { .. } | Ty::NumericHole(_) => return None,
    })
}
fn conditional(template: &ConstructorInfo, owner: &Ty) -> Match {
    let (
        Ty::Applied {
            constructor: family,
            arguments: actual,
        },
        Ty::Applied {
            constructor: declared,
            arguments: expected,
        },
    ) = (owner, &template.owner)
    else {
        return Match::Unresolved;
    };
    if family != declared || actual.len() != expected.len() {
        return Match::Excluded;
    }
    let mut substitutions = BTreeMap::new();
    let mut equations = BTreeMap::new();
    for (actual, expected) in actual.iter().zip(expected) {
        let (Some(actual), Some(expected)) = (argument_type(actual), argument_type(expected))
        else {
            return Match::Unresolved;
        };
        match (actual, expected) {
            (actual, Ty::Generic(identity))
                if closed_shape(actual) || matches!(actual, Ty::Generic(_)) =>
            {
                if !insert_equation(&mut substitutions, identity, actual) {
                    return Match::Excluded;
                }
            }
            (Ty::Generic(identity), expected) if closed_shape(expected) => {
                if !insert_equation(&mut equations, identity, expected) {
                    return Match::Excluded;
                }
            }
            (actual, expected) if closed_shape(actual) && closed_shape(expected) => {
                if actual != expected {
                    return Match::Excluded;
                }
            }
            _ => return Match::Unresolved,
        }
    }
    let Some(payload) = substitute(&template.payload, &substitutions) else {
        return Match::Unresolved;
    };
    let mut info = template.clone();
    info.owner = owner.clone();
    info.payload = payload;
    // The declaration syntax remains on the original callable metadata. This
    // conditional representation is used only for an already typed subject.
    info.payload_syntax = None;
    Match::Compatible(Box::new(Conditional { info, equations }))
}

impl Checker {
    /// A tested constructor supplies an equation only inside this arm. The
    /// original target must name the very same declaration-owned Type binder.
    /// Neither a semantic Generic nor an ambient expected type mints one.
    pub(in crate::sema::checker) fn constructor_arm_source_target(
        &self,
        source: &Value,
        tag: &str,
        target: &crate::sema::source_reception::Target,
    ) -> Option<crate::sema::source_reception::Target> {
        use crate::sema::{effect_identity::ArgumentKey, effect_identity::StaticBinderSort};
        let owner = self.expanded(&source.ty, &mut BTreeSet::new());
        let Match::Compatible(conditional) = self.conditional_constructor(tag, &owner) else {
            return None;
        };
        let ArgumentKey::Binder {
            identity,
            sort: StaticBinderSort::Type,
        } = target.key.as_ref()?
        else {
            return None;
        };
        let binder = self.generic_binders.get(identity)?;
        let declaration = self
            .functions
            .iter()
            .find(|function| function.definition == binder.definition)?;
        if !crate::sema::record_bounds::certifies_type_sort(
            identity,
            binder,
            declaration.syntax.generics.get(binder.index as usize)?,
            &self.record_bounds,
        ) {
            return None;
        }
        let selected = conditional.equations.get(identity)?;
        if !closed_shape(selected) {
            return None;
        }
        // closed_shape deliberately excludes all arrays, callables, nominal
        // applications and unknown rows; data_type cannot erase coordinates.
        let syntax = io_types::data_type(selected, target.span)?;
        let key = crate::static_eval::effects::bounded_argument_key(&syntax, &BTreeMap::new())?;
        crate::sema::source_reception::complete(&key, &mut 4096)?;
        Some(crate::sema::source_reception::Target {
            span: target.span,
            key: Some(key),
            syntax: Some(std::sync::Arc::new(syntax)),
            empty_array_context: None,
            sensitivity: crate::sema::source_reception::SchemaSensitivity::NotRequired,
        })
    }

    fn conditional_constructor(&self, name: &str, owner: &Ty) -> Match {
        let Ty::Applied {
            constructor: family,
            ..
        } = owner
        else {
            return Match::Unresolved;
        };
        let Some(declaration) = self.types.get(family) else {
            return Match::Unresolved;
        };
        if !self.generic_constructor_contract(declaration) {
            return Match::Unresolved;
        }
        let Some(template) = self.constructors.iter().find_map(|(identity, info)| {
            (identity == &info.tag && (identity == name || info.tag == name)).then_some(info)
        }) else {
            return Match::Unresolved;
        };
        if declaration.variants.iter().find(|variant|format!("{family}::{}",variant.name)==template.tag)
            .is_some_and(|variant|variant.generics.iter().any(|parameter|parameter.bound.as_ref().is_some_and(|bound| {
                !matches!(&bound.kind,TypeKind::Name {path,arguments} if path==&["Type"]&&arguments.is_empty())
            })))
        {return Match::Unresolved;}
        let mut template = template.clone();
        // Transparent aliases can expose a complete finite product. Keep
        // nominal/opaque identities and reject every remaining lossy shape in
        // `closed_shape`/`substitute`; this changes types, never value authority.
        template.owner = self.call_inference_type(&template.owner);
        template.payload = self.call_inference_type(&template.payload);
        conditional(&template, owner)
    }
    pub(in crate::sema::checker) fn conditional_constructor_info(
        &self,
        name: &str,
        owner: &Ty,
    ) -> Option<ConstructorInfo> {
        let mut names = BTreeSet::new();
        owner.generic_names(&mut names);
        if names.is_empty() {
            return None;
        }
        match self.conditional_constructor(name, owner) {
            Match::Compatible(value) => Some(value.info),
            _ => None,
        }
    }
    pub(in crate::sema::checker) fn conditional_constructor_schemas(
        &self,
        owner: &Ty,
    ) -> Option<Vec<(String, ConstructorInfo)>> {
        let Ty::Applied {
            constructor: family,
            ..
        } = owner
        else {
            return None;
        };
        let declaration = self.types.get(family)?;
        if declaration.variants.is_empty() || !self.generic_constructor_contract(declaration) {
            return None;
        }
        let mut names = BTreeSet::new();
        owner.generic_names(&mut names);
        if names.is_empty() {
            return None;
        }
        let mut schemas = vec![];
        for variant in &declaration.variants {
            let tag = format!("{family}::{}", variant.name);
            match self.conditional_constructor(&tag, owner) {
                Match::Compatible(value) => schemas.push((tag, value.info)),
                Match::Excluded => {}
                Match::Unresolved => return None,
            }
        }
        Some(schemas)
    }
    pub(in crate::sema::checker) fn constructor_possible_tags(
        &self,
        ty: &Ty,
    ) -> Option<BTreeSet<String>> {
        let owner = self.expanded(ty, &mut BTreeSet::new());
        if let Some(schemas) = self.conditional_constructor_schemas(&owner) {
            return Some(schemas.into_iter().map(|(_, info)| info.tag).collect());
        }
        let tags: BTreeSet<_> = self
            .constructors
            .values()
            .filter(|info| info.owner == owner && !info.nominal)
            .map(|info| info.tag.clone())
            .collect();
        (!tags.is_empty()).then_some(tags)
    }
    pub(in crate::sema::checker) fn constructor_pattern_unresolved(
        &self,
        name: &str,
        source: &Value,
    ) -> bool {
        let owner = self.expanded(&source.ty, &mut BTreeSet::new());
        let mut names = BTreeSet::new();
        owner.generic_names(&mut names);
        if names.is_empty() {
            return false;
        }
        let Ty::Applied {
            constructor: family,
            ..
        } = &owner
        else {
            return false;
        };
        self.types.get(family).is_some_and(|declaration| {
            declaration
                .variants
                .iter()
                .any(|variant| format!("{family}::{}", variant.name) == name)
        }) && matches!(
            self.conditional_constructor(name, &owner),
            Match::Unresolved
        )
    }
    /// Transport only the result of this tested arm. Existing values typed T,
    /// other bindings and the ambient generic context remain rigid.
    pub(in crate::sema::checker) fn transport_constructor_arm_result(
        &mut self,
        source: &Value,
        tag: &str,
        value: &mut Value,
        expected: Option<&Ty>,
    ) {
        let owner = self.expanded(&source.ty, &mut BTreeSet::new());
        let Match::Compatible(conditional) = self.conditional_constructor(tag, &owner) else {
            return;
        };
        if conditional.equations.is_empty() {
            return;
        }
        if let Some(expected) = expected {
            let mut names = BTreeSet::new();
            expected.generic_names(&mut names);
            if names
                .iter()
                .any(|identity| conditional.equations.contains_key(identity))
                && substitute(expected, &conditional.equations).as_ref() == Some(&value.ty)
            {
                value.ty = expected.clone();
                value.cause=self.cause(CauseKind::Projection,conditional.info.span,
                    "constructor result equation transports this arm result to its original type parameter",
                    [source.cause,value.cause]);
            }
            // An explicit concrete result context keeps its ordinary type.
            // It must not become T merely because this arm also proves T=int.
            return;
        }
        let matches: Vec<_> = conditional
            .equations
            .iter()
            .filter(|(_, actual)| **actual == value.ty)
            .collect();
        if matches.len() == 1 {
            value.ty = Ty::Generic(matches[0].0.clone());
            value.cause = self.cause(
                CauseKind::Projection,
                conditional.info.span,
                "constructor result equation proves the inferred arm result type",
                [source.cause, value.cause],
            );
        }
    }
}
