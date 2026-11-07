//! Finite, syntax-owned access binders. Named references do not expand schemas.
use super::{DefId, Index, ScopeId};
use crate::{
    ast::{
        MemberAccess, MemberMode, Parameter, ParameterMode, StorageModeKind, TypeExpr, TypeKind,
    },
    source::Span,
};

/// An index in `Hir::mode_parameters`, independent of source spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModeParameterId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModeOwner {
    Definition(DefId),
    CallableType(ScopeId),
    Closure(ScopeId),
    Module(ScopeId),
}

/// Coordinates describe a written occurrence, rather than an instantiated graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModeCoordinate {
    Input(usize),
    Schema(Span),
    Field(String),
    Position(usize),
    Element,
    Key,
    Value,
    Argument(usize),
    Alternative(usize),
    Optional,
    Rest,
    Row,
    Base,
}

#[derive(Debug)]
pub struct ModeParameter {
    pub owner: ModeOwner,
    pub coordinate: Vec<ModeCoordinate>,
    /// `via` binds access; the declared slot component is already fixed.
    pub replaceable: bool,
    pub span: Span,
}

impl Index {
    fn mode_owner(&self, mut scope: ScopeId) -> ModeOwner {
        loop {
            let current = &self.hir.scopes[scope.0];
            if let Some(owner) = current.mode_owner {
                return owner;
            }
            let Some(parent) = current.parent else {
                return ModeOwner::Module(scope);
            };
            scope = parent;
        }
    }

    pub(super) fn parameter_mode_binder(
        &mut self,
        scope: ScopeId,
        index: usize,
        parameter: &Parameter,
    ) {
        if parameter.mode == ParameterMode::Via {
            self.hir.mode_parameters.push(ModeParameter {
                owner: self.mode_owner(scope),
                coordinate: vec![ModeCoordinate::Input(index)],
                replaceable: false,
                span: parameter.mode_span.unwrap_or(parameter.span),
            });
        }
    }

    pub(super) fn schema_mode_binders(&mut self, scope: ScopeId, ty: &TypeExpr) {
        let mut coordinate = vec![ModeCoordinate::Schema(ty.span)];
        self.schema_modes(self.mode_owner(scope), ty, &mut coordinate);
    }

    fn member_mode_binder(
        &mut self,
        owner: ModeOwner,
        coordinate: &[ModeCoordinate],
        mode: Option<MemberMode>,
    ) {
        if let Some(mode) = mode
            && mode.access == MemberAccess::Via
        {
            self.hir.mode_parameters.push(ModeParameter {
                owner,
                coordinate: coordinate.to_owned(),
                replaceable: mode.replaceable,
                span: mode.span,
            });
        }
    }

    fn schema_child(
        &mut self,
        owner: ModeOwner,
        ty: &TypeExpr,
        coordinate: &mut Vec<ModeCoordinate>,
        step: ModeCoordinate,
    ) {
        coordinate.push(step);
        self.schema_modes(owner, ty, coordinate);
        coordinate.pop();
    }

    fn schema_modes(
        &mut self,
        owner: ModeOwner,
        ty: &TypeExpr,
        coordinate: &mut Vec<ModeCoordinate>,
    ) {
        // HIR also visits children for lexical resolution. Record each syntax
        // node once, retaining the first, complete coordinate from its root.
        if !self.indexed_schema_sites.insert(ty.span) {
            return;
        }
        use ModeCoordinate as C;
        match &ty.kind {
            TypeKind::Name { arguments, .. } => {
                for (index, argument) in arguments.iter().enumerate() {
                    self.schema_child(owner, argument, coordinate, C::Argument(index));
                }
            }
            TypeKind::Member { mode, ty } => {
                self.member_mode_binder(owner, coordinate, Some(*mode));
                self.schema_modes(owner, ty, coordinate);
            }
            TypeKind::Optional(ty) => self.schema_child(owner, ty, coordinate, C::Optional),
            TypeKind::Rest(ty) => self.schema_child(owner, ty, coordinate, C::Rest),
            TypeKind::Array { access, element }
            | TypeKind::Map {
                access,
                value: element,
                ..
            } => {
                if let TypeKind::Map { key, .. } = &ty.kind {
                    self.schema_child(owner, key, coordinate, C::Key);
                }
                coordinate.push(if matches!(ty.kind, TypeKind::Array { .. }) {
                    C::Element
                } else {
                    C::Value
                });
                if let Some(mode) = access
                    && mode.kind == StorageModeKind::Via
                {
                    self.hir.mode_parameters.push(ModeParameter {
                        owner,
                        coordinate: coordinate.clone(),
                        replaceable: false,
                        span: mode.span,
                    });
                }
                self.schema_modes(owner, element, coordinate);
                coordinate.pop();
            }
            TypeKind::ArrayPattern { element, .. } => {
                self.schema_child(owner, element, coordinate, C::Element);
            }
            TypeKind::Tuple(types) | TypeKind::Alternatives(types) => {
                for (index, child) in types.iter().enumerate() {
                    let step = if matches!(ty.kind, TypeKind::Tuple(_)) {
                        C::Position(index)
                    } else {
                        C::Alternative(index)
                    };
                    self.schema_child(owner, child, coordinate, step);
                }
            }
            TypeKind::VariantPayload(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    coordinate.push(C::Position(index));
                    self.member_mode_binder(owner, coordinate, field.mode);
                    self.schema_modes(owner, &field.ty, coordinate);
                    coordinate.pop();
                }
            }
            TypeKind::Record { fields, row } => {
                for field in fields {
                    coordinate.push(C::Field(field.name.clone()));
                    self.member_mode_binder(owner, coordinate, field.mode);
                    self.schema_modes(owner, &field.ty, coordinate);
                    coordinate.pop();
                }
                if let Some(row) = row {
                    self.schema_child(owner, row, coordinate, C::Row);
                }
            }
            TypeKind::Projection { base, .. }
            | TypeKind::ComputedProjection { base, .. }
            | TypeKind::KeyOf(base) => self.schema_child(owner, base, coordinate, C::Base),
            TypeKind::Mapped { value, .. } => {
                self.schema_child(owner, value, coordinate, C::Value);
            }
            TypeKind::KindArrow { parameter, result } => {
                self.schema_child(owner, parameter, coordinate, C::Input(0));
                self.schema_child(owner, result, coordinate, C::Value);
            }
            // Callable inputs belong to their own scope. Static bodies and
            // expressions are indexed when HIR visits their contained syntax.
            TypeKind::Callable { .. }
            | TypeKind::TypeFunction { .. }
            | TypeKind::Computation(_)
            | TypeKind::PatternMode { .. }
            | TypeKind::OpenRow
            | TypeKind::PatternRest(_)
            | TypeKind::TypeBinder(_)
            | TypeKind::ModeLiteral(_)
            | TypeKind::QualifiedMemberMode
            | TypeKind::Error => {}
        }
    }
}
