//! Binding identities and type projections come from original HIR edges.
//! This temporary plan is shared by elaboration and independent replay; it
//! contains no heap contents, source spans or producer validation flags.
use super::*;
use ril_compiler_core::projection::TypeProjection;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct PatternBinding {
    pub pattern: PatternId,
    pub name: String,
    /// None preserves an unresolved projection, for example a constructor
    /// without its independently resolved declaration and payload layout.
    pub projection: Option<Vec<TypeProjection>>,
    /// Value selection is separate from type selection: every array element
    /// has the same type projection but a distinct position in the subject.
    pub selection: Option<Vec<PatternValueProjection>>,
    /// Each alternative retains its own original introducer and projections.
    /// A common lexical binder cannot borrow the first alternative's origin.
    pub alternatives: Vec<PatternBindingAlternative>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternValueProjection {
    Tuple(u32),
    TupleFromEnd(u32),
    Field(String),
    ArrayFront(u32),
    ArrayBack(u32),
    ArrayRemainder { prefix: u32, suffix: u32 },
    RecordRemainder(BTreeSet<String>),
    Constructor(PatternId),
}

#[derive(Debug, Clone)]
pub struct PatternBindingAlternative {
    pub pattern: PatternId,
    pub projection: Option<Vec<TypeProjection>>,
    pub selection: Option<Vec<PatternValueProjection>>,
}

fn charge(work: &mut usize, units: usize) -> Result<(), LowerError> {
    *work = work
        .checked_sub(units)
        .ok_or(LowerError::Budget("pattern projections"))?;
    Ok(())
}

fn copy_path(path: &[TypeProjection], work: &mut usize) -> Result<Vec<TypeProjection>, LowerError> {
    charge(work, 1 + path.len())?;
    for step in path {
        match step {
            TypeProjection::Field(name) => charge(work, name.len().div_ceil(32))?,
            TypeProjection::RecordRemainder(fields) => {
                charge(work, fields.len())?;
                for name in fields {
                    charge(work, name.len().div_ceil(32))?;
                }
            }
            _ => {}
        }
    }
    Ok(path.to_vec())
}

fn copy_selection(
    path: &[PatternValueProjection],
    work: &mut usize,
) -> Result<Vec<PatternValueProjection>, LowerError> {
    charge(work, 1 + path.len())?;
    for step in path {
        match step {
            PatternValueProjection::Field(name) => charge(work, name.len().div_ceil(32))?,
            PatternValueProjection::RecordRemainder(fields) => {
                charge(work, fields.len())?;
                for name in fields {
                    charge(work, name.len().div_ceil(32))?;
                }
            }
            _ => {}
        }
    }
    Ok(path.to_vec())
}

struct Plan<'a, 'w> {
    hir: &'a HirProgram,
    work: &'w mut usize,
    visited: BTreeSet<PatternId>,
}

impl<'a> Plan<'a, '_> {
    fn visit(
        &mut self,
        id: PatternId,
        path: &mut Vec<TypeProjection>,
        selection: &mut Vec<PatternValueProjection>,
        known: bool,
        out: &mut Vec<PatternBinding>,
        depth: usize,
    ) -> Result<(), LowerError> {
        charge(self.work, 1)?;
        if depth >= 128 {
            return Err(LowerError::Budget("pattern projection depth"));
        }
        if !self.visited.insert(id) {
            return Err(LowerError::Correspondence);
        }
        let pattern = self.hir.pattern(id).ok_or(LowerError::Correspondence)?;
        match &pattern.kind {
            PatternKind::Name(name) => {
                let projection = known.then(|| copy_path(path, self.work)).transpose()?;
                charge(self.work, 1 + name.len().div_ceil(32))?;
                out.push(PatternBinding {
                    pattern: id,
                    name: name.clone(),
                    projection,
                    selection: Some(copy_selection(selection, self.work)?),
                    alternatives: Vec::new(),
                });
            }
            PatternKind::Mode { pattern, .. } => {
                self.visit(*pattern, path, selection, known, out, depth + 1)?;
            }
            PatternKind::Tuple(items) => {
                let rest = items.iter().position(|id| {
                    matches!(
                        self.hir.pattern(*id).map(|p| &p.kind),
                        Some(PatternKind::Rest(_))
                    )
                });
                for (index, item) in items.iter().enumerate() {
                    charge(self.work, 1)?;
                    if Some(index) == rest {
                        continue;
                    }
                    let from_end = rest.is_some_and(|rest| index > rest);
                    let coordinate = u32::try_from(if from_end {
                        items.len() - index - 1
                    } else {
                        index
                    })
                    .map_err(|_| LowerError::IdentitySpace)?;
                    path.push(if from_end {
                        TypeProjection::TupleFromEnd(coordinate)
                    } else {
                        TypeProjection::Tuple(coordinate)
                    });
                    selection.push(if from_end {
                        PatternValueProjection::TupleFromEnd(coordinate)
                    } else {
                        PatternValueProjection::Tuple(coordinate)
                    });
                    self.visit(*item, path, selection, known, out, depth + 1)?;
                    path.pop();
                    selection.pop();
                }
            }
            PatternKind::Array(items) => {
                let rest = items.iter().position(|id| {
                    matches!(
                        self.hir.pattern(*id).map(|p| &p.kind),
                        Some(PatternKind::Rest(_))
                    )
                });
                for (index, item) in items.iter().enumerate() {
                    charge(self.work, 1)?;
                    if Some(index) == rest {
                        let prefix = u32::try_from(index).map_err(|_| LowerError::IdentitySpace)?;
                        let suffix = u32::try_from(items.len() - index - 1)
                            .map_err(|_| LowerError::IdentitySpace)?;
                        path.push(TypeProjection::ArrayRemainder { prefix, suffix });
                        selection.push(PatternValueProjection::ArrayRemainder { prefix, suffix });
                    } else {
                        path.push(TypeProjection::Element);
                        selection.push(if rest.is_some_and(|rest| index > rest) {
                            PatternValueProjection::ArrayBack(
                                u32::try_from(items.len() - index - 1)
                                    .map_err(|_| LowerError::IdentitySpace)?,
                            )
                        } else {
                            PatternValueProjection::ArrayFront(
                                u32::try_from(index).map_err(|_| LowerError::IdentitySpace)?,
                            )
                        });
                    }
                    self.visit(*item, path, selection, known, out, depth + 1)?;
                    path.pop();
                    selection.pop();
                }
            }
            PatternKind::Rest(Some(name)) if name != "_" => {
                let projection = known.then(|| copy_path(path, self.work)).transpose()?;
                charge(self.work, 1 + name.len().div_ceil(32) + selection.len())?;
                out.push(PatternBinding {
                    pattern: id,
                    name: name.clone(),
                    projection,
                    selection: Some(copy_selection(selection, self.work)?),
                    alternatives: Vec::new(),
                });
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    charge(self.work, 1 + field.name.len().div_ceil(32))?;
                    path.push(TypeProjection::Field(field.name.clone()));
                    selection.push(PatternValueProjection::Field(field.name.clone()));
                    self.visit(field.pattern, path, selection, known, out, depth + 1)?;
                    path.pop();
                    selection.pop();
                }
                if let Some(name) = rest_binding {
                    charge(self.work, 1 + fields.len())?;
                    let mut excluded = BTreeSet::new();
                    for field in fields {
                        charge(self.work, field.name.len().div_ceil(32))?;
                        excluded.insert(field.name.clone());
                    }
                    path.push(TypeProjection::RecordRemainder(excluded.clone()));
                    selection.push(PatternValueProjection::RecordRemainder(excluded));
                    let projection = known.then(|| copy_path(path, self.work)).transpose()?;
                    charge(self.work, 1 + name.len().div_ceil(32))?;
                    out.push(PatternBinding {
                        pattern: id,
                        name: name.clone(),
                        projection,
                        selection: Some(copy_selection(selection, self.work)?),
                        alternatives: Vec::new(),
                    });
                    path.pop();
                    selection.pop();
                }
            }
            PatternKind::Constructor { arguments, .. } => {
                selection.push(PatternValueProjection::Constructor(id));
                for (index, argument) in arguments.iter().enumerate() {
                    if arguments.len() > 1 {
                        selection.push(PatternValueProjection::Tuple(
                            u32::try_from(index).map_err(|_| LowerError::IdentitySpace)?,
                        ));
                    }
                    self.visit(*argument, path, selection, false, out, depth + 1)?;
                    if arguments.len() > 1 {
                        selection.pop();
                    }
                }
                selection.pop();
            }
            PatternKind::Alternative(alternatives) => {
                let mut common: Option<BTreeMap<String, PatternBinding>> = None;
                for alternative in alternatives {
                    let mut bindings = Vec::new();
                    self.visit(
                        *alternative,
                        path,
                        selection,
                        known,
                        &mut bindings,
                        depth + 1,
                    )?;
                    charge(self.work, bindings.len())?;
                    let mut branch = BTreeMap::new();
                    for mut binding in bindings {
                        charge(self.work, binding.name.len().div_ceil(32))?;
                        if binding.alternatives.is_empty() {
                            charge(
                                self.work,
                                1 + binding.projection.as_ref().map_or(0, Vec::len)
                                    + binding.selection.as_ref().map_or(0, Vec::len),
                            )?;
                            binding.alternatives.push(PatternBindingAlternative {
                                pattern: binding.pattern,
                                projection: binding
                                    .projection
                                    .as_deref()
                                    .map(|path| copy_path(path, self.work))
                                    .transpose()?,
                                selection: binding
                                    .selection
                                    .as_deref()
                                    .map(|path| copy_selection(path, self.work))
                                    .transpose()?,
                            });
                        }
                        if branch.insert(binding.name.clone(), binding).is_some() {
                            return Err(LowerError::Correspondence);
                        }
                    }
                    if let Some(common) = &mut common {
                        charge(self.work, common.len())?;
                        if !common.keys().eq(branch.keys()) {
                            return Err(LowerError::Correspondence);
                        }
                        for (name, binding) in common {
                            if binding.projection != branch[name].projection {
                                binding.projection = None;
                            }
                            if binding.selection != branch[name].selection {
                                binding.selection = None;
                            }
                            charge(self.work, branch[name].alternatives.len())?;
                            for alternative in &branch[name].alternatives {
                                binding.alternatives.push(PatternBindingAlternative {
                                    pattern: alternative.pattern,
                                    projection: alternative
                                        .projection
                                        .as_deref()
                                        .map(|path| copy_path(path, self.work))
                                        .transpose()?,
                                    selection: alternative
                                        .selection
                                        .as_deref()
                                        .map(|path| copy_selection(path, self.work))
                                        .transpose()?,
                                });
                            }
                        }
                    } else {
                        common = Some(branch);
                    }
                }
                for mut binding in common.into_iter().flat_map(BTreeMap::into_values) {
                    // One lexical name is introduced by the whole alternative,
                    // rather than borrowing one branch's particular leaf.
                    binding.pattern = id;
                    charge(self.work, 1)?;
                    out.push(binding);
                }
            }
            PatternKind::Type {
                binder: Some(name), ..
            } => {
                charge(self.work, 1 + name.len().div_ceil(32))?;
                out.push(PatternBinding {
                    pattern: id,
                    name: name.clone(),
                    projection: None,
                    selection: None,
                    alternatives: Vec::new(),
                });
            }
            _ => {}
        }
        Ok(())
    }
}

impl HirProgram {
    pub fn pattern_bindings(
        &self,
        root: PatternId,
        work: &mut usize,
    ) -> Result<Vec<PatternBinding>, LowerError> {
        let mut out = Vec::new();
        Plan {
            hir: self,
            work,
            visited: BTreeSet::new(),
        }
        .visit(root, &mut Vec::new(), &mut Vec::new(), true, &mut out, 0)?;
        let mut names = BTreeSet::new();
        for binding in &out {
            charge(work, 1 + binding.name.len().div_ceil(32))?;
            if !names.insert(binding.name.as_str()) {
                return Err(LowerError::Correspondence);
            }
        }
        Ok(out)
    }
}
