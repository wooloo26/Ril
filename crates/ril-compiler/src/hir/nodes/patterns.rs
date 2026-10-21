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
                });
            }
            PatternKind::Mode { pattern, .. } => {
                self.visit(*pattern, path, known, out, depth + 1)?;
            }
            PatternKind::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    charge(self.work, 1)?;
                    path.push(TypeProjection::Tuple(
                        u32::try_from(index).map_err(|_| LowerError::IdentitySpace)?,
                    ));
                    self.visit(*item, path, known, out, depth + 1)?;
                    path.pop();
                }
            }
            PatternKind::Record {
                fields,
                rest_binding,
                ..
            } => {
                for field in fields {
                    charge(self.work, 1 + field.name.len().div_ceil(32))?;
                    path.push(TypeProjection::Field(field.name.clone()));
                    self.visit(field.pattern, path, known, out, depth + 1)?;
                    path.pop();
                }
                if let Some(name) = rest_binding {
                    charge(self.work, 1 + fields.len())?;
                    let mut excluded = BTreeSet::new();
                    for field in fields {
                        charge(self.work, field.name.len().div_ceil(32))?;
                        excluded.insert(field.name.clone());
                    }
                    path.push(TypeProjection::RecordRemainder(excluded));
                    let projection = known.then(|| copy_path(path, self.work)).transpose()?;
                    charge(self.work, 1 + name.len().div_ceil(32))?;
                    out.push(PatternBinding {
                        pattern: id,
                        name: name.clone(),
                        projection,
                    });
                    path.pop();
                }
            }
            PatternKind::Constructor { arguments, .. } => {
                for argument in arguments {
                    self.visit(*argument, path, false, out, depth + 1)?;
                }
            }
            PatternKind::Alternative(alternatives) => {
                let mut common: Option<BTreeMap<String, PatternBinding>> = None;
                for alternative in alternatives {
                    let mut bindings = Vec::new();
                    self.visit(*alternative, path, known, &mut bindings, depth + 1)?;
                    charge(self.work, bindings.len())?;
                    let mut branch = BTreeMap::new();
                    for binding in bindings {
                        charge(self.work, binding.name.len().div_ceil(32))?;
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
        .visit(root, &mut Vec::new(), true, &mut out, 0)?;
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
