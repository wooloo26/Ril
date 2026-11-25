use super::*;

pub(in crate::access) struct AccessConflict {
    pub capture: Option<CaptureEntry>,
    pub kind: ConflictKind,
}

pub(in crate::access) enum ConflictKind {
    Direct { writable: bool },
    Via(Box<ViaConflict>),
}

pub(in crate::access) type ForwardedMode = ModeExpression<Region>;

#[derive(Clone, Copy)]
enum Overlap {
    Region,
    Entry,
    Capture {
        formal_on_left: bool,
        capture: CaptureEntry,
    },
}

impl Overlap {
    fn potential(left: &Origin, right: &Origin) -> Option<Self> {
        if left.region.overlaps(&right.region) {
            return Some(Self::Region);
        }
        if let Some((a, b)) = left.entry_graph.as_ref().zip(right.entry_graph.as_ref())
            && a.callable == b.callable
            && if left.region.source == right.region.source {
                left.has_shared_boundary() || right.has_shared_boundary()
            } else {
                left.has_shared_boundary() && right.has_shared_boundary()
            }
        {
            return Some(Self::Entry);
        }
        for (formal_on_left, formal, captured) in [(true, left, right), (false, right, left)] {
            if let Some((entry, capture)) = formal.entry_graph.as_ref().zip(captured.capture)
                && entry.callable == capture.callable
                && formal.has_shared_boundary()
                && capture.shared
            {
                return Some(Self::Capture {
                    formal_on_left,
                    capture,
                });
            }
        }
        None
    }

    fn depends_on_modes(self, left: &Origin, right: &Origin) -> bool {
        let varies = |origin: &Origin| {
            origin
                .entry_graph
                .as_ref()
                .is_some_and(|entry| !entry.via_at.is_empty())
        };
        match self {
            Self::Region => false,
            Self::Entry => varies(left) || varies(right),
            Self::Capture { formal_on_left, .. } => {
                varies(if formal_on_left { left } else { right })
            }
        }
    }

    fn occurs(
        self,
        left: &Origin,
        right: &Origin,
        input: &impl Fn(&Region) -> Option<Input>,
    ) -> bool {
        match self {
            Self::Region => true,
            Self::Entry => {
                let a = left.shared_boundary(input);
                let b = right.shared_boundary(input);
                // Distinct shared boundaries can refer to the same entry object.
                if left.region.source == right.region.source {
                    a != b
                } else {
                    a.is_some() && b.is_some()
                }
            }
            Self::Capture { formal_on_left, .. } => (if formal_on_left { left } else { right })
                .shared_boundary(input)
                .is_some(),
        }
    }

    fn capture(self) -> Option<CaptureEntry> {
        match self {
            Self::Capture { capture, .. } => Some(capture),
            _ => None,
        }
    }
}

pub(in crate::access) struct ViaConflict {
    overlap: Overlap,
    left: (Origin, Mode, Option<ForwardedMode>),
    right: (Origin, Mode, Option<ForwardedMode>),
}

impl ViaConflict {
    pub(in crate::access) fn support_regions(&self) -> Vec<Region> {
        let mut regions = Vec::new();
        for (origin, _, recipe) in [&self.left, &self.right] {
            if let Some(entry) = &origin.entry_graph {
                regions.extend(entry.via_at.iter().cloned());
            }
            if let Some(recipe) = recipe {
                regions.extend(recipe.axes().cloned());
            }
        }
        regions
    }

    pub(in crate::access) fn mode_owner(&self) -> Option<Span> {
        let (left, _, lrecipe) = &self.left;
        let (right, _, rrecipe) = &self.right;
        let overlap_owner = if self.overlap.depends_on_modes(left, right) {
            match self.overlap {
                Overlap::Entry => left.entry_callable(),
                Overlap::Capture { capture, .. } => Some(capture.callable),
                Overlap::Region => None,
            }
        } else {
            None
        };
        let mut owners = [
            overlap_owner,
            lrecipe.as_ref().and_then(|_| left.entry_callable()),
            rrecipe.as_ref().and_then(|_| right.entry_callable()),
        ]
        .into_iter()
        .flatten();
        let owner = owners.next()?;
        owners.all(|other| other == owner).then_some(owner)
    }

    pub(in crate::access) fn classify(
        &self,
        input: impl Fn(&Region) -> Option<Input>,
    ) -> Option<bool> {
        let (left, lmode, lrecipe) = &self.left;
        let (right, rmode, rrecipe) = &self.right;
        let select = |mode, recipe: &Option<ForwardedMode>| {
            recipe
                .as_ref()
                .and_then(|recipe| recipe.select(&input))
                .map_or(mode, Input::mode)
        };
        self.overlap
            .occurs(left, right, &input)
            .then(|| {
                conflict_kind(
                    left,
                    select(*lmode, lrecipe),
                    right,
                    select(*rmode, rrecipe),
                )
            })
            .flatten()
    }
}

fn conflict_kind(left: &Origin, lmode: Mode, right: &Origin, rmode: Mode) -> Option<bool> {
    if lmode == Mode::Shared && rmode == Mode::Shared {
        return None;
    }
    let writes = |origin: &Origin, mode| {
        origin.mode.writes() && matches!(mode, Mode::Mut | Mode::Shared | Mode::New | Mode::Via)
    };
    let observes = |origin: &Origin, mode| {
        mode == Mode::Ref || mode == Mode::New && origin.mode == Access::Ref
    };
    let left_writable = writes(left, lmode);
    let right_writable = writes(right, rmode);
    let writable = left_writable && right_writable;
    (writable || left_writable && observes(right, rmode) || right_writable && observes(left, lmode))
        .then_some(writable)
}

pub(in crate::access) fn conflicts<'a>(
    left: &'a Datum,
    lmode: Mode,
    right: &'a Datum,
    rmode: Mode,
) -> impl Iterator<Item = AccessConflict> + 'a {
    left.call_participants(lmode).flat_map(move |(a, lmode)| {
        right
            .call_participants(rmode)
            .filter_map(move |(b, rmode)| {
                if !compatible(&a.branches, &b.branches) {
                    return None;
                }
                let overlap = Overlap::potential(a, b)?;
                let capture = overlap.capture();
                let lrecipe = (lmode == Mode::Via).then(|| a.forwarded_mode()).flatten();
                let rrecipe = (rmode == Mode::Via).then(|| b.forwarded_mode()).flatten();
                let direct = conflict_kind(a, lmode, b, rmode);
                if lrecipe.is_some()
                    || rrecipe.is_some()
                    || direct.is_some() && overlap.depends_on_modes(a, b)
                {
                    return Some(AccessConflict {
                        capture,
                        kind: ConflictKind::Via(Box::new(ViaConflict {
                            overlap,
                            left: (a.clone(), lmode, lrecipe),
                            right: (b.clone(), rmode, rrecipe),
                        })),
                    });
                }
                let writable = direct?;
                overlap.occurs(a, b, &|_| None).then_some(AccessConflict {
                    kind: ConflictKind::Direct { writable },
                    capture,
                })
            })
    })
}
