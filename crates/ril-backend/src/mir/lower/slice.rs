use ril_sema::{
    syntax::{Pattern, PatternId},
    ty::text_slice_fragment,
};

use super::{BlockId, Builder, Register, Result, Terminator};

impl Builder<'_, '_> {
    pub(super) fn test_slice(
        &mut self,
        text: bool,
        items: &[PatternId],
        value: Register,
        yes: BlockId,
        no: BlockId,
    ) -> Result<()> {
        let (before, rest, after) = self.ast().slice_parts(items);
        if text {
            let prefix = self.text_fragment(before)?;
            if rest.is_none() {
                let expected = self.string(&prefix);
                let condition = self.runtime("ril_rt_equal", vec![value, expected]);
                self.terminate(Terminator::Branch { condition, yes, no });
                return Ok(());
            }
            let suffix = self.text_fragment(after)?;
            self.test_slice_length(
                value,
                prefix.chars().count() + suffix.chars().count(),
                true,
                no,
            );
            if !prefix.is_empty() {
                let prefix = self.string(&prefix);
                let starts = self.runtime("ril_rt_str_starts_with", vec![value, prefix]);
                self.continue_slice_test(starts, no);
            }
            if suffix.is_empty() {
                self.terminate(Terminator::Jump(yes, Vec::new()));
            } else {
                let suffix = self.string(&suffix);
                let condition = self.runtime("ril_rt_str_ends_with", vec![value, suffix]);
                self.terminate(Terminator::Branch { condition, yes, no });
            }
            return Ok(());
        }

        let length = self.test_slice_length(value, before.len() + after.len(), rest.is_some(), no);
        for (item, index, from_end) in slice_indices(before, after) {
            let part = self.slice_element(value, length, index, from_end);
            let next = self.block(0);
            self.test_pattern(item, part, next, no)?;
            self.current = Some(next);
        }
        self.terminate(Terminator::Jump(yes, Vec::new()));
        Ok(())
    }

    pub(super) fn bind_slice(
        &mut self,
        text: bool,
        items: &[PatternId],
        value: Register,
    ) -> Result<()> {
        let (before, rest, after) = self.ast().slice_parts(items);
        let length = self.runtime("ril_rt_len", vec![value]);
        if !text {
            for (item, index, from_end) in slice_indices(before, after) {
                let part = self.slice_element(value, length, index, from_end);
                self.bind(item, part)?;
            }
        }
        if let Some(rest) = rest
            && matches!(self.ast().pattern(rest).value, Pattern::Rest(Some(_)))
        {
            let (start, trailing) = if text {
                (
                    self.text_fragment(before)?.chars().count(),
                    self.text_fragment(after)?.chars().count(),
                )
            } else {
                (before.len(), after.len())
            };
            let start = self.integer(&start.to_string());
            let end = self.subtract_offset(length, trailing);
            let exclusive = self.boolean(false);
            let slice = self.runtime("ril_rt_slice", vec![value, start, end, exclusive]);
            self.bind(rest, slice)?;
        }
        Ok(())
    }

    fn text_fragment(&self, items: &[PatternId]) -> Result<String> {
        text_slice_fragment(self.ast(), items).ok_or_else(|| {
            let span = items
                .first()
                .map(|&id| self.ast().pattern(id).span)
                .unwrap_or_default();
            self.unsupported(span, "invalid string slice fragment")
        })
    }

    fn test_slice_length(
        &mut self,
        value: Register,
        fixed: usize,
        rest: bool,
        no: BlockId,
    ) -> Register {
        let length = self.runtime("ril_rt_len", vec![value]);
        let fixed = self.integer(&fixed.to_string());
        let condition = self.runtime(
            if rest { "ril_rt_ge" } else { "ril_rt_equal" },
            vec![length, fixed],
        );
        self.continue_slice_test(condition, no);
        length
    }

    fn continue_slice_test(&mut self, condition: Register, no: BlockId) {
        let next = self.block(0);
        self.terminate(Terminator::Branch {
            condition,
            yes: next,
            no,
        });
        self.current = Some(next);
    }

    fn slice_element(
        &mut self,
        value: Register,
        length: Register,
        index: usize,
        from_end: bool,
    ) -> Register {
        let key = if from_end {
            self.subtract_offset(length, index)
        } else {
            self.integer(&index.to_string())
        };
        self.runtime("ril_rt_load", vec![value, key])
    }

    fn subtract_offset(&mut self, length: Register, offset: usize) -> Register {
        if offset == 0 {
            return length;
        }
        let offset = self.integer(&offset.to_string());
        self.runtime("ril_rt_int_sub", vec![length, offset])
    }
}

fn slice_indices<'a>(
    before: &'a [PatternId],
    after: &'a [PatternId],
) -> impl Iterator<Item = (PatternId, usize, bool)> + 'a {
    before
        .iter()
        .copied()
        .enumerate()
        .map(|(index, item)| (item, index, false))
        .chain(
            after
                .iter()
                .copied()
                .zip((1..=after.len()).rev())
                .map(|(item, offset)| (item, offset, true)),
        )
}
