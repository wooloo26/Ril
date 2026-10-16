//! Fixed read-only slot windows; replacement is observed through the backing
//! array. Structural lifetime permission belongs to source verification.
use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
#[cfg(test)]
#[path = "window_tests.rs"]
mod tests;
impl Runtime {
    pub(crate) fn array_window(&mut self, source: Handle, range: Handle) -> Result<Handle> {
        let (backing, start, length) = match self.heap.get(source)? {
            Object::Array(values) => (source, 0, values.len()),
            Object::ArrayWindow {
                backing,
                start,
                len,
            } => (*backing, *start, *len),
            _ => {
                return Err(RuntimeError::internal(
                    "certified slice source is not an array",
                ));
            }
        };
        let Object::Range {
            lower,
            upper,
            inclusive,
        } = self.heap.get(range)?
        else {
            return Err(RuntimeError::internal(
                "certified slice index is not a range",
            ));
        };
        let lower = lower
            .map(|handle| self.as_integer(handle))
            .transpose()?
            .unwrap_or(0);
        let written_upper = upper.is_some();
        let upper = upper
            .map(|handle| self.as_integer(handle))
            .transpose()?
            .unwrap_or(length as i128);
        if lower < 0
            || upper < lower
            || upper > length as i128
            || (*inclusive && written_upper && upper == length as i128)
        {
            return Err(RuntimeError::panic("slice bounds out of range"));
        }
        let end = upper as usize + usize::from(*inclusive && written_upper);
        let lower = lower as usize;
        self.allocate(Object::ArrayWindow {
            backing,
            start: start + lower,
            len: end - lower,
        })
    }
}
