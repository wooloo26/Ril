//! Versioned internal value and GC-storage layouts, independent of the host ABI.
use crate::TargetSpec;
use std::{error::Error, fmt, num::NonZeroU32};

/// Increment when a representation or object header changes incompatibly.
pub const LAYOUT_VERSION: u32 = 1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntegerType {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    BigInt,
}

impl IntegerType {
    pub const fn fixed_bytes(self) -> Option<u8> {
        match self {
            Self::I8 | Self::U8 => Some(1),
            Self::I16 | Self::U16 => Some(2),
            Self::I32 | Self::U32 => Some(4),
            Self::I64 | Self::U64 => Some(8),
            Self::BigInt => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatType {
    F32,
    F64,
}

/// Access modes, effects, and nominal names do not occur in erased layouts.
/// Nominal and opaque wrappers select their checked representation's layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueRepr {
    Unit,
    Never,
    Bool,
    Integer(IntegerType),
    Float(FloatType),
    Text,
    Bytes,
    SharedObject,
    Callable,
    IntegerRange(IntegerType),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Alignment(NonZeroU32);

impl Alignment {
    pub const fn new(bytes: u32) -> Option<Self> {
        if !bytes.is_power_of_two() {
            return None;
        }
        match NonZeroU32::new(bytes) {
            Some(bytes) => Some(Self(bytes)),
            None => None,
        }
    }

    pub const fn bytes(self) -> u32 {
        self.0.get()
    }

    pub fn round_up(self, offset: u64) -> Result<u64, LayoutError> {
        let mask = u64::from(self.bytes()) - 1;
        offset
            .checked_add(mask)
            .map(|value| value & !mask)
            .ok_or(LayoutError::ArithmeticOverflow)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueLayout {
    size: u64,
    alignment: Alignment,
    trace_offsets: Vec<u64>,
}

impl ValueLayout {
    pub const fn size(&self) -> u64 {
        self.size
    }

    pub const fn alignment(&self) -> Alignment {
        self.alignment
    }

    /// Offsets of strong managed pointers; code and descriptor pointers are excluded.
    pub fn trace_offsets(&self) -> &[u64] {
        &self.trace_offsets
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldLayout {
    offset: u64,
    representation: ValueRepr,
    value: ValueLayout,
}

impl FieldLayout {
    pub const fn offset(&self) -> u64 {
        self.offset
    }
    pub const fn representation(&self) -> ValueRepr {
        self.representation
    }
    pub fn value(&self) -> &ValueLayout {
        &self.value
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructLayout {
    size: u64,
    alignment: Alignment,
    fields: Vec<FieldLayout>,
    trace_offsets: Vec<u64>,
}

impl StructLayout {
    pub const fn size(&self) -> u64 {
        self.size
    }

    pub const fn alignment(&self) -> Alignment {
        self.alignment
    }

    pub fn fields(&self) -> &[FieldLayout] {
        &self.fields
    }

    pub fn trace_offsets(&self) -> &[u64] {
        &self.trace_offsets
    }
}

/// A fixed object has a descriptor pointer and flags word before its payload.
/// Field and trace offsets are relative to the object handle, including that prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObjectLayout {
    payload_offset: u64,
    storage: StructLayout,
}

impl ObjectLayout {
    pub const fn payload_offset(&self) -> u64 {
        self.payload_offset
    }
    pub fn storage(&self) -> &StructLayout {
        &self.storage
    }
}

/// A repeated buffer stores an i64 count after the common object header.
/// Its trace description stays bounded even for a very large logical extent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BufferLayout {
    size: u64,
    alignment: Alignment,
    count_offset: u64,
    elements_offset: u64,
    count: u64,
    element: ValueLayout,
}

impl BufferLayout {
    pub const fn count_offset(&self) -> u64 {
        self.count_offset
    }
    pub const fn elements_offset(&self) -> u64 {
        self.elements_offset
    }
    pub const fn count(&self) -> u64 {
        self.count
    }
    pub fn element(&self) -> &ValueLayout {
        &self.element
    }
    pub const fn size(&self) -> u64 {
        self.size
    }

    pub const fn alignment(&self) -> Alignment {
        self.alignment
    }

    pub fn trace_offsets(&self) -> impl Iterator<Item = u64> + '_ {
        let count = if self.element.trace_offsets.is_empty() {
            0
        } else {
            self.count
        };
        (0..count).flat_map(move |index| {
            self.element.trace_offsets.iter().map(move |offset| {
                // Construction checked the complete extent, including padding.
                self.elements_offset + index * self.element.size + offset
            })
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LayoutError {
    ArithmeticOverflow,
    ExtentExceeded { count: u64 },
    AddressSpaceExceeded { size: u64, maximum: u64 },
}

impl fmt::Display for LayoutError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArithmeticOverflow => formatter.write_str("layout size arithmetic overflow"),
            Self::ExtentExceeded { count } => {
                write!(formatter, "collection extent {count} exceeds i64")
            }
            Self::AddressSpaceExceeded { size, maximum } => write!(
                formatter,
                "layout size {size} exceeds target maximum {maximum}"
            ),
        }
    }
}

impl Error for LayoutError {}

fn alignment(bytes: u32) -> Alignment {
    Alignment::new(bytes).expect("representation alignments are nonzero powers of two")
}

impl TargetSpec {
    pub fn value_layout(self, representation: ValueRepr) -> ValueLayout {
        let pointer = u64::from(self.pointer_bytes());
        let (size, align, trace_offsets) = match representation {
            ValueRepr::Unit | ValueRepr::Never => (0, 1, vec![]),
            ValueRepr::Bool => (1, 1, vec![]),
            ValueRepr::Integer(integer) => match integer.fixed_bytes() {
                Some(bytes) => (u64::from(bytes), u32::from(bytes), vec![]),
                None => (pointer, u32::from(self.pointer_bytes()), vec![0]),
            },
            ValueRepr::Float(FloatType::F32) => (4, 4, vec![]),
            ValueRepr::Float(FloatType::F64) => (8, 8, vec![]),
            ValueRepr::Text | ValueRepr::Bytes | ValueRepr::SharedObject => {
                (pointer, u32::from(self.pointer_bytes()), vec![0])
            }
            ValueRepr::Callable => (pointer * 2, u32::from(self.pointer_bytes()), vec![pointer]),
            ValueRepr::IntegerRange(integer) => {
                let endpoint = self.value_layout(ValueRepr::Integer(integer));
                let align = u64::from(endpoint.alignment.bytes());
                // Endpoints are at most eight bytes. The final byte is the
                // inclusive flag; padding makes this value a valid array stride.
                let size = (endpoint.size * 2 + 1).div_ceil(align) * align;
                let roots = endpoint
                    .trace_offsets
                    .iter()
                    .copied()
                    .chain(
                        endpoint
                            .trace_offsets
                            .iter()
                            .map(|offset| endpoint.size + offset),
                    )
                    .collect();
                (size, endpoint.alignment.bytes(), roots)
            }
        };
        ValueLayout {
            size,
            alignment: alignment(align),
            trace_offsets,
        }
    }

    fn check_layout_size(self, size: u64) -> Result<(), LayoutError> {
        let maximum = self.max_object_bytes();
        if size > maximum {
            Err(LayoutError::AddressSpaceExceeded { size, maximum })
        } else {
            Ok(())
        }
    }

    pub fn struct_layout(
        self,
        fields: impl IntoIterator<Item = ValueRepr>,
    ) -> Result<StructLayout, LayoutError> {
        self.struct_layout_at(0, alignment(1), fields)
    }

    fn struct_layout_at(
        self,
        prefix: u64,
        minimum_alignment: Alignment,
        fields: impl IntoIterator<Item = ValueRepr>,
    ) -> Result<StructLayout, LayoutError> {
        let mut size = prefix;
        let mut aggregate_alignment = minimum_alignment;
        let mut layouts = vec![];
        let mut trace_offsets = vec![];
        for representation in fields {
            let value = self.value_layout(representation);
            aggregate_alignment = aggregate_alignment.max(value.alignment);
            let offset = value.alignment.round_up(size)?;
            size = offset
                .checked_add(value.size)
                .ok_or(LayoutError::ArithmeticOverflow)?;
            self.check_layout_size(size)?;
            for root in &value.trace_offsets {
                trace_offsets.push(
                    offset
                        .checked_add(*root)
                        .ok_or(LayoutError::ArithmeticOverflow)?,
                );
            }
            layouts.push(FieldLayout {
                offset,
                representation,
                value,
            });
        }
        size = aggregate_alignment.round_up(size)?;
        self.check_layout_size(size)?;
        Ok(StructLayout {
            size,
            alignment: aggregate_alignment,
            fields: layouts,
            trace_offsets,
        })
    }

    pub fn object_layout(
        self,
        fields: impl IntoIterator<Item = ValueRepr>,
    ) -> Result<ObjectLayout, LayoutError> {
        let prefix = u64::from(self.pointer_bytes()) * 2;
        let storage =
            self.struct_layout_at(prefix, alignment(u32::from(self.pointer_bytes())), fields)?;
        let payload_offset = storage.alignment.round_up(prefix)?;
        Ok(ObjectLayout {
            payload_offset,
            storage,
        })
    }

    pub fn buffer_layout(
        self,
        element: ValueRepr,
        count: u64,
    ) -> Result<BufferLayout, LayoutError> {
        if count > i64::MAX as u64 {
            return Err(LayoutError::ExtentExceeded { count });
        }
        let element = self.value_layout(element);
        let count_offset = u64::from(self.pointer_bytes()) * 2;
        let aggregate_alignment = alignment(8).max(element.alignment);
        let elements_offset = element.alignment.round_up(count_offset + 8)?;
        let bytes = element
            .size
            .checked_mul(count)
            .ok_or(LayoutError::ArithmeticOverflow)?;
        let size = elements_offset
            .checked_add(bytes)
            .ok_or(LayoutError::ArithmeticOverflow)?;
        let size = aggregate_alignment.round_up(size)?;
        self.check_layout_size(size)?;
        Ok(BufferLayout {
            size,
            alignment: aggregate_alignment,
            count_offset,
            elements_offset,
            count,
            element,
        })
    }
}
