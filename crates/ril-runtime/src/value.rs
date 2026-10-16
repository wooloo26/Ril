//! Managed-value operations. Language failure is a value in the control state;
//! it never uses Rust unwinding.
use crate::heap::{Handle, Heap, HeapError, Object};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use ril_runtime_api::abi::{BinaryOp, OutcomeTag};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct RuntimeError {
    pub tag: OutcomeTag,
    pub message: String,
    pub location: Option<(u32, u32, u32)>,
    /// Source element selected by a Parallel operation, if applicable.
    pub index: Option<usize>,
    pub primary: Option<Box<RuntimeError>>,
    pub cleanup: Option<Box<RuntimeError>>,
}

impl RuntimeError {
    pub(crate) fn cancelled() -> Self {
        Self {
            tag: OutcomeTag::Cancelled,
            message: "task cancelled".into(),
            location: None,
            index: None,
            primary: None,
            cleanup: None,
        }
    }
    pub fn panic(message: impl Into<String>) -> Self {
        Self {
            tag: OutcomeTag::LanguagePanic,
            message: message.into(),
            location: None,
            index: None,
            primary: None,
            cleanup: None,
        }
    }
    pub fn internal(message: impl Into<String>) -> Self {
        Self {
            tag: OutcomeTag::InternalFault,
            message: message.into(),
            location: None,
            index: None,
            primary: None,
            cleanup: None,
        }
    }
    pub fn double_fault(primary: RuntimeError, cleanup: RuntimeError) -> Self {
        Self {
            tag: OutcomeTag::DoubleFault,
            message: format!(
                "double fault: {}; cleanup: {}",
                primary.message, cleanup.message
            ),
            location: primary.location,
            index: primary.index,
            primary: Some(Box::new(primary)),
            cleanup: Some(Box::new(cleanup)),
        }
    }
}
impl From<HeapError> for RuntimeError {
    fn from(value: HeapError) -> Self {
        Self::internal(format!("managed heap error: {value:?}"))
    }
}
pub type Result<T> = std::result::Result<T, RuntimeError>;

#[derive(Debug, Default)]
struct Frame {
    roots: BTreeMap<u32, Handle>,
    temporaries: Vec<Handle>,
    cleanups: Vec<Handle>,
}

#[derive(Debug)]
pub struct Runtime {
    /// Stable across moving this logical runtime between OS workers.
    pub(crate) identity: std::sync::Arc<()>,
    pub heap: Heap,
    pub(crate) shared_worker: Option<crate::shared::Membership>,
    pub(crate) executor: Option<crate::scheduler::Executor>,
    pub(crate) external_roots: Vec<Handle>,
    pub(crate) budgets: crate::budget::Allowances,
    pub(crate) cancellation: std::sync::Arc<crate::process_io::Cancellation>,
    pub(crate) cancellation_mask: u32,
    pub(crate) read_permits: Vec<crate::io_reservations::ReadPermit>,
    pub(crate) foreign_bindings:
        std::sync::Arc<Vec<std::sync::Arc<ril_runtime_api::foreign::BoundCall>>>,
    pub(crate) foreign_calls: BTreeMap<u64, crate::foreign_runtime::Invocation>,
    pub(crate) concurrent_scopes: Vec<crate::concurrent::ActiveScope>,
    pub(crate) task_owner: crate::concurrent::TaskOwner,
    pub(crate) scope_lineage: Vec<u64>,
    pub(crate) scope_registry: Vec<std::sync::Arc<crate::concurrent::Scope>>,
    pub(crate) owned_endpoints: Vec<(Handle, crate::channel::Endpoint)>,
    pub(crate) owned_tickets: Vec<(Handle, std::sync::Arc<crate::channel::Detached>)>,
    pub(crate) files: Vec<std::sync::Arc<std::sync::Mutex<crate::file::FileState>>>,
    pub(crate) children: Vec<std::sync::Arc<std::sync::Mutex<crate::process::ChildState>>>,
    frames: Vec<Frame>,
    pub globals: BTreeMap<String, Handle>,
    pub fault: Option<RuntimeError>,
    pub source_location: (u32, u32, u32),
    pub(crate) cps_handlers: Handle,
    pub(crate) cps_activation: Handle,
    pub(crate) cps_delimiters: Vec<Handle>,
    pub(crate) cps_resume_returns: Vec<(Handle, Handle)>,
    pub(crate) cps_exits: Vec<crate::cps_exit::Frame>,
    pub(crate) next_cps_exit: u64,
    next_collection: usize,
}

impl Default for Runtime {
    fn default() -> Self {
        Self {
            identity: std::sync::Arc::new(()),
            heap: Heap::default(),
            shared_worker: None,
            executor: None,
            external_roots: vec![],
            budgets: crate::budget::Allowances::default(),
            cancellation: std::sync::Arc::default(),
            cancellation_mask: 0,
            read_permits: vec![],
            foreign_bindings: Default::default(),
            foreign_calls: BTreeMap::new(),
            concurrent_scopes: vec![],
            task_owner: crate::concurrent::TaskOwner::default(),
            scope_lineage: vec![],
            scope_registry: vec![],
            owned_endpoints: vec![],
            owned_tickets: vec![],
            files: Vec::new(),
            children: Vec::new(),
            frames: vec![Frame::default()],
            globals: BTreeMap::new(),
            fault: None,
            source_location: (0, 0, 0),
            cps_handlers: Handle::INVALID,
            cps_activation: Handle::INVALID,
            cps_delimiters: vec![],
            cps_resume_returns: vec![],
            cps_exits: vec![],
            next_cps_exit: 0,
            next_collection: 1024,
        }
    }
}

impl Runtime {
    /// Mandatory cleanup runs with cancellation masked, including its host IO.
    pub(crate) fn host_cancellation(&self) -> std::sync::Arc<crate::process_io::Cancellation> {
        if self.cancellation_mask == 0 {
            self.cancellation.clone()
        } else {
            std::sync::Arc::default()
        }
    }
    pub fn enter(&mut self) {
        self.frames.push(Frame::default());
    }
    pub fn leave(&mut self, value: Handle) -> Handle {
        if self.frames.len() > 1 {
            self.frames.pop();
        }
        if value != Handle::INVALID {
            self.frames.last_mut().unwrap().temporaries.push(value);
        }
        value
    }
    pub fn root(&mut self, slot: u32, value: Handle) -> Result<Handle> {
        self.heap.get(value)?;
        self.frames.last_mut().unwrap().roots.insert(slot, value);
        Ok(value)
    }
    pub fn statement_end(&mut self) {
        self.frames.last_mut().unwrap().temporaries.clear();
    }
    pub(crate) fn strong_roots(&self) -> Vec<Handle> {
        self.frames
            .iter()
            .flat_map(|frame| {
                frame
                    .roots
                    .values()
                    .copied()
                    .chain(frame.temporaries.iter().copied())
                    .chain(frame.cleanups.iter().copied())
            })
            .chain(self.globals.values().copied())
            .chain(self.budgets.roots())
            .chain(
                self.cps_exits
                    .iter()
                    .flat_map(crate::cps_exit::Frame::references),
            )
            .chain(
                self.foreign_calls
                    .values()
                    .flat_map(crate::foreign_runtime::Invocation::references),
            )
            .chain(
                self.read_permits
                    .iter()
                    .flat_map(crate::io_reservations::ReadPermit::references),
            )
            .chain(self.owned_endpoints.iter().map(|(handle, _)| *handle))
            .chain(self.owned_tickets.iter().map(|(handle, _)| *handle))
            .chain(
                self.concurrent_scopes
                    .iter()
                    .flat_map(crate::concurrent::ActiveScope::references),
            )
            .chain((self.cps_handlers != Handle::INVALID).then_some(self.cps_handlers))
            .chain((self.cps_activation != Handle::INVALID).then_some(self.cps_activation))
            .chain(self.cps_delimiters.iter().copied())
            .chain(
                self.cps_resume_returns
                    .iter()
                    .flat_map(|&(delimiter, continuation)| [delimiter, continuation]),
            )
            .collect()
    }
    pub(crate) fn seed_shared_roots(&mut self, roots: &[Handle]) {
        self.frames
            .last_mut()
            .unwrap()
            .temporaries
            .extend_from_slice(roots);
    }
    pub fn collect(&mut self) -> Result<usize> {
        let roots: Vec<_> = self
            .strong_roots()
            .into_iter()
            .chain(self.external_roots.iter().copied())
            .collect();
        let count = self.heap.collect(roots)?;
        self.next_collection = self.heap.live_objects().saturating_mul(2).max(1024);
        Ok(count)
    }
    pub fn allocate(&mut self, value: Object) -> Result<Handle> {
        let value = self.heap.allocate(value)?;
        self.frames.last_mut().unwrap().temporaries.push(value);
        if self.heap.live_objects() >= self.next_collection {
            self.collect()?;
        }
        Ok(value)
    }
    pub(crate) fn cleanup_marker(&self) -> u32 {
        self.frames.last().unwrap().cleanups.len() as u32
    }
    pub(crate) fn register_cleanup(&mut self, resource: Handle) -> Result<Handle> {
        if matches!(self.heap.get(resource)?, Object::File(_) | Object::Child(_)) {
            self.frames.last_mut().unwrap().cleanups.push(resource);
            return Ok(resource);
        }
        let action = self.field(resource, "on_close")?;
        if !matches!(
            self.heap.get(action)?,
            Object::Closure { .. }
                | Object::BudgetClosure {
                    normal_is_cps: false,
                    ..
                }
                | Object::Builtin(_)
        ) {
            return Err(RuntimeError::internal("invalid scoped cleanup contract"));
        }
        self.frames.last_mut().unwrap().cleanups.push(resource);
        Ok(resource)
    }
    pub(crate) fn pop_cleanup(&mut self, marker: u32) -> Result<Option<Handle>> {
        let frame = self.frames.last_mut().unwrap();
        if marker as usize > frame.cleanups.len() {
            return Err(RuntimeError::internal("invalid cleanup scope marker"));
        }
        if marker as usize == frame.cleanups.len() {
            return Ok(None);
        }
        let resource = frame.cleanups.pop().unwrap();
        frame.temporaries.push(resource);
        Ok(Some(resource))
    }
    pub(crate) fn abandon_cleanups(&mut self, marker: u32) {
        self.frames
            .last_mut()
            .unwrap()
            .cleanups
            .truncate(marker as usize);
    }
    pub(crate) fn keep_temporary(&mut self, value: Handle) {
        if value != Handle::INVALID
            && self.frames.last().unwrap().temporaries.last() != Some(&value)
        {
            self.frames.last_mut().unwrap().temporaries.push(value);
        }
    }
    pub fn unit(&mut self) -> Result<Handle> {
        self.allocate(Object::Unit)
    }
    pub fn boolean(&mut self, value: bool) -> Result<Handle> {
        self.allocate(Object::Bool(value))
    }
    pub fn integer(&mut self, value: i128, bits: u8, signed: bool) -> Result<Handle> {
        if !matches!(bits, 8 | 16 | 32 | 64) || !integer_fits(value, bits, signed) {
            return Err(RuntimeError::panic("integer overflow"));
        }
        self.allocate(Object::Integer {
            value,
            bits,
            signed,
        })
    }
    pub fn int(&mut self, value: i128) -> Result<Handle> {
        self.integer(value, 64, true)
    }
    pub fn float(&mut self, value: f64, bits: u8) -> Result<Handle> {
        let value = if bits == 32 {
            f64::from(canonical_f32(value as f32))
        } else {
            canonical_f64(value)
        };
        self.allocate(Object::Float { value, bits })
    }
    pub fn string(&mut self, value: String) -> Result<Handle> {
        self.allocate(Object::String(value))
    }
    pub fn as_integer(&self, value: Handle) -> Result<i128> {
        match self.heap.get(value)? {
            Object::Integer { value, .. } => Ok(*value),
            _ => Err(RuntimeError::internal("expected integer")),
        }
    }
    pub fn as_string(&self, value: Handle) -> Result<&str> {
        match self.heap.get(value)? {
            Object::String(value) => Ok(value),
            Object::Builtin(value) => Ok(value),
            _ => Err(RuntimeError::internal("expected string")),
        }
    }
    pub fn truth(&self, value: Handle) -> Result<bool> {
        match self.heap.get(value)? {
            Object::Bool(value) => Ok(*value),
            _ => Err(RuntimeError::internal("expected bool")),
        }
    }
    pub fn sequence(&self, value: Handle) -> Result<Vec<Handle>> {
        if let Some(values) = self.heap.array_elements(value)? {
            return Ok(values.to_vec());
        }
        match self.heap.get(value)? {
            Object::Array(values) | Object::Tuple(values) => Ok(values.clone()),
            _ => Err(RuntimeError::internal("expected sequence")),
        }
    }
    pub fn length(&self, value: Handle) -> Result<u64> {
        Ok(match self.heap.get(value)? {
            Object::Array(values) | Object::Tuple(values) => values.len() as u64,
            Object::ArrayWindow { len, .. } => *len as u64,
            Object::String(text) => text.chars().count() as u64,
            Object::Bytes(bytes) => bytes.len() as u64,
            Object::Map(entries) | Object::Set(entries) => entries.len() as u64,
            Object::Iterator { source, .. } => self.length(*source)?,
            Object::Range {
                lower: Some(lower),
                upper: Some(upper),
                inclusive,
            } => {
                let lower = self.as_integer(*lower)?;
                let upper = self.as_integer(*upper)?;
                let count = if upper < lower {
                    0
                } else {
                    upper - lower + i128::from(*inclusive)
                };
                u64::try_from(count).map_err(|_| RuntimeError::panic("range length overflow"))?
            }
            _ => return Err(RuntimeError::internal("value has no finite length")),
        })
    }
    pub fn append(&mut self, sequence: Handle, value: Handle) -> Result<Handle> {
        self.heap.get(value)?;
        match self.heap.get_mut(sequence)? {
            Object::Array(values) | Object::Tuple(values) => values.push(value),
            _ => return Err(RuntimeError::internal("expected sequence")),
        }
        Ok(sequence)
    }
    pub fn iterator(&mut self, source: Handle) -> Result<Handle> {
        let next = match self.heap.get(source)? {
            Object::Map(entries) | Object::Set(entries) => entries.first_slot(),
            Object::Array(_) | Object::ArrayWindow { .. } | Object::Range { .. } => None,
            _ => {
                return Err(RuntimeError::internal(
                    "inadmissible implicit iteration source",
                ));
            }
        };
        let range_next = match self.heap.get(source)? {
            Object::Range {
                lower: Some(lower),
                upper: Some(_),
                ..
            } => Some(*lower),
            Object::Range { .. } => {
                return Err(RuntimeError::internal(
                    "iteration requires both range endpoints",
                ));
            }
            _ => None,
        };
        self.allocate(Object::Iterator {
            source,
            index: 0,
            next,
            range_next,
            exhausted: false,
        })
    }
    pub fn iterator_item(&mut self, cursor: Handle, expected_index: u64) -> Result<Handle> {
        let (source, index, next) = match self.heap.get(cursor)? {
            Object::Iterator {
                source,
                index,
                next,
                ..
            } => (*source, *index, *next),
            _ => return Err(RuntimeError::internal("expected native iterator")),
        };
        if index != expected_index {
            return Err(RuntimeError::internal("iterator cursor is out of order"));
        }
        let _ = (source, next);
        self.iterator_next(cursor)?
            .ok_or_else(|| RuntimeError::internal("iterator cursor is exhausted"))
    }
    pub fn field(&mut self, base: Handle, name: &str) -> Result<Handle> {
        let result = match self.heap.get(base)? {
            Object::Record(fields) => fields.get(name).copied(),
            Object::Tuple(fields) | Object::Variant { fields, .. } => name
                .parse::<usize>()
                .ok()
                .and_then(|i| fields.get(i).copied()),
            Object::Nominal { payload, .. } if name == "0" => Some(*payload),
            _ => None,
        };
        result.ok_or_else(|| RuntimeError::internal(format!("missing field {name}")))
    }
    pub fn safe_field(&mut self, base: Handle, name: &str) -> Result<Handle> {
        let payload = match self.heap.get(base)? {
            Object::Variant { tag, fields } if tag == "None" && fields.is_empty() => {
                return Ok(base);
            }
            Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => fields[0],
            _ => {
                return Err(RuntimeError::internal(
                    "safe field requires a verified optional receiver",
                ));
            }
        };
        let selected = self.field(payload, name)?;
        if matches!(self.heap.get(selected)?, Object::Variant { tag, fields } if tag == "None" && fields.is_empty() || tag == "Some" && fields.len() == 1)
        {
            Ok(selected)
        } else {
            self.variant("Some", vec![selected])
        }
    }
    pub fn computed_field(&mut self, base: Handle, key: Handle) -> Result<Handle> {
        match (self.heap.get(base)?, self.heap.get(key)?) {
            (Object::Record(fields), Object::String(key)) => fields
                .get(key)
                .copied()
                .ok_or_else(|| RuntimeError::internal("certified record coordinate is absent")),
            (Object::Tuple(fields), Object::Integer { value, .. }) => usize::try_from(*value)
                .ok()
                .and_then(|index| fields.get(index).copied())
                .ok_or_else(|| RuntimeError::internal("certified tuple coordinate is absent")),
            _ => Err(RuntimeError::internal(
                "computed field coordinate differs from its verified sort",
            )),
        }
    }
    pub fn set_field(&mut self, base: Handle, name: String, value: Handle) -> Result<Handle> {
        self.heap.get(value)?;
        match self.heap.get_mut(base)? {
            Object::Record(fields) => {
                fields.insert(name, value);
            }
            Object::Tuple(fields) => {
                let i = name
                    .parse::<usize>()
                    .map_err(|_| RuntimeError::internal("invalid tuple index"))?;
                let target = fields
                    .get_mut(i)
                    .ok_or_else(|| RuntimeError::panic("tuple index out of bounds"))?;
                *target = value;
            }
            _ => return Err(RuntimeError::internal("expected record or tuple")),
        }
        Ok(value)
    }
    pub fn index(&mut self, base: Handle, index: Handle, safe: bool) -> Result<Handle> {
        let base = if safe {
            match self.heap.get(base)? {
                Object::Variant { tag, fields } if tag == "None" && fields.is_empty() => {
                    return Ok(base);
                }
                Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => fields[0],
                _ => base,
            }
        } else {
            base
        };
        if matches!(self.heap.get(index)?, Object::Range { .. }) {
            if safe {
                return Err(RuntimeError::internal(
                    "safe slicing is not a certified operation",
                ));
            }
            return self.array_window(base, index);
        }
        let map_lookup = matches!(self.heap.get(base)?, Object::Map(_));
        let result = match self.heap.get(base)? {
            Object::Map(entries) => entries.get(&self.key(index)?),
            Object::Array(values) | Object::Tuple(values) => {
                usize::try_from(self.as_integer(index)?)
                    .ok()
                    .and_then(|i| values.get(i).copied())
            }
            Object::ArrayWindow { .. } => {
                let values = self
                    .heap
                    .array_elements(base)?
                    .ok_or_else(|| RuntimeError::internal("invalid array window"))?;
                usize::try_from(self.as_integer(index)?)
                    .ok()
                    .and_then(|index| values.get(index).copied())
            }
            Object::String(text) => {
                let scalar = usize::try_from(self.as_integer(index)?)
                    .ok()
                    .and_then(|i| text.chars().nth(i))
                    .map(|c| c as u32);
                match scalar {
                    Some(scalar) => Some(self.integer(i128::from(scalar), 32, false)?),
                    None => None,
                }
            }
            Object::Bytes(bytes) => {
                let byte = usize::try_from(self.as_integer(index)?)
                    .ok()
                    .and_then(|i| bytes.get(i).copied());
                match byte {
                    Some(byte) => Some(self.integer(i128::from(byte), 8, false)?),
                    None => None,
                }
            }
            Object::Range {
                lower: Some(lower),
                upper: Some(_),
                ..
            } => {
                let index = self.as_integer(index)?;
                let length = self.length(base)?;
                if index < 0 || index >= i128::from(length) {
                    None
                } else {
                    let (value, bits, signed) = match self.heap.get(*lower)? {
                        Object::Integer {
                            value,
                            bits,
                            signed,
                        } => (*value, *bits, *signed),
                        _ => {
                            return Err(RuntimeError::internal("range endpoint is not an integer"));
                        }
                    };
                    Some(self.integer(value + index, bits, signed)?)
                }
            }
            _ => return Err(RuntimeError::internal("invalid indexed value")),
        };
        if safe || map_lookup {
            if safe
                && let Some(value) = result
                && matches!(self.heap.get(value)?, Object::Variant { tag, fields } if tag == "None" && fields.is_empty() || tag == "Some" && fields.len() == 1)
            {
                return Ok(value);
            }
            self.variant(
                if result.is_some() { "Some" } else { "None" },
                result.into_iter().collect(),
            )
        } else {
            result.ok_or_else(|| RuntimeError::panic("index out of bounds or missing key"))
        }
    }
    pub fn set_index(&mut self, base: Handle, index: Handle, value: Handle) -> Result<Handle> {
        if matches!(self.heap.get(base)?, Object::Map(_)) {
            self.map_set(base, index, value)?;
            return Ok(value);
        }
        let i = usize::try_from(self.as_integer(index)?)
            .map_err(|_| RuntimeError::panic("index out of bounds"))?;
        self.heap.get(value)?;
        match self.heap.get_mut(base)? {
            Object::Array(values) | Object::Tuple(values) => {
                *values
                    .get_mut(i)
                    .ok_or_else(|| RuntimeError::panic("index out of bounds"))? = value;
            }
            _ => return Err(RuntimeError::internal("expected writable sequence")),
        }
        Ok(value)
    }
    pub fn variant(&mut self, tag: &str, mut fields: Vec<Handle>) -> Result<Handle> {
        if tag == "Ok" && fields.is_empty() {
            fields.push(self.unit()?);
        }
        self.allocate(Object::Variant {
            tag: tag.into(),
            fields,
        })
    }
    pub fn constructor(&mut self, tag: String, nominal: bool, has_payload: bool) -> Result<Handle> {
        if has_payload {
            self.allocate(Object::DataConstructor { tag, nominal })
        } else if nominal {
            let payload = self.unit()?;
            self.allocate(Object::Nominal { tag, payload })
        } else {
            self.variant(&tag, vec![])
        }
    }
    pub fn construct(&mut self, constructor: Handle, arguments: Handle) -> Result<Handle> {
        let Object::DataConstructor { tag, nominal } = self.heap.get(constructor)?.clone() else {
            return Err(RuntimeError::internal("expected data constructor"));
        };
        let arguments = self.sequence(arguments)?;
        let payload = match arguments.as_slice() {
            [] => self.unit()?,
            [value] => *value,
            _ => self.allocate(Object::Tuple(arguments))?,
        };
        if nominal {
            self.allocate(Object::Nominal { tag, payload })
        } else {
            self.variant(&tag, vec![payload])
        }
    }
    pub fn copy(&mut self, value: Handle) -> Result<Handle> {
        let copy = self.heap.deep_clone(value)?;
        self.frames.last_mut().unwrap().temporaries.push(copy);
        Ok(copy)
    }
    pub fn contains(&mut self, element: Handle, collection: Handle) -> Result<Handle> {
        if let Some(values) = self.heap.array_elements(collection)? {
            let mut found = false;
            for &value in values {
                if self.heap.structurally_equal(element, value)? {
                    found = true;
                    break;
                }
            }
            return self.boolean(found);
        }
        let contained = match self.heap.get(collection)?.clone() {
            Object::Array(items) => {
                let mut found = false;
                for item in items {
                    if self.heap.structurally_equal(element, item)? {
                        found = true;
                        break;
                    }
                }
                found
            }
            Object::Map(items) | Object::Set(items) => items.contains(&self.key(element)?),
            Object::Range {
                lower,
                upper,
                inclusive,
            } => {
                fn compare(left: &Object, right: &Object) -> Result<std::cmp::Ordering> {
                    match (left, right) {
                        (
                            Object::Integer {
                                value: a,
                                bits: ab,
                                signed: asigned,
                            },
                            Object::Integer {
                                value: b,
                                bits: bb,
                                signed: bsigned,
                            },
                        ) if ab == bb && asigned == bsigned => Ok(a.cmp(b)),
                        (Object::BigInteger(a), Object::BigInteger(b)) => Ok(a.cmp(b)),
                        _ => Err(RuntimeError::internal(
                            "integer range element type mismatch",
                        )),
                    }
                }
                let value = self.heap.get(element)?;
                if !matches!(value, Object::Integer { .. } | Object::BigInteger(_)) {
                    return Err(RuntimeError::internal(
                        "integer range requires an integer element",
                    ));
                }
                let above = lower
                    .map(|lower| compare(value, self.heap.get(lower)?).map(|order| !order.is_lt()))
                    .transpose()?
                    .unwrap_or(true);
                let below = upper
                    .map(|upper| {
                        compare(value, self.heap.get(upper)?)
                            .map(|order| order.is_lt() || (inclusive && order.is_eq()))
                    })
                    .transpose()?
                    .unwrap_or(true);
                above && below
            }
            _ => return Err(RuntimeError::internal("unsupported containment receiver")),
        };
        self.boolean(contained)
    }
    pub fn binary(&mut self, op: BinaryOp, left: Handle, right: Handle) -> Result<Handle> {
        use BinaryOp::*;
        if matches!(op, ShiftLeft | ShiftRight) {
            return self.shift(left, right, op == ShiftLeft);
        }
        if matches!(op, SafeDivide | SafeRemainder) {
            let zero = match self.heap.get(right)? {
                Object::Integer { value, .. } => *value == 0,
                Object::BigInteger(value) => value.is_zero(),
                Object::Float { value, .. } => *value == 0.0,
                _ => return Err(RuntimeError::internal("invalid safe arithmetic operand")),
            };
            if zero {
                return self.variant("None", vec![]);
            }
            return match self.binary(
                if op == SafeDivide { Divide } else { Remainder },
                left,
                right,
            ) {
                Ok(value) => self.variant("Some", vec![value]),
                Err(error)
                    if error.tag == OutcomeTag::LanguagePanic
                        && error.message == "integer overflow" =>
                {
                    self.variant("None", vec![])
                }
                Err(error) => Err(error),
            };
        }
        if matches!(op, Equal | NotEqual) {
            let equal = self.heap.structurally_equal(left, right)?;
            return self.boolean(if op == Equal { equal } else { !equal });
        }
        let (left, right) = (self.heap.get(left)?.clone(), self.heap.get(right)?.clone());
        match (left, right) {
            (Object::BigInteger(a), Object::BigInteger(b)) => {
                if matches!(op, Less | LessEqual | Greater | GreaterEqual) {
                    return self.boolean(match op {
                        Less => a < b,
                        LessEqual => a <= b,
                        Greater => a > b,
                        _ => a >= b,
                    });
                }
                let value = match op {
                    Add => a + b,
                    Subtract => a - b,
                    Multiply => a * b,
                    Divide | Remainder => {
                        if b.is_zero() {
                            return Err(RuntimeError::panic("division by zero"));
                        }
                        if op == Divide { a / b } else { a % b }
                    }
                    BitAnd => a & b,
                    BitOr => a | b,
                    BitXor => a ^ b,
                    _ => return Err(RuntimeError::internal("unsupported bigint operation")),
                };
                self.allocate(Object::BigInteger(value))
            }
            (
                Object::Integer {
                    value: a,
                    bits,
                    signed,
                },
                Object::Integer {
                    value: b,
                    bits: other,
                    signed: other_signed,
                },
            ) if bits == other && signed == other_signed => {
                if matches!(op, Less | LessEqual | Greater | GreaterEqual) {
                    return self.boolean(match op {
                        Less => a < b,
                        LessEqual => a <= b,
                        Greater => a > b,
                        _ => a >= b,
                    });
                }
                let value = match op {
                    Add => a.checked_add(b),
                    Subtract => a.checked_sub(b),
                    Multiply => a.checked_mul(b),
                    Divide => {
                        if b == 0 {
                            return Err(RuntimeError::panic("division by zero"));
                        }
                        a.checked_div(b)
                    }
                    Remainder => {
                        if b == 0 {
                            return Err(RuntimeError::panic("division by zero"));
                        }
                        a.checked_rem(b)
                    }
                    BitAnd => Some(a & b),
                    BitOr => Some(a | b),
                    BitXor => Some(a ^ b),
                    WrappingAdd => Some(wrap_integer(a + b, bits, signed)),
                    WrappingSubtract => Some(wrap_integer(a - b, bits, signed)),
                    WrappingMultiply => Some(wrap_integer(a.wrapping_mul(b), bits, signed)),
                    _ => None,
                }
                .ok_or_else(|| RuntimeError::panic("integer overflow"))?;
                self.integer(value, bits, signed)
            }
            (
                Object::Float { value: a, bits },
                Object::Float {
                    value: b,
                    bits: other,
                },
            ) if bits == other => {
                if matches!(op, Less | LessEqual | Greater | GreaterEqual) {
                    return self.boolean(match op {
                        Less => a < b,
                        LessEqual => a <= b,
                        Greater => a > b,
                        _ => a >= b,
                    });
                }
                let value = if bits == 32 {
                    let (a, b) = (a as f32, b as f32);
                    f64::from(match op {
                        Add => a + b,
                        Subtract => a - b,
                        Multiply => a * b,
                        Divide => a / b,
                        Remainder => a % b,
                        _ => return Err(RuntimeError::internal("invalid float operator")),
                    })
                } else {
                    match op {
                        Add => a + b,
                        Subtract => a - b,
                        Multiply => a * b,
                        Divide => a / b,
                        Remainder => a % b,
                        _ => return Err(RuntimeError::internal("invalid float operator")),
                    }
                };
                self.float(value, bits)
            }
            (Object::String(a), Object::String(b)) => match op {
                Add => self.string(a + &b),
                Less => self.boolean(a < b),
                LessEqual => self.boolean(a <= b),
                Greater => self.boolean(a > b),
                GreaterEqual => self.boolean(a >= b),
                _ => Err(RuntimeError::internal("invalid string operator")),
            },
            (Object::Bytes(a), Object::Bytes(b)) => match op {
                Less => self.boolean(a < b),
                LessEqual => self.boolean(a <= b),
                Greater => self.boolean(a > b),
                GreaterEqual => self.boolean(a >= b),
                _ => Err(RuntimeError::internal("invalid byte ordering operator")),
            },
            _ => Err(RuntimeError::internal("incompatible operands")),
        }
    }

    fn shift(&mut self, left: Handle, right: Handle, leftward: bool) -> Result<Handle> {
        let count = match self.heap.get(right)? {
            Object::Integer { value, .. } => BigInt::from(*value),
            Object::BigInteger(value) => value.clone(),
            _ => return Err(RuntimeError::internal("noninteger shift count")),
        };
        if count.is_negative() {
            return Err(RuntimeError::panic("invalid shift count"));
        }
        match self.heap.get(left)?.clone() {
            Object::Integer {
                value,
                bits,
                signed,
            } => {
                let count = count
                    .to_u32()
                    .filter(|&count| count < u32::from(bits))
                    .ok_or_else(|| RuntimeError::panic("invalid shift count"))?;
                let value = if leftward {
                    wrap_integer(value << count, bits, signed)
                } else {
                    value >> count
                };
                self.integer(value, bits, signed)
            }
            Object::BigInteger(value) => {
                let value = if !leftward && count > BigInt::from(value.bits()) {
                    if value.is_negative() {
                        -BigInt::one()
                    } else {
                        BigInt::zero()
                    }
                } else {
                    let count = count.to_usize().ok_or_else(|| {
                        RuntimeError::internal("bigint shift exceeds address space")
                    })?;
                    if leftward {
                        value << count
                    } else {
                        value >> count
                    }
                };
                self.allocate(Object::BigInteger(value))
            }
            _ => Err(RuntimeError::internal("noninteger shift operand")),
        }
    }

    pub fn unary(&mut self, operation: u32, operand: Handle) -> Result<Handle> {
        match (operation, self.heap.get(operand)?.clone()) {
            (0, Object::BigInteger(value)) => self.allocate(Object::BigInteger(-value)),
            (2, Object::BigInteger(value)) => self.allocate(Object::BigInteger(!value)),
            (
                0,
                Object::Integer {
                    value,
                    bits,
                    signed,
                },
            ) => self.integer(
                value
                    .checked_neg()
                    .ok_or_else(|| RuntimeError::panic("integer overflow"))?,
                bits,
                signed,
            ),
            (0, Object::Float { value, bits }) => self.float(-value, bits),
            (1, Object::Bool(value)) => self.boolean(!value),
            (
                2,
                Object::Integer {
                    value,
                    bits,
                    signed,
                },
            ) => self.integer(wrap_integer(!value, bits, signed), bits, signed),
            _ => Err(RuntimeError::internal("invalid unary operator")),
        }
    }

    pub fn format(&self, handle: Handle) -> Result<String> {
        self.format_inner(handle, &mut Vec::new())
    }
    fn format_inner(&self, handle: Handle, seen: &mut Vec<Handle>) -> Result<String> {
        if seen.contains(&handle) {
            return Ok("<cycle>".into());
        }
        seen.push(handle);
        let result = match self.heap.get(handle)? {
            Object::Unit => "()".into(),
            Object::Bool(value) => value.to_string(),
            Object::Integer { value, .. } => value.to_string(),
            Object::BigInteger(value) => value.to_string(),
            Object::StringBuilder(value) => value.clone(),
            Object::Float { value, bits } => crate::formatting::default_float(*value, *bits),
            Object::String(text) | Object::Builtin(text) => text.clone(),
            Object::DataConstructor { .. } => "<constructor>".into(),
            Object::Nominal { tag, payload } => {
                format!("{tag}({})", self.format_inner(*payload, seen)?)
            }
            Object::Bytes(bytes) => format!("{bytes:?}"),
            Object::ArrayWindow { .. } => {
                let values = self
                    .sequence(handle)?
                    .iter()
                    .map(|&value| self.format_inner(value, seen))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ");
                format!("[{values}]")
            }
            Object::IoAccumulator(_) => "<stream accumulator>".into(),
            Object::ReadBuffer(buffer) => format!("<read buffer {}>", buffer.capacity),
            Object::WriteBuffer(buffer) => format!("<write buffer {}>", buffer.capacity),
            Object::Array(values) | Object::Tuple(values) => {
                let values = values
                    .iter()
                    .map(|value| self.format_inner(*value, seen))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ");
                if matches!(self.heap.get(handle)?, Object::Array(_)) {
                    format!("[{values}]")
                } else {
                    format!("({values})")
                }
            }
            Object::Record(fields) => format!(
                ".{{ {} }}",
                fields
                    .iter()
                    .map(|(name, value)| Ok(format!(
                        "{name}: {}",
                        self.format_inner(*value, seen)?
                    )))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ")
            ),
            Object::Variant { tag, fields } => {
                if fields.is_empty() {
                    tag.clone()
                } else {
                    format!(
                        "{tag}({})",
                        fields
                            .iter()
                            .map(|value| self.format_inner(*value, seen))
                            .collect::<Result<Vec<_>>>()?
                            .join(", ")
                    )
                }
            }
            Object::Map(_) => "<map>".into(),
            Object::Set(_) => "<set>".into(),
            Object::Deque(_) => "<deque>".into(),
            Object::PriorityHeap(_) => "<heap>".into(),
            Object::HeapMutation(_) => "<private heap mutation>".into(),
            Object::RandomState(_) => "<rng>".into(),
            Object::NativeString(_) => "<native-string>".into(),
            Object::Path(_) => "<path>".into(),
            Object::File(_) => "<file>".into(),
            Object::Child(_) => "<child>".into(),
            Object::TaskScope(_) => "<task scope>".into(),
            Object::Task(_) => "<task>".into(),
            Object::ParallelGroup(_) => "<parallel group>".into(),
            Object::ChannelSender(_) => "<channel sender>".into(),
            Object::ChannelReceiver(_) => "<channel receiver>".into(),
            Object::ChannelDetached(_) => "<detached endpoint>".into(),
            Object::MonotonicInstant { .. } => "<instant>".into(),
            Object::Closure { .. } | Object::BudgetClosure { .. } => "<function>".into(),
            Object::CpsClosure { .. } | Object::RetainedClosure { .. } => "<function>".into(),
            Object::CpsOperation(_)
            | Object::CpsContinuation { .. }
            | Object::CpsHandlers(_)
            | Object::CpsHandlerFrame(_)
            | Object::CpsResumption(_)
            | Object::CpsActivation(_)
            | Object::CpsScope { .. }
            | Object::CpsStep(_)
            | Object::CpsBudgetBoundary(_) => {
                return Err(RuntimeError::internal(
                    "internal continuation value escaped formatting",
                ));
            }
            Object::Iterator { .. } => {
                return Err(RuntimeError::internal("native iterator escaped"));
            }
            Object::Cell(value) => self.format_inner(*value, seen)?,
            Object::Range {
                lower,
                upper,
                inclusive,
            } => format!(
                "{}{}{}",
                lower
                    .map(|value| self.format_inner(value, seen))
                    .transpose()?
                    .unwrap_or_default(),
                if *inclusive { "..=" } else { ".." },
                upper
                    .map(|value| self.format_inner(value, seen))
                    .transpose()?
                    .unwrap_or_default()
            ),
        };
        seen.pop();
        Ok(result)
    }

    pub fn builtin(&mut self, name: &str, arguments: Handle) -> Result<Handle> {
        let name = name.strip_prefix("Prelude::").unwrap_or(name);
        let name = ril_runtime_api::builtins::canonical_builtin(name).unwrap_or(name);
        let args = self.sequence(arguments)?;
        if name.starts_with("\0ril.heap.") {
            return self.heap_transaction_builtin(name, &args);
        }
        if name.starts_with("Process::") {
            return self.process_builtin(name, &args);
        }
        if name.starts_with("Env::") {
            return self.environment_builtin(name, &args);
        }
        if name.starts_with("File::") {
            return self.file_builtin(name, &args);
        }
        if name.starts_with("Io::") || name.starts_with("__io_") {
            return self.io_builtin(name, &args);
        }
        if name.starts_with("Os::") {
            return self.native_builtin(name, &args);
        }
        if name.starts_with("Path::") {
            return self.path_builtin(name, &args);
        }
        if name.starts_with("Deque::") {
            return self.deque_builtin(name, &args);
        }
        if name.starts_with("Order::") {
            return self.order_builtin(name, &args);
        }
        if name.starts_with("Time::") || name.starts_with("Clock::") {
            return self.time_builtin(name, &args);
        }
        if name.starts_with("Random::") {
            return self.random_builtin(name, &args);
        }
        if name.starts_with("Math::") {
            return self.math(name, &args);
        }
        if name.starts_with("Num::") {
            return self.numeric_builtin(name, &args);
        }
        if name.starts_with("String::") {
            return self.string_builtin(name, &args);
        }
        if name.starts_with("Bytes::") || name.starts_with("Hex::") || name.starts_with("Binary::")
        {
            return self.encoding_builtin(name, &args);
        }
        if name.starts_with("Unicode::") {
            return self.unicode(name, &args);
        }
        if name.starts_with("Map::") || name.starts_with("Set::") {
            return self.collection_builtin(name, &args);
        }
        let arg = |i: usize| {
            args.get(i)
                .copied()
                .ok_or_else(|| RuntimeError::internal(format!("missing argument {i} to {name}")))
        };
        if name == "__iter_start" {
            return self.iterator(arg(0)?);
        }
        if name == "__iter_item" {
            let index = u64::try_from(self.as_integer(arg(1)?)?)
                .map_err(|_| RuntimeError::internal("invalid private iterator index"))?;
            return self.iterator_item(arg(0)?, index);
        }
        if name == "__iter_length" {
            let count = self.length(arg(0)?)?;
            return self.integer(i128::from(count), 64, false);
        }
        if name == "__iter_next" {
            let next = self.iterator_next(arg(0)?)?;
            return self.variant(
                if next.is_some() { "Some" } else { "None" },
                next.into_iter().collect(),
            );
        }
        if name == "__computed_field" {
            return self.computed_field(arg(0)?, arg(1)?);
        }
        if name == "__safe_field" {
            let field = self.as_string(arg(1)?)?.to_owned();
            return self.safe_field(arg(0)?, &field);
        }
        match name {
            "inner" => match self.heap.get(arg(0)?)? {
                Object::Nominal { payload, .. } => Ok(*payload),
                _ => Err(RuntimeError::internal("expected ordinary nominal wrapper")),
            },
            "assert" => {
                if !self.truth(arg(0)?)? {
                    return Err(RuntimeError::panic(if let Some(message) = args.get(1) {
                        self.format(*message)?
                    } else {
                        "assertion failed".into()
                    }));
                }
                self.unit()
            }
            "assert_eq" | "Test::assert_eq" => {
                if !self.heap.structurally_equal(arg(0)?, arg(1)?)? {
                    return Err(RuntimeError::panic(if let Some(message) = args.get(2) {
                        self.as_string(*message)?.to_owned()
                    } else {
                        "values differ".into()
                    }));
                }
                self.unit()
            }
            "assert_ne" | "Test::assert_ne" => {
                if self.heap.structurally_equal(arg(0)?, arg(1)?)? {
                    return Err(RuntimeError::panic(if let Some(message) = args.get(2) {
                        self.as_string(*message)?.to_owned()
                    } else {
                        "values are equal".into()
                    }));
                }
                self.unit()
            }
            "Test::assert_some" | "Test::assert_ok" => {
                let expected = if name == "Test::assert_some" {
                    "Some"
                } else {
                    "Ok"
                };
                if let Object::Variant { tag, fields } = self.heap.get(arg(0)?)?
                    && tag == expected
                    && fields.len() == 1
                {
                    return Ok(fields[0]);
                }
                Err(RuntimeError::panic(if let Some(message) = args.get(1) {
                    self.as_string(*message)?.to_owned()
                } else {
                    format!("expected {expected}")
                }))
            }
            "panic" => Err(RuntimeError::panic(self.format(arg(0)?)?)),
            "len" => {
                let count = self.length(arg(0)?)?;
                self.int(i128::from(count))
            }
            "clone" => {
                if let Some(value) = self.clone_channel_sender(arg(0)?)? {
                    Ok(value)
                } else {
                    self.copy(arg(0)?)
                }
            }
            "clone_immut" => self.copy(arg(0)?),
            "print" | "println" => {
                let request = crate::host_stdio::prepare(self, name, &args)?;
                crate::host_stdio::finish(self, request.perform()?)
            }
            "Array::push" => {
                self.append(arg(0)?, arg(1)?)?;
                self.unit()
            }
            "Array::pop" => {
                let value = match self.heap.get_mut(arg(0)?)? {
                    Object::Array(values) => values.pop(),
                    _ => return Err(RuntimeError::internal("expected array")),
                };
                self.variant(
                    if value.is_some() { "Some" } else { "None" },
                    value.into_iter().collect(),
                )
            }
            "Array::truncate" => {
                let length = usize::try_from(self.as_integer(arg(1)?)?)
                    .map_err(|_| RuntimeError::panic("negative length"))?;
                match self.heap.get_mut(arg(0)?)? {
                    Object::Array(values) => values.truncate(length),
                    _ => return Err(RuntimeError::internal("expected array")),
                };
                self.unit()
            }
            "Array::insert" => {
                let index = usize::try_from(self.as_integer(arg(1)?)?)
                    .map_err(|_| RuntimeError::panic("invalid index"))?;
                match self.heap.get_mut(arg(0)?)? {
                    Object::Array(values) if index <= values.len() => values.insert(index, arg(2)?),
                    _ => return Err(RuntimeError::panic("index out of bounds")),
                };
                self.unit()
            }
            "Array::remove" => {
                let index = usize::try_from(self.as_integer(arg(1)?)?)
                    .map_err(|_| RuntimeError::panic("invalid index"))?;
                match self.heap.get_mut(arg(0)?)? {
                    Object::Array(values) if index < values.len() => Ok(values.remove(index)),
                    _ => Err(RuntimeError::panic("index out of bounds")),
                }
            }
            "Array::reverse" => {
                let mut values = self.sequence(arg(0)?)?;
                values.reverse();
                self.allocate(Object::Array(values))
            }
            "Array::first" => {
                let values = self.sequence(arg(0)?)?;
                self.variant(
                    if values.is_empty() { "None" } else { "Some" },
                    values.first().copied().into_iter().collect(),
                )
            }
            "Array::concat" => {
                let mut values = self.sequence(arg(0)?)?;
                values.extend(self.sequence(arg(1)?)?);
                self.allocate(Object::Array(values))
            }
            "Array::contains" => {
                let values = self.sequence(arg(0)?)?;
                let expected = arg(1)?;
                let mut found = false;
                for value in values {
                    if self.heap.structurally_equal(value, expected)? {
                        found = true;
                        break;
                    }
                }
                self.boolean(found)
            }
            "Array::clear" => {
                match self.heap.get_mut(arg(0)?)? {
                    Object::Array(values) => values.clear(),
                    _ => return Err(RuntimeError::internal("expected array")),
                };
                self.unit()
            }
            "Array::get" => self.index(arg(0)?, arg(1)?, true),
            "Array::set" => {
                self.set_index(arg(0)?, arg(1)?, arg(2)?)?;
                self.unit()
            }
            "None" => self.variant(name, vec![]),
            "Some" | "Ok" | "Err" => {
                let payload = match args.as_slice() {
                    [] => self.unit()?,
                    [value] => *value,
                    _ => self.allocate(Object::Tuple(args))?,
                };
                self.variant(name, vec![payload])
            }
            "__option_unwrap" => match self.heap.get(arg(0)?)? {
                Object::Variant { tag, fields } if tag == "Some" && fields.len() == 1 => {
                    Ok(fields[0])
                }
                _ => Err(RuntimeError::internal(
                    "verified optional refinement was not satisfied",
                )),
            },
            "__variant_payload" => match self.heap.get(arg(0)?)? {
                Object::Variant { tag, fields }
                    if matches!(tag.as_str(), "Some" | "Ok") && fields.len() == 1 =>
                {
                    Ok(fields[0])
                }
                _ => Err(RuntimeError::internal(
                    "verified propagation receiver was not successful",
                )),
            },
            "__unwrap_tag" => {
                let expected = self.as_string(arg(1)?)?;
                let expected = expected.strip_prefix("Prelude::").unwrap_or(expected);
                match self.heap.get(arg(0)?)? {
                    Object::Variant { tag, fields }
                        if tag.strip_prefix("Prelude::").unwrap_or(tag) == expected
                            && fields.len() == 1 =>
                    {
                        Ok(fields[0])
                    }
                    Object::Nominal { tag, payload } if tag == expected => Ok(*payload),
                    _ => Err(RuntimeError::internal(
                        "verified tag refinement was not satisfied",
                    )),
                }
            }
            "__format" => {
                let text = self.format(arg(0)?)?;
                self.string(text)
            }
            "StringBuilder::new" => self.allocate(Object::StringBuilder(String::new())),
            "StringBuilder::append" => {
                let text = self.as_string(arg(1)?)?.to_owned();
                match self.heap.get_mut(arg(0)?)? {
                    Object::StringBuilder(buffer) => buffer.push_str(&text),
                    _ => return Err(RuntimeError::internal("expected string builder")),
                };
                self.unit()
            }
            "StringBuilder::clear" => {
                match self.heap.get_mut(arg(0)?)? {
                    Object::StringBuilder(buffer) => buffer.clear(),
                    _ => return Err(RuntimeError::internal("expected string builder")),
                };
                self.unit()
            }
            "StringBuilder::to_string" => {
                let text = match self.heap.get(arg(0)?)? {
                    Object::StringBuilder(buffer) => buffer.clone(),
                    _ => return Err(RuntimeError::internal("expected string builder")),
                };
                self.string(text)
            }
            "StringBuilder::append_scalar" => {
                let scalar = self.as_integer(arg(1)?)?;
                if let Some(value) = u32::try_from(scalar).ok().and_then(char::from_u32) {
                    match self.heap.get_mut(arg(0)?)? {
                        Object::StringBuilder(buffer) => buffer.push(value),
                        _ => return Err(RuntimeError::internal("expected string builder")),
                    };
                    let unit = self.unit()?;
                    self.variant("Ok", vec![unit])
                } else {
                    let error =
                        self.allocate(Object::Record([("value".into(), arg(1)?)].into()))?;
                    self.variant("Err", vec![error])
                }
            }
            "__format_spec" => {
                let value = self.heap.get(arg(0)?)?;
                let specification = self.as_string(arg(1)?)?;
                let text = crate::formatting::format(value, specification)?;
                self.string(text)
            }
            "Crypto::sha256" | "Crypto::sha256_bytes" => {
                use sha2::{Digest, Sha256};
                let bytes = if name.ends_with("_bytes") {
                    match self.heap.get(arg(0)?)? {
                        Object::Bytes(bytes) => bytes.as_slice(),
                        _ => return Err(RuntimeError::internal("expected bytes")),
                    }
                } else {
                    self.as_string(arg(0)?)?.as_bytes()
                };
                let digest = Sha256::digest(bytes);
                self.allocate(Object::Bytes(digest.to_vec().into()))
            }
            _ => Err(RuntimeError::internal(format!(
                "runtime builtin {name} has no implementation"
            ))),
        }
    }

    fn math(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let operation = name
            .trim_start_matches("Math::")
            .strip_suffix("_f32")
            .unwrap_or(name.trim_start_matches("Math::"));
        let bits = if name.ends_with("_f32") { 32 } else { 64 };
        let number = |index: usize| -> Result<f64> {
            match args
                .get(index)
                .and_then(|handle| self.heap.get(*handle).ok())
            {
                Some(Object::Float {
                    value,
                    bits: actual,
                }) if *actual == bits => Ok(*value),
                _ => Err(RuntimeError::internal("invalid Math argument")),
            }
        };
        let first = number(0)?;
        if operation == "is_nan" {
            return self.boolean(first.is_nan());
        }
        if operation == "is_finite" {
            return self.boolean(first.is_finite());
        }
        let value = match operation {
            "sqrt" => {
                if bits == 32 {
                    f64::from((first as f32).sqrt())
                } else {
                    first.sqrt()
                }
            }
            "floor" => first.floor(),
            "ceil" => first.ceil(),
            "round" => first.round_ties_even(),
            "abs" => first.abs(),
            "min" | "max" => {
                let second = number(1)?;
                if first.is_nan() || second.is_nan() {
                    f64::NAN
                } else if first == 0.0 && second == 0.0 {
                    if operation == "min" {
                        if first.is_sign_negative() || second.is_sign_negative() {
                            -0.0
                        } else {
                            0.0
                        }
                    } else if first.is_sign_positive() || second.is_sign_positive() {
                        0.0
                    } else {
                        -0.0
                    }
                } else if operation == "min" {
                    first.min(second)
                } else {
                    first.max(second)
                }
            }
            _ => return Err(RuntimeError::internal("unknown Math operation")),
        };
        self.float(value, bits)
    }
    fn unicode(&mut self, name: &str, args: &[Handle]) -> Result<Handle> {
        let first = args
            .first()
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing Unicode argument"))?;
        match name {
            "Unicode::decode_utf8" => {
                let bytes = match self.heap.get(first)? {
                    Object::Bytes(bytes) => bytes,
                    _ => return Err(RuntimeError::internal("expected UTF-8 byte input")),
                };
                match std::str::from_utf8(bytes) {
                    Ok(text) => {
                        let text = self.string(text.to_owned())?;
                        self.variant("Ok", vec![text])
                    }
                    Err(error) => {
                        let offset = self.int(error.valid_up_to() as i128)?;
                        let error =
                            self.allocate(Object::Record([("offset".into(), offset)].into()))?;
                        self.variant("Err", vec![error])
                    }
                }
            }
            "Unicode::from_scalar" => {
                let scalar = self.as_integer(first)?;
                if let Some(value) = u32::try_from(scalar).ok().and_then(char::from_u32) {
                    let text = self.string(value.to_string())?;
                    self.variant("Ok", vec![text])
                } else {
                    let error = self.allocate(Object::Record([("value".into(), first)].into()))?;
                    self.variant("Err", vec![error])
                }
            }
            "Unicode::lowercase" | "Unicode::uppercase" => {
                let text = self.as_string(first)?;
                let text = if name.ends_with("lowercase") {
                    crate::unicode::lowercase(text)
                } else {
                    crate::unicode::uppercase(text)
                };
                self.string(text)
            }
            _ => {
                let scalar = u32::try_from(self.as_integer(first)?).unwrap_or(u32::MAX);
                let property = match name {
                    "Unicode::is_white_space" => crate::unicode::is_white_space(scalar),
                    "Unicode::is_alphabetic" => crate::unicode::is_alphabetic(scalar),
                    "Unicode::is_decimal_digit" => crate::unicode::is_decimal_digit(scalar),
                    "Unicode::is_xid_start" => crate::unicode::is_xid_start(scalar),
                    "Unicode::is_xid_continue" => crate::unicode::is_xid_continue(scalar),
                    _ => return Err(RuntimeError::internal("unknown Unicode operation")),
                };
                self.boolean(property)
            }
        }
    }
}

fn integer_fits(value: i128, bits: u8, signed: bool) -> bool {
    if signed {
        let bound = 1i128 << (bits - 1);
        value >= -bound && value < bound
    } else {
        value >= 0 && value < (1i128 << bits)
    }
}
fn wrap_integer(value: i128, bits: u8, signed: bool) -> i128 {
    let modulus = 1i128 << bits;
    let value = value & (modulus - 1);
    if signed && value & (1i128 << (bits - 1)) != 0 {
        value - modulus
    } else {
        value
    }
}
fn canonical_f64(value: f64) -> f64 {
    if value.is_nan() {
        f64::from_bits(0x7ff8_0000_0000_0000)
    } else {
        value
    }
}
fn canonical_f32(value: f32) -> f32 {
    if value.is_nan() {
        f32::from_bits(0x7fc0_0000)
    } else {
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn numeric_panics_are_explicit_and_fixed_width_operations_are_checked() {
        let mut runtime = Runtime::default();
        let max = runtime.integer(127, 8, true).unwrap();
        let one = runtime.integer(1, 8, true).unwrap();
        assert_eq!(
            runtime.binary(BinaryOp::Add, max, one).unwrap_err().tag,
            OutcomeTag::LanguagePanic
        );
        let wrapped = runtime.binary(BinaryOp::WrappingAdd, max, one).unwrap();
        assert_eq!(runtime.as_integer(wrapped).unwrap(), -128);
        let zero = runtime.integer(0, 8, true).unwrap();
        assert_eq!(
            runtime
                .binary(BinaryOp::Divide, one, zero)
                .unwrap_err()
                .message,
            "division by zero"
        );
    }
    #[test]
    fn rooted_references_and_return_values_survive_collection() {
        let mut runtime = Runtime::default();
        runtime.enter();
        let value = runtime.int(42).unwrap();
        runtime.root(0, value).unwrap();
        runtime.statement_end();
        runtime.collect().unwrap();
        assert_eq!(runtime.as_integer(value).unwrap(), 42);
        runtime.leave(value);
        runtime.collect().unwrap();
        assert_eq!(runtime.as_integer(value).unwrap(), 42);
        runtime.statement_end();
        runtime.collect().unwrap();
        assert!(runtime.heap.get(value).is_err());
    }
}
