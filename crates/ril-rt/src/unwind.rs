use crate::{GcRuntime, Object, Value, gc::RootFrameHeader};

pub(crate) const UNWIND_NONE: u8 = 0;
pub(crate) const UNWIND_PANIC: u8 = 1;
pub(crate) const UNWIND_ABORT: u8 = 2;

#[derive(Default)]
pub(crate) enum UnwindState {
    #[default]
    None,
    Panic(String),
    #[cfg_attr(miri, allow(dead_code))]
    Abort,
}

#[derive(Default)]
#[repr(C)]
pub struct Runtime {
    pub unwinding: u8,
    pub gc: GcRuntime,
    unwind_state: UnwindState,
    suspended: Vec<UnwindState>,
    pub(crate) ctl: crate::ctl::State,
}

const _: () = {
    assert!(std::mem::offset_of!(Runtime, unwinding) == 0);
    assert!(std::mem::offset_of!(Runtime, gc) == 8);
    assert!(std::mem::offset_of!(GcRuntime, top_frame) == 0);
    assert!(std::mem::offset_of!(RootFrameHeader, prev) == 0);
    assert!(std::mem::offset_of!(RootFrameHeader, count) == 8);
    assert!(std::mem::size_of::<RootFrameHeader>() == 16);
};

impl Runtime {
    pub fn raise(&mut self, message: impl Into<String>) {
        if matches!(self.unwind_state, UnwindState::Panic(_))
            || self
                .suspended
                .iter()
                .any(|state| matches!(state, UnwindState::Panic(_)))
        {
            eprintln!("[RIL_RT_ABORT:DOUBLE_PANIC]");
            std::process::abort();
        }
        self.unwind_state = UnwindState::Panic(message.into());
        self.unwinding = UNWIND_PANIC;
    }

    #[cfg_attr(miri, allow(dead_code))]
    pub(crate) fn begin_abort(&mut self) {
        self.unwind_state = UnwindState::Abort;
        self.unwinding = UNWIND_ABORT;
    }

    pub fn take_panic(&mut self) -> Option<String> {
        if matches!(self.unwind_state, UnwindState::Panic(_)) {
            self.unwinding = UNWIND_NONE;
            match std::mem::replace(&mut self.unwind_state, UnwindState::None) {
                UnwindState::Panic(msg) => Some(msg),
                _ => None,
            }
        } else {
            None
        }
    }

    pub(crate) fn take_unwind(&mut self) -> UnwindState {
        self.unwinding = UNWIND_NONE;
        std::mem::replace(&mut self.unwind_state, UnwindState::None)
    }

    pub(crate) fn enter_cleanup(&mut self) {
        let pending = self.take_unwind();
        self.suspended.push(pending);
    }

    pub(crate) fn leave_cleanup(&mut self) {
        if let Some(pending) = self.suspended.pop()
            && self.unwinding == UNWIND_NONE
        {
            match pending {
                UnwindState::None => {}
                UnwindState::Panic(msg) => {
                    self.unwind_state = UnwindState::Panic(msg);
                    self.unwinding = UNWIND_PANIC;
                }
                UnwindState::Abort => {
                    self.unwind_state = UnwindState::Abort;
                    self.unwinding = UNWIND_ABORT;
                }
            }
        }
    }

    pub fn finish(&mut self, value: Value) -> i32 {
        if let Some(message) = self.take_panic() {
            eprintln!("[RIL_RT_PANIC] {message}");
            return 1;
        }
        match self.gc.object(value) {
            Some(Object::Tag(tag, values)) if tag == "Err" => {
                let message = values
                    .first()
                    .and_then(|&v| match self.gc.object(v) {
                        Some(Object::Str(msg)) => Some(msg.as_str()),
                        _ => None,
                    })
                    .unwrap_or("invalid error result");
                eprintln!("{message}");
                1
            }
            _ => 0,
        }
    }

    pub(crate) fn checked(&mut self, result: Result<Value, &'static str>) -> Value {
        match result {
            Ok(value) => value,
            Err(message) => {
                self.raise(message);
                Value::UNIT
            }
        }
    }
}
