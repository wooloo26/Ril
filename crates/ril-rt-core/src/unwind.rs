use crate::{GcRuntime, Object, Value};

#[derive(Default)]
#[repr(C)]
pub struct Runtime {
    pub unwinding: u8,
    pub gc: GcRuntime,
    message: Option<String>,
    suspended: Vec<Option<String>>,
}

impl Runtime {
    pub fn raise(&mut self, message: impl Into<String>) {
        if self.unwinding != 0 || self.suspended.iter().any(Option::is_some) {
            eprintln!("[RIL_RT_ABORT:DOUBLE_PANIC]");
            std::process::abort();
        }
        self.message = Some(message.into());
        self.unwinding = 1;
    }

    pub fn take_panic(&mut self) -> Option<String> {
        self.unwinding = 0;
        self.message.take()
    }

    pub(crate) fn enter_cleanup(&mut self) {
        let pending = self.take_panic();
        self.suspended.push(pending);
    }

    pub(crate) fn leave_cleanup(&mut self) {
        if let Some(Some(pending)) = self.suspended.pop() {
            self.message = Some(pending);
            self.unwinding = 1;
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
