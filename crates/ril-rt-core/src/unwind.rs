use crate::{GcRuntime, Object, Value};

#[derive(Default)]
#[repr(C)]
pub struct Runtime {
    pub unwinding: u8,
    pub gc: GcRuntime,
    message: Option<String>,
}

impl Runtime {
    pub fn raise(&mut self, message: impl Into<String>) {
        if self.unwinding != 0 {
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
