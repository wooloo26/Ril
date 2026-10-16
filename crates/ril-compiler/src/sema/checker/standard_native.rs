//! Native strings and paths are immutable target value data. Source permissions
//! are consumed for conversion reads and never lent to the produced snapshot.
use super::*;

pub(super) fn native_constant(name: &str) -> Option<Ty> {
    let ty = match name {
        "Os::NativeError::InvalidEncoding" | "Os::NativeError::WrongPlatform" => "Os::NativeError",
        "Os::Platform::Windows" | "Os::Platform::Posix" => "Os::Platform",
        _ => return None,
    };
    Some(Ty::Named(ty.into()))
}
fn native_signature(name: &str) -> Option<Signature> {
    use Output::*;
    let native = Ty::Named("Os::NativeString".into());
    let path = Ty::Named("Path::Path".into());
    let error = Ty::Named("Os::NativeError".into());
    let ordering = Ty::Named("Order::Ordering".into());
    Some(match name {
        "Os::platform" => signature(vec![], Value(Ty::Named("Os::Platform".into()))),
        "Os::from_string" => signature(vec![Ty::Str], Value(native)),
        "Os::to_string" => signature(vec![native], Result(Ty::Str, error)),
        "Os::from_posix_bytes" => signature(vec![Ty::Bytes], Result(native, error)),
        "Os::posix_bytes" => signature(vec![native], Result(Ty::Bytes, error)),
        "Os::from_windows_units" => Signature {
            inputs: vec![Ty::Array(Box::new(integer("u16")))],
            minimum: 1,
            output: Result(native, error),
            deep: true,
        },
        "Os::windows_units" => signature(
            vec![native],
            Result(Ty::Array(Box::new(integer("u16"))), error),
        ),
        "Os::compare" => signature(vec![native.clone(), native], Value(ordering)),
        "Path::from_string" => signature(vec![Ty::Str], Value(path)),
        "Path::from_native" => signature(vec![native], Value(path)),
        "Path::native" => signature(vec![path], Value(native)),
        "Path::to_string" => signature(vec![path], Result(Ty::Str, error)),
        "Path::join" => signature(vec![path.clone(), path.clone()], Value(path)),
        "Path::parent" => signature(vec![path.clone()], Optional(path)),
        "Path::file_name" | "Path::extension" => signature(vec![path], Optional(native)),
        "Path::is_absolute" => signature(vec![path], Value(Ty::Bool)),
        "Path::normalize_lexical" => signature(vec![path.clone()], Value(path)),
        "Path::compare" => signature(vec![path.clone(), path], Value(ordering)),
        _ => return None,
    })
}
pub(super) fn is_native_builtin(name: &str) -> bool {
    native_signature(name).is_some()
}

impl Checker {
    pub(super) fn standard_native_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        let signature = native_signature(name)?;
        self.standard_arguments(name, args, &signature.inputs, signature.minimum, span);
        for (_, value, argument_span) in args {
            if signature.deep {
                self.deep_read(value, *argument_span, frame);
            } else if !value.ty.scalar() {
                self.access(value, None, Mode::Read, *argument_span, frame);
            }
        }
        Some(match signature.output {
            Output::Value(ty) => self.standard_value(ty, span, frame.owner, 0),
            Output::Optional(ty) => {
                let payload = self.standard_value(ty, span, frame.owner, 0);
                self.standard_option(payload, None, span, frame.owner)
            }
            Output::Result(ok, error) if name == "Os::windows_units" => {
                let Ty::Array(element) = ok.clone() else {
                    unreachable!()
                };
                let mut payload = self.standard_array(*element, span, frame.owner);
                payload.permission = Permission::Read;
                payload.publication = Publication::Immutable;
                payload.construction = false;
                let mut value = self.make_result(true, payload, span, frame.owner);
                value.result_error = Some(Box::new(self.standard_value(
                    error.clone(),
                    span,
                    frame.owner,
                    2,
                )));
                value.ty = Ty::Result(Box::new(ok), Box::new(error));
                value.result_tag = None;
                value.result_payload = None;
                value
            }
            Output::Result(ok, error) => self.standard_result(ok, error, span, frame.owner),
            Output::Array(_) => unreachable!(),
        })
    }
}
