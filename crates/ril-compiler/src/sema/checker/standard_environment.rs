//! Environmental snapshots have fresh immutable storage and retain no authority.
use super::*;
pub(super) fn is_environment_builtin(name: &str) -> bool {
    matches!(
        name,
        "Env::args" | "Env::get" | "Env::all" | "Env::current_dir" | "Env::temp_dir"
    )
}
impl Checker {
    pub(super) fn standard_environment_builtin(
        &mut self,
        name: &str,
        args: &[(ParameterMode, Value, Span)],
        span: Span,
        frame: &mut Frame,
    ) -> Option<Value> {
        if !is_environment_builtin(name) {
            return None;
        }
        let native = Ty::Named("Os::NativeString".into());
        let inputs = if name == "Env::get" {
            vec![native.clone()]
        } else {
            vec![]
        };
        self.standard_arguments(name, args, &inputs, inputs.len(), span);
        frame.obligations.effects.insert("Fiber".into());
        frame.obligations.concrete_effects.insert("Fiber".into());
        Some(match name {
            "Env::args" | "Env::all" => {
                let element = if name == "Env::args" {
                    native.clone()
                } else {
                    Ty::Tuple(vec![native.clone(), native])
                };
                let mut snapshot = self.standard_array(element, span, frame.owner);
                snapshot.permission = Permission::Read;
                snapshot.publication = Publication::Immutable;
                snapshot.construction = false;
                snapshot
            }
            "Env::get" => self.standard_result(
                Ty::Optional(Box::new(native)),
                file::io_error(),
                span,
                frame.owner,
            ),
            _ => self.standard_result(
                Ty::Named("Path::Path".into()),
                file::io_error(),
                span,
                frame.owner,
            ),
        })
    }
}
