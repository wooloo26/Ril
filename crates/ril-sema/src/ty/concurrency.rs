use std::{
    collections::{BTreeMap, HashSet},
    sync::Arc,
};

use ril_hir::{DefinitionId, StdType};
use ril_source::{diag::Code, span::Span};
use ril_syntax::syntax::{Argument, Mode};

use super::{
    Callable, Member, MemberMode, Parameter, Ty,
    check::{Checker, Env, Phase, unknown_callable},
};

pub(super) fn channel_pair(item: Ty) -> Ty {
    let mode = MemberMode {
        variable: false,
        mode: Mode::Mut,
    };
    Ty::Record(
        BTreeMap::from([
            (
                "tx".into(),
                Member {
                    mode,
                    ty: Ty::Sender(Box::new(item.clone())),
                },
            ),
            (
                "rx".into(),
                Member {
                    mode,
                    ty: Ty::Receiver(Box::new(item)),
                },
            ),
        ]),
        false,
    )
}

impl Checker<'_> {
    pub(super) fn concurrent_call(
        &mut self,
        env: &mut Env,
        module: &str,
        name: &str,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        if env.phase != Phase::Runtime && !env.shadow {
            self.error(
                Code::E0810,
                span,
                "structured concurrency is a runtime call family",
            );
        }
        if module == "Fiber" {
            self.fiber(env, name, args, expected, span)
        } else {
            self.channel(env, name, args, expected, span)
        }
    }

    fn fiber(
        &mut self,
        env: &mut Env,
        name: &str,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        match (name, args) {
            ("run" | "uncancellable" | "supervise", [action]) => {
                let target = if name == "supervise" {
                    expected.and_then(|ty| match ty {
                        Ty::Result(ok, _) => Some(ok.as_ref()),
                        _ => None,
                    })
                } else {
                    expected
                };
                let result = self.callback(env, action, None, target, true);
                if matches!(name, "run" | "supervise")
                    && !self.is_sendable(env, &result, &mut HashSet::new())
                {
                    self.error(Code::E0301, span, "fiber result is not Sendable");
                }
                if name == "supervise" {
                    self.reject_nested_result(&result, span);
                    Ty::Result(
                        Box::new(result),
                        Box::new(self.std_adt(StdType::TaskFault, Vec::new())),
                    )
                } else {
                    result
                }
            }
            ("scope" | "try_scope", [body]) => {
                let result = self.callback(env, body, Some((Mode::Mut, Ty::Scope)), expected, true);
                if name == "try_scope"
                    && !matches!(
                        self.normalize(&result),
                        Ty::Result(..) | Ty::Unknown | Ty::Infer(_) | Ty::Never
                    )
                {
                    self.error(Code::E0301, span, "try_scope body must return Result");
                }
                result
            }
            ("spawn", [scope, work]) => {
                self.require_marker(scope, Mode::Mut, env);
                self.expect(env, scope.value, &Ty::Scope);
                let result = self.callback(env, work, None, None, true);
                if !self.is_sendable(env, &result, &mut HashSet::new()) {
                    self.error(Code::E0301, span, "task result is not Sendable");
                }
                Ty::Task(Box::new(result))
            }
            ("join" | "cancel", [scope, task]) => {
                self.require_marker(scope, Mode::Mut, env);
                self.expect(env, scope.value, &Ty::Scope);
                if name == "cancel" {
                    self.require_marker(task, Mode::New, env);
                }
                let task = self.expr(env, task.value, None);
                if let Ty::Task(output) = task {
                    if name == "cancel" {
                        Ty::Option(output)
                    } else {
                        *output
                    }
                } else {
                    self.error(Code::E0301, span, "expected a task handle");
                    Ty::Unknown
                }
            }
            ("cancel_scope", [scope]) => {
                self.require_marker(scope, Mode::Mut, env);
                self.expect(env, scope.value, &Ty::Scope);
                Ty::Unit
            }
            ("yield_now", []) => Ty::Unit,
            ("is_cancelled", []) => Ty::Bool,
            ("sleep_ms", [duration]) => {
                self.expect(env, duration.value, &Ty::Int);
                Ty::Unit
            }
            ("timeout_ms", [duration, work]) => {
                self.expect(env, duration.value, &Ty::Int);
                let result = self.callback(env, work, None, None, true);
                if !self.is_sendable(env, &result, &mut HashSet::new()) {
                    self.error(Code::E0301, span, "timeout_ms result is not Sendable");
                }
                self.reject_nested_result(&result, span);
                Ty::Result(
                    Box::new(result),
                    Box::new(self.std_adt(StdType::TimeoutError, Vec::new())),
                )
            }
            ("zip" | "try_zip" | "race", [left, right]) => {
                let a = self.callback(env, left, None, None, true);
                let b = self.callback(env, right, None, None, true);
                if name == "race" {
                    if !self.is_sendable(env, &a, &mut HashSet::new())
                        || !self.is_sendable(env, &b, &mut HashSet::new())
                    {
                        self.error(Code::E0301, span, "race result is not Sendable");
                    }
                    self.reject_nested_result(&a, span);
                    self.reject_nested_result(&b, span);
                    self.join(env, span, a, b)
                } else {
                    let record = |a, b| {
                        Ty::Record(
                            BTreeMap::from([
                                ("first".into(), Member::plain(a)),
                                ("second".into(), Member::plain(b)),
                            ]),
                            false,
                        )
                    };
                    if name == "try_zip" {
                        if let (Ty::Result(a, e), Ty::Result(b, f)) = (a, b) {
                            if !self.is_sendable(env, &a, &mut HashSet::new())
                                || !self.is_sendable(env, &b, &mut HashSet::new())
                                || !self.is_sendable(env, &e, &mut HashSet::new())
                                || !self.is_sendable(env, &f, &mut HashSet::new())
                            {
                                self.error(Code::E0301, span, "try_zip result is not Sendable");
                            }
                            self.reject_nested_result(&a, span);
                            self.reject_nested_result(&b, span);
                            let err = self.join(env, span, *e, *f);
                            Ty::Result(Box::new(record(*a, *b)), Box::new(err))
                        } else {
                            self.error(Code::E0301, span, "try_zip actions must return Result");
                            Ty::Unknown
                        }
                    } else {
                        if !self.is_sendable(env, &a, &mut HashSet::new())
                            || !self.is_sendable(env, &b, &mut HashSet::new())
                        {
                            self.error(Code::E0301, span, "zip result is not Sendable");
                        }
                        self.reject_nested_result(&a, span);
                        self.reject_nested_result(&b, span);
                        record(a, b)
                    }
                }
            }
            ("map" | "try_map", [items, work]) => {
                let item = self.fresh();
                self.expect(
                    env,
                    items.value,
                    &Ty::Array(Box::new(Member::plain(item.clone()))),
                );
                let item = self.normalize(&item);
                if !self.is_sendable(env, &item, &mut HashSet::new()) {
                    self.error(
                        Code::E0301,
                        span,
                        "Fiber::map input element is not Sendable",
                    );
                }
                let result = self.callback(env, work, Some((Mode::Plain, item)), None, false);
                let array = |ty| Ty::Array(Box::new(Member::plain(ty)));
                if name == "try_map" {
                    if let Ty::Result(ok, err) = result {
                        if !self.is_sendable(env, &ok, &mut HashSet::new())
                            || !self.is_sendable(env, &err, &mut HashSet::new())
                        {
                            self.error(Code::E0301, span, "try_map result is not Sendable");
                        }
                        self.reject_nested_result(&ok, span);
                        Ty::Result(Box::new(array(*ok)), err)
                    } else {
                        self.error(Code::E0301, span, "try_map action must return Result");
                        Ty::Unknown
                    }
                } else {
                    if !self.is_sendable(env, &result, &mut HashSet::new()) {
                        self.error(Code::E0301, span, "map result is not Sendable");
                    }
                    self.reject_nested_result(&result, span);
                    array(result)
                }
            }
            _ => {
                self.error(
                    Code::E0314,
                    span,
                    format!("incorrect Fiber::{name} arguments"),
                );
                Ty::Unknown
            }
        }
    }

    fn channel(
        &mut self,
        env: &mut Env,
        name: &str,
        args: &[Argument],
        expected: Option<&Ty>,
        span: Span,
    ) -> Ty {
        let item = |typed: &Ty| match typed {
            Ty::Sender(t) | Ty::Receiver(t) => (**t).clone(),
            _ => Ty::Unknown,
        };
        match (name, args) {
            ("bounded", [capacity]) => {
                self.expect(env, capacity.value, &Ty::Int);
                if let Some(value) = self.eval_root(env, capacity.value, false)
                    && matches!(value, super::Value::Int(n) if num_traits::Signed::is_negative(&n))
                {
                    self.error(
                        Code::E0815,
                        self.ast(env.file).expr(capacity.value).span,
                        "negative static channel capacity",
                    );
                }
                self.channel_shape(expected)
            }
            ("unbounded", []) => self.channel_shape(expected),
            ("clone", [channel]) => {
                self.require_marker(channel, Mode::Ref, env);
                let ty = self.expr(env, channel.value, None);
                if !matches!(ty, Ty::Sender(_)) {
                    self.error(Code::E0301, span, "only a sender can be cloned");
                }
                ty
            }
            ("send" | "try_send", [sender, value]) => {
                self.require_marker(sender, Mode::Mut, env);
                let sender = self.expr(env, sender.value, None);
                if !matches!(sender, Ty::Sender(_)) {
                    self.error(Code::E0301, span, "send requires a channel sender");
                }
                let item = self.expect(env, value.value, &item(&sender));
                if !self.is_sendable(env, &item, &mut HashSet::new()) {
                    self.error(Code::E0301, span, "channel item is not Sendable");
                }
                let error = if name == "send" {
                    StdType::SendError
                } else {
                    StdType::TrySendError
                };
                Ty::Result(
                    Box::new(Ty::Unit),
                    Box::new(self.std_adt(
                        error,
                        vec![super::GenericValue::Type(self.normalize(&item))],
                    )),
                )
            }
            ("recv" | "try_recv", [receiver]) => {
                self.require_marker(receiver, Mode::Mut, env);
                let ty = self.expr(env, receiver.value, None);
                if !matches!(ty, Ty::Receiver(_)) {
                    self.error(Code::E0301, span, "recv requires a channel receiver");
                }
                if name == "recv" {
                    Ty::Option(Box::new(item(&ty)))
                } else {
                    Ty::Result(
                        Box::new(item(&ty)),
                        Box::new(self.std_adt(StdType::TryRecvError, Vec::new())),
                    )
                }
            }
            ("close" | "close_recv", [endpoint]) => {
                self.require_marker(endpoint, Mode::New, env);
                let ty = self.expr(env, endpoint.value, None);
                if !matches!(
                    (name, &ty),
                    ("close", Ty::Sender(_)) | ("close_recv", Ty::Receiver(_))
                ) {
                    self.error(Code::E0301, span, "wrong endpoint for channel close");
                }
                if name == "close_recv" {
                    self.reject_nested_result(&item(&ty), span);
                }
                Ty::Unit
            }
            ("drain", [endpoint, consumer]) => {
                self.require_marker(endpoint, Mode::New, env);
                let ty = self.expr(env, endpoint.value, None);
                if !matches!(
                    self.normalize(&ty),
                    Ty::Receiver(_) | Ty::Unknown | Ty::Infer(_)
                ) {
                    self.error(Code::E0301, span, "drain requires a channel receiver");
                }
                self.callback(
                    env,
                    consumer,
                    Some((Mode::Via, item(&ty))),
                    Some(&Ty::Unit),
                    true,
                );
                Ty::Unit
            }
            _ => {
                self.error(
                    Code::E0314,
                    span,
                    format!("incorrect Channel::{name} arguments"),
                );
                Ty::Unknown
            }
        }
    }

    fn channel_shape(&mut self, expected: Option<&Ty>) -> Ty {
        if let Some(expected @ Ty::Record(..)) = expected {
            expected.clone()
        } else {
            channel_pair(self.fresh())
        }
    }

    fn callback(
        &mut self,
        env: &mut Env,
        arg: &Argument,
        param: Option<(Mode, Ty)>,
        result: Option<&Ty>,
        allow_state: bool,
    ) -> Ty {
        let expected = Ty::Callable(Arc::new(Callable {
            open_effects: true,
            open_state: allow_state,
            result_mode: Mode::Infer,
            result: result.cloned().unwrap_or(Ty::Unknown),
            parameters: param
                .into_iter()
                .map(|(mode, ty)| Parameter {
                    label: None,
                    mode,
                    ty,
                    optional: false,
                    is_meta: false,
                })
                .collect(),
            ..unknown_callable()
        }));
        let ty = self.expr(env, arg.value, Some(&expected));
        if let Ty::Callable(sig) = ty {
            let Ty::Callable(expect) = &expected else {
                ril_source::ice!("callback expected type is not callable");
            };
            if sig.parameters.len() != expect.parameters.len() {
                self.error(
                    Code::E0314,
                    self.ast(env.file).expr(arg.value).span,
                    "incorrect callback arity",
                );
            } else if !allow_state && (sig.open_state || !sig.state.is_empty()) {
                self.error(
                    Code::E0534,
                    self.ast(env.file).expr(arg.value).span,
                    "concurrent callback must be stateless",
                );
            }
            sig.result.clone()
        } else {
            self.error(
                Code::E0338,
                self.ast(env.file).expr(arg.value).span,
                "expected a callable",
            );
            Ty::Unknown
        }
    }

    fn require_marker(&mut self, arg: &Argument, mode: Mode, env: &Env) {
        if arg.mode != mode {
            let code = if arg.mode == Mode::Plain {
                Code::E0405
            } else {
                Code::E0406
            };
            self.error(
                code,
                self.ast(env.file).expr(arg.value).span,
                "concurrency endpoint argument has the wrong explicit access mode",
            );
        }
    }

    fn reject_nested_result(&mut self, ty: &Ty, span: Span) {
        if ty.is_result() {
            self.error(Code::E0720, span, "operation would hide a fallible payload");
        }
    }

    pub(super) fn is_sendable(
        &mut self,
        env: &Env,
        ty: &Ty,
        active: &mut HashSet<DefinitionId>,
    ) -> bool {
        match self.normalize(ty) {
            Ty::Scope | Ty::Task(_) | Ty::Draft(_) | Ty::TypeValue(_) | Ty::Mode => false,
            Ty::Param(id) => {
                env.sendable_guards.contains(&id)
                    || env.domains.get(&id).is_some_and(|domain| {
                        domain.iter().all(|ty| self.is_sendable(env, ty, active))
                    })
            }
            Ty::Adt(adt) => {
                if adt.kind == super::AdtKind::Foreign {
                    return false;
                }
                if !active.insert(adt.definition) {
                    return true;
                }
                let result = if matches!(adt.kind, super::AdtKind::Sum | super::AdtKind::OpaqueSum)
                {
                    self.sum_variants(&adt)
                        .values()
                        .flatten()
                        .all(|ty| self.is_sendable(env, ty, active))
                } else {
                    self.representation(env, &adt)
                        .is_none_or(|ty| self.is_sendable(env, &ty, active))
                };
                active.remove(&adt.definition);
                result
            }
            Ty::Record(fields, _) => fields
                .values()
                .all(|member| self.sendable_member(env, member, active)),
            Ty::Tuple(items) => items
                .iter()
                .all(|member| self.sendable_member(env, member, active)),
            Ty::Array(item) => self.sendable_member(env, &item, active),
            Ty::Map(key, item) => {
                self.is_sendable(env, &key, active) && self.sendable_member(env, &item, active)
            }
            Ty::Option(t) | Ty::Set(t) | Ty::Sender(t) | Ty::Receiver(t) => {
                self.is_sendable(env, &t, active)
            }
            Ty::Result(a, b) => {
                self.is_sendable(env, &a, active) && self.is_sendable(env, &b, active)
            }
            Ty::Callable(sig) => !sig.open_effects && !sig.open_state && sig.state.is_empty(),
            _ => true,
        }
    }

    fn sendable_member(
        &mut self,
        env: &Env,
        member: &Member,
        active: &mut HashSet<DefinitionId>,
    ) -> bool {
        !matches!(member.mode.mode, Mode::Ref | Mode::Shared)
            && self.is_sendable(env, &member.ty, active)
    }
}
