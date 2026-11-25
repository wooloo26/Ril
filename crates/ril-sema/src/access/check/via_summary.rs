use super::*;

impl Analyzer<'_> {
    pub(super) fn via_table(
        &mut self,
        fun: &DefinitionCheck,
        summary: &Summary,
        facts: &BTreeSet<Fact>,
    ) -> ViaDomain {
        if fun.via.is_empty() && fun.member_axes.is_empty() {
            return ViaDomain::default();
        }
        let mut permitted = Vec::new();
        let mut formals = BTreeMap::new();
        let mut axes = Vec::new();
        for (index, formal) in fun.formals.iter().enumerate() {
            let Some(source) = formal.filter(|span| fun.via.contains(span)) else {
                continue;
            };
            formals.insert(index, formals.len());
            axes.push(Region::root(source));
            let domain = domains::root_modes(facts, fun.owner, source);
            if domain.is_empty() {
                self.error(
                    Code::E0548,
                    fun.owner,
                    "via source cannot be both handed off as new and retained as shared",
                );
                return ViaDomain::default();
            }
            permitted.push(domain.to_vec());
        }
        for (_, axis) in &fun.member_axes {
            axes.push(axis.clone());
            let domain = domains::member_modes(facts, fun.owner, axis);
            if domain.is_empty() {
                self.error(
                    Code::E0520,
                    fun.owner,
                    "member via template has incompatible access requirements",
                );
                return ViaDomain::default();
            }
            permitted.push(domain);
        }
        if fun.declared.result_mode != Mode::Infer
            && summary
                .invocations
                .iter()
                .all(|invocation| matches!(invocation.mode, InvocationMode::Input(_)))
            && summary.mode_calls.as_ref().is_none_or(Vec::is_empty)
            && summary.callback_returns.is_empty()
            && summary
                .storage_updates
                .iter()
                .all(|update| update.callback_returns.is_empty())
        {
            return ViaDomain::uniform(&permitted, summary);
        }
        let mut relevant = BTreeSet::new();
        let formal_axis = |formal: usize| formals.get(&formal).copied();
        let mode_axis_idx = |axis: &crate::access::ModeAxis| {
            if axis.path.is_empty() {
                formals.get(&axis.parameter).copied()
            } else {
                fun.member_axes
                    .iter()
                    .position(|(parameter, region)| {
                        *parameter == axis.parameter && region.selection == axis.path
                    })
                    .map(|pos| formals.len() + pos)
            }
        };
        for invocation in &summary.invocations {
            if let InvocationMode::Formal(formal) = invocation.mode
                && let Some(idx) = formal_axis(formal)
            {
                relevant.insert(idx);
            }
        }
        if let Some(calls) = &summary.mode_calls {
            for call in calls {
                for (_, expr) in &call.arguments {
                    for axis in expr.axes() {
                        if let Some(idx) = mode_axis_idx(axis) {
                            relevant.insert(idx);
                        }
                    }
                }
            }
        }
        fn collect_callback_return_formals(
            result: &crate::access::CallbackReturn,
            out: &mut BTreeSet<usize>,
        ) {
            for arg in &result.arguments {
                for mode in &arg.modes {
                    if let InvocationMode::Formal(formal) = *mode {
                        out.insert(formal);
                    }
                }
                for nested in &arg.callback_returns {
                    collect_callback_return_formals(nested, out);
                }
            }
        }
        let mut cb_formals = BTreeSet::new();
        for result in &summary.callback_returns {
            collect_callback_return_formals(result, &mut cb_formals);
        }
        for update in &summary.storage_updates {
            for result in &update.callback_returns {
                collect_callback_return_formals(result, &mut cb_formals);
            }
        }
        for formal in cb_formals {
            if let Some(idx) = formal_axis(formal) {
                relevant.insert(idx);
            }
        }
        if fun.declared.result_mode == Mode::Infer {
            for value in &fun.returns {
                for origin in &value.roots {
                    if origin.inherits_mode
                        && origin.region.selection.is_empty()
                        && let Some(index) = fun
                            .formals
                            .iter()
                            .position(|formal| *formal == Some(origin.region.source))
                        && let Some(idx) = formal_axis(index)
                    {
                        relevant.insert(idx);
                    }
                }
                value.visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                    let Some(formal) = fun
                        .formals
                        .iter()
                        .position(|decl| *decl == Some(origin.region.source))
                    else {
                        return;
                    };
                    if !result_path.is_empty() && origin.new {
                        return;
                    }
                    if origin.inherits_mode {
                        for (idx, decl) in axes.iter().enumerate() {
                            if decl.matches_axis(&origin.region) {
                                relevant.insert(idx);
                            }
                        }
                    } else if origin.reception.is_empty() {
                        if let Some(idx) = formal_axis(formal) {
                            relevant.insert(idx);
                        }
                    } else {
                        for step in &origin.reception {
                            if let Reception::Axis(axis) = step {
                                for (idx, decl) in axes.iter().enumerate() {
                                    if decl.matches_axis(axis) {
                                        relevant.insert(idx);
                                    }
                                }
                            }
                        }
                    }
                });
            }
        }

        ViaDomain::build_relevant(&permitted, &relevant, |modes| {
            let mut summary = summary.clone();
            let input = |formal| {
                formals
                    .get(&formal)
                    .and_then(|&axis| modes.get(axis))
                    .copied()
            };
            for invocation in &mut summary.invocations {
                if let InvocationMode::Formal(formal) = invocation.mode
                    && let Some(input) = input(formal)
                {
                    invocation.mode = InvocationMode::Input(input);
                }
            }
            summary.normalize_invocations();
            let axis_input = |axis: &crate::access::ModeAxis| {
                if axis.path.is_empty() {
                    input(axis.parameter)
                } else {
                    fun.member_axes
                        .iter()
                        .position(|(parameter, region)| {
                            *parameter == axis.parameter && region.selection == axis.path
                        })
                        .and_then(|index| modes.get(formals.len() + index))
                        .copied()
                }
            };
            if let Some(calls) = &mut summary.mode_calls {
                for call in &mut *calls {
                    call.specialize(&axis_input);
                }
                calls.sort_unstable();
                calls.dedup();
            }
            for result in &mut summary.callback_returns {
                result.specialize(&input);
            }
            summary.callback_returns.sort_unstable();
            summary.callback_returns.dedup();
            for update in &mut summary.storage_updates {
                for result in &mut update.callback_returns {
                    result.specialize(&input);
                }
                update.callback_returns.sort_unstable();
                update.callback_returns.dedup();
            }
            if fun.declared.result_mode == Mode::Infer {
                summary.constructs = !fun.returns.is_empty()
                    && fun.returns.iter().all(|value| {
                        value.requires_new
                            || (!value.roots.is_empty()
                                && value.roots.iter().all(|origin| {
                                    origin.inherits_mode
                                        && origin.region.selection.is_empty()
                                        && fun
                                            .formals
                                            .iter()
                                            .position(|formal| {
                                                *formal == Some(origin.region.source)
                                            })
                                            .and_then(|index| formals.get(&index))
                                            .is_some_and(|&position| {
                                                modes.get(position) == Some(&Input::New)
                                            })
                                }))
                    });
                let mut sources = BTreeSet::new();
                for value in &fun.returns {
                    value.visit_origins(&mut Vec::new(), &mut |result_path, origin| {
                        let Some(formal) = fun
                            .formals
                            .iter()
                            .position(|decl| *decl == Some(origin.region.source))
                        else {
                            return;
                        };
                        if !result_path.is_empty() && origin.new {
                            return;
                        }
                        let input = |axis: &Region| {
                            axes.iter()
                                .zip(modes)
                                .find(|(decl, _)| decl.matches_axis(axis))
                                .map_or(Access::Mut, |(_, mode)| mode.access())
                        };
                        let access = if origin.inherits_mode {
                            input(&origin.region)
                        } else if origin.reception.is_empty() {
                            formals
                                .get(&formal)
                                .and_then(|index| modes.get(*index))
                                .map_or(origin.mode, |mode| mode.access().project(origin.mode))
                        } else {
                            origin
                                .reception
                                .iter()
                                .map(|step| match step {
                                    Reception::Fixed(access) => *access,
                                    Reception::Axis(axis) => input(axis),
                                })
                                .fold(Access::Mut, Access::project)
                        };
                        sources.insert(ReturnSource {
                            formal,
                            source_path: origin.region.selection.clone(),
                            result_path: result_path.to_vec(),
                            access,
                        });
                    });
                }
                summary.return_sources = sources.into_iter().collect();
            }
            summary
        })
    }

    pub(super) fn schema_axis(&self, region: &Region) -> Option<&Region> {
        self.member_schemas
            .get(&region.source)?
            .iter()
            .find(|axis| axis.matches_axis(region))
    }

    pub(super) fn register_member_axes(&mut self, axes: &[(usize, Region)]) {
        for (_, axis) in axes {
            let regions = self.member_schemas.entry(axis.source).or_default();
            if !regions.contains(axis) {
                regions.push(axis.clone());
            }
        }
    }

    pub(super) fn navigate(
        &mut self,
        ctx: &mut Context,
        ledger: &mut Ledger,
        base: ExprId,
        steps: &[ExprId],
        span: Span,
    ) -> Datum {
        let ast = self.ast(ctx.file);
        let mut value = self.expr(ctx, ledger, base);
        let entry = ledger.clone();
        let mut present_ctx = ctx.clone();
        let mut missing = Vec::new();
        let mut ty = self.ty(ast.expr(base).span);
        let payload = Coordinate::Index("0".into());
        for &step in steps {
            let step = ast.expr(step);
            let (safe, index) = match &step.value {
                Expr::Member { safe, .. } => (*safe, None),
                Expr::Index { safe, index, .. } => (*safe, Some(*index)),
                _ => ril_source::ice!("unexpected navigation step"),
            };
            if safe && let Ty::Option(inner) = ty {
                let mut absent = ledger.clone();
                absent.take_choice(step.span, 1);
                missing.push(absent);
                ledger.take_choice(step.span, 0);
                value = ledger.project(&value, payload.clone(), Access::Immutable);
                ty = inner;
            }
            value = if let Some(index) = index {
                self.expr(&mut present_ctx, ledger, index);
                if safe {
                    missing.push(ledger.clone());
                }
                self.project_index(&present_ctx, ledger, &value, (ty, index, step.span))
            } else if let Expr::Member { member, .. } = &step.value {
                let coordinate = self.coordinate(&mut present_ctx, ledger, member);
                let mode = self.schema_mode(ty, &coordinate).0;
                self.project_observed(&present_ctx, ledger, &value, (coordinate, mode, step.span))
            } else {
                ril_source::ice!("unexpected navigation coordinate");
            };
            ty = self
                .program
                .navigation_values
                .get(&step.span)
                .unwrap_or(&Ty::Unknown);
        }
        ctx.return_values = present_ctx.return_values;
        missing.push(ledger.clone());
        ledger.merge(&entry, &missing);
        ctx.reachable &= !ledger.no_continuation;
        if matches!(ty, Ty::Option(_)) {
            value
        } else {
            let mut option = Datum::source(span, Access::Mut, true);
            option.members.insert(payload, value);
            option
        }
    }
}

pub(super) fn member_axes(callable: &Callable, formals: &[Option<Span>]) -> Vec<(usize, Region)> {
    let mut axes = Vec::new();
    for (index, (parameter, decl)) in callable.parameters.iter().zip(formals).enumerate() {
        if let Some(source) = decl {
            collect_axes(&parameter.ty, &mut Vec::new(), &mut |selection| {
                let mut region = Region::root(*source);
                region.selection.extend_from_slice(selection);
                axes.push((index, region));
            });
        }
    }
    axes
}

pub(super) fn collect_axes(
    ty: &Ty,
    path: &mut Vec<Coordinate>,
    output: &mut impl FnMut(&[Coordinate]),
) {
    let mut visit = |coord, member: &ty::Member| {
        path.push(coord);
        if member.mode.mode == Mode::Via {
            output(path);
        }
        collect_axes(&member.ty, path, output);
        path.pop();
    };
    match ty {
        Ty::Array(item) | Ty::Map(_, item) => visit(Coordinate::Dynamic, item),
        Ty::Tuple(items) => {
            for (position, item) in items.iter().enumerate() {
                visit(Coordinate::Index(position.to_string()), item);
            }
        }
        Ty::Record(fields, _) => {
            for (name, item) in fields {
                visit(Coordinate::Field(name.clone()), item);
            }
        }
        _ => {}
    }
}
