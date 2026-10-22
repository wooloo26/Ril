//! Conservative well-founded descent for direct scalar recursion. Each cycle
//! must contain a strict decrease of max(parameter, 0), and every other edge
//! must preserve that measure. Unknown calls, shadowing, or transfers do not
//! establish a recursive proof.
use super::*;
#[derive(Clone, Copy, PartialEq, Eq)]
enum Change {
    Same,
    Decrease,
    Unknown,
}
struct Edge {
    target: String,
    change: Change,
}

struct Measure<'a> {
    local: &'a str,
    index: usize,
    labels: Vec<Option<&'a str>>,
    locals: BTreeSet<&'a str>,
}

fn spend(work: &std::cell::Cell<usize>, units: usize) -> bool {
    let Some(remaining) = work.get().checked_sub(units) else {
        work.set(0);
        return false;
    };
    work.set(remaining);
    true
}

fn pay(work: &std::cell::Cell<usize>, units: usize) -> Option<()> {
    spend(work, units).then_some(())
}

fn pay_key(work: &std::cell::Cell<usize>, entries: usize, key: &str) -> Option<()> {
    let units =
        (1 + entries.checked_ilog2().unwrap_or(0) as usize).checked_mul(1 + key.len().div_ceil(32));
    match units {
        Some(units) => pay(work, units),
        None => {
            work.set(0);
            None
        }
    }
}

fn push_name(pending: &mut Vec<String>, name: &str, work: &std::cell::Cell<usize>) -> Option<()> {
    pay(work, 1 + name.len().div_ceil(32))?;
    pending.push(name.to_owned());
    Some(())
}

pub(super) fn proved_components(functions: &BTreeMap<String, Function>) -> BTreeSet<String> {
    let work = std::cell::Cell::new(4_000_000usize);
    let mut parameters = BTreeMap::new();
    for (name, function) in functions {
        if !spend(&work, 1 + function.parameters.len().saturating_mul(2)) {
            return BTreeSet::new();
        }
        if function.parameters.iter().any(|parameter| {
            !matches!(
                parameter.pattern.kind,
                PatternKind::Name(_) | PatternKind::Wildcard
            )
        }) {
            continue;
        }
        let Some((index, parameter)) = function.parameters.iter().enumerate().find(|(_, parameter)| {
            parameter.mode == ParameterMode::Read
                && matches!(parameter.pattern.kind, PatternKind::Name(_))
                && matches!(parameter.ty.as_ref().map(|ty| &ty.kind), Some(TypeKind::Name { path, arguments })
                    if arguments.is_empty() && path.len() == 1 && matches!(path[0].as_str(),
                        "int" | "bigint" | "i8" | "u8" | "i16" | "u16" | "i32" | "u32" | "i64" | "u64"))
        }) else { continue; };
        let PatternKind::Name(local) = &parameter.pattern.kind else {
            unreachable!();
        };
        if !spend(
            &work,
            function.parameters.len() + 1 + name.len().div_ceil(32),
        ) {
            return BTreeSet::new();
        }
        let labels = crate::hir::application::parameter_labels(&function.parameters);
        let mut locals = BTreeSet::new();
        for name in labels.iter().flatten() {
            if pay_key(&work, locals.len(), name).is_none() {
                return BTreeSet::new();
            }
            locals.insert(*name);
        }
        if pay_key(&work, parameters.len(), name).is_none() {
            return BTreeSet::new();
        }
        parameters.insert(
            name.clone(),
            Measure {
                local,
                index,
                labels,
                locals,
            },
        );
    }
    let mut graph = BTreeMap::new();
    for (name, parameter) in &parameters {
        if pay_key(&work, functions.len(), name).is_none() {
            return BTreeSet::new();
        }
        let Some(body) = functions[name].body.as_ref() else {
            continue;
        };
        let mut scanner = Scanner {
            parameters: &parameters,
            parameter: parameter.local,
            locals: &parameter.locals,
            functions,
            work: &work,
            edges: vec![],
        };
        if scanner.block(body, false) {
            if pay_key(&work, graph.len(), name).is_none() {
                return BTreeSet::new();
            }
            graph.insert(name.clone(), scanner.edges);
        }
        if work.get() == 0 {
            return BTreeSet::new();
        }
    }
    close_graph(&graph, &work).unwrap_or_default()
}

/// The existing reachability/SCC/weak-cycle relation, sharing the scanner's
/// remaining allowance. None withdraws every provisional component proof.
fn close_graph(
    graph: &BTreeMap<String, Vec<Edge>>,
    work: &std::cell::Cell<usize>,
) -> Option<BTreeSet<String>> {
    let reach = |start: &str| -> Option<BTreeSet<String>> {
        let mut pending = Vec::new();
        push_name(&mut pending, start, work)?;
        let mut seen = BTreeSet::new();
        while let Some(name) = pending.pop() {
            pay(work, 1)?;
            pay_key(work, seen.len(), &name)?;
            if seen.insert(name.clone()) {
                pay_key(work, graph.len(), &name)?;
                if let Some(edges) = graph.get(&name) {
                    for edge in edges {
                        pay(work, 1)?;
                        push_name(&mut pending, &edge.target, work)?;
                    }
                }
            }
        }
        Some(seen)
    };
    let mut reaches = BTreeMap::new();
    for name in graph.keys() {
        pay(work, 1)?;
        let reachable = reach(name)?;
        pay_key(work, reaches.len(), name)?;
        reaches.insert(name.clone(), reachable);
    }
    let mut visited = BTreeSet::new();
    let mut proved = BTreeSet::new();
    for name in graph.keys() {
        pay_key(work, visited.len(), name)?;
        if visited.contains(name) {
            continue;
        }
        let mut component = BTreeSet::new();
        pay_key(work, reaches.len(), name)?;
        let forward = reaches.get(name)?;
        for other in graph.keys() {
            pay(work, 1)?;
            pay_key(work, forward.len(), other)?;
            if !forward.contains(other) {
                continue;
            }
            pay_key(work, reaches.len(), other)?;
            let reverse = reaches.get(other)?;
            pay_key(work, reverse.len(), name)?;
            if reverse.contains(name) {
                pay_key(work, component.len(), other)?;
                component.insert(other.clone());
            }
        }
        for member in &component {
            pay_key(work, visited.len(), member)?;
            visited.insert(member.clone());
        }
        pay_key(work, graph.len(), name)?;
        let edges = graph.get(name)?;
        let mut self_edge = false;
        if component.len() == 1 {
            for edge in edges {
                pay(
                    work,
                    1 + edge.target.len().div_ceil(32) + name.len().div_ceil(32),
                )?;
                self_edge |= edge.target == *name;
            }
        }
        if component.len() == 1 && !self_edge {
            continue;
        }
        let mut unknown = false;
        for member in &component {
            pay_key(work, graph.len(), member)?;
            for edge in graph.get(member)? {
                pay(work, 1)?;
                pay_key(work, graph.len(), &edge.target)?;
                pay_key(work, component.len(), &edge.target)?;
                unknown |= !graph.contains_key(&edge.target)
                    || component.contains(&edge.target) && edge.change == Change::Unknown;
            }
        }
        if unknown {
            continue;
        }
        // Removing strict edges must break every cycle. Reachability is finite
        // and handles mutually recursive components without a recursion stack.
        let mut weak_cycle = false;
        for start in &component {
            pay_key(work, graph.len(), start)?;
            let mut pending = Vec::new();
            for edge in graph.get(start)? {
                pay(work, 1)?;
                pay_key(work, component.len(), &edge.target)?;
                if edge.change == Change::Same && component.contains(&edge.target) {
                    push_name(&mut pending, &edge.target, work)?;
                }
            }
            let mut seen = BTreeSet::new();
            while let Some(member) = pending.pop() {
                pay(
                    work,
                    1 + member.len().div_ceil(32) + start.len().div_ceil(32),
                )?;
                if member == *start {
                    weak_cycle = true;
                    break;
                }
                pay_key(work, seen.len(), &member)?;
                if seen.insert(member.clone()) {
                    pay_key(work, graph.len(), &member)?;
                    for edge in graph.get(&member)? {
                        pay(work, 1)?;
                        pay_key(work, component.len(), &edge.target)?;
                        if edge.change == Change::Same && component.contains(&edge.target) {
                            push_name(&mut pending, &edge.target, work)?;
                        }
                    }
                }
            }
            if weak_cycle {
                break;
            }
        }
        if !weak_cycle {
            for member in component {
                pay_key(work, proved.len(), &member)?;
                proved.insert(member);
            }
        }
    }
    Some(proved)
}
struct Scanner<'a> {
    parameters: &'a BTreeMap<String, Measure<'a>>,
    parameter: &'a str,
    locals: &'a BTreeSet<&'a str>,
    functions: &'a BTreeMap<String, Function>,
    work: &'a std::cell::Cell<usize>,
    edges: Vec<Edge>,
}
impl Scanner<'_> {
    fn block(&mut self, block: &Block, positive: bool) -> bool {
        if !spend(self.work, 1 + block.statements.len()) {
            return false;
        }
        if !block.where_items.is_empty() {
            return false;
        }
        block
            .statements
            .iter()
            .all(|statement| match &statement.kind {
                StmtKind::Expr { expression, .. } => self.expr(expression, positive),
                _ => false,
            })
    }
    fn expr(&mut self, value: &Expr, positive: bool) -> bool {
        if !spend(self.work, 1) {
            return false;
        }
        match &value.kind {
            ExprKind::Literal(_) | ExprKind::Name(_) | ExprKind::Path(_) => true,
            ExprKind::Unary { operand, .. } => self.expr(operand, positive),
            ExprKind::Binary {
                operator,
                left,
                right,
            } if !matches!(operator.as_str(), "|>" | "!>" | "??") => {
                self.expr(left, positive) && self.expr(right, positive)
            }
            ExprKind::Block(block) => self.block(block, positive),
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.expr(condition, positive)
                    && self.expr(then_branch, positive || self.positive(condition, true))
                    && else_branch.as_ref().is_none_or(|branch| {
                        self.expr(branch, positive || self.positive(condition, false))
                    })
            }
            ExprKind::Control {
                operation: ControlOperation::Return,
                value,
            } => value
                .as_ref()
                .is_none_or(|value| self.expr(value, positive)),
            ExprKind::Tuple(values) | ExprKind::Array(values) => {
                values.iter().all(|value| self.expr(value, positive))
            }
            ExprKind::Call { callee, arguments } => {
                let mut remaining = self.work.get();
                let base = crate::hir::application::callee_base_with_work(callee, &mut remaining);
                self.work.set(remaining);
                let Ok(base) = base else {
                    return false;
                };
                let target = match &base.kind {
                    ExprKind::Name(name) => {
                        if !spend(self.work, 1 + name.len().div_ceil(32)) {
                            return false;
                        }
                        name.clone()
                    }
                    ExprKind::Path(path) => {
                        for part in path {
                            if !spend(self.work, 1 + part.len().div_ceil(32)) {
                                return false;
                            }
                        }
                        path.join("::")
                    }
                    _ => return false,
                };
                if pay_key(self.work, self.locals.len(), &target).is_none()
                    || pay_key(self.work, self.parameters.len(), &target).is_none()
                    || pay_key(self.work, self.functions.len(), &target).is_none()
                {
                    return false;
                }
                if self.locals.contains(target.as_str()) {
                    return false;
                }
                if let Some(measure) = self.parameters.get(&target) {
                    if arguments.len() != measure.labels.len() {
                        return false;
                    }
                    let count = measure.labels.len() + arguments.len();
                    let cost = 2 + count.checked_ilog2().unwrap_or(0) as usize;
                    if !spend(self.work, count.saturating_mul(cost)) {
                        return false;
                    }
                    for name in measure.labels.iter().flatten().copied().chain(
                        arguments
                            .iter()
                            .filter_map(|argument| argument.label.as_deref()),
                    ) {
                        if !spend(self.work, cost.saturating_mul(name.len().div_ceil(32))) {
                            return false;
                        }
                    }
                    let slots = crate::hir::application::bind_slots(
                        &measure.labels,
                        arguments.iter().map(|argument| argument.label.as_deref()),
                    );
                    let mut argument = None;
                    for (actual, slot) in arguments.iter().zip(slots) {
                        let Ok(slot) = slot else {
                            return false;
                        };
                        if slot == measure.index {
                            if actual.mode != ParameterMode::Read {
                                return false;
                            }
                            argument = Some(&actual.value);
                        }
                    }
                    let Some(argument) = argument else {
                        return false;
                    };
                    let change = if matches!(&argument.kind,ExprKind::Name(name)if name==self.parameter)
                    {
                        Change::Same
                    } else if positive
                        && matches!(&argument.kind,ExprKind::Binary{operator,left,right}if operator=="-"&&matches!(&left.kind,ExprKind::Name(name)if name==self.parameter)&&self.integer(right).is_some_and(|value|value>0))
                    {
                        Change::Decrease
                    } else {
                        Change::Unknown
                    };
                    if !spend(self.work, 1) {
                        return false;
                    }
                    self.edges.push(Edge { target, change });
                } else if self.functions.contains_key(&target)
                    || super::standard_termination(&target)
                        .is_none_or(|judgment| !judgment.callable_parameters.is_empty())
                {
                    return false;
                }
                arguments
                    .iter()
                    .all(|argument| self.expr(&argument.value, positive))
            }
            _ => false,
        }
    }
    fn positive(&self, condition: &Expr, truth: bool) -> bool {
        let ExprKind::Binary {
            operator,
            left,
            right,
        } = &condition.kind
        else {
            return false;
        };
        if !matches!(&left.kind,ExprKind::Name(name)if name==self.parameter) {
            return false;
        }
        let Some(bound) = self.integer(right) else {
            return false;
        };
        match (operator.as_str(), truth) {
            (">", true) | ("<=", false) => bound >= 0,
            (">=", true) | ("<", false) => bound >= 1,
            _ => false,
        }
    }
    fn integer(&self, value: &Expr) -> Option<i128> {
        if let ExprKind::Literal(Literal::Integer(text)) = &value.kind
            && !spend(self.work, 1 + text.len())
        {
            return None;
        }
        integer(value)
    }
}
fn integer(value: &Expr) -> Option<i128> {
    let ExprKind::Literal(Literal::Integer(text)) = &value.kind else {
        return None;
    };
    let mut text = text.replace('_', "");
    for suffix in [
        "bigint", "int", "i64", "u64", "i32", "u32", "i16", "u16", "i8", "u8",
    ] {
        if let Some(number) = text.strip_suffix(suffix) {
            text = number.to_owned();
            break;
        }
    }
    if let Some(value) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
        i128::from_str_radix(value, 16).ok()
    } else if let Some(value) = text.strip_prefix("0o").or_else(|| text.strip_prefix("0O")) {
        i128::from_str_radix(value, 8).ok()
    } else if let Some(value) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B")) {
        i128::from_str_radix(value, 2).ok()
    } else {
        text.parse().ok()
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn graph_closure_and_weak_cycles_share_work_and_never_publish_partial_proofs() {
        let mut graph = BTreeMap::new();
        for index in 0..12 {
            graph.insert(
                format!("node_{index:02}"),
                vec![Edge {
                    target: format!("node_{:02}", (index + 1) % 12),
                    change: if index == 11 {
                        Change::Decrease
                    } else {
                        Change::Same
                    },
                }],
            );
        }
        let work = std::cell::Cell::new(4_000_000);
        let proved = close_graph(&graph, &work).unwrap();
        assert_eq!(proved.len(), graph.len());
        let required = 4_000_000 - work.get();
        let exact = std::cell::Cell::new(required);
        assert_eq!(close_graph(&graph, &exact), Some(proved));
        assert_eq!(exact.get(), 0);
        assert!(close_graph(&graph, &std::cell::Cell::new(required - 1)).is_none());
        graph.get_mut("node_11").unwrap()[0].change = Change::Same;
        assert_eq!(
            close_graph(&graph, &std::cell::Cell::new(4_000_000)),
            Some(BTreeSet::new())
        );

        let separate = BTreeMap::from([
            (
                "first".into(),
                vec![Edge {
                    target: "first".into(),
                    change: Change::Decrease,
                }],
            ),
            (
                "second".into(),
                vec![Edge {
                    target: "second".into(),
                    change: Change::Decrease,
                }],
            ),
        ]);
        let work = std::cell::Cell::new(4_000_000);
        assert_eq!(close_graph(&separate, &work).unwrap().len(), 2);
        let required = 4_000_000 - work.get();
        for units in 0..required {
            assert!(
                close_graph(&separate, &std::cell::Cell::new(units)).is_none(),
                "budget {units} retained an incompletely audited SCC set"
            );
        }
    }
    fn analyze(source: &str) -> Analysis {
        let source = source.replace("} fn", "}\nfn");
        let parsed = ril_syntax::parse(&source);
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        super::super::analyze(&parsed.program)
    }
    fn proved(program: &Program) -> BTreeSet<String> {
        let functions = program
            .statements
            .iter()
            .filter_map(|statement| match &statement.kind {
                StmtKind::Function(function) => Some((function.name.clone(), function.clone())),
                _ => None,
            })
            .collect();
        proved_components(&functions)
    }
    #[test]
    fn explicit_generic_descent_uses_the_actual_readonly_integer_parameter_slot() {
        use crate::sema::recursive::review_fixture as fixture;
        let original = fixture::program();
        assert!(proved(&original).contains("recur"));
        let analysis = super::super::analyze(&original);
        assert!(
            analysis.diagnostics.is_empty() && analysis.unsupported.is_empty(),
            "{:?} {:?}",
            analysis.diagnostics,
            analysis.unsupported
        );
        let mut named = original.clone();
        let function = fixture::function_mut(&mut named, "recur");
        function.parameters.swap(0, 1);
        let ExprKind::Call { arguments, .. } = &mut fixture::call_mut(function).kind else {
            unreachable!();
        };
        arguments[0].label = Some("count".into());
        arguments[1].label = Some("value".into());
        fixture::identify(&mut named);
        assert!(proved(&named).contains("recur"));
        for mutation in 0..9 {
            let mut changed = original.clone();
            let function = fixture::function_mut(&mut changed, "recur");
            match mutation {
                2 => {
                    let body = fixture::body_expression_mut(function);
                    let ExprKind::If { then_branch, .. } = &body.kind else {
                        unreachable!();
                    };
                    *body = *then_branch.clone();
                }
                3 => {
                    let mut parameter = function.parameters[0].clone();
                    parameter.pattern.kind = PatternKind::Name("other".into());
                    function.parameters.push(parameter);
                    let ExprKind::Call { arguments, .. } = &mut fixture::call_mut(function).kind
                    else {
                        unreachable!();
                    };
                    let decrease = arguments[0].clone();
                    arguments[0].value.kind = ExprKind::Name("other".into());
                    arguments.push(decrease);
                }
                4 => function.parameters[1].pattern.kind = PatternKind::Name("recur".into()),
                5 => function.parameters[0].mode = ParameterMode::Mut,
                _ => {
                    let ExprKind::Call { callee, arguments } =
                        &mut fixture::call_mut(function).kind
                    else {
                        unreachable!();
                    };
                    match mutation {
                        0 | 7 => {
                            let ExprKind::Binary { left, .. } = &arguments[0].value.kind else {
                                unreachable!();
                            };
                            arguments[0].value = *left.clone();
                            if mutation == 7 {
                                let ExprKind::Generic { arguments, .. } = &mut callee.kind else {
                                    unreachable!();
                                };
                                let element = arguments[0].clone();
                                arguments[0].kind = TypeKind::Array {
                                    length: None,
                                    element: Box::new(element),
                                };
                            }
                        }
                        1 => {
                            let ExprKind::Binary { operator, .. } = &mut arguments[0].value.kind
                            else {
                                unreachable!();
                            };
                            *operator = "+".into();
                        }
                        6 => {
                            let argument = arguments[1].clone();
                            let mut base = argument.value.clone();
                            base.kind = ExprKind::Name("unknown".into());
                            arguments[1].value.kind = ExprKind::Call {
                                callee: Box::new(base),
                                arguments: vec![argument],
                            };
                        }
                        8 => {
                            arguments[0].label = Some("count".into());
                            arguments[1].label = Some("count".into());
                        }
                        _ => unreachable!(),
                    }
                }
            }
            fixture::identify(&mut changed);
            assert!(
                !proved(&changed).contains("recur"),
                "unproved generic descent mutation {mutation} was accepted"
            );
        }
    }
    #[test]
    fn mutual_descent_requires_progress_on_every_cycle() {
        let good = analyze(
            "halt fn even(n:int)->bool{if n<=0{true}else{odd(n-1)}} fn odd(n:int)->bool{if n<=0{false}else{even(n-1)}}",
        );
        assert!(
            good.diagnostics.is_empty() && good.unsupported.is_empty(),
            "{:?} {:?}",
            good.diagnostics,
            good.unsupported
        );
        for source in [
            "halt fn a(n:int)->bool{b(n)} fn b(n:int)->bool{a(n)}",
            "halt fn a(n:bigint)->bool{b(n-1bigint)} fn b(n:bigint)->bool{a(n)}",
            "halt fn a(n:int)->bool{if n<=0{true}else{b(n+1)}} fn b(n:int)->bool{a(n)}",
            "halt fn a(n:int)->bool{if n<=0{true}else{if n>2{a(n)}else{a(n-1)}}}",
            "halt fn a(n:int)->bool{let n=10;a(n-1)}",
        ] {
            let result = analyze(source);
            assert!(
                !result.unsupported.is_empty(),
                "unproved recursion accepted: {source}"
            );
        }
    }
}
