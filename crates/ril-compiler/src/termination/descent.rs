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

pub(super) fn proved_components(functions: &BTreeMap<String, Function>) -> BTreeSet<String> {
    let parameters: BTreeMap<_, _> = functions
        .iter()
        .filter_map(|(name, function)| {
            if !function.generics.is_empty() || function.parameters.len() != 1 {
                return None;
            }
            let parameter = &function.parameters[0];
            let PatternKind::Name(local) = &parameter.pattern.kind else {
                return None;
            };
            let Some(TypeExpr {
                kind: TypeKind::Name { path, arguments },
                ..
            }) = &parameter.ty
            else {
                return None;
            };
            if parameter.mode != ParameterMode::Read
                || !arguments.is_empty()
                || path.len() != 1
                || !matches!(
                    path[0].as_str(),
                    "int" | "bigint" | "i8" | "u8" | "i16" | "u16" | "i32" | "u32" | "i64" | "u64"
                )
            {
                return None;
            }
            Some((name.clone(), local.clone()))
        })
        .collect();
    let mut graph = BTreeMap::new();
    for (name, parameter) in &parameters {
        let Some(body) = functions[name].body.as_ref() else {
            continue;
        };
        let mut scanner = Scanner {
            parameters: &parameters,
            parameter,
            edges: vec![],
        };
        if scanner.block(body, false) {
            graph.insert(name.clone(), scanner.edges);
        }
    }
    let reach = |start: &str| {
        let mut pending = vec![start.to_owned()];
        let mut seen = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if seen.insert(name.clone())
                && let Some(edges) = graph.get(&name)
            {
                pending.extend(edges.iter().map(|edge| edge.target.clone()));
            }
        }
        seen
    };
    let reaches: BTreeMap<_, _> = graph
        .keys()
        .map(|name| (name.clone(), reach(name)))
        .collect();
    let mut visited = BTreeSet::new();
    let mut proved = BTreeSet::new();
    for name in graph.keys() {
        if visited.contains(name) {
            continue;
        }
        let component: BTreeSet<_> = graph
            .keys()
            .filter(|other| reaches[name].contains(*other) && reaches[*other].contains(name))
            .cloned()
            .collect();
        visited.extend(component.iter().cloned());
        if component.len() == 1 && !graph[name].iter().any(|edge| edge.target == *name) {
            continue;
        }
        if component.iter().any(|member| {
            graph[member].iter().any(|edge| {
                !graph.contains_key(&edge.target)
                    || component.contains(&edge.target) && edge.change == Change::Unknown
            })
        }) {
            continue;
        }
        // Removing strict edges must break every cycle. Reachability is finite
        // and handles mutually recursive components without a recursion stack.
        let weak_cycle = component.iter().any(|start| {
            let mut pending: Vec<_> = graph[start]
                .iter()
                .filter(|edge| edge.change == Change::Same && component.contains(&edge.target))
                .map(|edge| edge.target.clone())
                .collect();
            let mut seen = BTreeSet::new();
            while let Some(member) = pending.pop() {
                if member == *start {
                    return true;
                }
                if seen.insert(member.clone()) {
                    pending.extend(
                        graph[&member]
                            .iter()
                            .filter(|edge| {
                                edge.change == Change::Same && component.contains(&edge.target)
                            })
                            .map(|edge| edge.target.clone()),
                    );
                }
            }
            false
        });
        if !weak_cycle {
            proved.extend(component);
        }
    }
    proved
}
struct Scanner<'a> {
    parameters: &'a BTreeMap<String, String>,
    parameter: &'a str,
    edges: Vec<Edge>,
}
impl Scanner<'_> {
    fn block(&mut self, block: &Block, positive: bool) -> bool {
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
                let target = match &callee.kind {
                    ExprKind::Name(name) => name.clone(),
                    ExprKind::Path(path) => path.join("::"),
                    _ => return false,
                };
                if self.parameters.contains_key(&target) {
                    if arguments.len() != 1
                        || arguments[0].label.is_some()
                        || arguments[0].mode != ParameterMode::Read
                    {
                        return false;
                    }
                    let argument = &arguments[0].value;
                    let change = if matches!(&argument.kind,ExprKind::Name(name)if name==self.parameter)
                    {
                        Change::Same
                    } else if positive
                        && matches!(&argument.kind,ExprKind::Binary{operator,left,right}if operator=="-"&&matches!(&left.kind,ExprKind::Name(name)if name==self.parameter)&&integer(right).is_some_and(|value|value>0))
                    {
                        Change::Decrease
                    } else {
                        Change::Unknown
                    };
                    self.edges.push(Edge { target, change });
                } else if super::standard_termination(&target)
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
        let Some(bound) = integer(right) else {
            return false;
        };
        match (operator.as_str(), truth) {
            (">", true) | ("<=", false) => bound >= 0,
            (">=", true) | ("<", false) => bound >= 1,
            _ => false,
        }
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
    fn analyze(source: &str) -> Analysis {
        let source = source.replace("} fn", "}\nfn");
        let parsed = ril_syntax::parse(&source);
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        super::super::analyze(&parsed.program)
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
