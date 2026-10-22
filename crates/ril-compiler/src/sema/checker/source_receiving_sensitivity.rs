//! Finite declaration reachability, independent of an operand's erased Ty.
//! A backedge skips an already visited declaration body, not its arguments.
//! The root joins every visited leaf; no provisional per-alias answer is cached.
use super::*;

pub(super) fn annotation(checker: &Checker, syntax: &TypeExpr) -> SchemaSensitivity {
    Walk {
        checker,
        declarations: BTreeSet::new(),
        work: 4096,
    }
    .ty(syntax, &[], true, 0)
}

fn join(left: SchemaSensitivity, right: SchemaSensitivity) -> SchemaSensitivity {
    use SchemaSensitivity::*;
    match (left, right) {
        (Required, _) | (_, Required) => Required,
        (Unknown, _) | (_, Unknown) => Unknown,
        _ => NotRequired,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sort<'a> {
    Type,
    Key,
    Const(&'a str),
}

fn sort(parameter: &GenericParameter) -> Option<Sort<'_>> {
    match parameter.bound.as_ref().map(|bound| &bound.kind) {
        None if parameter.name.starts_with(char::is_uppercase) => Some(Sort::Type),
        Some(TypeKind::Record { .. }) => Some(Sort::Type),
        Some(TypeKind::KeyOf(_)) => Some(Sort::Key),
        Some(TypeKind::Name { path, arguments }) if arguments.is_empty() => {
            let name = path.last()?.as_str();
            if path.len() > 1 && path.first()?.as_str() != "Prelude" {
                return None;
            }
            match name {
                "Type" => Some(Sort::Type),
                "int" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32"
                | "u64" | "u128" | "usize" | "bigint" | "f32" | "f64" | "bool" | "str"
                | "bytes" => Some(Sort::Const(name)),
                _ => None,
            }
        }
        _ => None,
    }
}

struct Walk<'a> {
    checker: &'a Checker,
    declarations: BTreeSet<String>,
    work: usize,
}

impl Walk<'_> {
    fn charge(&mut self, depth: usize) -> Option<()> {
        if depth >= 64 {
            return None;
        }
        self.work = self.work.checked_sub(1)?;
        Some(())
    }

    fn binder<'a>(
        &'a mut self,
        name: &str,
        locals: &'a [GenericParameter],
        caller: bool,
    ) -> Option<(Sort<'a>, bool)> {
        for parameter in locals {
            self.work = self.work.checked_sub(1)?;
            if parameter.name == name {
                return Some((sort(parameter)?, true));
            }
        }
        if !caller {
            // A free captured binder belongs to the alias's declaration
            // environment, which cannot be borrowed from the current caller.
            return None;
        }
        let identity = self
            .checker
            .type_source
            .environment
            .generic_context
            .get(name)
            .or_else(|| self.checker.effect_type_binders.get(name))?;
        let binder = self.checker.generic_binders.get(identity)?;
        if &binder.identity != identity
            || (binder.name != name && self.checker.effect_type_binders.get(name) != Some(identity))
        {
            return None;
        }
        for function in &self.checker.functions {
            self.work = self.work.checked_sub(1)?;
            if function.definition == binder.definition {
                let parameter = function.syntax.generics.get(binder.index as usize)?;
                if parameter.name != binder.name {
                    return None;
                }
                return Some((sort(parameter)?, false));
            }
        }
        None
    }

    fn argument(
        &mut self,
        syntax: &TypeExpr,
        expected: Sort<'_>,
        locals: &[GenericParameter],
        caller: bool,
        depth: usize,
    ) -> SchemaSensitivity {
        if expected == Sort::Type {
            return self.ty(syntax, locals, caller, depth);
        }
        if self.charge(depth).is_none() {
            return SchemaSensitivity::Unknown;
        }
        if let TypeKind::Name { path, arguments } = &syntax.kind
            && arguments.is_empty()
            && let Some((actual, _)) = self.binder(&path.join("::"), locals, caller)
            && actual == expected
        {
            return SchemaSensitivity::NotRequired;
        }
        let literal = match &syntax.kind {
            TypeKind::Computation(expression) => match &expression.kind {
                ExprKind::Literal(literal) => Some(literal),
                _ => None,
            },
            _ => None,
        };
        let proven = match (expected, literal) {
            (Sort::Const(name), Some(Literal::Integer(_))) => {
                !matches!(name, "bool" | "str" | "bytes" | "f32" | "f64")
            }
            (Sort::Const("f32" | "f64"), Some(Literal::Float(_)))
            | (Sort::Const("bool"), Some(Literal::Bool(_)))
            | (Sort::Const("str"), Some(Literal::String(_) | Literal::RawString(_)))
            | (Sort::Const("bytes"), Some(Literal::Bytes(_))) => true,
            _ => false,
        };
        if proven {
            SchemaSensitivity::NotRequired
        } else {
            SchemaSensitivity::Unknown
        }
    }

    fn ty(
        &mut self,
        syntax: &TypeExpr,
        locals: &[GenericParameter],
        caller: bool,
        depth: usize,
    ) -> SchemaSensitivity {
        use SchemaSensitivity::*;
        if self.charge(depth).is_none() {
            return Unknown;
        }
        match &syntax.kind {
            TypeKind::Array { .. } | TypeKind::Callable { .. } => Required,
            TypeKind::Optional(inner) => self.ty(inner, locals, caller, depth + 1),
            TypeKind::Map { key, value } => {
                let first = self.ty(key, locals, caller, depth + 1);
                join(first, self.ty(value, locals, caller, depth + 1))
            }
            TypeKind::Tuple(items) => items.iter().fold(NotRequired, |answer, item| {
                join(answer, self.ty(item, locals, caller, depth + 1))
            }),
            TypeKind::Record { fields, row } => {
                let mut answer = NotRequired;
                for field in fields {
                    answer = join(answer, self.ty(&field.ty, locals, caller, depth + 1));
                }
                if let Some(row) = row {
                    answer = join(answer, self.ty(row, locals, caller, depth + 1));
                }
                answer
            }
            TypeKind::Name { path, arguments } => {
                let full = path.join("::");
                self.work = match self.work.checked_sub(full.len().div_ceil(32)) {
                    Some(work) => work,
                    None => return Unknown,
                };
                if arguments.is_empty()
                    && let Some((bound, declaration_parameter)) = self.binder(&full, locals, caller)
                {
                    return match bound {
                        // Alias formal arguments are visited at each actual
                        // application. A caller's unselected Type is opaque.
                        Sort::Type if !declaration_parameter => Unknown,
                        _ => NotRequired,
                    };
                }
                let checker = self.checker;
                let declarations = &checker.types;
                if let Some(declaration) = declarations.get(&full) {
                    if arguments.len() > declaration.generics.len() {
                        return Unknown;
                    }
                    let mut answer = NotRequired;
                    for (index, parameter) in declaration.generics.iter().enumerate() {
                        let Some(expected) = sort(parameter) else {
                            return Unknown;
                        };
                        answer = join(
                            answer,
                            if let Some(argument) = arguments.get(index) {
                                self.argument(argument, expected, locals, caller, depth + 1)
                            } else if let Some(default) = &parameter.default {
                                self.argument(
                                    default,
                                    expected,
                                    &declaration.generics,
                                    false,
                                    depth + 1,
                                )
                            } else {
                                Unknown
                            },
                        );
                    }
                    // Nominal/opaque identity seals the implementation. Its
                    // exact static arguments remain ordinary typing duties;
                    // transparent aliases must expose their original body.
                    if declaration.nominal || declaration.opaque || !declaration.variants.is_empty()
                    {
                        return answer;
                    }
                    if !self.declarations.insert(full) {
                        return answer;
                    }
                    return join(
                        answer,
                        declaration.value.as_ref().map_or(Unknown, |body| {
                            self.ty(body, &declaration.generics, false, depth + 1)
                        }),
                    );
                }
                // Expand genuine builtin operation/stream records. Treating
                // every known builtin as a scalar would hide their Fn fields.
                let schema = io_types::operation_type(syntax)
                    .or_else(|| super::super::iter_types::schema(syntax))
                    .or_else(|| {
                        let ty = super::super::standard::file_type(&full)?;
                        matches!(ty, Ty::Record(_))
                            .then(|| io_types::data_type(&ty, syntax.span))
                            .flatten()
                    });
                if let Some(schema) = schema {
                    return self.ty(&schema, locals, caller, depth + 1);
                }
                let head = TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span: syntax.span,
                    kind: TypeKind::Name {
                        path: path.clone(),
                        arguments: vec![],
                    },
                };
                let head = SourceTypeWitness {
                    key: crate::static_eval::normalized_argument_key(&head),
                    syntax: head,
                };
                if !crate::sema::source_type_validation::resolved_names(&head, declarations) {
                    return Unknown;
                }
                arguments.iter().fold(NotRequired, |answer, argument| {
                    join(answer, self.ty(argument, locals, caller, depth + 1))
                })
            }
            // Even a scalar-looking type computation or arbitrary projection
            // can produce an Array/Fn. Only real static-key binder sort above
            // supplies a no-coordinate proof, not spelling or erased Ty.
            _ => Unknown,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty(source: &str) -> TypeExpr {
        let parsed = ril_syntax::parse(&format!("let SOURCE:{source}=[]"));
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        let StmtKind::Binding(binding) = &parsed.program.statements[0].kind else {
            panic!("binding fixture");
        };
        binding.ty.clone().unwrap()
    }

    fn checker(source: &str) -> Checker {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{source}: {:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        for statement in parsed.program.statements {
            let StmtKind::Type(declaration) = statement.kind else {
                panic!("declaration fixture");
            };
            checker.types.insert(declaration.name.clone(), declaration);
        }
        checker
    }

    #[test]
    fn recursive_backedges_do_not_mask_other_members_or_unresolved_leaves() {
        use SchemaSensitivity::*;
        for (declarations, root, expected) in [
            ("type Node={value:int,following:?Node}", "Node", NotRequired),
            ("type Node={following:?Node,items:[]int}", "Node", Required),
            (
                "type Node={following:?Node,callback:fn()->int}",
                "Node",
                Required,
            ),
            ("type Node={following:?Node,value:Missing}", "Node", Unknown),
            (
                "type Left={right:?Right}\ntype Right={left:?Left,value:int}",
                "(Left,Right)",
                NotRequired,
            ),
            (
                "type Left={right:?Right,items:[]int}\ntype Right={left:?Left}",
                "(Right,Left)",
                Required,
            ),
        ] {
            let mut checker = checker(declarations);
            let target = checker.freeze_source_receiving_target(&ty(root));
            assert_eq!(target.sensitivity, expected, "{declarations}: {root}");
        }
    }

    #[test]
    fn transparent_aliases_and_nominal_static_argument_sorts_stay_distinct() {
        use SchemaSensitivity::*;
        let mut checker = checker("type Alias<T>=[2]T\ntype Token<size:int>(int)");
        for (syntax, expected) in [
            ("Alias<int>", Required),
            ("Token<1>", NotRequired),
            ("Token<int>", Unknown),
            ("Missing<int>", Unknown),
        ] {
            assert_eq!(
                checker
                    .freeze_source_receiving_target(&ty(syntax))
                    .sensitivity,
                expected,
                "{syntax}"
            );
        }
        let parsed = ril_syntax::parse("type Computed=int");
        assert!(parsed.is_ok());
        let StmtKind::Type(mut declaration) = parsed.program.statements[0].kind.clone() else {
            unreachable!()
        };
        let expression = ril_syntax::parse_expression("if true{int}else{str}", FileId(0));
        assert!(expression.diagnostics.is_empty() && !expression.incomplete);
        declaration.value = Some(TypeExpr {
            hir_id: None,
            text: String::new(),
            span: declaration.span,
            kind: TypeKind::Computation(Box::new(expression.expression)),
        });
        // Inspect the unnormalized computation, not an evaluated result.
        checker.types.insert(declaration.name.clone(), declaration);
        assert_eq!(annotation(&checker, &ty("Computed")), Unknown);
    }

    #[test]
    fn static_key_and_const_binders_require_the_actual_registered_header() {
        use SchemaSensitivity::*;
        let parsed = ril_syntax::parse(
            "fn coordinates<T:{item:int},K:keyof T,size:int>(record:T,key:K){}\ntype Token<count:int>(int)",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let mut checker = Checker::new(FileId(0));
        let mut frame = checker.frame(Env::new(), false);
        checker.declarations(&parsed.program.statements, &mut frame);
        checker.generic_scope(0);
        assert_eq!(annotation(&checker, &ty("K")), NotRequired);
        assert_eq!(annotation(&checker, &ty("T")), Unknown);
        assert_eq!(annotation(&checker, &ty("Token<size>")), NotRequired);
        let identity = checker.type_source.environment.generic_context["K"].clone();
        checker.generic_binders.get_mut(&identity).unwrap().name = "different".into();
        assert_eq!(annotation(&checker, &ty("K")), Unknown);
    }

    #[test]
    fn builtin_operation_records_are_not_mistaken_for_resource_scalars() {
        use SchemaSensitivity::*;
        let checker = Checker::new(FileId(0));
        assert_eq!(annotation(&checker, &ty("File::Handle")), NotRequired);
        assert_eq!(
            annotation(&checker, &ty("Io::ReadOps<File::Handle>")),
            Required
        );
        assert_eq!(annotation(&checker, &ty("Missing::Handle")), Unknown);
    }

    #[test]
    fn reconstruction_exhaustion_and_projection_failure_keep_unknown() {
        use SchemaSensitivity::*;
        let checker = Checker::new(FileId(0));
        let syntax = ty("(int,int)");
        assert_eq!(
            Walk {
                checker: &checker,
                declarations: BTreeSet::new(),
                work: 1
            }
            .ty(&syntax, &[], true, 0),
            Unknown
        );
        let mut checker = checker;
        let target = checker.freeze_source_receiving_target(&ty("([2]int,int)"));
        let failed = tuple_target(&target, 9, target.span);
        assert!(failed.schema.is_none());
        assert_eq!(failed.sensitivity, Unknown);
    }
}
