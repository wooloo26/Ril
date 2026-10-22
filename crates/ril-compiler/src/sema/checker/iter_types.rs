//! Standard iteration schemas keep original type syntax and real sum identities.
use super::*;

fn named(name: &str, arguments: Vec<TypeExpr>, span: Span) -> TypeExpr {
    TypeExpr {
        hir_id: None,
        text: name.into(),
        kind: TypeKind::Name {
            path: name.split("::").map(str::to_owned).collect(),
            arguments,
        },
        span,
    }
}

pub(super) fn schema(syntax: &TypeExpr) -> Option<TypeExpr> {
    let TypeKind::Name { path, arguments } = &syntax.kind else {
        return None;
    };
    let span = syntax.span;
    let fields = match (path.join("::").as_str(), arguments.as_slice()) {
        ("Iter::Source", [state, item]) => vec![TypeField {
            name: "step".into(),
            mutable: false,
            span,
            ty: TypeExpr {
                hir_id: None,
                text: String::new(),
                span,
                kind: TypeKind::Callable {
                    parameters: vec![Parameter {
                        pattern: Pattern {
                            hir_id: None,
                            kind: PatternKind::Name("ril__iter_state".into()),
                            span,
                        },
                        mode: ParameterMode::Read,
                        ty: Some(state.clone()),
                        default: None,
                        span,
                    }],
                    result: Some(Box::new(named(
                        "Iter::Step",
                        vec![state.clone(), item.clone()],
                        span,
                    ))),
                    annotations: vec![],
                },
            },
        }],
        ("Iter::Cursor", [state]) => vec![
            TypeField {
                name: "state".into(),
                mutable: true,
                ty: state.clone(),
                span,
            },
            TypeField {
                name: "ended".into(),
                mutable: true,
                ty: named("bool", vec![], span),
                span,
            },
        ],
        _ => return None,
    };
    Some(TypeExpr {
        hir_id: None,
        text: String::new(),
        kind: TypeKind::Record { fields, row: None },
        span,
    })
}

impl Checker {
    pub(in crate::sema::checker) fn register_standard_iter_types(&mut self) {
        if self.types.contains_key("Iter::Step") {
            return;
        }
        let declaration = crate::sema::model::iteration::step_declaration();
        self.types
            .insert(declaration.name.clone(), declaration.clone());
        let previous = self.type_source.environment.generic_context.clone();
        for (index, parameter) in declaration.generics.iter().enumerate() {
            self.type_source.environment.generic_context.insert(
                parameter.name.clone(),
                format!("std:Iter::Step:{index}:{}", parameter.name),
            );
        }
        self.declare_constructors(&declaration);
        self.type_source.environment.generic_context = previous;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn custom_steps_keep_the_payload_shape_of_each_possible_return_tag() {
        let source = "fn step(state:int)->Iter::Step<int,int>{if state<2{Iter::Step::Yielded(state,state+1)}else{Iter::Step::Done}}\nfn read(state:int)->int{match step(state){Iter::Step::Done->0,Iter::Step::Yielded(item,following)->item+following}}\nfn example(){assert(read(0)==1);assert(read(2)==0)}";
        let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, crate::session::CompilationOutcome::Accepted { .. }),
            "{outcome:?}"
        );
        let source = "type Cell={mut count:int}\ntype Choice{Empty,Value(Cell)}\nfn choose(flag:bool,cell:Cell)->Choice{if flag{Choice::Value(cell)}else{Choice::Empty}}\nfn example(flag:bool){let mut original=Cell.{count:0};let choice=choose(flag,original);match choice{Choice::Empty->(),Choice::Value(payload)->{let mut changed=payload;changed.count+=1}}}";
        let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome,crate::session::CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|matches!(diagnostic.code.as_str(),"E0520"|"E0522"))),
            "{outcome:?}"
        );
    }
    #[test]
    fn standard_step_and_source_types_check_real_constructor_and_callable_boundaries() {
        let source = "fn yielded()->Iter::Step<int,int>{Iter::Step::Yielded(7,1)}\nfn done()->Iter::Step<int,int>{Iter::Step::Done}\nfn pull(source:Iter::Source<int,int>)->Iter::Step<int,int>{source.step(0)}\nfn example(){let result=yielded();assert(result is Iter::Step::Yielded(_,_));let end=done();assert(end is Iter::Step::Done);let mut cursor:Iter::Cursor<int>=.{state:0,ended:false};cursor.state+=1;assert(cursor.state==1);let second=pull(.{step:\\state:int->yielded()});assert(second is Iter::Step::Yielded(_,_))}";
        let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome, crate::session::CompilationOutcome::Accepted { .. }),
            "{outcome:?}"
        );
        let source = "fn wrong()->Iter::Step<int,str>{Iter::Step::Yielded(\"bad\",1)}\nfn example(){let source:Iter::Source<int,int>=.{step:\\state:int->wrong()}}";
        let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome,crate::session::CompilationOutcome::Rejected {ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{outcome:?}"
        );
    }
    #[test]
    fn schemas_preserve_written_dimensions_and_the_readonly_step_field() {
        let parsed = ril_syntax::parse(
            "type State=Iter::Source<[2]int,fn(mut []int)->() &mut>\ntype C=Iter::Cursor<[3]int>",
        );
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let StmtKind::Type(declaration) = &parsed.program.statements[0].kind else {
            panic!()
        };
        let source = declaration.value.as_ref().unwrap();
        let TypeKind::Name { arguments, .. } = &source.kind else {
            panic!()
        };
        let TypeKind::Record { fields, row: None } = schema(source).unwrap().kind else {
            panic!()
        };
        assert!(!fields[0].mutable);
        let TypeKind::Callable {
            parameters,
            result,
            annotations,
        } = &fields[0].ty.kind
        else {
            panic!()
        };
        assert_eq!(parameters[0].mode, ParameterMode::Read);
        assert_eq!(parameters[0].ty.as_ref(), Some(&arguments[0]));
        assert!(annotations.is_empty());
        let TypeKind::Name {
            path,
            arguments: step_arguments,
        } = &result.as_ref().unwrap().kind
        else {
            panic!()
        };
        assert_eq!(path, &["Iter", "Step"]);
        assert_eq!(step_arguments, arguments);
        let StmtKind::Type(cursor) = &parsed.program.statements[1].kind else {
            panic!()
        };
        let TypeKind::Record { fields, .. } = schema(cursor.value.as_ref().unwrap()).unwrap().kind
        else {
            panic!()
        };
        assert!(fields.iter().all(|field| field.mutable));
    }
    #[test]
    fn real_generic_step_instances_use_complete_distinct_owners() {
        let mut checker = Checker::new(FileId(0));
        checker.register_standard_iter_types();
        let span = Span {
            file: FileId(0),
            start: 0,
            end: 0,
        };
        let state = TypeExpr {
            hir_id: None,
            text: String::new(),
            span,
            kind: TypeKind::Tuple(vec![
                named("int", vec![], span),
                named("bool", vec![], span),
            ]),
        };
        let declaration = checker.types["Iter::Step"].clone();
        let first = checker.applied_type(
            &declaration,
            &[state.clone(), named("str", vec![], span)],
            span,
        );
        let second =
            checker.applied_type(&declaration, &[state, named("bool", vec![], span)], span);
        assert_ne!(first, second);
        assert_eq!(
            checker
                .constructors
                .values()
                .filter(|constructor| constructor.owner == first)
                .count(),
            2
        );
        let yielded = checker
            .constructors
            .values()
            .find(|constructor| {
                constructor.owner == first && constructor.tag == "Iter::Step::Yielded"
            })
            .unwrap();
        assert_eq!(
            yielded.payload,
            Ty::Tuple(vec![
                Ty::Str,
                Ty::Tuple(vec![Ty::Int("int".into()), Ty::Bool])
            ])
        );
    }
}
