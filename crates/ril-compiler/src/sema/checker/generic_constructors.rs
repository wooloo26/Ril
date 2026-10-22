//! Constructor instances retain their owner identity and instantiated syntax.
//! The private callable identity and the source declaration tag are distinct.
use super::*;
use crate::static_eval::const_nominal::{simple_sort, static_parameter};
#[path = "gadt.rs"]
mod gadt;
std::thread_local! {
    static INSTANCE_DEPTH:std::cell::Cell<usize>=const{std::cell::Cell::new(0)};
}
struct InstanceDepth;
impl InstanceDepth {
    fn enter() -> Option<Self> {
        INSTANCE_DEPTH.with(|depth| {
            if depth.get() >= 64 {
                None
            } else {
                depth.set(depth.get() + 1);
                Some(Self)
            }
        })
    }
}
impl Drop for InstanceDepth {
    fn drop(&mut self) {
        INSTANCE_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

fn instance_identity(tag: &str, owner: &Ty) -> String {
    use std::fmt::Write;
    let source = format!("{tag}\0{owner:?}");
    let mut encoded = String::with_capacity(source.len() * 2 + 20);
    encoded.push_str("ril__constructor_");
    for byte in source.bytes() {
        write!(encoded, "{byte:02x}").unwrap();
    }
    encoded
}
impl Checker {
    /// A sealed nominal's value arguments introduce no type-source
    /// coordinates. This certificate is deliberately limited to all-Const
    /// declarations; a neighbouring Type argument cannot be hidden by it.
    pub(in crate::sema::checker) fn certified_nominal_const_arguments(
        &self,
        syntax: &TypeExpr,
    ) -> bool {
        if self.bounded_static_source_input(syntax).is_none() {
            return false;
        }
        let TypeKind::Name { path, arguments } = &syntax.kind else {
            return false;
        };
        let Some(declaration) = self.types.get(&path.join("::")) else {
            return false;
        };
        if !declaration.nominal
            || declaration.opaque
            || declaration.generics.is_empty()
            || arguments.len() != declaration.generics.len()
            || !self.generic_constructor_contract(declaration)
            || declaration.generics.iter().any(|parameter| {
                !static_parameter(parameter)
                    || matches!(
                        parameter.bound.as_ref().map(|bound| &bound.kind),
                        Some(TypeKind::KeyOf(_))
                    )
                    || !parameter.bound.as_ref().is_some_and(simple_sort)
            })
            || arguments.iter().any(|argument| {
                !crate::static_eval::effects::type_dependencies(argument).is_empty()
            })
        {
            return false;
        }
        crate::static_eval::normalize_constructor_arguments(
            declaration,
            arguments,
            &self.types,
            self.layout,
        )
        .is_ok()
    }

    pub(in crate::sema::checker) fn generic_constructor_contract(
        &self,
        declaration: &TypeDeclaration,
    ) -> bool {
        if declaration.opaque || (!declaration.nominal && declaration.variants.is_empty()) {
            return false;
        }
        if declaration.generics.iter().any(|parameter| {
            if static_parameter(parameter) {
                parameter.default.is_some() || !parameter.bound.as_ref().is_some_and(simple_sort)
            } else {
                parameter.bound.as_ref().is_some_and(|bound|
                    !matches!(&bound.kind,TypeKind::Name{path,arguments} if path==&["Type"]&&arguments.is_empty()))
            }
        }) {return false;}
        declaration.variants.iter().all(|variant| {
            variant.generics.iter().all(|parameter| {
                !static_parameter(parameter)
                    && parameter.default.is_none()
                    && parameter.bound.as_ref().is_none_or(|bound| {
                        !matches!(bound.kind, TypeKind::KindArrow { .. })
                    })
                    && variant.result.as_ref().is_some_and(|result| {
                        self.constructor_parameter_recoverable(result, &parameter.name)
                    })
            }) && variant.result.as_ref().is_none_or(|result| {
                matches!(&result.kind,TypeKind::Name{path,arguments}
                    if path.join("::")==declaration.name && arguments.len()==declaration.generics.len())
            })
        })
    }
    pub(in crate::sema::checker) fn constructor_template_owner(
        &self,
        declaration: &TypeDeclaration,
    ) -> Ty {
        if declaration.generics.is_empty() {
            return Ty::Named(declaration.name.clone());
        }
        Ty::Applied {
            constructor: declaration.name.clone(),
            arguments: declaration
                .generics
                .iter()
                .enumerate()
                .map(|(index, parameter)| {
                    let identity = if declaration.name == "Iter::Step" {
                        format!("std:Iter::Step:{index}:{}", parameter.name)
                    } else {
                        format!(
                            "{}:{}:type:{index}:{}",
                            declaration.span.file.0, declaration.span.start, parameter.name
                        )
                    };
                    if static_parameter(parameter) {
                        TypeArgument::Symbolic(identity)
                    } else {
                        TypeArgument::Type(Box::new(Ty::Generic(identity)))
                    }
                })
                .collect(),
        }
    }
    pub(in crate::sema::checker) fn register_constructor_instance(
        &mut self,
        declaration: &TypeDeclaration,
        arguments: &[TypeExpr],
        owner: &Ty,
        span: Span,
    ) {
        if !self.generic_constructor_contract(declaration) {
            return;
        }
        let mut generics = BTreeSet::new();
        owner.generic_names(&mut generics);
        if !generics.is_empty() {
            return;
        }
        if self.constructors.iter().any(|(identity, constructor)| {
            identity != &constructor.tag && constructor.owner == *owner
        }) {
            return;
        }
        let Some(_depth) = InstanceDepth::enter() else {
            self.unsupported(
                span,
                "constructor instance shape expansion exceeds the implementation traversal budget",
            );
            return;
        };
        // Insert the finite instance's entries before checking payload types, so
        // a recursive mention cannot repeatedly instantiate the same owner.
        let normalized = match crate::static_eval::normalize_constructor_arguments(
            declaration,
            arguments,
            &self.types,
            self.layout,
        ) {
            Ok(arguments) => arguments,
            Err(crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message)) => {
                self.error(code, span, message, []);
                return;
            }
            Err(crate::static_eval::ArgumentNormalizationError::Unsupported(message)) => {
                self.unsupported(span, message);
                return;
            }
        };
        let templates: Vec<_> = self
            .constructors
            .iter()
            .filter(|(identity, constructor)| {
                *identity == &constructor.tag
                    && matches!(&constructor.owner,Ty::Applied {constructor:family,..} if family==&declaration.name)
            })
            .map(|(_, constructor)| constructor.clone())
            .collect();
        if templates.is_empty() {
            return;
        }
        let instance_environment = self.capture_typing_environment();
        let mut pending = vec![];
        for template in templates {
            if !normalized.payloads.contains_key(&template.tag) {
                continue;
            }
            let key = instance_identity(&template.tag, owner);
            let syntax = normalized.payloads[&template.tag].clone();
            self.constructors.insert(
                key.clone(),
                ConstructorInfo {
                    typing_environment: instance_environment.clone(),
                    source: None,
                    source_syntax: None,
                    source_type_witness: None,
                    tag: template.tag,
                    owner: owner.clone(),
                    payload: Ty::Unknown,
                    nominal: template.nominal,
                    has_payload: template.has_payload,
                    payload_syntax: syntax.clone(),
                    span: template.span,
                },
            );
            self.register_constructor_source_type(
                &key,
                &TypeExpr {
                    hir_id: None,
                    text: String::new(),
                    span,
                    kind: TypeKind::Name {
                        path: declaration.name.split("::").map(str::to_owned).collect(),
                        arguments: normalized.arguments.clone(),
                    },
                },
            );
            pending.push((key, syntax));
        }
        for (key, syntax) in pending {
            let payload = syntax
                .as_ref()
                .map(|syntax| self.ty(syntax))
                .unwrap_or(Ty::Unit);
            self.constructors.get_mut(&key).unwrap().payload = payload;
        }
    }
    pub(in crate::sema::checker) fn constructor_generic(
        &mut self,
        value: &mut Value,
        arguments: &[TypeExpr],
        span: Span,
    ) -> bool {
        let Some(name) = value
            .callables
            .iter()
            .find_map(|callable| match callable {
                Callable::Constructor(name) => Some(name.clone()),
                _ => None,
            })
            .or_else(|| {
                value.variant_tag.clone().filter(|tag| {
                    self.constructors
                        .get(tag)
                        .is_some_and(|constructor| !constructor.has_payload)
                })
            })
        else {
            return false;
        };
        let Some(template) = self.constructors.get(&name).cloned() else {
            return false;
        };
        let declaration_name = match &template.owner {
            Ty::Named(name)
            | Ty::Applied {
                constructor: name, ..
            } => name,
            _ => return false,
        };
        let Some(declaration) = self.types.get(declaration_name).cloned() else {
            return false;
        };
        if declaration.generics.is_empty() {
            self.error(
                "E0340",
                span,
                "constructor declaration has no generic parameters",
                [value.cause],
            );
            return true;
        }
        if !self.generic_constructor_contract(&declaration) {
            self.unsupported(span,"constructor instantiation requires proved result equations and parameter constraints");
            return true;
        }
        let normalized = match crate::static_eval::normalize_constructor_arguments(
            &declaration,
            arguments,
            &self.types,
            self.layout,
        ) {
            Ok(arguments) => arguments,
            Err(crate::static_eval::ArgumentNormalizationError::Diagnostic(code, message)) => {
                self.error(code, span, message, []);
                return true;
            }
            Err(crate::static_eval::ArgumentNormalizationError::Unsupported(message)) => {
                self.unsupported(span, message);
                return true;
            }
        };
        if !normalized.payloads.contains_key(&template.tag) {
            self.error(
                "E0301",
                span,
                "constructor result equation excludes the requested instance",
                [value.cause],
            );
            return true;
        }
        let owner = self.applied_type(&declaration, &normalized.arguments, span);
        self.register_constructor_instance(&declaration, &normalized.arguments, &owner, span);
        let key = instance_identity(&template.tag, &owner);
        if let Some(instance) = self.constructors.get(&key).cloned() {
            if instance.has_payload {
                value.ty = Ty::Callable(vec![instance.payload], Box::new(instance.owner));
                value.callables = vec![Callable::Constructor(key)];
            } else {
                let payload = self.unit(span);
                *value = self.wrap_constructor(&instance, payload, span);
            }
        } else {
            self.unsupported(
                span,
                "constructor instance retains unresolved type or static arguments",
            );
        }
        true
    }
    pub(in crate::sema::checker) fn constructor_pattern_info(
        &self,
        name: &str,
        source: &Value,
    ) -> Option<ConstructorInfo> {
        let owner = self.expanded(&source.ty, &mut BTreeSet::new());
        self.constructors
            .iter()
            .find_map(|(identity, constructor)| {
                ((identity == name || constructor.tag == name)
                    && self.expanded(&constructor.owner, &mut BTreeSet::new()) == owner)
                    .then(|| constructor.clone())
            })
            .or_else(|| self.conditional_constructor_info(name, &owner))
    }
    /// A concrete indexed sum can exclude only its own declared variant. A
    /// different declaration, unresolved index, or unregistered family supplies
    /// no proof of impossibility.
    pub(in crate::sema::checker) fn constructor_pattern_excluded(
        &self,
        name: &str,
        source: &Value,
    ) -> bool {
        let Ty::Applied {
            constructor: family,
            ..
        } = self.expanded(&source.ty, &mut BTreeSet::new())
        else {
            return false;
        };
        let mut generic = BTreeSet::new();
        source.ty.generic_names(&mut generic);
        if !generic.is_empty() || self.constructor_pattern_info(name, source).is_some() {
            return false;
        }
        let Some(declaration) = self.types.get(&family) else {
            return false;
        };
        self.generic_constructor_contract(declaration)
            && declaration.variants.iter().any(|variant| {
                variant.result.is_some() && format!("{family}::{}", variant.name) == name
            })
            && self
                .constructors
                .values()
                .any(|info| info.owner == source.ty)
    }
    pub(in crate::sema::checker) fn constructor_parameter_recoverable(
        &self,
        syntax: &TypeExpr,
        parameter: &str,
    ) -> bool {
        crate::static_eval::constructor_parameter_recoverable(syntax, parameter, &self.types)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn check(source: &str) -> crate::sema::AnalyzeOutcome {
        let parsed = ril_syntax::parse(source);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let evaluated = crate::static_eval::evaluate(
            &parsed.program,
            ril_compiler_core::target::TargetLayout::POINTER64,
        );
        let mut analyzed = crate::sema::analyze(&evaluated.program, FileId(0));
        analyzed.diagnostics.extend(evaluated.diagnostics);
        analyzed.unsupported.extend(evaluated.unsupported);
        if !analyzed.diagnostics.is_empty() || !analyzed.unsupported.is_empty() {
            analyzed.program = None;
        }
        analyzed
    }
    #[test]
    fn explicit_constructor_instances_keep_owners_and_stable_declaration_tags() {
        let source = "type Token<size:int>(int)\ntype Box<T>{Item(T),Empty}\nfn read(value:Box<int>)->int{match value{Box::Item(number)->number,Box::Empty->0}}\nfn example(){let first:Token<1>=Token<1>(1);let second:Token<2>=Token<2>(2);assert(inner(first)==1);assert(inner(second)==2);let item:Box<int>=Box::Item<int>(3);assert(read(item)==3);let empty:Box<int>=Box::Empty<int>;assert(read(empty)==0)}";
        let result = check(source);
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let facts = result.program.unwrap();
        let constructors = &facts.facts().constructors;
        let token_owner = facts
            .syntax()
            .statements
            .iter()
            .find_map(|statement| match &statement.kind {
                StmtKind::Type(declaration)
                    if declaration
                        .generics
                        .iter()
                        .any(|generic| generic.name == "size") =>
                {
                    Some(declaration.name.clone())
                }
                _ => None,
            })
            .unwrap();
        let tokens:Vec<_>=constructors.values().filter(|constructor|constructor.tag==token_owner&&matches!(&constructor.owner,Ty::Applied{arguments,..} if matches!(arguments.as_slice(),[TypeArgument::Static(_)]))).collect();
        assert_eq!(tokens.len(), 2);
        assert_ne!(tokens[0].owner, tokens[1].owner);
        assert!(
            tokens
                .iter()
                .all(|constructor| constructor.payload == Ty::Int("int".into())
                    && constructor.payload_syntax.is_some())
        );
    }
    #[test]
    fn concrete_gadt_instances_recover_payloads_and_exclude_incompatible_equations() {
        let valid = check(
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn read(value:Expr<int>)->int{match value{Expr::Int(n)->n}}\nfn example(){let value:Expr<int>=Expr::Int(7);assert(read(value)==7)}",
        );
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        let facts = valid.program.unwrap();
        let int_owner = facts
            .facts()
            .constructors
            .values()
            .find(|info| info.tag.ends_with("::Int"))
            .unwrap()
            .owner
            .clone();
        assert!(
            facts
                .facts()
                .constructors
                .values()
                .filter(|info| info.owner == int_owner)
                .all(|info| info.tag.ends_with("::Int"))
        );
        let valid = check(
            "type Box<T>{Item<U>(U)->Box<U>}\nfn read(value:Box<int>)->int{match value{Box::Item(n)->n}}\nfn example(){let item:Box<int>=Box::Item(7);assert(read(item)==7)}",
        );
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        for source in [
            "type Box<T>{Item<U>(U)->Box<U>}\nfn bad(){let value:Box<int>=Box::Item(\"wrong\")}",
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn bad(){let value:Expr<int>=Expr::Bool(true)}",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0301"),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
    }
    #[test]
    fn local_constructor_parameters_require_rigid_recovery_and_all_occurrences_agree() {
        for source in [
            "type Pair<T>=(T,T)\ntype Box<T>{Item<U>(U)->Box<Pair<U>>}\nfn example(){let value:Box<(int,int)>=Box::Item(1)}",
            "type Box<T>{Item<U>(U)->Box<fn(U)->U>}\nfn example(){let value:Box<fn(int)->int>=Box::Item(1)}",
            "type Box<T>{Item<T>(T)->Box<T>}\nfn example(){let value:Box<int>=Box::Item(1)}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_some(),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        for source in [
            "type Drop<T>=int\ntype Box<T>{Item<U>(U)->Box<Drop<U>>}",
            "type Identity=\\T->type<T>\ntype Box<T>{Item<U>(U)->Box<Identity<U>>}",
            "type Box<T>{Item<U>(U)}",
        ] {
            let result = check(source);
            assert!(
                result
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0354"),
                "{source}: {:?} {:?}",
                result.diagnostics,
                result.unsupported
            );
        }
        let result = check(
            "type Box<T>{Item<U>(U)->Box<(U,U)>}\nfn bad(){let value:Box<(int,bool)>=Box::Item(1)}",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn universal_gadt_results_transport_only_the_selected_arm_equation() {
        let valid = check(
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn eval<T>(value:Expr<T>)->T{match value{Expr::Int(n)->n,Expr::Bool(b)->b}}\nfn number<T>(value:Expr<T>)->int{match value{Expr::Int(n)->n,Expr::Bool(_)->0}}\nfn example(){assert(eval(Expr::Int(7))==7);assert(eval(Expr::Bool(true)));assert(number(Expr::Bool(false))==0)}",
        );
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        let valid = check(
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn example<T>(value:Expr<T>){let number:int=match value{Expr::Int(n)->n,Expr::Bool(_)->0}} ",
        );
        assert!(
            valid.program.is_some(),
            "{:?} {:?}",
            valid.diagnostics,
            valid.unsupported
        );
        for source in [
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn bad<T>(value:Expr<T>,other:T)->int{match value{Expr::Int(_)->other+1,Expr::Bool(_)->0}}",
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn bad<T>(value:Expr<T>)->T{match value{Expr::Int(n)->n,Expr::Bool(_)->1}}",
            "type Expr<T>{Int(int)->Expr<int>,Bool(bool)->Expr<bool>}\nfn bad<T>(value:Expr<T>)->Expr<T>{Expr::Int<T>(1)}",
        ] {
            let result = check(source);
            assert!(
                result.program.is_none(),
                "{source}: conditional pattern schema supplied an unrelated type proof"
            );
            assert!(!result.diagnostics.is_empty() || !result.unsupported.is_empty());
        }
    }
    #[test]
    fn closed_aggregate_const_sorts_keep_normalized_instance_identity() {
        let source = "type Token<value:f64>(int)\ntype Point<value:{x:int,y:int}>(int)\ntype Order<value:[str:int]>(int)\nmeta let _=assert(type<Token<0.0>>!=type<Token<-0.0>>)\nmeta let _=assert(type<Token<0.0/0.0>>==type<Token<0.0/0.0>>)\nmeta let _=assert(type<Point<.{x:1,y:2}>>==type<Point<.{y:2,x:1}>>)\nmeta let _=assert(type<Order<[\"a\":1,\"b\":2]>>!=type<Order<[\"b\":2,\"a\":1]>>)\nfn example(){let value:Point<.{x:1,y:2}>=Point<.{y:2,x:1}>(7);assert(inner(value)==7)}";
        let outcome = crate::session::Session::new(source.as_bytes().to_vec()).verify();
        assert!(outcome.is_ok(), "{outcome:?}");
        for (source, code) in [
            ("type Bad<value:[f64:int]>(int)", "E0328"),
            ("type Bad<value:[-1]int>(int)", "E0815"),
            (
                "type Point<value:{x:int,y:int}>(int)\nfn bad(){let value:Point<.{x:1,y:2}>=Point<.{x:1,y:3}>(7)}",
                "E0301",
            ),
            (
                "type Point<value:{x:int,y:int}>(int)\nfn bad(){let value=Point<.{x:1,y:\"wrong\"}>(7)}",
                "E0323",
            ),
            (
                "type Fixed<value:[2]int>(int)\nfn bad(){let value=Fixed<[1]>(7)}",
                "E0323",
            ),
        ] {
            let outcome = crate::session::Session::new(source.as_bytes().to_vec()).check();
            let crate::session::CompilationOutcome::Rejected { diagnostics } = outcome else {
                panic!("{source}: {outcome:?}");
            };
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic.code == code),
                "{source}: {diagnostics:?}"
            );
        }
    }
    #[test]
    fn generic_wrapping_never_launders_payload_authority_or_static_sorts() {
        let result = check(
            "type Cell={mut value:int}\ntype Wrap<T>(T)\nfn example(mut cell:Cell)&mut{let wrapped=Wrap<Cell>(cell);let mut alias=^mut inner(wrapped);alias.value+=1}",
        );
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0520"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check("type Token<size:int>(int)\nfn example(){let value=Token<\"bad\">(1)}");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0323"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check("type Token<size:int>(int)\nfn example(){let value=Token(1)}");
        assert!(!result.unsupported.is_empty(), "{:?}", result.diagnostics);
        let result =
            check("type Wrap<T>(T)\nfn example(){let value:Wrap<int>=Wrap<str>(\"text\")}");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0301"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
    #[test]
    fn explicit_expected_instances_supply_arguments_after_declaration_selection() {
        let result = check(
            "type Token<size:int>(int)\ntype Box<T>{Item(T),Empty}\nfn example(){let value:Token<1>=Token(1);assert(inner(value)==1);let item:Box<int>=Box::Item(2);let empty:Box<int>=Box::Empty;assert(item is Box::Item(2));assert(empty is Box::Empty)}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "type Wrap<T=int>(T)\nfn example(){let value:Wrap=Wrap(1);assert(inner(value)==1)}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check("type Wrap<T=U,U=int>(T)");
        assert!(
            result
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0320"),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result = check(
            "type Token<size:int>(int)\nfn make(flag:bool)->Token<1>{if flag{return Token(1)};Token(2)}\nfn example(){let make:fn()->Token<1>=\\->Token(3);let value=make()}",
        );
        assert!(
            result.program.is_some(),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
        let result =
            check("type Token<size:int>(int)\nfn make()->Token<1>{{Token(1)};Token<1>(2)}");
        assert!(
            !result.unsupported.is_empty(),
            "discarded inner block gained an unrelated expected type: {:?}",
            result.diagnostics
        );
    }
    #[test]
    fn expanding_instance_families_stop_before_exhausting_the_compiler_stack() {
        let parsed =
            ril_syntax::parse("type Growing<T>(Growing<[]T>)\nfn consume(value:Growing<int>){}");
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        let result = crate::sema::analyze(&parsed.program, FileId(0));
        assert!(result.program.is_none());
        assert!(
            result
                .unsupported
                .iter()
                .any(|feature| feature.description.contains("instance shape expansion")),
            "{:?} {:?}",
            result.diagnostics,
            result.unsupported
        );
    }
}
