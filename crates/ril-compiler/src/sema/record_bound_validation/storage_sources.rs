//! Replay immutable storage declarations and every actual assignment occurrence.
//! Source rows are duties, never a substitute for the ordinary access checker.
use super::*;
use crate::sema::{
    effect_identity::InvocationContext,
    facts::ScopeId,
    model::{BindingId, Constant},
    source_reception::{self, Construction},
    storage_sources::{BindingSource, StorageDestination, StorageObservation},
};
use ril_syntax::ast::{Pattern, PatternKind};

impl Replay<'_> {
    pub(super) fn storage_binding_source_key(
        &self,
        expression: &Expr,
        value: &Value,
        _context: InvocationContext,
        _sites: &super::explicit_named::SourceSites<'_>,
    ) -> Option<Check<ArgumentKey>> {
        let mut path = Vec::new();
        let name = expression_path(expression, &mut path, &mut 4096)?;
        if value.sources.len() != 1 { return None; }
        let id = *value.sources.first()?;
        let rows: Vec<_> = self.facts.binding_sources.iter().filter(|row| row.binding == id).collect();
        if rows.is_empty() { return None; }
        Some((|| {
            require(rows.len() == 1, "storage Name has duplicate declaration sources")?;
            let binding = self.facts.bindings.get(id).ok_or_else(|| "storage Name binding is absent".to_owned())?;
            require(binding.name == name, "storage source borrowed another named binding")?;
            let key = rows[0].key.as_ref().ok_or_else(|| "storage declaration source remains unknown".to_owned())?;
            projection(key, &path).cloned().ok_or_else(|| "storage path has no original declared source coordinate".to_owned())
        })())
    }

    fn storage_observation(
        &self,
        observed: StorageObservation,
        syntax: &Expr,
        context: InvocationContext,
    ) -> Check<&Value> {
        let original = self.facts.expressions.get(observed.expression)
            .ok_or_else(|| "storage operand observation is outside its arena".to_owned())?;
        require(original.span == syntax.span
            && observed.allocation_epoch <= self.facts.allocation_history.len()
            && self.facts.invocation_expressions.iter().filter(|row|
                row.expression == observed.expression && row.context == context).count() == 1,
            "storage operand belongs to another syntax, epoch or full invocation context")?;
        Ok(&original.value)
    }

    fn storage_activation(&self, context: InvocationContext, activation: ScopeId) -> Check {
        require(self.facts.allocated_scopes.contains(&activation), "storage activation is not allocated")?;
        if let Some(id) = context.closure_invocation {
            let call = self.facts.closure_invocations.get(id.0 as usize)
                .filter(|call| call.id == id)
                .ok_or_else(|| "storage closure activation is absent".to_owned())?;
            return require(call.activation == Some(activation)
                && context.closure == Some(call.closure)
                && self.facts.closures.get(call.closure).is_some_and(|closure|
                    closure.site.map(CallableOwner::Lambda) == context.owner),
                "storage closure source borrowed another activation");
        }
        if context.invocation.is_some() {
            return require(self.facts.invocations.iter().any(|summary|
                summary.activation == Some(activation) && summary.context == Some(context)),
                "storage named source borrowed another actual activation");
        }
        require(context.owner == Some(CallableOwner::Global) && activation == ScopeId(0),
            "storage source has no original global or callable activation")
    }

    fn storage_declared_key(
        &self,
        row: &BindingSource,
        sites: &super::explicit_named::SourceSites<'_>,
    ) -> Check<Option<ArgumentKey>> {
        let binding = self.facts.bindings.get(row.binding)
            .ok_or_else(|| "storage declaration binding is absent".to_owned())?;
        require(!binding.parameter && binding.owner == row.activation,
            "storage declaration borrowed a parameter or another frame")?;
        self.storage_activation(row.context, row.activation)?;
        let declarations: Vec<_> = sites.bindings.iter().filter(|site|
            Some(site.owner) == row.context.owner && site.binding.pattern.span == row.declaration).collect();
        let [declaration] = declarations.as_slice() else {
            return Err("storage declaration is not a unique original binding AST".into());
        };
        let declaration = declaration.binding;
        require(row.declared == declaration.ty.is_some(), "storage declaration changed written/inferred origin")?;
        let mut names = Vec::new();
        pattern_paths(&declaration.pattern, &mut Vec::new(), true, &mut names, &mut 4096)?;
        let names: Vec<_> = names.iter().filter(|(span,name,_,_)|
            *span == binding.span && *name == binding.name).collect();
        let [(_,_,path,known)] = names.as_slice() else {
            return Err("storage binding does not belong to its original pattern".into());
        };
        require(row.path == *path, "storage binding changed its declared pattern projection")?;
        let initial = self.storage_observation(row.initializer, &declaration.value, row.context)?;
        require(initial.ty != Ty::Never && initial.sources.iter().all(|source| *source < row.binding),
            "storage initializer is abrupt or creates a forward declaration cycle")?;
        if !known { return Ok(None); }
        let key = if let Some(syntax) = &declaration.ty {
            let scope = self.lambda_input_scope(declarations[0].owner)?;
            let key = self.input_callable_source_key(syntax, &scope)?;
            super::call_input_source::input_select_key(
                &key, &self.binding_source_selections(binding, declarations[0].owner)?, 0)?
        } else {
            self.original_source_key(&declaration.value, initial, row.context, sites)?
        };
        Ok(projection(&key, path).cloned())
    }

    pub(super) fn storage_sources(&self) -> Result<(), Failure> {
        let fallback = self.facts.source_program.as_ref().and_then(|program|program.statements.first())
            .map(|statement|statement.span).unwrap_or(Span {file:ril_compiler_core::source::FileId(0),start:0,end:0});
        let run = || -> Check {
            let sites = super::explicit_named::source_sites(self.facts)?;
            require(self.facts.binding_sources.len() <= LIMIT && self.facts.storage_writes.len() <= LIMIT,
                "storage source replay budget exhausted")?;
            let mut declarations = BTreeMap::new();
            for row in &self.facts.binding_sources {
                require(declarations.insert(row.binding, row).is_none(), "storage declaration was recorded twice")?;
                // An unresolved source stays conservative. A present key must
                // independently equal its actual source declaration/initializer.
                let reconstructed = self.storage_declared_key(row, &sites);
                if let Some(key) = &row.key {
                    require(source_reception::complete(key, &mut 4096).is_some()
                        && reconstructed? == Some(key.clone()),
                        "storage declaration key differs from its original complete source")?;
                } else {
                    // Structural identity still has to validate even when the
                    // source key itself is legitimately unavailable.
                    let binding = self.facts.bindings.get(row.binding)
                        .ok_or_else(|| "unknown storage declaration binding is absent".to_owned())?;
                    require(!binding.parameter && binding.owner == row.activation,
                        "unknown storage declaration borrowed another binding")?;
                    self.storage_activation(row.context,row.activation)?;
                    let originals:Vec<_>=sites.bindings.iter().filter(|site|
                        Some(site.owner)==row.context.owner && site.binding.pattern.span==row.declaration).collect();
                    require(originals.len()==1 && row.declared==originals[0].binding.ty.is_some(),
                        "unknown storage declaration lost its original AST")?;
                    self.storage_observation(row.initializer,&originals[0].binding.value,row.context)?;
                    let mut names=Vec::new();
                    pattern_paths(&originals[0].binding.pattern,&mut Vec::new(),true,&mut names,&mut4096)?;
                    require(names.iter().any(|(span,name,path,_)|*span==binding.span && *name==binding.name && *path==row.path),
                        "unknown storage declaration changed its actual pattern path")?;
                }
            }
            // The original binding arena independently requires ledger rows.
            // Removing a ledger and every later write certificate cannot hide
            // a local declaration that was actually introduced by the program.
            for (id,binding) in self.facts.bindings.iter().enumerate().filter(|(_,binding)|!binding.parameter) {
                let mut matches=false;
                for site in &sites.bindings {
                    let mut names=Vec::new();
                    pattern_paths(&site.binding.pattern,&mut Vec::new(),true,&mut names,&mut4096)?;
                    matches |= names.iter().any(|(span,name,_,_)|*span==binding.span && *name==binding.name);
                }
                if matches { require(declarations.contains_key(&id), "an actual binding lost its immutable storage source")?; }
            }
            let mut covered = BTreeSet::new();
            for write in &self.facts.storage_writes {
                require(covered.insert(write.rhs.expression), "storage writes borrowed one RHS occurrence twice")?;
                self.storage_activation(write.context,write.activation)?;
                let originals:Vec<_>=sites.assignments.iter().filter(|site|
                    Some(site.owner)==write.context.owner && site.target.span==write.span
                    && site.operator==write.operator).collect();
                let [site]=originals.as_slice() else { return Err("storage write is not an original assignment".into()); };
                let input=self.storage_observation(write.rhs,site.value,write.context)?;
                require(input.ty!=Ty::Never,"completed RHS storage receipt claims an abrupt expression")?;
                let expected=match (&site.target.kind,&write.destination) {
                    (ExprKind::Name(name),StorageDestination::Binding(id))=>{
                        let binding=self.facts.bindings.get(*id).ok_or_else(||"storage target binding is absent".to_owned())?;
                        require(binding.name==*name && binding.mode.is_reassignable() && write.completed,
                            "storage Name destination differs from its real assignable binding")?;
                        let declaration=declarations.get(id).ok_or_else(||"storage target lost its declaration source".to_owned())?;
                        require(declaration.initializer.expression<write.rhs.expression,
                            "storage target declaration is later than its write")?;
                        if binding.owner!=write.activation {
                            let captured=if let Some(index)=write.context.closure {
                                self.facts.closures.get(index).is_some_and(|closure|
                                    closure.lexical.get(name)==Some(id) && closure.captures.contains(id))
                            } else if let Some(CallableOwner::Function(owner))=write.context.owner {
                                self.facts.functions.iter().any(|function|function.definition==owner
                                    && function.lexical.get(name)==Some(id) && function.captures.contains(id))
                            } else {false};
                            require(captured,"storage target is not the actual captured lexical binding")?;
                        } else {
                            // Without a recorded target read, two simultaneously
                            // plausible same-named slots cannot prove a choice.
                            let alternatives=declarations.values().filter(|candidate|
                                candidate.activation==write.activation && candidate.initializer.expression<write.rhs.expression
                                && self.facts.bindings.get(candidate.binding).is_some_and(|other|
                                    other.name==*name && other.mode.is_reassignable())).count();
                            require(alternatives==1,"storage target has ambiguous same-name declaration sources")?;
                        }
                        declaration.key.clone()
                    }
                    (ExprKind::Field{base,field,..},StorageDestination::Projection{receiver,selector,slot})=>{
                        require(selector.is_none() && *slot==field.parse().map(Slot::Tuple).unwrap_or_else(|_|Slot::Field(field.clone())),
                            "storage field destination changed its original projection")?;
                        self.storage_write_interval(write.rhs,*receiver,site.value,write.context)?;
                        let source=self.storage_observation(*receiver,base,write.context)?;
                        if source.ty==Ty::Never {
                            require(!write.completed && write.expected.is_none(),"abrupt storage receiver claims a completed write")?;
                            continue;
                        }
                        require(write.completed,"normal storage field write was marked aborted")?;
                        let key=self.original_source_key(base,source,write.context,&sites)?;
                        projection(&key,std::slice::from_ref(slot)).cloned()
                    }
                    (ExprKind::Index{base,index,..},StorageDestination::Projection{receiver,selector,slot})=>{
                        self.storage_write_interval(write.rhs,*receiver,site.value,write.context)?;
                        let source=self.storage_observation(*receiver,base,write.context)?;
                        if source.ty==Ty::Never {
                            require(!write.completed && selector.is_none() && write.expected.is_none(),"abrupt indexed receiver claims a write")?;
                            continue;
                        }
                        let selector=selector.ok_or_else(||"storage index lost its actual selector".to_owned())?;
                        self.storage_write_interval(*receiver,selector,base,write.context)?;
                        let selected=self.storage_observation(selector,index,write.context)?;
                        if selected.ty==Ty::Never {
                            require(!write.completed && write.expected.is_none(),"abrupt storage selector claims a write")?;
                            continue;
                        }
                        require(write.completed,"normal storage index write was marked aborted")?;
                        let key=self.original_source_key(base,source,write.context,&sites)?;
                        let expected_slot=if matches!(key,ArgumentKey::Map{..}) { Slot::AnyIndex }
                            else if let Some(Constant::Integer(index))=selected.constant { Slot::Index(index as i64) }
                            else { Slot::AnyIndex };
                        require(*slot==expected_slot,"storage index changed its actual selected slot")?;
                        if let ArgumentKey::Map{key:map_key,..}=&key {
                            let actual=self.original_source_key(index,selected,write.context,&sites).ok();
                            let fresh=source_reception::construction(index,&mut4096);
                            require(storage_compatible(map_key,actual.as_ref(),fresh.as_ref())==Some(true),
                                "storage map selector does not fit its original key source")?;
                        }
                        projection(&key,std::slice::from_ref(slot)).cloned()
                    }
                    _=>return Err("storage write changed its real destination form".into()),
                };
                require(expected==write.expected,"storage write borrowed a different expected source schema")?;
                let expected=expected.ok_or_else(||"storage write has an unresolved original destination source".to_owned())?;
                let actual=self.original_source_key(site.value,input,write.context,&sites).ok();
                let fresh=source_reception::construction(site.value,&mut4096);
                let answer=if source_reception::sensitive(&expected,&mut4096)==Some(false) {Some(true)}
                    else if write.operator!="=" {Some(false)} else {storage_compatible(&expected,actual.as_ref(),fresh.as_ref())};
                require(answer==Some(true),"storage original RHS does not prove the destination source coordinates")?;
            }
            // Reverse coverage starts from actual RHS roots, not from a
            // supposedly complete list supplied by the write certificates.
            for site in &sites.assignments {
                for row in self.facts.invocation_expressions.iter().filter(|row|row.context.owner==Some(site.owner)) {
                    let value=self.facts.expressions.get(row.expression)
                        .ok_or_else(||"storage reverse coverage expression is absent".to_owned())?;
                    if value.span==site.value.span && value.value.ty!=Ty::Never {
                        require(covered.contains(&row.expression),"an actual assignment lost its storage reception receipt")?;
                    }
                }
            }
            Ok(())
        };
        run().map_err(|message|(fallback,None,message))
    }

    fn storage_write_interval(&self,before:StorageObservation,after:StorageObservation,before_syntax:&Expr,context:InvocationContext)->Check {
        require(before.expression<after.expression && before.allocation_epoch<=after.allocation_epoch,
            "storage operand order or allocation epochs moved backwards")?;
        require(!self.facts.invocation_expressions.iter().any(|row|
            row.context==context && before.expression<row.expression && row.expression<after.expression
            && self.facts.expressions.get(row.expression).is_some_and(|value|value.span==before_syntax.span)),
            "storage target borrowed a later repeated RHS occurrence")
    }
}

pub(in crate::sema::record_bound_validation) fn storage_compatible(expected:&ArgumentKey,actual:Option<&ArgumentKey>,fresh:Option<&Construction>)->Option<bool> {
    if contains_callable(expected,&mut4096)? { return None; }
    if source_reception::sensitive(expected,&mut4096)==Some(false) {return Some(true);}
    if let Some(actual)=actual {return source_reception::compatible(expected,actual,fresh,&mut4096);}
    match(expected,fresh) {
        (ArgumentKey::Array{length,element},Some(Construction::Array(items))) if items.is_empty()=>{
            source_reception::complete(element,&mut4096)?;
            Some(length.as_ref().is_none_or(|length|length=="const(int:0)"))
        }
        _=>None,
    }
}

fn contains_callable(key:&ArgumentKey,work:&mut usize)->Option<bool> {
    *work=work.checked_sub(1)?;
    let children:Vec<&ArgumentKey>=match key {
        ArgumentKey::Callable{..}=>return Some(true),
        ArgumentKey::Array{element,..}=>vec![element],
        ArgumentKey::Map{key,value}=>vec![key,value],
        ArgumentKey::Name{arguments,..}|ArgumentKey::Tuple(arguments)=>arguments.iter().collect(),
        ArgumentKey::Record{fields,row}=>fields.iter().map(|field|&field.2).chain(row.iter().map(|row|row.as_ref())).collect(),
        ArgumentKey::Closed(_)=>return None,
        ArgumentKey::Binder{..}=>vec![],
    };
    for child in children {if contains_callable(child,work)?{return Some(true);}}
    Some(false)
}

fn projection<'a>(mut key:&'a ArgumentKey,path:&[Slot])->Option<&'a ArgumentKey> {
    for slot in path {
        while let ArgumentKey::Name{name,arguments}=key {
            if !matches!(name.as_str(),"Immut"|"Prelude::Immut") || arguments.len()!=1 {break;}
            key=&arguments[0];
        }
        key=match(key,slot) {
            (ArgumentKey::Record{fields,..},Slot::Field(name))=>&fields.iter().find(|field|&field.0==name)?.2,
            (ArgumentKey::Tuple(items),Slot::Tuple(index))=>items.get(*index as usize)?,
            (ArgumentKey::Array{element,..},Slot::Index(_)|Slot::AnyIndex)=>element,
            (ArgumentKey::Map{value,..},Slot::Index(_)|Slot::AnyIndex)=>value,
            _=>return None,
        };
    }
    Some(key)
}

fn expression_path<'a>(expression:&'a Expr,path:&mut Vec<Slot>,work:&mut usize)->Option<&'a str> {
    *work=work.checked_sub(1)?;
    match &expression.kind {
        ExprKind::Name(name)=>Some(name),
        ExprKind::Field{base,field,..}=>{let root=expression_path(base,path,work)?;path.push(field.parse().map(Slot::Tuple).unwrap_or_else(|_|Slot::Field(field.clone())));Some(root)},
        ExprKind::Index{base,..}=>{let root=expression_path(base,path,work)?;path.push(Slot::AnyIndex);Some(root)},
        _=>None,
    }
}

fn pattern_paths(pattern:&Pattern,path:&mut Vec<Slot>,known:bool,out:&mut Vec<(Span,String,Vec<Slot>,bool)>,work:&mut usize)->Check {
    *work=work.checked_sub(1).ok_or_else(||"storage pattern replay exceeds its budget".to_owned())?;
    match &pattern.kind {
        PatternKind::Name(name)=>out.push((pattern.span,name.clone(),path.clone(),known)),
        PatternKind::Mode{pattern,..}=>pattern_paths(pattern,path,known,out,work)?,
        PatternKind::Tuple(items)=>for(index,item)in items.iter().enumerate(){path.push(Slot::Tuple(index as u32));pattern_paths(item,path,known,out,work)?;path.pop();},
        PatternKind::Record{fields,rest_binding,..}=>{
            for field in fields {path.push(Slot::Field(field.name.clone()));pattern_paths(&field.pattern,path,known,out,work)?;path.pop();}
            if let Some(name)=rest_binding{out.push((pattern.span,name.clone(),Vec::new(),false));}
        }
        PatternKind::Constructor{arguments,..}|PatternKind::Alternative(arguments)=>for argument in arguments{pattern_paths(argument,&mut Vec::new(),false,out,work)?;},
        PatternKind::Type{binder:Some(name),..}=>out.push((pattern.span,name.clone(),Vec::new(),false)),
        _=>{}
    }
    Ok(())
}
