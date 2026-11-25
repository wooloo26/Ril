use std::path::PathBuf;

use ril_source::diag::{Code, Diagnostic};

use ril_syntax::syntax::{Import, ImportTarget, Name, StmtId, StmtKind, Visibility};

use super::{Entry, Program, ScopeId, Target, module_name};

impl Program {
    pub(super) fn load_imports(
        &mut self,
        mut pending: Vec<(ScopeId, StmtId)>,
        errors: &mut Vec<Diagnostic>,
    ) {
        while !pending.is_empty() {
            let mut retry = Vec::new();
            let mut missing = Vec::new();
            let mut changed = false;
            for (scope, id) in pending {
                let file = self.scope(scope).file;
                let stmt = self.file(file).ast.stmt(id);
                let StmtKind::Import(import) = &stmt.value.kind else {
                    continue;
                };
                let vis = stmt.value.visibility;
                match self.import_targets(scope, import) {
                    Ok(targets) => {
                        for (name, entry) in targets {
                            if vis > entry.visibility {
                                errors.push(Diagnostic::error(
                                    Code::E0201,
                                    name.span,
                                    "import visibility would widen the target visibility",
                                ));
                            } else if let Err(err) = self.insert(
                                scope,
                                &name,
                                Entry {
                                    target: entry.target,
                                    visibility: vis,
                                },
                            ) {
                                errors.push(err);
                            }
                        }
                        changed = true;
                    }
                    Err(err) if err.code == Some(Code::E0209) => {
                        retry.push((scope, id));
                        missing.push(err);
                    }
                    Err(err) => errors.push(err),
                }
            }
            if !changed {
                errors.extend(missing);
                break;
            }
            pending = retry;
        }
    }

    fn import_targets(
        &self,
        scope: ScopeId,
        import: &Import,
    ) -> Result<Vec<(Name, Entry)>, Diagnostic> {
        let mut namespace = scope;
        let mut path_vis = Visibility::Public;
        if let Some(parts) = &import.file {
            let path: PathBuf = parts.iter().map(|name| name.value.as_str()).collect();
            let anchor = parts
                .first()
                .unwrap_or_else(|| ril_source::ice!("empty import path"));
            let filename = parts.last().unwrap_or(anchor);
            let key = if anchor.value == "pkg" {
                let mut key = PathBuf::from(&self.scope(scope).package);
                key.extend(parts.iter().skip(1).map(|name| &name.value));
                key
            } else {
                path.clone()
            };
            namespace = *self.modules.get(&key).ok_or_else(|| {
                Diagnostic::error(
                    Code::E0208,
                    filename.span,
                    format!("missing module {}", path.display()),
                )
            })?;
            path_vis = self.scope(namespace).cap;
            if self.scope(namespace).package != self.scope(scope).package
                && path_vis < Visibility::Public
            {
                return Err(Diagnostic::error(
                    Code::E0201,
                    filename.span,
                    "module has package visibility",
                ));
            }
        }
        for (index, part) in import.modules.iter().enumerate() {
            if import.file.is_none() && part.value == "Super" {
                namespace = self.scope(namespace).parent.ok_or_else(|| {
                    Diagnostic::error(Code::E0208, part.span, "no enclosing module")
                })?;
            } else {
                let target = self.lookup(scope, namespace, part, Code::E0209)?;
                if let Some(entry) = self.scope(namespace).names.get(&part.value)
                    && (import.file.is_some() || index != 0)
                {
                    path_vis = path_vis.min(entry.visibility);
                }
                namespace = self.namespace(target).ok_or_else(|| {
                    Diagnostic::error(Code::E0208, part.span, "import path does not name a module")
                })?;
            }
        }
        let mut bindings = Vec::new();
        match &import.target {
            ImportTarget::Module(alias) => {
                let name = if let Some(alias) = alias {
                    alias.clone()
                } else if let Some(name) = import.modules.last() {
                    name.clone()
                } else {
                    let filename = import
                        .file
                        .as_ref()
                        .and_then(|parts| parts.last())
                        .unwrap_or_else(|| ril_source::ice!("import has no module name"));
                    module_name(filename)?
                };
                bindings.push((
                    name,
                    Entry {
                        target: Target::Module(namespace),
                        visibility: path_vis,
                    },
                ));
            }
            ImportTarget::Items(items) => {
                for (name, alias) in items {
                    let target = self.lookup(scope, namespace, name, Code::E0209)?;
                    let visibility = self
                        .scope(namespace)
                        .names
                        .get(&name.value)
                        .map_or(path_vis, |entry| path_vis.min(entry.visibility));
                    bindings.push((
                        alias.as_ref().unwrap_or(name).clone(),
                        Entry { target, visibility },
                    ));
                }
            }
            ImportTarget::Glob => {
                for (name, entry) in &self.scope(namespace).names {
                    if self.visible(namespace, scope, entry.visibility) {
                        bindings.push((
                            Name::new(name.clone(), self.import_span(import)),
                            Entry {
                                target: entry.target,
                                visibility: path_vis.min(entry.visibility),
                            },
                        ));
                    }
                }
            }
        }
        Ok(bindings)
    }

    fn import_span(&self, import: &Import) -> ril_source::span::Span {
        import
            .modules
            .last()
            .or_else(|| import.file.as_ref()?.last())
            .unwrap_or_else(|| ril_source::ice!("import has no span"))
            .span
    }
}
