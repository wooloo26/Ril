use std::path::PathBuf;

use ril_source::{
    diag::Diagnostic,
    span::{FileId, Span},
};
use ril_syntax::syntax::{Name, StmtId, Visibility};

use crate::{DefinitionKind, Entry, PrimitivePhase, Program, ScopeId, Target, builtins};

const LANGUAGE_PRIMITIVES: &[(PrimitivePhase, Visibility, &[&str])] = &[
    (
        PrimitivePhase::Both,
        Visibility::Public,
        &["bool", "int", "f64", "str", "bytes", "never", "Type"],
    ),
    (
        PrimitivePhase::Static,
        Visibility::Public,
        &["KeyOf", "Nominal", "Reflects", "Implies", "Ensures"],
    ),
];

impl Program {
    pub(crate) fn init_prelude(&mut self) {
        let file = FileId::BUILTIN;
        self.prelude = self.new_scope(file, "ril".into(), None, Visibility::Public);
        self.scope_mut(self.prelude).primitive_module = Some("Prelude");
        for &(phase, visibility, names) in LANGUAGE_PRIMITIVES {
            for &name in names {
                self.primitive(self.prelude, name, phase, visibility);
            }
        }
    }

    pub(crate) fn attach_stdlib(
        &mut self,
        imports: &mut Vec<(ScopeId, StmtId)>,
        errors: &mut Vec<Diagnostic>,
    ) {
        for module in builtins::stdlib_modules() {
            let key = PathBuf::from(module.import_key);
            if module.module_name == "Prelude" {
                if self.scope(self.prelude).file != FileId::BUILTIN {
                    continue;
                }
                let file = module.file.clone();
                let id = file.id;
                let items = file.ast.items.clone();
                self.stdlib_files.insert(id);
                self.files.insert(id.0, file);
                self.scope_mut(self.prelude).file = id;
                self.roots.insert(id.0, self.prelude);
                self.modules.entry(key).or_insert(self.prelude);
                self.collect(self.prelude, &items, imports, errors);
                continue;
            }
            if self.modules.contains_key(&key) {
                continue;
            }
            let file = module.file.clone();
            let id = file.id;
            let items = file.ast.items.clone();
            let scope = self.new_scope(id, "ril".into(), None, Visibility::Public);
            self.scope_mut(scope).primitive_module = Some(module.module_name);
            self.stdlib_files.insert(id);
            self.files.insert(id.0, file);
            self.roots.insert(id.0, scope);
            self.modules.insert(key, scope);
            self.collect(scope, &items, imports, errors);
        }
    }

    fn primitive(
        &mut self,
        scope: ScopeId,
        name: &str,
        phase: PrimitivePhase,
        visibility: Visibility,
    ) {
        let def = self.new_def(
            scope,
            Name::new(name.into(), Span::new(FileId::BUILTIN, 0, 0)),
            DefinitionKind::Primitive(phase),
            None,
            visibility,
        );
        self.scope_mut(scope).names.insert(
            name.into(),
            Entry {
                target: Target::Def(def),
                visibility,
            },
        );
    }
}
