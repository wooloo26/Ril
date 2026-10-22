//! Frontend definitions and the semantic verification boundary.
use ril_compiler_core::{ids::DefinitionId, source::Span};
pub mod application;
pub mod blocks;
pub mod execution;
pub mod lexical;
pub mod nodes;
pub use nodes::HirProgram;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct Definition {
    pub id: DefinitionId,
    pub span: Span,
}

/// Construction is private to the compiler; IR data alone does not imply verification.
#[derive(Debug)]
pub struct VerifiedProgram {
    definitions: Vec<Definition>,
    syntax: Arc<ril_syntax::ast::Program>,
    resolved_source: Arc<ril_syntax::ast::Program>,
    facts: Arc<crate::sema::SemanticFacts>,
    semantic_hir: Arc<HirProgram>,
    diagnostics: Vec<ril_compiler_core::diagnostic::Diagnostic>,
    static_definitions: Vec<ril_syntax::ast::Function>,
    type_functions: Vec<ril_syntax::ast::TypeDeclaration>,
    static_termination: std::collections::BTreeMap<String, crate::termination::Judgment>,
    external_declarations: Vec<crate::modules::ExternalDeclaration>,
    type_declarations: std::collections::BTreeMap<String, String>,
}
impl VerifiedProgram {
    pub fn type_declarations(&self) -> &std::collections::BTreeMap<String, String> {
        &self.type_declarations
    }
    pub(crate) fn attach_type_declarations(
        &mut self,
        types: std::collections::BTreeMap<String, String>,
    ) {
        self.type_declarations = types;
    }
    pub fn external_declarations(&self) -> &[crate::modules::ExternalDeclaration] {
        &self.external_declarations
    }
    pub(crate) fn attach_external_declarations(
        &mut self,
        declarations: Vec<crate::modules::ExternalDeclaration>,
    ) {
        self.external_declarations = declarations;
    }
    /// The complete resolved source before static materialization, including
    /// lexical nesting and definitions erased from the executable program.
    pub fn resolved_source(&self) -> &ril_syntax::ast::Program {
        &self.resolved_source
    }
    pub(crate) fn attach_resolved_source(&mut self, source: ril_syntax::ast::Program) {
        self.resolved_source = Arc::new(source);
    }
    pub fn static_definitions(&self) -> &[ril_syntax::ast::Function] {
        &self.static_definitions
    }
    pub fn type_functions(&self) -> &[ril_syntax::ast::TypeDeclaration] {
        &self.type_functions
    }
    pub fn static_termination(
        &self,
    ) -> &std::collections::BTreeMap<String, crate::termination::Judgment> {
        &self.static_termination
    }
    pub(crate) fn attach_static_metadata(
        &mut self,
        definitions: Vec<ril_syntax::ast::Function>,
        types: Vec<ril_syntax::ast::TypeDeclaration>,
        termination: std::collections::BTreeMap<String, crate::termination::Judgment>,
    ) {
        self.static_definitions = definitions;
        self.type_functions = types;
        self.static_termination = termination;
    }
    pub fn definitions(&self) -> &[Definition] {
        &self.definitions
    }
    pub fn program(&self) -> &ril_syntax::ast::Program {
        &self.syntax
    }
    pub fn syntax(&self) -> &ril_syntax::ast::Program {
        &self.syntax
    }
    pub fn facts(&self) -> &crate::sema::SemanticFacts {
        &self.facts
    }
    pub fn semantic_hir(&self) -> &HirProgram {
        &self.semantic_hir
    }
    pub(crate) fn shared_facts(&self) -> Arc<crate::sema::SemanticFacts> {
        self.facts.clone()
    }
    pub(crate) fn shared_hir(&self) -> Arc<HirProgram> {
        self.semantic_hir.clone()
    }
    pub(crate) fn shared_source(&self) -> Arc<ril_syntax::ast::Program> {
        self.resolved_source.clone()
    }
    pub fn diagnostics(&self) -> &[ril_compiler_core::diagnostic::Diagnostic] {
        &self.diagnostics
    }
    pub(crate) fn verified(
        syntax: Arc<ril_syntax::ast::Program>,
        definitions: Vec<Definition>,
        facts: Arc<crate::sema::SemanticFacts>,
        semantic_hir: Arc<HirProgram>,
        diagnostics: Vec<ril_compiler_core::diagnostic::Diagnostic>,
    ) -> Self {
        Self {
            definitions,
            resolved_source: syntax.clone(),
            syntax,
            facts,
            semantic_hir,
            diagnostics,
            static_definitions: vec![],
            type_functions: vec![],
            static_termination: Default::default(),
            external_declarations: vec![],
            type_declarations: Default::default(),
        }
    }
}
