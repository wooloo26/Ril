use ril_compiler_core::phase::{NotImplemented, Stage};
use rowan::GreenNode;

pub fn parse(_text: &str) -> Result<GreenNode, NotImplemented> {
    Err(NotImplemented::new(Stage::Syntax, "Ril lexer and parser"))
}
