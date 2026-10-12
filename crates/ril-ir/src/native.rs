/// Initial backend probe subset, not the Ril language or the complete native MIR.
#[derive(Debug, Clone)]
pub struct Module {
    pub functions: Vec<Function>,
}
#[derive(Debug, Clone)]
pub struct Function {
    pub symbol: String,
    pub body: Body,
}
#[derive(Debug, Clone)]
pub enum Body {
    ReturnI64(i64),
}
