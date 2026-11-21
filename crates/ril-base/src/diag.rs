use std::{fmt, io, str::FromStr};

use ariadne::{Config, IndexType, Label, Report, ReportKind, Source};

use crate::span::{SourceMap, Span};

macro_rules! diagnostic_codes {
    ($(($code:ident, $name:ident)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Code { $($code),+ }

        impl Code {
            pub const ALL: &'static [Self] = &[$(Self::$code),+];

            pub const fn as_str(self) -> &'static str {
                match self { $(Self::$code => stringify!($code)),+ }
            }

            pub const fn name(self) -> &'static str {
                match self { $(Self::$code => stringify!($name)),+ }
            }
        }

        impl FromStr for Code {
            type Err = UnknownCode;

            fn from_str(text: &str) -> Result<Self, Self::Err> {
                match text {
                    $(stringify!($code) => Ok(Self::$code)),+,
                    _ => Err(UnknownCode(text.into())),
                }
            }
        }
    };
}

include!("codes.rs");

impl fmt::Display for Code {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug)]
pub struct UnknownCode(String);

impl fmt::Display for UnknownCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown diagnostic code {}", self.0)
    }
}

impl std::error::Error for UnknownCode {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub code: Option<Code>,
    pub primary: Option<Span>,
    pub message: String,
}

impl Diagnostic {
    pub fn error(code: Code, span: Span, message: impl Into<String>) -> Self {
        Self {
            code: Some(code),
            primary: Some(span),
            message: message.into(),
        }
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self {
            code: None,
            primary: None,
            message: message.into(),
        }
    }

    pub fn render(&self, sources: &SourceMap, mut out: impl io::Write) -> io::Result<()> {
        if let Some(span) = self.primary
            && let Some(file) = sources.get(span.file)
        {
            let path = file.path().to_string_lossy();
            let range = span.start..span.end;
            let mut report = Report::build(ReportKind::Error, (path.as_ref(), range.clone()))
                .with_config(
                    Config::new()
                        .with_index_type(IndexType::Byte)
                        .with_color(false),
                )
                .with_message(&self.message)
                .with_label(Label::new((path.as_ref(), range)).with_message(&self.message));
            if let Some(code) = self.code {
                report = report.with_code(code.as_str());
            }
            return report
                .finish()
                .write((path.as_ref(), Source::from(file.text())), out);
        }
        writeln!(out, "{self}")
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(code) = self.code {
            write!(f, "{code}: ")?;
        }
        f.write_str(&self.message)
    }
}
