//! Pure Ril scalar formatting shared by static evaluation and native execution.
//! No source, compiler, heap, ABI, or host layout types cross this boundary.
mod renderer;
pub use renderer::default_float;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Integer,
    Float,
    String,
    Bool,
}

#[derive(Debug, Clone, Copy)]
pub enum Scalar<'a> {
    Integer { value: i128 },
    BigInteger(&'a num_bigint::BigInt),
    Float { value: f64, bits: u8 },
    String(&'a str),
    Bool(bool),
}
impl Scalar<'_> {
    pub fn kind(&self) -> Kind {
        match self {
            Self::Integer { .. } | Self::BigInteger(_) => Kind::Integer,
            Self::Float { .. } => Kind::Float,
            Self::String(_) => Kind::String,
            Self::Bool(_) => Kind::Bool,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Malformed,
    Incompatible,
    LimitExceeded,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Malformed => "malformed interpolation format",
            Self::Incompatible => "value type does not admit this format or precision",
            Self::LimitExceeded => "formatted text exceeds the available output allocation budget",
        })
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FormatSpec {
    fill: Option<char>,
    align: Option<char>,
    width: u64,
    precision: Option<u64>,
    kind: Option<char>,
    zero: bool,
}
impl FormatSpec {
    /// Widths use the selected Ril int layout, never the compiler host's usize.
    pub fn parse(text: &str, pointer_bits: u8) -> Result<Self> {
        let maximum = match pointer_bits {
            32 => i32::MAX as u64,
            64 => i64::MAX as u64,
            _ => return Err(Error::Malformed),
        };
        let chars: Vec<_> = text.chars().collect();
        let mut index = 0;
        let mut spec = Self::default();
        if chars.get(1).is_some_and(|c| matches!(c, '<' | '>' | '^')) {
            if matches!(chars[0], '{' | '}' | '\n' | '\r') {
                return Err(Error::Malformed);
            }
            spec.fill = Some(chars[0]);
            spec.align = Some(chars[1]);
            index = 2;
        } else if chars.first().is_some_and(|c| matches!(c, '<' | '>' | '^')) {
            spec.align = Some(chars[0]);
            index = 1;
        }
        spec.zero = chars.get(index) == Some(&'0');
        spec.width = number(&chars, &mut index, maximum)?.unwrap_or(0);
        if chars.get(index) == Some(&'.') {
            index += 1;
            spec.precision = Some(number(&chars, &mut index, maximum)?.ok_or(Error::Malformed)?);
        }
        if let Some(&kind) = chars.get(index) {
            if !matches!(kind, 'b' | 'o' | 'x' | 'X' | 'e' | 'f' | 's') {
                return Err(Error::Malformed);
            }
            spec.kind = Some(kind);
            index += 1;
        }
        if index != chars.len() {
            return Err(Error::Malformed);
        }
        Ok(spec)
    }
    pub fn validate(&self, kind: Kind) -> Result<()> {
        let valid = match kind {
            Kind::Integer => {
                self.precision.is_none() && matches!(self.kind, None | Some('b' | 'o' | 'x' | 'X'))
            }
            Kind::Float => {
                matches!(self.kind, None | Some('e' | 'f'))
                    && (self.precision.is_none() || matches!(self.kind, Some('e' | 'f')))
            }
            Kind::String => matches!(self.kind, None | Some('s')),
            Kind::Bool => self.kind.is_none() && self.precision.is_none(),
        };
        if valid {
            Ok(())
        } else {
            Err(Error::Incompatible)
        }
    }
    /// The limit is an implementation allocation budget, not a language bound.
    pub fn render(&self, value: Scalar<'_>, output_limit: usize) -> Result<String> {
        renderer::render(&value, self, output_limit)
    }
}
fn number(chars: &[char], index: &mut usize, maximum: u64) -> Result<Option<u64>> {
    let start = *index;
    let mut value = 0u64;
    while let Some(digit) = chars.get(*index).filter(|c| c.is_ascii_digit()) {
        value = value
            .checked_mul(10)
            .and_then(|value| value.checked_add(u64::from(*digit as u8 - b'0')))
            .filter(|value| *value <= maximum)
            .ok_or(Error::Malformed)?;
        *index += 1;
    }
    Ok((*index != start).then_some(value))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn text(value: Scalar<'_>, spec: &str) -> String {
        FormatSpec::parse(spec, 64)
            .unwrap()
            .render(value, 1_000_000)
            .unwrap()
    }
    #[test]
    fn normative_conversions_include_scalar_width_rounding_and_special_values() {
        assert_eq!(text(Scalar::Integer { value: -42 }, "05"), "-0042");
        assert_eq!(text(Scalar::Integer { value: -42 }, "X"), "-2A");
        assert_eq!(
            text(
                Scalar::Float {
                    value: 1.25,
                    bits: 64
                },
                ".1f"
            ),
            "1.2"
        );
        assert_eq!(
            text(
                Scalar::Float {
                    value: 9.99,
                    bits: 64
                },
                ".1e"
            ),
            "1.0e1"
        );
        assert_eq!(
            text(
                Scalar::Float {
                    value: -0.0,
                    bits: 64
                },
                ".0e"
            ),
            "-0e0"
        );
        assert_eq!(
            text(
                Scalar::Float {
                    value: f64::INFINITY,
                    bits: 64
                },
                "08.2f"
            ),
            "     inf"
        );
        assert_eq!(
            text(
                Scalar::Float {
                    value: f64::NEG_INFINITY,
                    bits: 64
                },
                "08"
            ),
            "    -inf"
        );
        assert_eq!(
            text(
                Scalar::Float {
                    value: f64::NAN,
                    bits: 32
                },
                "06.0e"
            ),
            "   nan"
        );
        assert_eq!(text(Scalar::String("é🙂x"), "🙂^5.2s"), "🙂é🙂🙂🙂");
        assert_eq!(text(Scalar::String("x"), "<^4s"), "<x<<");
    }
    #[test]
    fn parsing_uses_target_int_bounds_and_type_checks_precision() {
        assert!(FormatSpec::parse("2147483647", 32).is_ok());
        assert_eq!(FormatSpec::parse("2147483648", 32), Err(Error::Malformed));
        assert!(FormatSpec::parse("2147483648", 64).is_ok());
        assert_eq!(
            FormatSpec::parse("9223372036854775808", 64),
            Err(Error::Malformed)
        );
        for spec in ["{<5", "}\u{003e}5", "\n^5", ".s", "d", "4q"] {
            assert_eq!(FormatSpec::parse(spec, 64), Err(Error::Malformed), "{spec}");
        }
        assert_eq!(
            FormatSpec::parse(".2", 64).unwrap().validate(Kind::Float),
            Err(Error::Incompatible)
        );
        assert_eq!(
            FormatSpec::parse(".2f", 64)
                .unwrap()
                .validate(Kind::Integer),
            Err(Error::Incompatible)
        );
        assert_eq!(
            FormatSpec::parse("s", 64).unwrap().validate(Kind::Bool),
            Err(Error::Incompatible)
        );
    }
    #[test]
    fn allocation_limits_do_not_misclassify_valid_formats() {
        let spec = FormatSpec::parse("2147483648", 64).unwrap();
        assert_eq!(
            spec.render(Scalar::Bool(true), 1024),
            Err(Error::LimitExceeded)
        );
        let spec = FormatSpec::parse(".9223372036854775807s", 64).unwrap();
        assert_eq!(spec.render(Scalar::String("é"), 2).unwrap(), "é");
        let spec = FormatSpec::parse(".9223372036854775807f", 64).unwrap();
        assert_eq!(
            spec.render(
                Scalar::Float {
                    value: f64::INFINITY,
                    bits: 64
                },
                3
            )
            .unwrap(),
            "inf"
        );
        assert_eq!(
            spec.render(
                Scalar::Float {
                    value: 1.0,
                    bits: 64
                },
                1024
            ),
            Err(Error::LimitExceeded)
        );
    }
}
