//! Parsed format syntax for both static evaluation and run-time formatting.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Alignment {
    Left,
    Center,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Conversion {
    Binary,
    Octal,
    LowerHex,
    UpperHex,
    Scientific,
    Fixed,
    Text,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormatSpec {
    pub fill: Option<char>,
    pub alignment: Option<Alignment>,
    pub width: Option<i64>,
    pub leading_zero: bool,
    pub precision: Option<i64>,
    pub conversion: Option<Conversion>,
}

impl FormatSpec {
    pub(crate) fn parse(text: &str) -> Option<Self> {
        let mut chars = text.chars().peekable();
        let mut prefix = chars.clone();
        let (fill, alignment) = if let Some(first) = prefix.next() {
            if let Some(alignment) = prefix.peek().copied().and_then(alignment) {
                if matches!(first, '{' | '}' | '\r' | '\n') {
                    return None;
                }
                prefix.next();
                chars = prefix;
                (Some(first), Some(alignment))
            } else if let Some(alignment) = alignment(first) {
                chars = prefix;
                (None, Some(alignment))
            } else {
                (None, None)
            }
        } else {
            (None, None)
        };
        let leading_zero = chars.peek() == Some(&'0');
        let width = number(&mut chars)?;
        let precision = if chars.next_if_eq(&'.').is_some() {
            Some(number(&mut chars)??)
        } else {
            None
        };
        let conversion = match chars.next() {
            None => None,
            Some('b') => Some(Conversion::Binary),
            Some('o') => Some(Conversion::Octal),
            Some('x') => Some(Conversion::LowerHex),
            Some('X') => Some(Conversion::UpperHex),
            Some('e') => Some(Conversion::Scientific),
            Some('f') => Some(Conversion::Fixed),
            Some('s') => Some(Conversion::Text),
            _ => return None,
        };
        chars.next().is_none().then_some(Self {
            fill,
            alignment,
            width,
            leading_zero,
            precision,
            conversion,
        })
    }
}

fn alignment(character: char) -> Option<Alignment> {
    match character {
        '<' => Some(Alignment::Left),
        '^' => Some(Alignment::Center),
        '>' => Some(Alignment::Right),
        _ => None,
    }
}

fn number(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<Option<i64>> {
    let mut value = None::<i64>;
    while let Some(digit) = chars.next_if(char::is_ascii_digit) {
        value = Some(
            value
                .unwrap_or(0)
                .checked_mul(10)?
                .checked_add(i64::from(digit as u8 - b'0'))?,
        );
    }
    Some(value)
}
