use super::*;

pub fn default_float(value: f64, bits: u8) -> String {
    if value.is_nan() {
        return "nan".into();
    }
    if value.is_infinite() {
        return if value.is_sign_negative() {
            "-inf".into()
        } else {
            "inf".into()
        };
    }
    if value == 0.0 {
        return if value.is_sign_negative() {
            "-0.0".into()
        } else {
            "0.0".into()
        };
    }
    let mut buffer = ryu::Buffer::new();
    let raw = if bits == 32 {
        buffer.format_finite(value as f32)
    } else {
        buffer.format_finite(value)
    };
    let (negative, raw) = raw
        .strip_prefix('-')
        .map_or((false, raw), |text| (true, text));
    let (mantissa, power) = raw
        .split_once('e')
        .map_or((raw, 0), |(mantissa, exponent)| {
            (mantissa, exponent.parse::<i32>().unwrap())
        });
    let decimal = mantissa.find('.').unwrap_or(mantissa.len()) as i32;
    let digits = mantissa.replace('.', "");
    let leading = digits.bytes().position(|byte| byte != b'0').unwrap_or(0);
    let exponent = power + decimal - leading as i32 - 1;
    let digits = digits[leading..].trim_end_matches('0');
    let mut text = if (-6..=20).contains(&exponent) {
        let point = exponent + 1;
        if point <= 0 {
            format!("0.{}{}", "0".repeat((-point) as usize), digits)
        } else if point as usize >= digits.len() {
            format!("{}{}.0", digits, "0".repeat(point as usize - digits.len()))
        } else {
            format!(
                "{}.{}",
                &digits[..point as usize],
                &digits[point as usize..]
            )
        }
    } else {
        let mut mantissa = digits[..1].to_owned();
        if digits.len() > 1 {
            mantissa.push('.');
            mantissa.push_str(&digits[1..]);
        }
        format!("{mantissa}e{exponent}")
    };
    if negative {
        text.insert(0, '-');
    }
    text
}

pub(super) fn render(value: &Scalar<'_>, spec: &FormatSpec, limit: usize) -> Result<String> {
    spec.validate(value.kind())?;
    if spec.width > limit as u64
        || (matches!(value,Scalar::Float {value,..} if value.is_finite())
            && spec.precision.is_some_and(|p| p > limit as u64))
    {
        return Err(Error::LimitExceeded);
    }
    let numeric = matches!(
        value,
        Scalar::Integer { .. } | Scalar::BigInteger(_) | Scalar::Float { .. }
    );
    let text = match value {
        Scalar::Integer { value, .. } => match spec.kind {
            None => value.to_string(),
            Some('x') => {
                if *value < 0 {
                    format!("-{:x}", value.unsigned_abs())
                } else {
                    format!("{value:x}")
                }
            }
            Some('X') => {
                if *value < 0 {
                    format!("-{:X}", value.unsigned_abs())
                } else {
                    format!("{value:X}")
                }
            }
            Some('b') => {
                if *value < 0 {
                    format!("-{:b}", value.unsigned_abs())
                } else {
                    format!("{value:b}")
                }
            }
            Some('o') => {
                if *value < 0 {
                    format!("-{:o}", value.unsigned_abs())
                } else {
                    format!("{value:o}")
                }
            }
            _ => return Err(Error::Incompatible),
        },
        Scalar::BigInteger(value) => match spec.kind {
            None => value.to_string(),
            Some('x') => value.to_str_radix(16),
            Some('X') => value.to_str_radix(16).to_ascii_uppercase(),
            Some('b') => value.to_str_radix(2),
            Some('o') => value.to_str_radix(8),
            _ => return Err(Error::Incompatible),
        },
        Scalar::Float { value, bits } => {
            if value.is_nan() || value.is_infinite() {
                default_float(*value, *bits)
            } else {
                match (spec.kind, spec.precision) {
                    (None, None) => default_float(*value, *bits),
                    (Some('f'), Some(precision)) => {
                        let precision = precision as usize;
                        if *bits == 32 {
                            format!("{:.*}", precision, *value as f32)
                        } else {
                            format!("{value:.*}", precision)
                        }
                    }
                    (Some('f'), None) => {
                        if *bits == 32 {
                            format!("{:.6}", *value as f32)
                        } else {
                            format!("{value:.6}")
                        }
                    }
                    (Some('e'), precision) => {
                        let text = if *bits == 32 {
                            format!("{:.*e}", precision.unwrap_or(6) as usize, *value as f32)
                        } else {
                            format!("{value:.*e}", precision.unwrap_or(6) as usize)
                        };
                        let (mantissa, exponent) = text.split_once('e').unwrap();
                        format!("{mantissa}e{}", exponent.parse::<i32>().unwrap())
                    }
                    _ => return Err(Error::Incompatible),
                }
            }
        }
        Scalar::String(value) => {
            if !matches!(spec.kind, None | Some('s')) {
                return Err(Error::Incompatible);
            }
            if let Some(precision) = spec.precision {
                value
                    .chars()
                    .take(usize::try_from(precision).unwrap_or(usize::MAX))
                    .collect()
            } else {
                (*value).to_owned()
            }
        }
        Scalar::Bool(value) if spec.kind.is_none() && spec.precision.is_none() => value.to_string(),
        _ => {
            return Err(Error::Incompatible);
        }
    };
    let padding = (spec.width as usize).saturating_sub(text.chars().count());
    let fill_bytes = spec.fill.unwrap_or(' ').len_utf8();
    if padding
        .checked_mul(fill_bytes)
        .and_then(|bytes| text.len().checked_add(bytes))
        .is_none_or(|bytes| bytes > limit)
    {
        return Err(Error::LimitExceeded);
    }
    if padding == 0 {
        return Ok(text);
    }
    if spec.zero
        && spec.align.is_none()
        && numeric
        && !matches!(value,Scalar::Float {value,..} if !value.is_finite())
    {
        if let Some(unsigned) = text.strip_prefix('-') {
            return Ok(format!("-{}{unsigned}", "0".repeat(padding)));
        }
        return Ok(format!("{}{text}", "0".repeat(padding)));
    }
    let fill = spec.fill.unwrap_or(' ');
    let align = spec.align.unwrap_or(if numeric { '>' } else { '<' });
    let left = match align {
        '<' => 0,
        '^' => padding / 2,
        _ => padding,
    };
    let right = padding - left;
    Ok(format!(
        "{}{text}{}",
        fill.to_string().repeat(left),
        fill.to_string().repeat(right)
    ))
}
