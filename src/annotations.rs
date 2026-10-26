use regex::Regex;
use std::sync::LazyLock;

#[derive(Clone, Copy)]
enum Context {
    Code { interpolation: bool, depth: usize },
    Raw,
    String,
    Bytes,
}

/// Recognizes expectation comments, not Ril syntax or container framing.
pub(crate) fn line_comments(text: &str) -> Vec<String> {
    static FORMAT: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(r"^:(?:[^{}\r\n]?[<^>])?[0-9]*(?:\.[0-9]*)?[A-Za-z]*\}").unwrap()
    });
    let chars: Vec<_> = text.chars().collect();
    let byte_offsets: Vec<_> = text.char_indices().map(|(offset, _)| offset).collect();
    let mut result = Vec::new();
    let mut stack = vec![Context::Code {
        interpolation: false,
        depth: 0,
    }];
    let (mut i, mut block) = (0, 0usize);
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        let pair = |a, b| c == a && next == Some(b);
        if block > 0 {
            if pair('{', '-') {
                block += 1;
                i += 2;
            } else if pair('-', '}') {
                block -= 1;
                i += 2;
            } else {
                i += 1;
            }
            continue;
        }
        match *stack.last().unwrap() {
            Context::Raw => {
                if c == '`' {
                    stack.pop();
                }
                i += 1;
            }
            context @ (Context::String | Context::Bytes) => {
                if c == '\\' {
                    i += if matches!(context, Context::String)
                        && next == Some('u')
                        && chars.get(i + 2) == Some(&'{')
                    {
                        3
                    } else {
                        2
                    };
                } else if c == '"' {
                    stack.pop();
                    i += 1;
                } else if matches!(context, Context::String) && (pair('{', '{') || pair('}', '}')) {
                    i += 2;
                } else if matches!(context, Context::String) && c == '{' {
                    stack.push(Context::Code {
                        interpolation: true,
                        depth: 0,
                    });
                    i += 1;
                } else {
                    i += 1;
                }
            }
            Context::Code {
                interpolation,
                depth,
            } => {
                if pair('{', '-') {
                    block = 1;
                    i += 2;
                } else if pair('-', '-') {
                    let end = (i..chars.len())
                        .find(|&j| chars[j] == '\n')
                        .unwrap_or(chars.len());
                    result.push(chars[i..end].iter().collect());
                    i = end + 1;
                } else if pair('b', '"') {
                    stack.push(Context::Bytes);
                    i += 2;
                } else if c == '"' || c == '`' {
                    stack.push(if c == '"' {
                        Context::String
                    } else {
                        Context::Raw
                    });
                    i += 1;
                } else if interpolation {
                    if pair(':', ':') {
                        i += 2;
                    } else if c == ':' && depth == 0 {
                        let suffix = &text[byte_offsets[i]..];
                        if let Some(found) = FORMAT.find(suffix) {
                            i += suffix[..found.end()].chars().count();
                            stack.pop();
                        } else {
                            i += 1;
                        }
                    } else if c == '}' && depth == 0 {
                        stack.pop();
                        i += 1;
                    } else {
                        let depth = if "([{".contains(c) {
                            depth + 1
                        } else if ")]}".contains(c) {
                            depth.saturating_sub(1)
                        } else {
                            depth
                        };
                        *stack.last_mut().unwrap() = Context::Code {
                            interpolation,
                            depth,
                        };
                        i += 1;
                    }
                } else {
                    i += 1;
                }
            }
        }
    }
    result
}
