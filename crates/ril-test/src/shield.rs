// Only track lexical regions which can hide an otherwise column-zero directive.
// This scanner never interprets user code or emits compiler diagnostics.
#[derive(Default)]
pub(super) struct Shield(Vec<Mode>);

enum Mode {
    Raw(usize),
    String { interpolate: bool },
    Interpolation(usize),
}

impl Shield {
    pub(super) fn exposed(&self) -> bool {
        self.0.is_empty()
    }

    pub(super) fn scan(&mut self, line: &str) {
        let mut remaining = line.as_bytes();
        while let Some((&first, rest)) = remaining.split_first() {
            match self.0.last_mut() {
                Some(Mode::Raw(hashes)) => {
                    remaining = rest;
                    if first == b'"'
                        && rest.iter().take(*hashes).filter(|&&b| b == b'#').count() == *hashes
                    {
                        remaining = rest.get(*hashes..).unwrap_or_default();
                        self.0.pop();
                    }
                }
                Some(Mode::String { interpolate }) => {
                    remaining = rest;
                    match first {
                        b'\\' => remaining = rest.get(1..).unwrap_or_default(),
                        b'"' | b'\n' => {
                            self.0.pop();
                        }
                        b'{' if *interpolate => {
                            if let Some(next) = rest.strip_prefix(b"{") {
                                remaining = next;
                            } else {
                                self.0.push(Mode::Interpolation(1));
                            }
                        }
                        b'}' if *interpolate => {
                            remaining = rest.strip_prefix(b"}").unwrap_or(rest);
                        }
                        _ => {}
                    }
                }
                _ => {
                    if remaining.starts_with(b"--") {
                        break;
                    }
                    if let Some(next) = remaining.strip_prefix(b"bytes\"") {
                        self.0.push(Mode::String { interpolate: false });
                        remaining = next;
                        continue;
                    }
                    remaining = rest;
                    if first == b'#' {
                        let hashes = 1 + rest.iter().take_while(|&&b| b == b'#').count();
                        if let Some(after_hashes) = remaining.get(hashes - 1..) {
                            remaining = after_hashes;
                            if let Some(next) = after_hashes.strip_prefix(b"\"") {
                                self.0.push(Mode::Raw(hashes));
                                remaining = next;
                            }
                        }
                    } else if first == b'"' {
                        self.0.push(Mode::String { interpolate: true });
                    } else if let Some(Mode::Interpolation(depth)) = self.0.last_mut() {
                        match first {
                            b'{' => *depth += 1,
                            b'}' => {
                                *depth -= 1;
                                if *depth == 0 {
                                    self.0.pop();
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }
}
