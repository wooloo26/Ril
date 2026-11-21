use std::path::Path;

use crate::{Case, CaseMode, Milestone, Stage, Suite, Unit, VirtualPackage};

pub fn spec_suite(path: &Path, source: &str, stage: Stage) -> Result<Suite, String> {
    let mut open = None;
    let mut cases = Vec::new();
    let mut snippet = Vec::new();
    for (index, line) in source.split_inclusive('\n').enumerate() {
        let current = index + 1;
        let text = line.trim();
        let ticks = text.bytes().take_while(|&byte| byte == b'`').count();
        if let Some((count, start, ril)) = open {
            if ticks >= count && text.get(ticks..).is_some_and(str::is_empty) {
                if ril {
                    cases.push(make_case(stage, start, &snippet));
                    snippet.clear();
                }
                open = None;
            } else if ril {
                snippet.push((current, line));
            }
        } else if ticks >= 3 {
            open = Some((
                ticks,
                current,
                text.get(ticks..).is_some_and(|lang| lang.trim() == "ril"),
            ));
        }
    }
    if let Some((_, start, _)) = open {
        return Err(format!(
            "{}:{start}: unclosed Markdown fence",
            path.display()
        ));
    }
    if cases.is_empty() {
        return Err(format!("{}: no Ril snippets", path.display()));
    }
    Ok(Suite {
        name: "spec".into(),
        path: path.into(),
        cases,
    })
}

fn make_case(stage: Stage, line: usize, text: &[(usize, &str)]) -> Case {
    let filename = text
        .iter()
        .find_map(|(_, line)| line.trim().strip_prefix("-- File: "));
    let mut pkg = VirtualPackage::new(if filename.is_some_and(|name| name.ends_with(".d.ril")) {
        Unit::Decl
    } else {
        Unit::Snippet
    });
    if let Some(filename) = filename {
        pkg.entry = Path::new("pkg").join(filename);
    }
    let file = pkg.files.entry(pkg.entry.clone()).or_default();
    for &(number, source) in text {
        file.push(source, number);
    }
    Case::spec(
        format!("line_{line}"),
        line,
        CaseMode::CompilePass,
        stage,
        pkg,
        Milestone::M1,
    )
}
