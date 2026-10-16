//! One case index is shared by source-level, structural and mutation tests.
//! Loading bytes does not run a compiler or change a case's expected outcome.
use crate::{Case, Error, Result, discover_cases};
use std::{collections::BTreeMap, path::Path, sync::LazyLock};

#[derive(Debug)]
pub struct CaseRegistry {
    cases: BTreeMap<String, Case>,
}

impl CaseRegistry {
    pub fn discover(root: &Path) -> Result<Self> {
        Self::new(discover_cases(root)?)
    }

    pub fn new(cases: impl IntoIterator<Item = Case>) -> Result<Self> {
        let mut indexed = BTreeMap::new();
        for case in cases {
            if indexed.insert(case.id.clone(), case).is_some() {
                return Err(Error::Invalid("duplicate case ID in registry".into()));
            }
        }
        Ok(Self { cases: indexed })
    }

    pub fn get(&self, id: &str) -> Result<&Case> {
        self.cases
            .get(id)
            .ok_or_else(|| Error::Invalid(format!("unknown corpus case ID: {id}")))
    }

    pub fn iter(&self) -> impl Iterator<Item = &Case> {
        self.cases.values()
    }
}

static WORKSPACE_CASES: LazyLock<CaseRegistry> = LazyLock::new(|| {
    CaseRegistry::discover(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests"))
        .unwrap_or_else(|error| panic!("cannot load test corpus: {error}"))
});

/// Load a repository case by its complete, stable `tests/...ril::case` ID.
pub fn case_by_id(id: &str) -> &'static Case {
    WORKSPACE_CASES
        .get(id)
        .unwrap_or_else(|error| panic!("{error}"))
}

/// Root source bytes, including original line endings and final-newline state.
pub fn case_bytes(id: &str) -> &'static [u8] {
    let case = case_by_id(id);
    &case
        .files
        .iter()
        .find(|file| file.name == case.root)
        .expect("validated compilation root")
        .bytes
}

/// UTF-8 fixture convenience; malformed encoding tests should use `case_bytes`.
pub fn case_source(id: &str) -> &'static str {
    std::str::from_utf8(case_bytes(id))
        .unwrap_or_else(|error| panic!("{id}: source is not UTF-8: {error}"))
}
