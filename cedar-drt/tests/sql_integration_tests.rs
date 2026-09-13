/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! The `cedar-integration-tests` corpus through `cedar-sql`: every request of
//! every test whose policies validate strictly (the compiler's precondition)
//! and whose schema `cedar-sql` can store must get the expected decision,
//! determining policies and erroring policies. Tests outside that envelope
//! are counted, not failed: policies that do not validate strictly (most of
//! the generated corpus), extension types in the schema, and constructs
//! `cedar-sql` does not compile yet, which the tally names.
//!
//! Needs the corpus at `cedar/cedar-integration-tests` (see the README) and
//! `CEDAR_SQL_PG_URL`. The full corpus (about ten thousand tests) runs with
//! `CEDAR_SQL_FULL_CORPUS=1`; by default a deterministic sixteenth runs.

#![cfg(feature = "integration-testing")]

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use cedar_drt::sql_impl::SqlTestImpl;
use cedar_policy::{PolicyId, ValidationMode, Validator};
use cedar_sql::Error as SqlError;
use cedar_testing::integration_testing::{
    JsonTest, parse_entities_from_test, parse_policies_from_test, parse_request_from_test,
    parse_schema_from_test, resolve_integration_test_path,
};
use cedar_testing::test_files::{get_corpus_tests, get_integration_tests};

/// What running one test file did.
#[derive(Debug, Default)]
struct Tally {
    /// Tests with at least one request checked.
    checked_tests: usize,
    /// Requests checked.
    checked_requests: usize,
    /// Why tests or requests were skipped, with counts.
    skipped: BTreeMap<String, usize>,
}

impl Tally {
    fn skip(&mut self, why: impl Into<String>) {
        *self.skipped.entry(why.into()).or_default() += 1;
    }
}

/// Runs one test file; panics on a disagreement.
fn run(path: &Path, tally: &mut Tally) {
    let name = path.display().to_string();
    let text = std::fs::read_to_string(resolve_integration_test_path(path))
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    let test: JsonTest = serde_json::from_str(&text).unwrap_or_else(|e| panic!("{name}: {e}"));
    let policies = parse_policies_from_test(&test);
    let schema = parse_schema_from_test(&test);
    let entities = parse_entities_from_test(&test, &schema);
    if !Validator::new(schema.clone())
        .validate(&policies, ValidationMode::Strict)
        .validation_passed()
    {
        tally.skip("test: the policies do not validate strictly");
        return;
    }
    let sql = match SqlTestImpl::new(schema.clone(), true) {
        Ok(sql) => sql,
        Err(SqlError::Unsupported(what)) => {
            tally.skip(format!("test: unsupported: {what}"));
            return;
        }
        Err(SqlError::Schema(message)) => {
            tally.skip(format!("test: schema: {message}"));
            return;
        }
        Err(e) => panic!("{name}: cannot set up the database: {e}"),
    };
    let mut checked = 0;
    for json_request in &test.requests {
        let request = parse_request_from_test(json_request, &schema, &name);
        let response = match sql.authorize(&request, &policies, &entities) {
            Ok(response) => response,
            Err(SqlError::Unsupported(what)) => {
                tally.skip(format!("request: unsupported: {what}"));
                continue;
            }
            Err(SqlError::Nul(_)) => {
                tally.skip("request: a string with a NUL character");
                continue;
            }
            Err(e) => panic!(
                "{name}: request \"{}\" failed: {e}",
                json_request.description
            ),
        };
        let expected_reason: BTreeSet<PolicyId> = json_request.reason.iter().cloned().collect();
        let expected_errors: BTreeSet<PolicyId> = json_request.errors.iter().cloned().collect();
        assert_eq!(
            (response.decision, &response.reason, &response.errors),
            (json_request.decision, &expected_reason, &expected_errors),
            "{name}: request \"{}\" disagrees with the expected result\nPolicies:\n{policies}",
            json_request.description
        );
        checked += 1;
    }
    tally.checked_requests += checked;
    if checked > 0 {
        tally.checked_tests += 1;
    }
}

#[test]
fn handwritten_integration_tests() {
    let mut tally = Tally::default();
    let mut total = 0;
    for path in get_integration_tests() {
        total += 1;
        run(&path, &mut tally);
    }
    eprintln!("handwritten tests: {total}; {tally:#?}");
    assert!(
        total > 0,
        "no integration tests found; is the corpus cloned?"
    );
    assert!(tally.checked_tests > 0, "no handwritten test was checked");
}

#[test]
fn corpus_tests() {
    let full = std::env::var_os("CEDAR_SQL_FULL_CORPUS").is_some();
    let prefix = if full { "" } else { "0" };
    let mut tally = Tally::default();
    let mut total = 0;
    for path in get_corpus_tests(prefix) {
        total += 1;
        run(&path, &mut tally);
    }
    eprintln!("corpus tests (prefix {prefix:?}): {total}; {tally:#?}");
    assert!(
        total > 0,
        "no corpus tests found; is corpus-tests.tar.gz unpacked?"
    );
}
