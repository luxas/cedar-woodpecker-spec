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

//! Support for the `dnf-lean-drt` fuzz target: differential testing of the
//! Rust DNF converter (`cedar_policy_symcc::dnf`) against its Lean model
//! (`Cedar.DNF` in `cedar-lean`), whose equivalence theorems are
//! machine-checked (`Cedar.Thm.DNF`). Agreement here transfers those theorems
//! to the Rust implementation, input by input: both sides convert the same
//! expression and the rendered DNFs must be structurally identical.
//!
//! Each input is checked under both closure-free `can_error` extremes —
//! every atom can error (`Dnf::of_expr`, which keeps exactly the never-true
//! cubes with an uncovered node) and no atom can error (which drops every
//! never-true cube) — so both pruning behaviours are compared.

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy_core::ast::Expr;
use cedar_policy_generators::abac::Type;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_symcc::dnf::{DEFAULT_MAX_CUBES, Dnf, DnfError};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;

use crate::symeval::{SETTINGS, Skip, Verdict};

/// Input to `dnf-lean-drt`: a generated (mostly well-typed) boolean
/// expression. The DNF check is purely syntactic, so no request or entities
/// are needed; the schema and hierarchy only steer the generator towards
/// realistic atoms.
#[derive(Debug, Clone)]
pub struct DnfFuzzTargetInput {
    /// generated boolean expression
    pub expression: Expr,
}

impl<'a> Arbitrary<'a> for DnfFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let expression = schema
            .exprgenerator(Some(&hierarchy))
            .generate_expr_for_type(&Type::bool(), SETTINGS.max_depth, u)?;
        Ok(Self { expression })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

/// Runs the Rust converter and the Lean model on `expression` for one
/// `can_error` extreme and compares the rendered DNFs structurally.
/// Panics on a mismatch; a Rust-side resource limit is a benign skip (the
/// Lean model deliberately has no budgets).
fn check_one(ffi: &CedarLeanFfi, expression: &Expr, can_error_all: bool) -> Verdict {
    let converted = if can_error_all {
        Dnf::of_expr(expression)
    } else {
        Dnf::of(expression, |_| false, DEFAULT_MAX_CUBES)
    };
    let dnf = match converted {
        Ok(dnf) => dnf,
        Err(e @ (DnfError::TooLarge { .. } | DnfError::RecursionLimit)) => {
            return Skip::Benign(format!("the Rust conversion hit a resource limit: {e}")).into();
        }
        Err(e @ DnfError::Unsupported(_)) => {
            // With `tolerant-ast` off, `Unsupported` can only mean a Rust
            // invariant breach (a rebuild lost or duplicated a child) — the
            // very bug class this DRT exists to catch.
            panic!("the Rust conversion violated an invariant on `{expression}`: {e}");
        }
    };
    let expected = dnf.to_expr();
    debug!("can_error_all = {can_error_all}: Rust DNF: {expected}\n");
    match ffi.run_dnf_check(expression, &expected, can_error_all) {
        Ok(result) => {
            assert!(
                result.agrees,
                "the Rust DNF and the Lean model disagree (can_error_all = \
                 {can_error_all}) on `{expression}`:\n  Rust: {}\n  Lean: {}",
                result.expected, result.actual
            );
            Verdict::Checked
        }
        Err(e) => panic!("the Lean FFI call failed on `{expression}`: {e}"),
    }
}

/// Checks `expression` under both `can_error` extremes; `Checked` when at
/// least one conversion ran to completion on the Rust side. (Today the two
/// extremes always skip together — `can_error` only affects `prune`, while
/// every skip-producing error arises in `paths` — so the combination only
/// matters if `Dnf::of` ever grows a `can_error`-dependent limit. A
/// divergence panics inside [`check_one`] regardless of the combination.)
pub fn test_dnf_vs_lean(ffi: &CedarLeanFfi, expression: &Expr) -> Verdict {
    let all = check_one(ffi, expression, true);
    let none = check_one(ffi, expression, false);
    match (all, none) {
        (Verdict::Checked, _) | (_, Verdict::Checked) => Verdict::Checked,
        (skipped, _) => skipped,
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use std::str::FromStr;

    use cedar_policy::Expression;
    use rand::{Rng, SeedableRng};

    use super::*;

    fn expr(text: &str) -> Expr {
        Expression::from_str(text).unwrap().as_ref().clone()
    }

    /// Hand-picked expressions covering the converter's interesting paths:
    /// dedup, contradiction truncation, `if` grafting, never-true-cube
    /// coverage, record and set atoms (the record-order transport path), and
    /// the trivial inputs. The generated inputs are depth-limited and pick
    /// record/set atoms rarely, so long dedup chains and the record path
    /// lean on this list. `(context.a && false) || (context.e && false)`
    /// separates the two `can_error` extremes, so a mis-wired
    /// `can_error_all` flag mismatches loudly here.
    #[test]
    fn dnf_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let cases = [
            "true",
            "false",
            "context.a",
            "context.a || context.a",
            "context.a && (context.b && context.a)",
            "(context.a && context.b) || (context.a && !context.a)",
            "(context.a || context.b) && context.c",
            "context.a && (context.b || context.c)",
            "!(context.a && context.b)",
            "if context.a then context.b else context.c",
            "if (context.a && context.b) then context.c else context.e",
            "(context.a && false) || (context.e && false)",
            "context.a == context.b",
            "{a: 1, b: context.x} == context.r && context.a",
            "[1, 2] == context.s || context.a",
            "principal.foo == 1 || (!(principal.foo == 1) && resource.bar)",
        ];
        for text in cases {
            let expression = expr(text);
            match test_dnf_vs_lean(&ffi, &expression) {
                Verdict::Checked => {}
                Verdict::Skipped(skip) => panic!("`{text}` was skipped: {skip:?}"),
            }
        }
    }

    /// Exercises the target's plumbing on generated inputs from a fixed seed,
    /// so `cargo test` covers it even though CI runs no fuzz target.
    #[test]
    fn dnf_lean_target_smoke() {
        let ffi = CedarLeanFfi::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xd9f_5eed);
        let (wanted, max_attempts) = (30, 2_000);
        let mut checked = 0;
        let mut skipped: HashMap<&'static str, usize> = HashMap::new();
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = DnfFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes)) else {
                *skipped.entry("not generated").or_default() += 1;
                continue;
            };
            match test_dnf_vs_lean(&ffi, &input.expression) {
                Verdict::Checked => checked += 1,
                Verdict::Skipped(_) => *skipped.entry("skipped").or_default() += 1,
            }
            if checked >= wanted {
                break;
            }
        }
        eprintln!("checked {checked} inputs; skipped: {skipped:?}");
        assert!(
            checked >= wanted,
            "only {checked} of {wanted} wanted inputs were checked; skipped: {skipped:?}"
        );
    }
}
