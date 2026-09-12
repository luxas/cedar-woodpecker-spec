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
use cedar_policy_symcc::dnf::{
    DEFAULT_MAX_CUBES, DEFAULT_MAX_SPLIT_NODES, Dnf, DnfError, likes_have_wildcards, rewrite_like,
    split_atoms,
};
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

/// Runs the Rust atom splitter and the Lean model on `expression` and
/// compares the outputs structurally. Panics on a mismatch; a Rust-side
/// resource limit is a benign skip (the Lean model has no budgets).
pub fn test_split_vs_lean(ffi: &CedarLeanFfi, expression: &Expr) -> Verdict {
    let split = match split_atoms(expression, DEFAULT_MAX_SPLIT_NODES) {
        Ok(split) => split,
        Err(e @ (DnfError::TooLarge { .. } | DnfError::RecursionLimit)) => {
            return Skip::Benign(format!("the Rust split hit a resource limit: {e}")).into();
        }
        Err(e @ DnfError::Unsupported(_)) => {
            // With `tolerant-ast` off, `Unsupported` can only mean a Rust
            // invariant breach (a rebuild lost or duplicated a child) — the
            // very bug class this DRT exists to catch.
            panic!("the Rust split violated an invariant on `{expression}`: {e}");
        }
    };
    debug!("Rust split: {split}\n");
    match ffi.run_split_check(expression, &split) {
        Ok(result) => {
            assert!(
                result.agrees,
                "the Rust split and the Lean model disagree on `{expression}`:\n  Rust: {}\n  Lean: {}",
                result.expected, result.actual
            );
            Verdict::Checked
        }
        Err(e) => panic!("the Lean FFI call failed on `{expression}`: {e}"),
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

#[cfg(test)]
mod split_test {
    use std::collections::HashMap;
    use std::str::FromStr;

    use cedar_policy::Expression;
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::symeval::Verdict;
    use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

    fn expr(text: &str) -> Expr {
        Expression::from_str(text).unwrap().as_ref().clone()
    }

    /// Hand-picked expressions covering the splitter's interesting paths:
    /// `if`s at any position inside atoms (including nested in the hoisted
    /// test), boolean structure under `==` and inside set/record literals,
    /// `lit == lit` folds (same and cross type), already-clean no-ops, and
    /// the guards: left siblings at one and two levels, a record whose second
    /// field holds the offender, literal and variable siblings (never
    /// guarded), an opaque `iferror` sibling, and a guard re-derived by the
    /// split of a substituted atom.
    #[test]
    fn split_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let cases = [
            "true",
            "context.a",
            "context.a && context.b",
            "(if context.a then 1 else 2) == 1",
            "(if context.a then 1 else 2) == 3",
            "context.n == (if context.a then 1 else 2)",
            "(context.a && context.b) == context.c",
            "(context.a && context.b) == (context.c || context.d)",
            "[context.a && context.b].contains(context.c)",
            "{f: context.a || context.b} == context.r",
            "{a: context.x && context.y, b: context.z && context.w} == context.r",
            "(if (if context.a then context.b else false) then 1 else 2) == 1",
            "context.a && (if context.b && context.c then context.u else context.v).d == 1",
            "1 == 2 || context.a",
            "\"x\" == 1 || context.a",
            "(if context.a then {b: [context.c && context.d]} else context.r).b == [true]",
            "context.a && !(context.b == context.c)",
            // a boolean-node operand of `==` is hoisted like any other
            // offender (plan 10; an earlier experiment made them opaque, since reverted), as are an
            // `if` operand and deeper structure inside an operand
            "!context.a == context.b",
            "(if context.a then context.b else context.c) == context.d",
            "[context.a && context.b].contains(context.c) == context.d",
            // guards (the `iferror` sibling's equality hoists an `if`
            // operand: an equality of booleans is opaque)
            "context.m < context.n + (if context.a then 1 else 2)",
            "{a: context.x, b: context.y && context.z} == context.r",
            "[1, principal, context.n, if context.a then 2 else 3].contains(context.m)",
            "iferror(context.a, false) == (if context.b && context.c then true else false)",
            "context.n == (if context.a then (if context.b then 1 else 2) else 3)",
            // an opaque equality of booleans as a left sibling is a guard whole
            "((context.a && context.b) == [context.c || context.d].contains(context.u))
             == (if context.v then true else false)",
            "[context.k, context.n + (if context.a then 1 else 2)].contains(context.m)",
            // siblings that cannot err (after folding) get no guard
            "[\"x\", \"y\"].contains(if context.a then context.s else \"z\")",
            "((if context.a then 1 else 2) == 1) == (context.b || context.c)",
            "[{a: 1}, {a: principal}].contains(if context.a then context.r else {a: 2})",
            // two identical erring siblings: guarded once
            "[context.n, context.n, if context.a then 1 else 2].contains(context.m)",
            // an offender inside an opaque `iferror` call stays put, as an
            // atom and at structure position
            "iferror(context.a && context.b, false) == context.c",
            "iferror(context.a && context.b, false)",
            // a set or record literal sibling contributes its elements' guards
            "[context.n, 7].containsAll(if context.a then [1] else [2])",
            "{a: context.n, b: context.s} == (if context.a then context.r else context.q)",
            // guards learned from an `&&`'s left operand and an `if`'s test
            "context.n == context.n && context.n == (if context.a then 1 else 2)",
            "if context.n == context.n then context.n == (if context.a then 1 else 2) else context.b",
        ];
        for text in cases {
            let expression = expr(text);
            match test_split_vs_lean(&ffi, &expression) {
                Verdict::Checked => {}
                Verdict::Skipped(skip) => panic!("`{text}` was skipped: {skip:?}"),
            }
        }
    }

    /// Exercises the target's plumbing on generated inputs from a fixed seed.
    #[test]
    fn split_lean_target_smoke() {
        let ffi = CedarLeanFfi::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x5b117_5eed);
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
            match test_split_vs_lean(&ffi, &input.expression) {
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

/// Runs the Rust like-rewrite (`rewrite_like`) and the Lean model on
/// `expression` and compares the outputs structurally; also checks the
/// Rust result satisfies the completeness predicate. Panics on a mismatch.
pub fn test_like_vs_lean(ffi: &CedarLeanFfi, expression: &Expr) -> Verdict {
    let rewritten = match rewrite_like(expression) {
        Ok(rewritten) => rewritten,
        Err(e) => panic!("the Rust like-rewrite failed on `{expression}`: {e}"),
    };
    assert!(
        likes_have_wildcards(&rewritten),
        "the Rust like-rewrite left a wildcard-free like in `{rewritten}`"
    );
    debug!("Rust like-rewrite: {rewritten}\n");
    match ffi.run_like_check(expression, &rewritten) {
        Ok(result) => {
            assert!(
                result.agrees,
                "the Rust like-rewrite and the Lean model disagree on `{expression}`:\n  Rust: {}\n  Lean: {}",
                result.expected, result.actual
            );
            Verdict::Checked
        }
        Err(e) => panic!("the Lean FFI call failed on `{expression}`: {e}"),
    }
}

#[cfg(test)]
mod like_test {
    use std::collections::HashMap;
    use std::str::FromStr;

    use cedar_policy::Expression;
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::symeval::Verdict;
    use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

    fn expr(text: &str) -> Expr {
        Expression::from_str(text).unwrap().as_ref().clone()
    }

    /// Hand-picked shapes: wildcard-free (incl. the empty pattern and an
    /// escaped star), a wildcard kept, and likes inside every node kind.
    #[test]
    fn like_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let cases = [
            r#"context.s like "abc""#,
            r#"context.s like """#,
            r#"context.s like "a\*b""#,
            r#"context.s like "a*b""#,
            r#"context.s like "*""#,
            r#"if context.s like "x" then {a: context.t like "y", b: context.u} == context.r else [context.s like "z*"].contains(true)"#,
            r#"iferror(context.s like "x", context.t like "y") && !(context.s like "w")"#,
            r#"(context.s like "x") == (context.s like "*x")"#,
            r#"context.a && context.b"#,
        ];
        for text in cases {
            let expression = expr(text);
            match test_like_vs_lean(&ffi, &expression) {
                Verdict::Checked => {}
                Verdict::Skipped(skip) => panic!("`{text}` was skipped: {skip:?}"),
            }
        }
    }

    /// Exercises the target's plumbing on generated inputs from a fixed
    /// seed; only inputs the rewrite actually changes count.
    #[test]
    fn like_lean_target_smoke() {
        let ffi = CedarLeanFfi::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x11ce_5eed);
        let (wanted, max_attempts) = (10, 4_000);
        let mut checked = 0;
        let mut skipped: HashMap<&'static str, usize> = HashMap::new();
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = DnfFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes)) else {
                *skipped.entry("not generated").or_default() += 1;
                continue;
            };
            let touched = rewrite_like(&input.expression).unwrap() != input.expression;
            match test_like_vs_lean(&ffi, &input.expression) {
                Verdict::Checked if touched => checked += 1,
                Verdict::Checked => *skipped.entry("no wildcard-free like").or_default() += 1,
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
