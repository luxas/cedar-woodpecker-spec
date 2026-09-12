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

//! Support for the DNF-family DRT targets comparing the Rust `dnf` module
//! against its Lean models (`cedar-spec/cedar-lean/Cedar/DNF*.lean`):
//! `dnf-lean-drt` (Step 1, `Dnf::of` at both `can_error` extremes),
//! `split-atoms-lean-drt` (Step 2, `split_atoms`) and
//! `split-policies-lean-drt` (Step 3, `split_policy` — the split policies'
//! cube conditions, in order; scope/effect/id copying is covered by the
//! solver-checked tests in `cedar-policy-symcc/tests/dnf.rs`) and
//! `combine-lean-drt` (Step 4, `combine_allow_deny` and `allow_cubes` — whole
//! policy sets, compared policy by policy in id order). Every check is purely
//! syntactic, so no request or entities are needed: the inputs are generated
//! boolean expressions (or small policy sets of them), and the Rust output
//! and the model's must be structurally identical up to record-field order.

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy_core::ast::{
    ActionConstraint, Annotations, Effect, Expr, PolicyID, PrincipalConstraint, ResourceConstraint,
    StaticPolicy,
};
use cedar_policy_generators::abac::ABACRequest;
use cedar_policy_generators::abac::Type;
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_symcc::dnf::{
    DEFAULT_MAX_CUBES, DEFAULT_MAX_SPLIT_NODES, Dnf, DnfError, allow_cubes, combine_allow_deny,
    likes_have_wildcards, normalize_atoms, rewrite_like, split_atoms, split_policy,
};
use cedar_policy_symcc::evaluator::request_env_of;
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
        Err(
            e @ (DnfError::Unsupported(_)
            | DnfError::NotWellTyped { .. }
            | DnfError::RequestEnvNotFound(_)
            | DnfError::Typecheck(_)),
        ) => {
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

/// Input to `elim-lean-drt`: a schema, a request (for its environment) and
/// a (mostly) well-typed boolean expression; the pipeline typechecks the
/// expression in that environment and an ill-typed one is a benign skip.
#[derive(Debug, Clone)]
pub struct ElimFuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated request
    pub request: ABACRequest,
    /// generated boolean expression
    pub expression: Expr,
}

impl<'a> Arbitrary<'a> for ElimFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let expression = schema
            .exprgenerator(Some(&hierarchy))
            .generate_expr_for_type(&Type::bool(), SETTINGS.max_depth, u)?;
        let request = schema.arbitrary_request(&hierarchy, u)?;
        Ok(Self {
            schema,
            request,
            expression,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

/// Runs the Rust normalization pipeline (`normalize_atoms`: split, eliminate
/// record and set literals, split again) and the Lean model on the input's
/// expression and compares the outputs structurally. Panics on a mismatch;
/// an ill-typed expression (the pipeline's precondition), a request outside
/// the schema and a Rust-side resource limit are benign skips.
pub fn test_elim_vs_lean(ffi: &CedarLeanFfi, input: &ElimFuzzTargetInput) -> Verdict {
    let expression = &input.expression;
    let Ok(schema) = cedar_policy::Schema::try_from(input.schema.clone()) else {
        return Skip::Benign("the generated schema does not convert".into()).into();
    };
    let request: cedar_policy::Request = input.request.clone().into();
    let Some(env) = request_env_of(&request, &schema) else {
        return Skip::Benign("the request has no environment in the schema".into()).into();
    };
    let normalized = match normalize_atoms(expression, &schema, &env, DEFAULT_MAX_SPLIT_NODES) {
        Ok(normalized) => normalized,
        Err(DnfError::NotWellTyped { .. }) => {
            return Skip::Benign("the expression is not well typed".into()).into();
        }
        Err(e @ (DnfError::RequestEnvNotFound(_) | DnfError::Typecheck(_))) => {
            return Skip::Benign(format!("the Rust typecheck could not run: {e}")).into();
        }
        Err(e @ (DnfError::TooLarge { .. } | DnfError::RecursionLimit)) => {
            return Skip::Benign(format!("the Rust normalization hit a resource limit: {e}"))
                .into();
        }
        Err(e @ DnfError::Unsupported(_)) => {
            panic!("the Rust normalization violated an invariant on `{expression}`: {e}");
        }
    };
    debug!("Rust normalization: {normalized}\n");
    match ffi.run_elim_check(expression, &normalized) {
        Ok(result) => {
            assert!(
                result.agrees,
                "the Rust normalization and the Lean model disagree on `{expression}`:\n  Rust: {}\n  Lean: {}",
                result.expected, result.actual
            );
            Verdict::Checked
        }
        Err(e) => panic!("the Lean FFI call failed on `{expression}`: {e}"),
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
        Err(
            e @ (DnfError::Unsupported(_)
            | DnfError::NotWellTyped { .. }
            | DnfError::RequestEnvNotFound(_)
            | DnfError::Typecheck(_)),
        ) => {
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

/// Runs the Rust policy splitter on `permit(principal, action, resource)
/// when { expression }` and compares the split policies' conditions, in
/// order, with the Lean model's `splitCondExprs`. Panics on a mismatch; an
/// ill-typed expression (the split validates the policy against `schema`)
/// and a Rust-side resource limit are benign skips.
pub fn test_split_policy_vs_lean(
    ffi: &CedarLeanFfi,
    schema: &cedar_policy::Schema,
    expression: &Expr,
) -> Verdict {
    let policy = StaticPolicy::new(
        PolicyID::from_string("p"),
        None,
        Annotations::new(),
        Effect::Permit,
        PrincipalConstraint::any(),
        ActionConstraint::any(),
        ResourceConstraint::any(),
        Some(expression.clone()),
    )
    .expect("a generated expression contains no slot");
    let split = match split_policy(
        &policy.into(),
        schema,
        DEFAULT_MAX_SPLIT_NODES,
        DEFAULT_MAX_CUBES,
    ) {
        Ok(split) => split,
        Err(DnfError::NotWellTyped { .. }) => {
            return Skip::Benign("the policy is not well typed".into()).into();
        }
        Err(e @ (DnfError::RequestEnvNotFound(_) | DnfError::Typecheck(_))) => {
            return Skip::Benign(format!("the Rust typecheck could not run: {e}")).into();
        }
        Err(e @ (DnfError::TooLarge { .. } | DnfError::RecursionLimit)) => {
            return Skip::Benign(format!("the Rust policy split hit a resource limit: {e}")).into();
        }
        Err(e @ DnfError::Unsupported(_)) => {
            // With `tolerant-ast` off, `Unsupported` can only mean a Rust
            // invariant breach — the very bug class this DRT exists to catch.
            panic!("the Rust policy split violated an invariant on `{expression}`: {e}");
        }
    };
    let conditions: Vec<Expr> = split
        .iter()
        .map(|p| {
            p.non_scope_constraints()
                .expect("a split policy carries its cube as its condition")
                .clone()
        })
        .collect();
    debug!("Rust policy split: {} policies\n", conditions.len());
    match ffi.run_split_policy_check(expression, &conditions) {
        Ok(result) => {
            assert!(
                result.agrees,
                "the Rust policy split and the Lean model disagree on `{expression}`:\n  Rust: {}\n  Lean: {}",
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

#[cfg(test)]
mod elim_test {
    use std::collections::HashMap;
    use std::str::FromStr;

    use cedar_policy::Expression;
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::symeval::Verdict;
    use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

    /// A schema and request for the fixed cases: `User` principals with a
    /// `Long` `n`, a `String` `s`, a set of strings `tags` and a record
    /// `r {x: Long}`, viewing `Doc` resources with a `Long` `level`.
    fn fixture() -> (cedar_policy::Schema, cedar_policy::RequestEnv) {
        let schema = cedar_policy::Schema::from_cedarschema_str(
            r#"
            entity User in [Group] { n: Long, s: String, tags: Set<String>, r: { x: Long },
                                     rs: Set<{ x: Long }> };
            entity Group;
            entity Doc { level: Long };
            action view appliesTo { principal: User, resource: Doc };
            "#,
        )
        .unwrap()
        .0;
        let env = cedar_policy::RequestEnv::new(
            "User".parse().unwrap(),
            r#"Action::"view""#.parse().unwrap(),
            "Doc".parse().unwrap(),
        );
        (schema, env)
    }

    fn expr(text: &str) -> Expr {
        Expression::from_str(text).unwrap().as_ref().clone()
    }

    /// Hand-picked expressions covering every rule and the guards: `.attr`,
    /// `has` and `==` on record literals (nested too), `contains`,
    /// `containsAll`, `containsAny` (both sides), `isEmpty` and `in` on set
    /// literals, a rewritten node under an erring node, a rule's output
    /// meeting literals again, an opaque `iferror`, and the untouched
    /// `<set>.contains(<record>)` shape via a non-literal set.
    #[test]
    fn elim_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let (schema, env) = fixture();
        let cases = [
            "{x: principal.n, y: principal.s}.x == 3",
            "{x: {y: principal.n}}.x.y == 1",
            "{x: 1} has x",
            "{x: principal.n, y: 1} == {x: 3, y: 1}",
            "{x: {y: principal.n}} == {x: {y: 2}}",
            "[principal.s, \"x\"].contains(principal.s)",
            "[1, 2].containsAll([principal.n])",
            "principal.tags.containsAll([\"a\", principal.s])",
            "[principal.n].containsAny([resource.level, 7])",
            "[\"a\"].containsAny(principal.tags)",
            "[principal.n].isEmpty()",
            "principal in [Group::\"g1\", Group::\"g2\"]",
            "({x: principal.n}.x + 1) == resource.level + 1",
            "principal.r == {x: principal.n}",
            "iferror({x: principal.n}.x == 1, false)",
            "principal.n == 1 && {x: principal.n}.x == resource.level",
            "if {x: principal.n} has x then principal.n == 1 else principal.s == \"a\"",
            // `has` false; a record and a set literal above a rewritten child
            // without a rule of their own (an extension call with a rewritten
            // argument never typechecks: constructors take literals);
            // `contains` on a set of record literals; and the one shape that
            // stays, a non-literal set of records
            "{x: 1} has y",
            "{x: {y: principal.n}.y} == principal.r",
            "[{x: principal.n}.x] == [resource.level]",
            "[{x: 1}, {x: 2}].contains({x: principal.n})",
            "principal.rs.contains({x: principal.n})",
            // set equality with a literal side: on the right, on the left,
            // both, and nested in a record field and a `contains` element
            r#"principal.tags == ["a", principal.s]"#,
            r#"[principal.s, "b"] == principal.tags"#,
            r#"[principal.s, "a"] == ["a", principal.s]"#,
            r#"{x: principal.tags} == {x: [principal.s]}"#,
            r#"[[principal.s]].contains(principal.tags)"#,
        ];
        for text in cases {
            let expression = expr(text);
            let normalized =
                normalize_atoms(&expression, &schema, &env, DEFAULT_MAX_SPLIT_NODES).unwrap();
            match ffi.run_elim_check(&expression, &normalized) {
                Ok(result) => assert!(
                    result.agrees,
                    "`{text}`:\n  Rust: {}\n  Lean: {}",
                    result.expected, result.actual
                ),
                Err(e) => panic!("`{text}`: {e}"),
            }
        }
    }

    /// Exercises the target's plumbing on generated inputs from a fixed seed.
    #[test]
    fn elim_lean_target_smoke() {
        let ffi = CedarLeanFfi::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xe11_5eed);
        let (wanted, max_attempts) = (30, 4_000);
        let mut checked = 0;
        let mut skipped: HashMap<&'static str, usize> = HashMap::new();
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = ElimFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes)) else {
                *skipped.entry("not generated").or_default() += 1;
                continue;
            };
            match test_elim_vs_lean(&ffi, &input) {
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
            "only {checked} of {wanted} inputs were checked; skipped: {skipped:?}"
        );
    }
}

#[cfg(test)]
mod split_policy_test {
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

    /// Hand-picked conditions: the README `a || b` example (`[a, !a && b]`),
    /// the trivial `true` (one empty cube) and `false` (no policies at all),
    /// the Step-2 worked shapes (ifs and boolean structure under `==`),
    /// and a two-field record (the hoist-order transport path).
    /// A schema for the fixed cases: `view`'s context carries the booleans
    /// `a`–`d`, `x`, `y`, `z`, `w` and the record `r {a: Bool, b: Bool}`.
    fn fixture() -> cedar_policy::Schema {
        cedar_policy::Schema::from_cedarschema_str(
            r#"
            entity User;
            entity Doc;
            action view appliesTo {
                principal: User,
                resource: Doc,
                context: { a: Bool, b: Bool, c: Bool, d: Bool, x: Bool, y: Bool, z: Bool, w: Bool,
                           r: { a: Bool, b: Bool } }
            };
            "#,
        )
        .unwrap()
        .0
    }

    #[test]
    fn split_policy_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let schema = fixture();
        let cases = [
            "context.a || context.b",
            "true",
            "false",
            "context.a && context.b",
            "context.a && false",
            "!context.a",
            "if context.a then context.b else context.c",
            "(if context.a then 1 else 2) == 1",
            "(context.a && context.b) == (context.c || context.d)",
            "{a: context.x && context.y, b: context.z && context.w} == context.r",
            "context.a || (context.b && (context.c || context.d))",
            // the normalization's elimination, at policy level
            "{a: context.x, b: context.y}.a && context.b",
            "[context.x, context.y].contains(context.a)",
        ];
        for text in cases {
            let expression = expr(text);
            match test_split_policy_vs_lean(&ffi, &schema, &expression) {
                Verdict::Checked => {}
                Verdict::Skipped(skip) => panic!("`{text}` was skipped: {skip:?}"),
            }
        }
    }

    #[test]
    fn split_policy_lean_target_smoke() {
        let ffi = CedarLeanFfi::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x5b117_9011);
        let (wanted, max_attempts) = (30, 4_000);
        let mut checked = 0;
        let mut skipped: HashMap<&'static str, usize> = HashMap::new();
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = ElimFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes)) else {
                *skipped.entry("not generated").or_default() += 1;
                continue;
            };
            let Ok(schema) = cedar_policy::Schema::try_from(input.schema.clone()) else {
                *skipped.entry("schema").or_default() += 1;
                continue;
            };
            match test_split_policy_vs_lean(&ffi, &schema, &input.expression) {
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

#[derive(Debug, Clone)]
pub struct CombineFuzzTargetInput {
    /// generated schema, which the cube split validates the policies against
    pub schema: schema::Schema,
    /// generated policy set
    pub policies: cedar_policy_core::ast::PolicySet,
}

impl<'a> Arbitrary<'a> for CombineFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let count = u.int_in_range(1..=3)?;
        let mut policies = cedar_policy_core::ast::PolicySet::new();
        for i in 0..count {
            let expression = schema
                .exprgenerator(Some(&hierarchy))
                .generate_expr_for_type(&Type::bool(), SETTINGS.max_depth, u)?;
            let effect = if bool::arbitrary(u)? {
                Effect::Permit
            } else {
                Effect::Forbid
            };
            let policy = StaticPolicy::new(
                PolicyID::from_string(format!("p{i}")),
                None,
                Annotations::new(),
                effect,
                PrincipalConstraint::any(),
                ActionConstraint::any(),
                ResourceConstraint::any(),
                Some(expression),
            )
            .expect("a generated expression contains no slot");
            policies
                .add_static(policy)
                .expect("the ids p0, p1, … are distinct");
        }
        Ok(Self { schema, policies })
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

/// Renders a policy set for messages, one policy per line.
fn render(policies: &cedar_policy_core::ast::PolicySet) -> String {
    policies
        .policies()
        .map(|p| p.to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Runs the Rust allow/deny combination (`combine_allow_deny`) and its cube
/// split (`allow_cubes`) on `policies` and compares both, policy by policy
/// in id order, with the Lean model's `combineAllowDeny` and `allowCubes`.
/// Panics on a mismatch; a Rust-side resource limit in the split is a
/// benign skip (the Lean model has no budgets).
pub fn test_combine_vs_lean(
    ffi: &CedarLeanFfi,
    schema: &cedar_policy::Schema,
    policies: &cedar_policy_core::ast::PolicySet,
) -> Verdict {
    let combined = match combine_allow_deny(policies) {
        Ok(combined) => combined,
        Err(e) => panic!("the Rust combination failed on\n{}\n{e}", render(policies)),
    };
    let cubes = match allow_cubes(policies, schema, DEFAULT_MAX_SPLIT_NODES, DEFAULT_MAX_CUBES) {
        Ok(cubes) => cubes,
        Err(DnfError::NotWellTyped { .. }) => {
            return Skip::Benign("the combined policies are not well typed".into()).into();
        }
        Err(e @ (DnfError::RequestEnvNotFound(_) | DnfError::Typecheck(_))) => {
            return Skip::Benign(format!("the Rust typecheck could not run: {e}")).into();
        }
        Err(e @ (DnfError::TooLarge { .. } | DnfError::RecursionLimit)) => {
            return Skip::Benign(format!("the Rust cube split hit a resource limit: {e}")).into();
        }
        Err(e @ DnfError::Unsupported(_)) => {
            // With `tolerant-ast` off, `Unsupported` can only mean a Rust
            // invariant breach — the very bug class this DRT exists to catch.
            panic!(
                "the Rust cube split violated an invariant on\n{}\n{e}",
                render(policies)
            );
        }
    };
    debug!(
        "Rust combination:\n{}\nRust cubes:\n{}\n",
        render(&combined),
        render(&cubes)
    );
    match ffi.run_combine_check(policies, &combined, &cubes) {
        Ok(result) => {
            assert!(
                result.agrees,
                "the Rust combination and the Lean model disagree on\n{}\n  Rust: {}\n  Lean: {}",
                render(policies),
                result.expected,
                result.actual
            );
            Verdict::Checked
        }
        Err(e) => panic!("the Lean FFI call failed on\n{}\n{e}", render(policies)),
    }
}

#[cfg(test)]
mod combine_test {
    use std::collections::HashMap;

    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::symeval::Verdict;
    use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

    /// A schema for the fixed cases: the entity types and actions they name,
    /// and a `view`/`edit` context with the booleans `a`–`d`, the records
    /// `x`, `y` (`{y: Long}`) and `r` (`{a: {y: Long}, b: {y: Long}}`).
    fn fixture() -> cedar_policy::Schema {
        cedar_policy::Schema::from_cedarschema_str(
            r#"
            entity Group;
            entity User in [Group];
            entity Folder;
            entity Doc in [Folder];
            action view, edit appliesTo {
                principal: User,
                resource: Doc,
                context: { a: Bool, b: Bool, c: Bool, d: Bool,
                           x: { y: Long }, y: { y: Long },
                           r: { a: { y: Long }, b: { y: Long } } }
            };
            "#,
        )
        .unwrap()
        .0
    }

    fn pset(text: &str) -> cedar_policy_core::ast::PolicySet {
        cedar_policy_core::parser::parse_policyset(text).unwrap()
    }

    /// Hand-picked sets: the README rule (`permit a; forbid b`), a forbid
    /// chain (the nested witness), two forbids (id order), forbids with
    /// every scope kind (the scopes are conjuncts of the chain on both
    /// sides), an erroring conjunct, a `has` guard, a record (the
    /// canonicalization path), and the edge sets: no forbids, no permits,
    /// forbid-only, empty.
    #[test]
    fn combine_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let cases = [
            "permit(principal, action, resource) when { context.a };
             forbid(principal, action, resource) when { context.b };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal, action, resource) when { context.b && context.c && context.d };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal, action, resource) when { context.c };
             forbid(principal, action, resource) when { context.b };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal == User::\"alice\", action == Action::\"view\", resource in Folder::\"f\") when { context.b };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal is User in Group::\"g\", action in [Action::\"view\", Action::\"edit\"], resource is Doc) when { context.b };",
            "permit(principal is User, action, resource == Doc::\"d\");
             forbid(principal, action, resource) when { context.b };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal, action, resource) when { context.x.y == 1 && context.b };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal, action, resource) when { context has b && context.b };",
            "permit(principal, action, resource) when { context.a };
             forbid(principal, action, resource) when { {a: context.x, b: context.y} == context.r };",
            "permit(principal, action, resource) when { context.a || context.b };
             forbid(principal, action, resource) when { context.c || context.d };",
            "permit(principal, action, resource) when { context.a };
             permit(principal, action, resource) when { context.b };",
            "permit(principal, action, resource);",
            "forbid(principal, action, resource) when { context.b };",
            "",
            // the two live-fuzz findings: an explicit `when { true }` is a
            // conjunct (a missing clause is not), and a trivially-true
            // forbid's witness is the literal `false`, which `Expr::and`
            // would fold into a literal permit condition
            "permit(principal, action, resource) when { true };
             forbid(principal, action, resource) when { true };",
            "forbid(principal, action, resource) when { true };
             permit(principal, action, resource) when { false };",
        ];
        for text in cases {
            let policies = pset(text);
            match test_combine_vs_lean(&ffi, &fixture(), &policies) {
                Verdict::Checked => {}
                Verdict::Skipped(skip) => panic!("`{text}` was skipped: {skip:?}"),
            }
        }
        // forbid ids out of insertion order (the sort on both sides), and a
        // template-linked forbid (its filled scope is in the chain)
        let mut ordered = cedar_policy_core::ast::PolicySet::new();
        for (id, text) in [
            (
                "p",
                "permit(principal, action, resource) when { context.a };",
            ),
            (
                "z",
                "forbid(principal, action, resource) when { context.c };",
            ),
            (
                "a",
                "forbid(principal, action, resource) when { context.b };",
            ),
        ] {
            let policy =
                cedar_policy_core::parser::parse_policy(Some(PolicyID::from_string(id)), text)
                    .unwrap();
            ordered.add_static(policy).unwrap();
        }
        let mut linked = pset(
            "permit(principal, action, resource) when { context.a };
             forbid(principal == ?principal, action, resource == ?resource) when { context.b };",
        );
        linked
            .link(
                PolicyID::from_string("policy1"),
                PolicyID::from_string("linked"),
                std::collections::HashMap::from([
                    (
                        cedar_policy_core::ast::SlotId::principal(),
                        r#"User::"u""#.parse().unwrap(),
                    ),
                    (
                        cedar_policy_core::ast::SlotId::resource(),
                        r#"Doc::"d""#.parse().unwrap(),
                    ),
                ]),
            )
            .unwrap();
        for policies in [ordered, linked] {
            match test_combine_vs_lean(&ffi, &fixture(), &policies) {
                Verdict::Checked => {}
                Verdict::Skipped(skip) => panic!("a fixed set was skipped: {skip:?}"),
            }
        }
    }

    /// Exercises the target's plumbing on generated inputs from a fixed seed.
    #[test]
    fn combine_lean_target_smoke() {
        let ffi = CedarLeanFfi::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0xc0_3b1_9e);
        let (wanted, max_attempts) = (30, 2_000);
        let mut checked = 0;
        let mut skipped: HashMap<&'static str, usize> = HashMap::new();
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = CombineFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes))
            else {
                *skipped.entry("not generated").or_default() += 1;
                continue;
            };
            let Ok(schema) = cedar_policy::Schema::try_from(input.schema.clone()) else {
                *skipped.entry("schema").or_default() += 1;
                continue;
            };
            match test_combine_vs_lean(&ffi, &schema, &input.policies) {
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
