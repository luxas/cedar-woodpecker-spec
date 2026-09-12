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

//! Fixed-case evaluation checks for the `iferror` extension function against
//! the Lean model (`Cedar.Spec.evaluate`'s `.call .ifError` arm): the rows of
//! its table, laziness of the fallback, and nesting under `!`. The generated
//! coverage comes from `iferror` being in the generators' extension-function
//! table, which the type-directed targets that reach the Lean model draw on
//! (evaluation, validation, the symbolic evaluator replay, the DNF pipeline,
//! and the Lean-TPE authorization targets, which also see the residual shapes).

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use cedar_drt::tests::run_eval_test;
    use cedar_lean_ffi::CedarLeanFfi;
    use cedar_policy::{Context, Entities, EntityUid, Expression, Request, eval_expression};
    use cedar_testing::cedar_test_impl::{CedarTestImplementation, TestResult};

    fn request() -> Request {
        Request::new(
            EntityUid::from_str(r#"User::"alice""#).unwrap(),
            EntityUid::from_str(r#"Action::"view""#).unwrap(),
            EntityUid::from_str(r#"Doc::"d""#).unwrap(),
            Context::empty(),
            None,
        )
        .unwrap()
    }

    /// The rows of the `iferror` table (`e` true/false/non-boolean/erroring,
    /// `d` boolean/non-boolean/erroring), laziness of the fallback, wrong
    /// arity, and the negated form Step 4 uses — Rust vs Lean.
    #[test]
    fn iferror_lean_fixed_cases() {
        let ffi = CedarLeanFfi::new();
        let request = request();
        let entities = Entities::empty();
        // `9223372036854775807 + 1` overflows; `{}.x` is a missing attribute
        let cases = [
            "iferror(true, false)",
            "iferror(false, true)",
            "iferror(true, 9223372036854775807 + 1 == 0)",
            "iferror(false, 9223372036854775807 + 1 == 0)",
            "iferror(9223372036854775807 + 1 == 0, true)",
            "iferror(9223372036854775807 + 1 == 0, false)",
            "iferror({}.x, true)",
            "iferror(1, true)",
            "iferror(\"x\", false)",
            "iferror(9223372036854775807 + 1 == 0, 1)",
            "iferror(9223372036854775807 + 1 == 0, 9223372036854775807 + 2 == 0)",
            "iferror(true)",
            "iferror(true, false, true)",
            "!iferror(9223372036854775807 + 1 == 0, false)",
            "!iferror(true, false) || iferror(false, true)",
            "iferror(iferror(9223372036854775807 + 1 == 0, true), false)",
            "[iferror(9223372036854775807 + 1 == 0, false)].contains(false)",
            "if iferror(9223372036854775807 + 1 == 0, true) then 1 else 2",
        ];
        for text in cases {
            let expr = Expression::from_str(text).unwrap_or_else(|e| panic!("`{text}`: {e}"));
            run_eval_test(&ffi, &request, &expr, &entities);
            // `run_eval_test` skips a definitional "unknown extension function"
            // failure; make sure the Lean side really evaluated `iferror`
            let expected = eval_expression(&request, &entities, &expr).ok();
            assert!(
                matches!(
                    ffi.interpret(&request, &entities, &expr, expected),
                    TestResult::Success(true)
                ),
                "the Lean model did not evaluate `{text}` like Rust"
            );
        }
    }
}
