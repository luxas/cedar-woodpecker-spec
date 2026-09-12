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

//! FFI wrapper for replaying a recorded Rust symbolic evaluation through the
//! Lean model (`Cedar.SymCC.Opt.symEvalWithBase`).

use crate::datatypes::{self as datatypes, ResultDef, TimedDef};
use crate::err::FfiError;
use crate::messages::proto;

use cedar_policy::RequestEnv;

use super::{CedarLeanFfi, LeanSchema, call_lean_ffi_takes_obj_and_protobuf, runSymEvalReplay};

impl CedarLeanFfi {
    /// Replays a recorded symbolic evaluation through the Lean model: the
    /// model re-runs the evaluator over `expr` and `base` with an oracle that
    /// pops `queries` in order — failing at the first query whose assert list
    /// diverges from the recording — and compares its result (and, when
    /// `ce_base` is given, its own `checkEquivalent` verdict) against
    /// `expected` / `expected_outcomes` (can-true, can-false, can-error).
    #[allow(clippy::too_many_arguments)]
    pub fn run_symeval_replay(
        &self,
        schema: LeanSchema,
        request_env: &RequestEnv,
        expr: &cedar_policy_core::ast::Expr,
        base: &[datatypes::Term],
        queries: &[(Vec<datatypes::Term>, bool)],
        expected: &cedar_policy_core::ast::Expr,
        expected_outcomes: (bool, bool, bool),
        ce_base: Option<&[datatypes::Term]>,
    ) -> Result<datatypes::tpe::CheckResult, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_obj_and_protobuf(
                runSymEvalReplay,
                schema.0,
                &proto::SymEvalReplayRequest::new(
                    request_env,
                    expr,
                    base,
                    queries,
                    expected,
                    expected_outcomes,
                    ce_base,
                ),
            )
        };
        match response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<datatypes::tpe::CheckResult>>>()?
        {
            ResultDef::Ok(resp) => Ok(resp.data),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
}
