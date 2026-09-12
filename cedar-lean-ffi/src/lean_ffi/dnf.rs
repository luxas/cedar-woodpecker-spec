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

//! FFI wrapper for checking a Rust DNF conversion against the Lean model
//! (`Cedar.DNF.dnf`).

use crate::datatypes::{ResultDef, TimedDef, tpe::CheckResult};
use crate::err::FfiError;
use crate::messages::proto;

use super::{CedarLeanFfi, call_lean_ffi_takes_protobuf, runCheckDnf, runCheckSplit};

impl CedarLeanFfi {
    /// Checks a Rust DNF conversion against the Lean model: the model
    /// recomputes the DNF of `expr` with the `can_error` extreme that
    /// `can_error_all` records (`true` for every atom, i.e. `Dnf::of_expr`,
    /// or `false` for every atom) and compares it structurally with
    /// `expected` (the Rust `Dnf::…​.to_expr()`), after canonicalizing
    /// record-field order on both sides.
    pub fn run_dnf_check(
        &self,
        expr: &cedar_policy_core::ast::Expr,
        expected: &cedar_policy_core::ast::Expr,
        can_error_all: bool,
    ) -> Result<CheckResult, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                runCheckDnf,
                &proto::DnfCheckRequest::new(expr, expected, can_error_all),
            )
        };
        match response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<CheckResult>>>()?
        {
            ResultDef::Ok(resp) => Ok(resp.data),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
}

impl CedarLeanFfi {
    /// Checks a Rust atom split against the Lean model: the model recomputes
    /// `Cedar.DNF.splitAtoms` on `expr` and compares it structurally with
    /// `expected` (the Rust `split_atoms(expr, ..)` output), after
    /// canonicalizing record-field order on both sides.
    pub fn run_split_check(
        &self,
        expr: &cedar_policy_core::ast::Expr,
        expected: &cedar_policy_core::ast::Expr,
    ) -> Result<CheckResult, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                runCheckSplit,
                &proto::SplitCheckRequest::new(expr, expected),
            )
        };
        match response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<CheckResult>>>()?
        {
            ResultDef::Ok(resp) => Ok(resp.data),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
}
