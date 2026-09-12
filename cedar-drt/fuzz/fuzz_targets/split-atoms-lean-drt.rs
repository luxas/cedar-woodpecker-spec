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

//! DRT fuzz target comparing the Rust atom splitter against its Lean model.
//!
//! The Lean model's equivalence and cleanliness theorems are machine-checked
//! (`Cedar.Thm.DNF`); this target ties them to the Rust implementation
//! (`cedar_policy_symcc::dnf::split_atoms`): both sides split the same
//! generated boolean expression and the outputs must be structurally
//! identical, up to record-field order.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    dnf::{DnfFuzzTargetInput, test_split_vs_lean},
    fuzz_target,
};
use cedar_lean_ffi::CedarLeanFfi;
use log::debug;

fuzz_target!(|input: DnfFuzzTargetInput| {
    initialize_log();
    debug!("expr: {}\n", input.expression);
    let ffi = CedarLeanFfi::new();
    let verdict = test_split_vs_lean(&ffi, &input.expression);
    debug!("verdict: {verdict:?}");
});
