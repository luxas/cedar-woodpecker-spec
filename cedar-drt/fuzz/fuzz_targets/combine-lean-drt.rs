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

//! DRT fuzz target comparing the Rust allow/deny combiner against its Lean
//! model.
//!
//! The Lean model's decision-equivalence theorems are machine-checked
//! (`Cedar.Thm.DNF.combineAllowDeny_decision`, `allowCubes_decision`); this
//! target ties them to the Rust implementation
//! (`cedar_policy_symcc::dnf::{combine_allow_deny, allow_cubes}`): a
//! generated policy set of permits and forbids is combined and split on both
//! sides, and the resulting policies must match, id by id, up to
//! record-field order.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    dnf::{CombineFuzzTargetInput, test_combine_vs_lean},
    fuzz_target,
};
use cedar_lean_ffi::CedarLeanFfi;
use log::debug;

fuzz_target!(|input: CombineFuzzTargetInput| {
    initialize_log();
    debug!("policies: {:?}\n", input.policies);
    let ffi = CedarLeanFfi::new();
    let Ok(schema) = cedar_policy::Schema::try_from(input.schema.clone()) else {
        debug!("the generated schema does not convert");
        return;
    };
    let verdict = test_combine_vs_lean(&ffi, &schema, &input.policies);
    debug!("verdict: {verdict:?}");
});
