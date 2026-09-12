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

//! DRT fuzz target comparing the symbolic evaluator against the typed partial
//! evaluator (TPE) on partially known data.
//!
//! For every policy TPE produces a residual for, the symbolic evaluator's
//! (exact) outcome set for the policy condition must be a subset of the
//! residual's (over-approximated) possible outcomes, and the residual and the
//! symbolic result must both be equivalent to the policy condition on every
//! completion of the partial data (checked with the solver).

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    symcc::RUNTIME,
    symeval::test_symbolic_vs_tpe,
    tpe::{TpeFuzzTargetInput, passes_policyset_validation},
};
use cedar_policy::{Schema, Validator};
use log::debug;

fuzz_target!(|input: TpeFuzzTargetInput| {
    initialize_log();
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let policies = input.abac_input.policy.into_policy_set();
        if passes_policyset_validation(&validator, &policies) {
            for partial_request in &input.partial_requests {
                let verdict = RUNTIME.block_on(test_symbolic_vs_tpe(
                    &schema,
                    &policies,
                    partial_request,
                    &input.partial_entities,
                ));
                debug!("verdict: {verdict:?}");
            }
        }
    }
});
