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

//! DRT fuzz target comparing the Rust symbolic evaluator against its Lean
//! model.
//!
//! The Rust evaluator runs on fully known data with a recorded trace (every
//! solver query with its full assert list and answer, plus the
//! `check_equivalent` self-check). Lean replays the trace through
//! `Cedar.SymCC.Opt.symEvalWithBase` with the recorded answers as its oracle:
//! any divergence — a different query, a different fold, a different outcome
//! set — fails at the exact query where the two implementations part ways.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    symcc::RUNTIME,
    symeval::{ConcreteFuzzTargetInput, test_symbolic_vs_lean},
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Request, Schema};
use log::debug;

fuzz_target!(|input: ConcreteFuzzTargetInput| {
    initialize_log();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("expr: {}\n", input.expression);
    debug!("request: {}\n", input.request);
    debug!("Entities: {}\n", input.entities.as_ref());
    if let Ok(schema) = Schema::try_from(input.schema) {
        let ffi = CedarLeanFfi::new();
        let Ok(lean_schema) = ffi.load_lean_schema_object(&schema) else {
            return;
        };
        let request: Request = input.request.into();
        let verdict = RUNTIME.block_on(test_symbolic_vs_lean(
            &ffi,
            &lean_schema,
            &schema,
            &input.entities,
            &request,
            &input.expression,
        ));
        debug!("verdict: {verdict:?}");
    }
});
