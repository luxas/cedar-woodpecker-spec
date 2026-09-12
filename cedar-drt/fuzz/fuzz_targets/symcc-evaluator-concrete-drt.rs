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

//! DRT fuzz target comparing the symbolic evaluator against the concrete
//! evaluator on fully known data.
//!
//! With the whole entity store and the request assumed, the symbolic
//! evaluator must fold a (mostly) well-typed boolean expression to exactly the
//! outcome the concrete evaluator computes, and its result must be equivalent
//! to the input expression under those assumptions (checked with the solver).
//! Inputs that are not strongly well-formed — the envelope of SymCC's
//! soundness theorems — are skipped.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    symcc::RUNTIME,
    symeval::{ConcreteFuzzTargetInput, test_symbolic_vs_concrete},
};
use cedar_policy::{Request, Schema};
use log::debug;

fuzz_target!(|input: ConcreteFuzzTargetInput| {
    initialize_log();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("expr: {}\n", input.expression);
    debug!("request: {}\n", input.request);
    debug!("Entities: {}\n", input.entities.as_ref());
    if let Ok(schema) = Schema::try_from(input.schema) {
        let request: Request = input.request.into();
        let verdict = RUNTIME.block_on(test_symbolic_vs_concrete(
            &schema,
            &input.entities,
            &request,
            &input.expression,
        ));
        debug!("verdict: {verdict:?}");
    }
});
