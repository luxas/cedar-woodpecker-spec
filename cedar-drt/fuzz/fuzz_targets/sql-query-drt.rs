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

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::fuzz_target;
use cedar_drt_inner::sql::{SqlQueryFuzzTargetInput, check_query};
use log::debug;

// `cedar-sql`'s partial requests (an unknown principal and/or resource)
// against `cedar-policy`'s authorizer over every candidate.
fuzz_target!(|input: SqlQueryFuzzTargetInput| {
    initialize_log();
    debug!("Schema: {}\n", input.base.schema.schemafile_string());
    debug!("Policy: {:?}\n", input.base.policy);
    debug!("Entities: {}\n", input.base.entities.as_ref());
    let verdict = check_query(&input);
    debug!("Verdict: {verdict:?}");
});
