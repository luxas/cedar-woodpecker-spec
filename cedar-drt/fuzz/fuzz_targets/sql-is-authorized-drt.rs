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
use cedar_drt_inner::sql::{SqlFuzzTargetInput, check_is_authorized};
use log::debug;

// `cedar-sql`'s concrete authorization against `cedar-policy`'s authorizer:
// type-directed ABAC inputs without extension types, loaded into Postgres.
fuzz_target!(|input: SqlFuzzTargetInput| {
    initialize_log();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("Policy: {:?}\n", input.policy);
    debug!("Entities: {}\n", input.entities.as_ref());
    let outcome = check_is_authorized(&input);
    debug!("Outcome: {outcome:?}");
});
