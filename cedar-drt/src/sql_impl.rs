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

//! `cedar-sql` as a [`CedarTestImplementation`]: authorization loads the
//! entities into the tables generated from the schema (inside a transaction
//! that is rolled back afterwards, on the Postgres of
//! `cedar_sql::testing::SharedPostgres`) and runs the compiled query;
//! validation and evaluation delegate to the Rust implementation.

use std::cell::RefCell;
use std::collections::HashMap;

use cedar_policy::{
    Entities, EvalResult, Expression, PolicySet, Request, Schema, ValidationMode, ffi,
};
use cedar_sql::authorizer::{QueryRow, Response, SqlAuthorizer, action_entities, partial_request};
use cedar_sql::backend::Backend;
use cedar_sql::backend::postgres::PgBackend;
use cedar_sql::config::DatabaseConfiguration;
use cedar_sql::ddl::create_tables;
use cedar_sql::dialect::Postgres;
use cedar_sql::load::entities_to_sql;
use cedar_sql::testing::SharedPostgres;
use cedar_testing::cedar_test_impl::{
    CedarTestImplementation, ErrorComparisonMode, Micros, RustEngine, TestResponse, TestResult,
    TestValidationResult, ValidationComparisonMode, time_function,
};
use miette::miette;

/// The statement timeout of one authorization, after which the input is skipped.
const STATEMENT_TIMEOUT: &str = "30s";

/// `cedar-sql` over one schema, with one database connection.
pub struct SqlTestImpl {
    schema: Schema,
    config: DatabaseConfiguration,
    db: RefCell<PgBackend>,
    rust: RustEngine,
}

impl SqlTestImpl {
    /// The default mapping of `schema` (over-long generated names shortened),
    /// without foreign keys (Cedar data may reference entities that do not
    /// exist); `hierarchy_closed` selects the closed-table `in` or the
    /// recursive ancestors CTE.
    pub fn new(schema: Schema, hierarchy_closed: bool) -> Result<Self, cedar_sql::Error> {
        let mut config = DatabaseConfiguration::from_schema_shortening_names(&schema)?;
        config.emit_foreign_keys = false;
        // The loader stores the closure, so both modes are correct; the
        // recursive CTE is exercised when `hierarchy_closed` is off.
        config.hierarchy_closed = hierarchy_closed;
        let db = SharedPostgres::get()?.connect()?;
        Ok(Self {
            schema,
            config,
            db: RefCell::new(db),
            rust: RustEngine::new(),
        })
    }

    /// The database configuration in use.
    pub fn config(&self) -> &DatabaseConfiguration {
        &self.config
    }

    /// Runs `f` on a database holding exactly `entities`, in a transaction
    /// that is rolled back afterwards.
    pub fn with_loaded<T>(
        &self,
        entities: &Entities,
        f: impl FnOnce(&mut PgBackend) -> Result<T, cedar_sql::Error>,
    ) -> Result<T, cedar_sql::Error> {
        let mut db = self.db.borrow_mut();
        // A previous input may have left a transaction open (a panic mid-way).
        let _ = db.execute_batch("ROLLBACK");
        db.begin()?;
        let result = (|| {
            db.execute_batch(&format!(
                "SET LOCAL statement_timeout = '{STATEMENT_TIMEOUT}'"
            ))?;
            for statement in create_tables(&self.config, &Postgres)? {
                db.execute_batch(&statement)?;
            }
            let load = entities_to_sql(entities, &self.schema, &self.config, &Postgres)?;
            for statement in &load.statements {
                db.execute_batch(statement)?;
            }
            f(&mut db)
        })();
        let _ = db.rollback();
        result
    }

    /// Authorizes `request` for `policies` over `entities`.
    pub fn authorize(
        &self,
        request: &Request,
        policies: &PolicySet,
        entities: &Entities,
    ) -> Result<Response, cedar_sql::Error> {
        let authorizer = SqlAuthorizer::new(&self.schema, &self.config, &Postgres, policies)?;
        self.with_loaded(entities, |db| {
            authorizer.is_authorized(db, request, entities)
        })
    }
}

impl SqlTestImpl {
    /// Authorizes `request` with its principal and/or resource id dropped:
    /// one row per candidate entity (pair) in `entities`.
    pub fn query(
        &self,
        request: &Request,
        unknown_principal: bool,
        unknown_resource: bool,
        policies: &PolicySet,
        entities: &Entities,
    ) -> Result<Vec<QueryRow>, cedar_sql::Error> {
        let authorizer = SqlAuthorizer::new(&self.schema, &self.config, &Postgres, policies)?;
        let partial = partial_request(request, unknown_principal, unknown_resource, &self.schema)?;
        let actions = action_entities(entities, &self.schema)?;
        self.with_loaded(entities, |db| authorizer.query(db, &partial, &actions))
    }
}

impl CedarTestImplementation for SqlTestImpl {
    fn is_authorized(
        &self,
        request: &Request,
        policies: &PolicySet,
        entities: &Entities,
    ) -> TestResult<TestResponse> {
        let (result, duration) = time_function(|| self.authorize(request, policies, entities));
        match result {
            Ok(response) => TestResult::Success(TestResponse {
                response: ffi::Response::new(
                    response.decision,
                    response.reason.into_iter().collect(),
                    response
                        .errors
                        .into_iter()
                        .map(|id| {
                            ffi::AuthorizationError::new_from_report(id.clone(), miette!("{id}"))
                        })
                        .collect(),
                ),
                timing_info: HashMap::from([("authorize".into(), Micros(duration.as_micros()))]),
            }),
            Err(e) => TestResult::Failure(e.to_string()),
        }
    }

    fn interpret(
        &self,
        request: &Request,
        entities: &Entities,
        expr: &Expression,
        expected: Option<EvalResult>,
    ) -> TestResult<bool> {
        self.rust.interpret(request, entities, expr, expected)
    }

    fn validate(
        &self,
        schema: &Schema,
        policies: &PolicySet,
        mode: ValidationMode,
    ) -> TestResult<TestValidationResult> {
        self.rust.validate(schema, policies, mode)
    }

    fn validate_with_level(
        &self,
        schema: &Schema,
        policies: &PolicySet,
        mode: ValidationMode,
        level: i32,
    ) -> TestResult<TestValidationResult> {
        self.rust.validate_with_level(schema, policies, mode, level)
    }

    fn validate_request(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> TestResult<TestValidationResult> {
        self.rust.validate_request(schema, request)
    }

    fn validate_entities(
        &self,
        schema: &Schema,
        entities: &Entities,
    ) -> TestResult<TestValidationResult> {
        self.rust.validate_entities(schema, entities)
    }

    fn error_comparison_mode(&self) -> ErrorComparisonMode {
        ErrorComparisonMode::PolicyIds
    }

    fn validation_comparison_mode(&self) -> ValidationComparisonMode {
        ValidationComparisonMode::AgreeOnAll
    }
}
