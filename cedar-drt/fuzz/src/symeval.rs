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

//! Test utilities for the symbolic evaluator fuzz targets
//! (`symcc-evaluator-concrete-drt`, `symcc-evaluator-tpe-drt`).
//!
//! Both targets compare `cedar_policy_symcc::evaluator::Evaluator` against an
//! oracle in Rust: the concrete evaluator on fully known data, and the typed
//! partial evaluator (TPE) on partially known data. The Lean model is not
//! involved (the symbolic evaluator has no Lean counterpart yet); see
//! `docs/plans/5-symbolic-evaluator.md`.

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use cedar_lean_ffi::{CedarLeanFfi, LeanSchema};
use cedar_policy::{Entities, PartialEntities, PartialRequest, PolicySet, Request, Schema};
use cedar_policy_core::ast::{
    self, EntityUID, Expr, ExprKind, Literal, PartialValue, Value, ValueKind,
};
use cedar_policy_core::evaluator::{
    EvaluationError as ConcreteEvaluationError, Evaluator as ConcreteEvaluator,
};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_core::tpe::residual::{EvaluationOutcome, Residual};
use cedar_policy_generators::abac::{ABACRequest, Type};
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::settings::ABACSettings;
use cedar_policy_symcc::CedarSymCompiler;
use cedar_policy_symcc::err::{CompileError, EncodeError, Error};
use cedar_policy_symcc::evaluator::{
    EvaluationError, EvaluationMetadata, EvaluationTrace, Evaluator, erase_metadata,
    request_env_of, with_default_metadata,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, warn};
use tokio::time::{Duration, timeout};

use crate::schemas;
use crate::symcc::{WrappedLocalSolver, new_symcc};

/// Settings for the symbolic evaluator fuzz targets.
pub const SETTINGS: ABACSettings = ABACSettings {
    max_depth: 3,
    max_width: 3,
    ..ABACSettings::type_directed()
};

/// Input to `symcc-evaluator-concrete-drt`: a schema, a *complete* entity
/// store for it, a request and a (mostly) well-typed boolean expression.
///
/// Unlike `eval-type-directed`, no entities are dropped from the generated
/// hierarchy: the symbolic evaluator only promises anything about strongly
/// well-formed inputs (see [`is_strongly_well_formed_for`]).
#[derive(Debug, Clone)]
pub struct ConcreteFuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated entity store (the whole hierarchy, plus the action entities)
    pub entities: Entities,
    /// generated request
    pub request: ABACRequest,
    /// generated boolean expression
    pub expression: Expr,
}

impl<'a> Arbitrary<'a> for ConcreteFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let expression = schema
            .exprgenerator(Some(&hierarchy))
            .generate_expr_for_type(&Type::bool(), SETTINGS.max_depth, u)?;
        let request = schema.arbitrary_request(&hierarchy, u)?;
        let entities =
            Entities::try_from(hierarchy).map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let cedar_schema =
            Schema::try_from(schema.clone()).map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let entities = schemas::add_actions_to_entities(&cedar_schema, entities)?;
        Ok(Self {
            schema,
            entities,
            request,
            expression,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

/// Every entity UID a value mentions, recursively through sets and records.
fn uids_in_value<'a>(value: &'a Value, out: &mut Vec<&'a EntityUID>) {
    match &value.value {
        ValueKind::Lit(Literal::EntityUID(uid)) => out.push(uid),
        ValueKind::Lit(_) | ValueKind::ExtensionValue(_) => {}
        ValueKind::Set(set) => set.iter().for_each(|v| uids_in_value(v, out)),
        ValueKind::Record(map) => map.values().for_each(|v| uids_in_value(v, out)),
    }
}

fn uids_in_partial_value<'a>(value: &'a PartialValue, out: &mut Vec<&'a EntityUID>) {
    match value {
        PartialValue::Value(v) => uids_in_value(v, out),
        PartialValue::Residual(e) => uids_in_expr(e, out),
    }
}

fn uids_in_expr<'a>(expr: &'a Expr, out: &mut Vec<&'a EntityUID>) {
    out.extend(expr.subexpressions().filter_map(|e| match e.expr_kind() {
        ExprKind::Lit(Literal::EntityUID(uid)) => Some(uid.as_ref()),
        _ => None,
    }));
}

/// Whether `(request, entities)` is *strongly well-formed* for `expr` in the
/// sense of the Lean SymCC development (`Cedar/Thm/SymCC/Data/Hierarchy.lean`,
/// `StronglyWellFormedFor`): every entity referenced by the expression, by the
/// request (principal, action, resource, and any entity in the context), or by
/// the entity data itself (attribute values, ancestors, tag values) exists in
/// the store.
///
/// Acyclicity and transitive closure of the hierarchy are not checked here:
/// `Entities` computes/enforces them on construction.
///
/// Why this matters: the generators deliberately emit UIDs that (probably)
/// don't exist, and a dangling UID is not always a concrete evaluation error —
/// `e has attr` on a missing entity is `false` concretely but `true`
/// symbolically — so inputs outside the envelope must be filtered out rather
/// than detected by an `EntityDoesNotExist` error.
pub fn is_strongly_well_formed_for(entities: &Entities, request: &Request, expr: &Expr) -> bool {
    let store: HashSet<&EntityUID> = entities.as_ref().iter().map(|e| e.uid()).collect();
    let mut referenced: Vec<&EntityUID> = Vec::new();
    uids_in_expr(expr, &mut referenced);
    let req: &ast::Request = request.as_ref();
    for entry in [req.principal(), req.action(), req.resource()] {
        match entry.uid() {
            Some(uid) => referenced.push(uid),
            None => return false,
        }
    }
    match req.context() {
        Some(ast::Context::Value(attrs)) => attrs
            .values()
            .for_each(|v| uids_in_value(v, &mut referenced)),
        Some(ast::Context::RestrictedResidual(_)) | None => return false,
    }
    for entity in entities.as_ref().iter() {
        referenced.extend(entity.ancestors());
        entity
            .attrs()
            .for_each(|(_, v)| uids_in_partial_value(v, &mut referenced));
        entity
            .tags()
            .for_each(|(_, v)| uids_in_partial_value(v, &mut referenced));
    }
    referenced.into_iter().all(|uid| store.contains(uid))
}

/// Why an input was skipped instead of checked.
#[derive(Debug)]
pub enum Skip {
    /// The input is outside what the symbolic evaluator promises anything
    /// about (not strongly well-formed, entity data or request rejected by the
    /// schema, TPE rejected the input, ...).
    OutsideEnvelope(String),
    /// The expression is not (strictly) well typed in the request env, or the
    /// request env is not in the schema. The generators are only *mostly*
    /// type-directed.
    NotWellTyped(String),
    /// A known limitation of the crate under test — for SymCC: SMT-LIB
    /// strings are not full Unicode, some `like` patterns cannot be encoded,
    /// and some features (e.g. the empty set literal) are not supported by
    /// the compiler; for the DNF converter: a resource limit was hit.
    Benign(String),
    /// The solver took longer than [`TIMEOUT_DUR`]; it was restarted.
    Timeout,
    /// The solver answered `unknown`.
    Unknown,
}

/// Solver timeout for one evaluator call (an evaluation issues up to three
/// solver queries per atom, so this is per call, not per query).
pub const TIMEOUT_DUR: Duration = Duration::from_secs(300);

/// Maximum number of evaluators built on one solver process before it is
/// restarted (mirrors `symcc::SymCCWithUsageLimit`).
const SOLVER_USAGE_LIMIT: usize = 10_000;

struct SharedCompiler {
    compiler: Option<CedarSymCompiler<WrappedLocalSolver>>,
    uses: usize,
}

/// The solver process shared by every [`SymEval`]. The evaluator owns its
/// compiler, so it is taken out of here while an evaluator lives and put back
/// when the evaluator is finished.
static SHARED: Mutex<SharedCompiler> = Mutex::new(SharedCompiler {
    compiler: None,
    uses: 0,
});

async fn acquire_compiler() -> CedarSymCompiler<WrappedLocalSolver> {
    let (compiler, uses) = {
        let mut shared = SHARED.lock().unwrap();
        shared.uses += 1;
        (shared.compiler.take(), shared.uses)
    };
    match compiler {
        Some(compiler) if uses < SOLVER_USAGE_LIMIT => compiler,
        Some(compiler) => {
            discard_compiler(compiler).await;
            SHARED.lock().unwrap().uses = 0;
            new_symcc()
        }
        None => new_symcc(),
    }
}

fn release_compiler(compiler: CedarSymCompiler<WrappedLocalSolver>) {
    SHARED.lock().unwrap().compiler = Some(compiler);
}

/// Kills the solver process; the next [`acquire_compiler`] starts a new one.
async fn discard_compiler(mut compiler: CedarSymCompiler<WrappedLocalSolver>) {
    let _ = compiler.solver_mut().solver.clean_up().await;
}

/// A symbolic evaluator on the shared solver, with the error handling the
/// fuzz targets need: infrastructure errors that are expected on generated
/// inputs become [`Skip`]s, everything else panics.
pub struct SymEval {
    evaluator: Evaluator<WrappedLocalSolver>,
    /// Whether the solver process may be in a bad state (a timeout dropped a
    /// query half-way) and must not be reused.
    poisoned: bool,
}

impl SymEval {
    /// Builds an evaluator for `schema`. `None` when SymCC cannot compile the
    /// schema.
    pub async fn new(schema: &Schema) -> Option<Self> {
        let compiler = acquire_compiler().await;
        match Evaluator::new(compiler, schema) {
            Ok(evaluator) => Some(Self {
                evaluator,
                poisoned: false,
            }),
            Err(err) => {
                // `Evaluator::new` consumed the compiler; start afresh next time.
                warn!("SymCC cannot compile the schema: {err}");
                None
            }
        }
    }

    /// Hands the solver process back for the next evaluator, or kills it if
    /// it may be in a bad state.
    pub async fn finish(self) {
        let compiler = self.evaluator.into_compiler();
        if self.poisoned {
            discard_compiler(compiler).await;
        } else {
            release_compiler(compiler);
        }
    }

    /// See [`Evaluator::record_trace`].
    pub fn record_trace(&mut self, on: bool) {
        self.evaluator.record_trace(on);
    }

    /// See [`Evaluator::take_trace`].
    pub fn take_trace(&mut self) -> Option<EvaluationTrace> {
        self.evaluator.take_trace()
    }

    /// See [`Evaluator::assume_entities`]. Entity data the schema rejects is
    /// outside the envelope.
    pub fn assume_entities(&mut self, entities: &Entities) -> Result<(), Skip> {
        self.evaluator
            .assume_entities(entities)
            .map_err(|e| Skip::OutsideEnvelope(e.to_string()))
    }

    /// See [`Evaluator::assume_request`].
    pub fn assume_request(&mut self, request: &Request) -> Result<(), Skip> {
        self.evaluator
            .assume_request(request)
            .map_err(|e| Skip::OutsideEnvelope(e.to_string()))
    }

    /// See [`Evaluator::assume_partial_entities`].
    pub fn assume_partial_entities(&mut self, entities: &PartialEntities) {
        self.evaluator
            .assume_partial_entities(entities.as_ref().clone());
    }

    /// See [`Evaluator::assume_partial_request`].
    pub fn assume_partial_request(&mut self, request: &PartialRequest) {
        self.evaluator
            .assume_partial_request(request.as_ref().clone());
    }

    /// See [`Evaluator::evaluate`].
    pub async fn evaluate(
        &mut self,
        expr: &Expr,
        env: &cedar_policy::RequestEnv,
    ) -> Result<Expr<EvaluationMetadata>, Skip> {
        let res = timeout(
            TIMEOUT_DUR,
            self.evaluator.evaluate(expr, env, Vec::<Expr>::new()),
        )
        .await;
        self.classify(res)
    }

    /// See [`Evaluator::check_equivalent`].
    pub async fn check_equivalent(
        &mut self,
        expr: &Expr,
        result: &Expr<EvaluationMetadata>,
        env: &cedar_policy::RequestEnv,
    ) -> Result<bool, Skip> {
        let res = timeout(
            TIMEOUT_DUR,
            self.evaluator
                .check_equivalent(expr, result, env, Vec::<Expr>::new()),
        )
        .await;
        self.classify(res)
    }

    fn classify<T>(
        &mut self,
        res: Result<Result<T, EvaluationError>, tokio::time::error::Elapsed>,
    ) -> Result<T, Skip> {
        match res {
            Ok(Ok(v)) => Ok(v),
            Err(_elapsed) => {
                debug!(
                    "found a slow unit (solver took more than {secs:.2} sec)",
                    secs = TIMEOUT_DUR.as_secs_f32()
                );
                self.poisoned = true;
                Err(Skip::Timeout)
            }
            Ok(Err(err)) => match err {
                EvaluationError::NotWellTyped { .. }
                | EvaluationError::NotBoolean { .. }
                | EvaluationError::RequestEnvNotFound(_) => {
                    Err(Skip::NotWellTyped(err.to_string()))
                }
                EvaluationError::InvalidEntities(_) | EvaluationError::InvalidRequest(_) => {
                    Err(Skip::OutsideEnvelope(err.to_string()))
                }
                EvaluationError::SymCC(Error::EncodeError(EncodeError::EncodeStringFailed(_)))
                | EvaluationError::SymCC(Error::EncodeError(EncodeError::EncodePatternFailed(_)))
                | EvaluationError::SymCC(Error::CompileError(CompileError::UnsupportedFeature(
                    _,
                ))) => Err(Skip::Benign(err.to_string())),
                EvaluationError::SymCC(Error::SolverUnknown) => Err(Skip::Unknown),
                EvaluationError::SymCC(Error::SolverError(e)) => panic!("solver failed: {e}"),
                // Contradictory assumptions on data that came from a concrete
                // store, an ill-typed *assumption*, an internal invariant
                // violation, or an unexpected SymCC error: all real bugs.
                other => panic!("unexpected symbolic evaluation error: {other}"),
            },
        }
    }
}

/// What a differential test did with its input.
#[derive(Debug)]
pub enum Verdict {
    /// All assertions ran and passed.
    Checked,
    /// The input was skipped.
    Skipped(Skip),
}

impl From<Skip> for Verdict {
    fn from(skip: Skip) -> Self {
        Self::Skipped(skip)
    }
}

/// The concrete evaluator's outcome for a boolean expression: `None` when the
/// expression does not evaluate to a boolean (which the symbolic evaluator
/// rejects as ill-typed) or refers to an entity that does not exist.
fn concrete_outcome(
    request: &Request,
    entities: &Entities,
    expr: &Expr,
) -> Result<EvaluationOutcome, Skip> {
    let evaluator = ConcreteEvaluator::new(
        request.as_ref().clone(),
        entities.as_ref(),
        Extensions::all_available(),
    );
    match evaluator.interpret(expr, &HashMap::new()) {
        Ok(value) => match value.get_as_bool() {
            Ok(true) => Ok(EvaluationOutcome::True),
            Ok(false) => Ok(EvaluationOutcome::False),
            Err(_) => Err(Skip::NotWellTyped(format!(
                "evaluates to the non-boolean `{value}`"
            ))),
        },
        // Should already be excluded by `is_strongly_well_formed_for`; kept
        // as a safety net.
        Err(ConcreteEvaluationError::EntityDoesNotExist(e)) => {
            Err(Skip::OutsideEnvelope(e.to_string()))
        }
        Err(_) => Ok(EvaluationOutcome::Error),
    }
}

fn outcome_set<'a>(
    outcomes: impl IntoIterator<Item = &'a EvaluationOutcome>,
) -> HashSet<EvaluationOutcome> {
    outcomes.into_iter().cloned().collect()
}

/// Differential test of the symbolic evaluator against the concrete evaluator
/// on a fully known store and request.
///
/// With everything known, the symbolic evaluator must fold `expr` to exactly
/// the concrete outcome (exactness, contract (C)), and its result must be
/// equivalent to `expr` under the assumptions (contract (S2)).
pub async fn test_symbolic_vs_concrete(
    schema: &Schema,
    entities: &Entities,
    request: &Request,
    expr: &Expr,
) -> Verdict {
    if !is_strongly_well_formed_for(entities, request, expr) {
        return Skip::OutsideEnvelope("not strongly well-formed".into()).into();
    }
    let expected = match concrete_outcome(request, entities, expr) {
        Ok(o) => o,
        Err(skip) => return skip.into(),
    };
    let Some(env) = request_env_of(request, schema) else {
        return Skip::NotWellTyped("request env not in the schema".into()).into();
    };
    let Some(mut ev) = SymEval::new(schema).await else {
        return Skip::Benign("schema not compilable".into()).into();
    };
    let verdict = async {
        ev.assume_entities(entities)?;
        ev.assume_request(request)?;
        let result = ev.evaluate(expr, &env).await?;
        assert_eq!(
            outcome_set(result.data().outcomes().iter()),
            outcome_set([&expected]),
            "symbolic evaluator disagrees with the concrete evaluator\n\
             expression: {expr}\n\
             request: {request}\n\
             entities: {}\n\
             concrete outcome: {expected:?}\n\
             symbolic result: {result}",
            entities.as_ref()
        );
        let equivalent = ev.check_equivalent(expr, &result, &env).await?;
        assert!(
            equivalent,
            "symbolic result is not equivalent to the input under the assumptions\n\
             expression: {expr}\n\
             result: {result}"
        );
        Ok::<_, Skip>(())
    }
    .await;
    ev.finish().await;
    match verdict {
        Ok(()) => Verdict::Checked,
        Err(skip) => skip.into(),
    }
}

/// The concrete outcome on a store that may be open: a missing entity is an
/// ordinary error here.
fn concrete_outcome_open(
    request: &Request,
    entities: &Entities,
    expr: &Expr,
) -> Result<EvaluationOutcome, Skip> {
    match concrete_outcome(request, entities, expr) {
        Err(Skip::OutsideEnvelope(_)) => Ok(EvaluationOutcome::Error),
        other => other,
    }
}

/// Differential test of the symbolic evaluator against the concrete
/// evaluator on fully known data whose store may be *open* (the request, the
/// expression or the entity data may reference entities that are not in the
/// store): the concrete outcome must be in the symbolic outcome set (S1), and
/// the folded result, evaluated concretely, must agree with the input up to
/// the error kind (S2). Nothing is proved about this envelope; it is what the
/// evaluator's existence questions are for. Inputs the concrete target
/// checks (strongly well-formed ones) are checked here too.
pub async fn test_symbolic_vs_open(
    schema: &Schema,
    entities: &Entities,
    request: &Request,
    expr: &Expr,
) -> Verdict {
    let expected = match concrete_outcome_open(request, entities, expr) {
        Ok(o) => o,
        Err(skip) => return skip.into(),
    };
    let Some(env) = request_env_of(request, schema) else {
        return Skip::NotWellTyped("request env not in the schema".into()).into();
    };
    let Some(mut ev) = SymEval::new(schema).await else {
        return Skip::Benign("schema not compilable".into()).into();
    };
    let verdict = async {
        ev.assume_entities(entities)?;
        ev.assume_request(request)?;
        let result = ev.evaluate(expr, &env).await?;
        let symbolic = outcome_set(result.data().outcomes().iter());
        assert!(
            symbolic.contains(&expected),
            "the concrete outcome is not in the symbolic outcome set (open store)\n\
             expression: {expr}\n\
             request: {request}\n\
             entities: {}\n\
             concrete outcome: {expected:?}\n\
             symbolic result: {result}",
            entities.as_ref()
        );
        let folded = erase_metadata(&result).map_err(|e| Skip::Benign(e.to_string()))?;
        let folded_outcome = concrete_outcome_open(request, entities, &folded)?;
        assert_eq!(
            folded_outcome,
            expected,
            "the folded result does not evaluate like the input (open store)\n\
             expression: {expr}\n\
             folded: {folded}\n\
             request: {request}\n\
             entities: {}",
            entities.as_ref()
        );
        Ok::<_, Skip>(())
    }
    .await;
    ev.finish().await;
    match verdict {
        Ok(()) => Verdict::Checked,
        Err(skip) => skip.into(),
    }
}

/// Differential test of the Rust symbolic evaluator against its Lean model
/// (`Cedar.SymCC.Opt`): the Rust evaluator runs with a recorded trace, which
/// Lean replays with the recorded solver answers as its oracle — checking
/// every query's assert list, the folded result, the root outcome set, and
/// the `check_equivalent` verdict. Also asserts everything
/// [`test_symbolic_vs_concrete`] does, since the input is fully concrete.
pub async fn test_symbolic_vs_lean(
    ffi: &CedarLeanFfi,
    lean_schema: &LeanSchema,
    schema: &Schema,
    entities: &Entities,
    request: &Request,
    expr: &Expr,
) -> Verdict {
    if !is_strongly_well_formed_for(entities, request, expr) {
        return Skip::OutsideEnvelope("not strongly well-formed".into()).into();
    }
    let expected = match concrete_outcome(request, entities, expr) {
        Ok(o) => o,
        Err(skip) => return skip.into(),
    };
    let Some(env) = request_env_of(request, schema) else {
        return Skip::NotWellTyped("request env not in the schema".into()).into();
    };
    let Some(mut ev) = SymEval::new(schema).await else {
        return Skip::Benign("schema not compilable".into()).into();
    };
    ev.record_trace(true);
    let verdict = async {
        ev.assume_entities(entities)?;
        ev.assume_request(request)?;
        let result = ev.evaluate(expr, &env).await?;
        assert!(
            result.data().can(&expected),
            "symbolic evaluator disagrees with the concrete evaluator\n\
             expression: {expr}\nconcrete outcome: {expected:?}\nsymbolic result: {result}"
        );
        let equivalent = ev.check_equivalent(expr, &result, &env).await?;
        assert!(
            equivalent,
            "symbolic result is not equivalent to the input: {result}"
        );
        Ok::<_, Skip>(result)
    }
    .await;
    let trace = ev.take_trace();
    ev.finish().await;
    let result = match verdict {
        Ok(result) => result,
        Err(skip) => return skip.into(),
    };
    let trace: EvaluationTrace = trace.expect("recording was on");

    let to_lean = |ts: &[cedar_policy_symcc::term::Term]| -> Vec<cedar_lean_ffi::Term> {
        ts.iter().map(|t| t.clone().into()).collect()
    };
    let base = to_lean(&trace.base);
    let queries: Vec<(Vec<cedar_lean_ffi::Term>, bool)> = trace
        .queries
        .iter()
        .map(|q| (to_lean(&q.asserts), q.unsat))
        .collect();
    let ce_base = trace.ce_base.as_deref().map(to_lean);
    let erased_result = erase_metadata(&result).expect("erasing the result should not fail");
    let outcomes = result.data();
    let expected_outcomes = (
        outcomes.can(&EvaluationOutcome::True),
        outcomes.can(&EvaluationOutcome::False),
        outcomes.can(&EvaluationOutcome::Error),
    );
    let check = ffi
        .run_symeval_replay(
            lean_schema.clone(),
            &env,
            &trace.erased,
            &base,
            &queries,
            &erased_result,
            expected_outcomes,
            ce_base.as_deref(),
        )
        .unwrap_or_else(|e| panic!("Lean replay FFI failed: {e}"));
    assert!(
        check.agrees,
        "Lean model disagrees with the Rust symbolic evaluator\n\
         expression: {expr}\nrequest: {request}\nentities: {}\n\
         expected: {}\nactual: {}",
        entities.as_ref(),
        check.expected,
        check.actual
    );
    Verdict::Checked
}

/// Whether a residual (converted to an expression) contains an error node.
/// TPE renders `Residual::Error` as a call to an extension function named
/// `error`, which the symbolic compiler cannot compile.
fn contains_error_node(expr: &Expr) -> bool {
    expr.subexpressions().any(|e| {
        matches!(
            e.expr_kind(),
            ExprKind::ExtensionFunctionApp { fn_name, .. } if fn_name.to_string() == "error"
        )
    })
}

/// Differential test of the symbolic evaluator against TPE on partially known
/// data: for every policy TPE produces a residual for,
///
/// 1. the symbolic evaluator's outcome set for the policy condition is a
///    subset of the residual's `possible_bool_outcomes` (which is documented
///    as an over-approximation; the symbolic set is exact),
/// 2. the symbolic result is equivalent to the condition under the partial
///    data (contract (S2)), and
/// 3. the residual itself is equivalent to the condition under the partial
///    data, i.e. the two partial evaluators agree on every completion of the
///    data — checked unless the residual contains an error node, which the
///    symbolic compiler cannot express.
///
/// Linked template policies are skipped: SymCC does not compile slots.
///
/// The residual is compiled directly, never re-typechecked: like the symbolic
/// evaluator's own results, a concretised residual may have lost the `has`
/// capability an attribute access relied on.
pub async fn test_symbolic_vs_tpe(
    schema: &Schema,
    policies: &PolicySet,
    partial_request: &PartialRequest,
    partial_entities: &PartialEntities,
) -> Verdict {
    let response = match policies.tpe(partial_request, partial_entities, schema) {
        Ok(r) => r,
        Err(err) => return Skip::OutsideEnvelope(format!("TPE failed: {err}")).into(),
    };
    let env = response.request_env();
    let Some(mut ev) = SymEval::new(schema).await else {
        return Skip::Benign("schema not compilable".into()).into();
    };
    ev.assume_partial_entities(partial_entities);
    ev.assume_partial_request(partial_request);
    let verdict = async {
        let mut checked = false;
        for residual_policy in response.as_ref().policies() {
            let id = residual_policy.get_policy_id();
            let policy = policies
                .as_ref()
                .get(id)
                .unwrap_or_else(|| panic!("TPE returned a residual for unknown policy {id}"));
            if !policy.is_static() {
                // SymCC does not compile template slots (`CompileError::UnsupportedFeature`),
                // and `Policy::condition()` of a linked policy still contains them.
                debug!("skipping linked policy {id}: templates are not supported by SymCC");
                continue;
            }
            let condition = policy.condition();
            let residual: Residual = (*residual_policy.get_residual()).clone();
            let result = ev.evaluate(&condition, &env).await?;
            let symbolic = outcome_set(result.data().outcomes().iter());
            let tpe = outcome_set(residual.possible_bool_outcomes().iter());
            assert!(
                symbolic.is_subset(&tpe),
                "symbolic evaluator finds an outcome TPE rules out\n\
                 policy: {policy}\n\
                 partial request: {:?}\n\
                 partial entities: {:?}\n\
                 TPE residual: {residual:?} with outcomes {tpe:?}\n\
                 symbolic result: {result} with outcomes {symbolic:?}",
                partial_request.as_ref(),
                partial_entities.as_ref()
            );
            let equivalent = ev.check_equivalent(&condition, &result, &env).await?;
            assert!(
                equivalent,
                "symbolic result is not equivalent to the policy condition under the partial data\n\
                 policy: {policy}\n\
                 result: {result}"
            );
            let residual_expr = Expr::from(residual);
            if !contains_error_node(&residual_expr) {
                let annotated = with_default_metadata(&residual_expr)
                    .expect("annotating a residual expression should not fail");
                match ev.check_equivalent(&condition, &annotated, &env).await {
                    Ok(equivalent) => assert!(
                        equivalent,
                        "TPE residual is not equivalent to the policy condition under the partial data\n\
                         policy: {policy}\n\
                         partial request: {:?}\n\
                         partial entities: {:?}\n\
                         TPE residual: {residual_expr}\n\
                         symbolic result: {result}",
                        partial_request.as_ref(),
                        partial_entities.as_ref()
                    ),
                    // A concretised residual can contain values the compiler
                    // does not accept as expressions (e.g. an empty set).
                    Err(Skip::Benign(msg)) => debug!("residual not compilable: {msg}"),
                    Err(skip) => return Err(skip),
                }
            }
            checked = true;
        }
        Ok::<_, Skip>(checked)
    }
    .await;
    ev.finish().await;
    match verdict {
        Ok(true) => Verdict::Checked,
        Ok(false) => Skip::OutsideEnvelope("no residual policies".into()).into(),
        Err(skip) => skip.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symcc::RUNTIME;
    use crate::tpe::TpeFuzzTargetInput;
    use cedar_policy::{Context, EntityUid};
    use rand::{Rng, SeedableRng};
    use std::str::FromStr;

    /// Whether cvc5 is available; the DRT CI job builds the fuzz targets but
    /// does not install a solver.
    fn have_cvc5() -> bool {
        let path = std::env::var("CVC5").unwrap_or_else(|_| "cvc5".into());
        std::process::Command::new(path)
            .arg("--version")
            .output()
            .is_ok()
    }

    #[test]
    fn strongly_well_formed_filter() {
        let schema = Schema::from_cedarschema_str(
            r#"
            entity Group;
            entity User in [Group] { boss?: User };
            action view appliesTo { principal: User, resource: User, context: { who: User } };
            "#,
        )
        .unwrap()
        .0;
        let entities = |json: &str| Entities::from_json_str(json, Some(&schema)).unwrap();
        let store = entities(
            r#"[
              { "uid": { "type": "User", "id": "a" }, "attrs": {}, "parents": [ { "type": "Group", "id": "g" } ] },
              { "uid": { "type": "User", "id": "b" }, "attrs": { "boss": { "__entity": { "type": "User", "id": "a" } } }, "parents": [] },
              { "uid": { "type": "Group", "id": "g" }, "attrs": {}, "parents": [] },
              { "uid": { "type": "Action", "id": "view" }, "attrs": {}, "parents": [] }
            ]"#,
        );
        let request = |ctx_who: &str| {
            Request::new(
                EntityUid::from_str(r#"User::"a""#).unwrap(),
                EntityUid::from_str(r#"Action::"view""#).unwrap(),
                EntityUid::from_str(r#"User::"b""#).unwrap(),
                Context::from_json_str(
                    &format!(
                        r#"{{ "who": {{ "__entity": {{ "type": "User", "id": "{ctx_who}" }} }} }}"#
                    ),
                    None,
                )
                .unwrap(),
                None,
            )
            .unwrap()
        };
        let expr = |text: &str| {
            cedar_policy::Expression::from_str(text)
                .unwrap()
                .as_ref()
                .clone()
        };

        assert!(is_strongly_well_formed_for(
            &store,
            &request("a"),
            &expr(r#"principal in Group::"g" && User::"b" has boss"#)
        ));
        // dangling UID in the expression
        assert!(!is_strongly_well_formed_for(
            &store,
            &request("a"),
            &expr(r#"User::"nobody" has boss"#)
        ));
        // dangling UID in the context
        assert!(!is_strongly_well_formed_for(
            &store,
            &request("nobody"),
            &expr("true")
        ));
        // dangling ancestor in the store
        let dangling_parent = entities(
            r#"[
              { "uid": { "type": "User", "id": "a" }, "attrs": {}, "parents": [ { "type": "Group", "id": "nope" } ] },
              { "uid": { "type": "User", "id": "b" }, "attrs": {}, "parents": [] },
              { "uid": { "type": "Action", "id": "view" }, "attrs": {}, "parents": [] }
            ]"#,
        );
        assert!(!is_strongly_well_formed_for(
            &dangling_parent,
            &request("a"),
            &expr("true")
        ));
        // dangling entity-valued attribute in the store
        let dangling_attr = entities(
            r#"[
              { "uid": { "type": "User", "id": "a" }, "attrs": { "boss": { "__entity": { "type": "User", "id": "nope" } } }, "parents": [] },
              { "uid": { "type": "User", "id": "b" }, "attrs": {}, "parents": [] },
              { "uid": { "type": "Action", "id": "view" }, "attrs": {}, "parents": [] }
            ]"#,
        );
        assert!(!is_strongly_well_formed_for(
            &dangling_attr,
            &request("a"),
            &expr("true")
        ));
    }

    /// Runs `f` on inputs generated from a fixed seed until `wanted` of them
    /// were actually checked (not skipped), so the plumbing of both targets is
    /// exercised by `cargo test` even though CI runs no fuzz target.
    fn run_seeded<I: for<'a> Arbitrary<'a>>(
        seed: u64,
        wanted: usize,
        max_attempts: usize,
        f: impl Fn(I) -> Verdict,
    ) {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut checked = 0;
        let mut skipped: HashMap<&'static str, usize> = HashMap::new();
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = I::arbitrary(&mut Unstructured::new(&bytes)) else {
                *skipped.entry("not generated").or_default() += 1;
                continue;
            };
            match f(input) {
                Verdict::Checked => checked += 1,
                Verdict::Skipped(skip) => {
                    let key = match skip {
                        Skip::OutsideEnvelope(_) => "outside envelope",
                        Skip::NotWellTyped(_) => "not well typed",
                        Skip::Benign(_) => "benign",
                        Skip::Timeout => "timeout",
                        Skip::Unknown => "unknown",
                    };
                    *skipped.entry(key).or_default() += 1;
                }
            }
            if checked >= wanted {
                break;
            }
        }
        eprintln!("checked {checked} inputs; skipped: {skipped:?}");
        assert!(
            checked >= wanted,
            "only {checked} of {wanted} wanted inputs were checked; skipped: {skipped:?}"
        );
    }

    /// Fixed open-store cases: the shapes the missing-entity handling is
    /// for — a literal UID absent from the store, an absent principal, a
    /// required `has` on it, a nested receiver with only the outer entity
    /// present, a `getTag` on an absent entity — and closed-store controls.
    #[test]
    fn open_store_fixed_cases() {
        if !have_cvc5() {
            eprintln!("cvc5 not found; skipping");
            return;
        }
        let schema = Schema::from_cedarschema_str(
            r#"
            entity Group;
            entity User in [Group] { name: String, boss: User, nick?: String } tags Long;
            action view appliesTo { principal: User, resource: User, context: { who: User } };
            "#,
        )
        .unwrap()
        .0;
        let entities = Entities::from_json_str(
            r#"[
              { "uid": { "type": "User", "id": "a" }, "attrs": { "name": "a", "boss": { "__entity": { "type": "User", "id": "ghost" } } }, "parents": [], "tags": { "t": 1 } },
              { "uid": { "type": "User", "id": "b" }, "attrs": { "name": "b", "boss": { "__entity": { "type": "User", "id": "a" } } }, "parents": [] },
              { "uid": { "type": "Action", "id": "view" }, "attrs": {}, "parents": [] }
            ]"#,
            Some(&schema),
        )
        .unwrap();
        let request = |principal: &str| {
            Request::new(
                EntityUid::from_str(principal).unwrap(),
                EntityUid::from_str(r#"Action::"view""#).unwrap(),
                EntityUid::from_str(r#"User::"b""#).unwrap(),
                cedar_policy::Context::from_pairs([(
                    "who".to_string(),
                    cedar_policy::RestrictedExpression::new_entity_uid(
                        EntityUid::from_str(r#"User::"a""#).unwrap(),
                    ),
                )])
                .unwrap(),
                Some(&schema),
            )
            .unwrap()
        };
        let cases = [
            // an absent literal UID: errors concretely
            (r#"User::"a""#, r#"User::"nobody".name == "x""#),
            // an absent principal: `getAttr` errors, a required `has` is false
            (r#"User::"nobody""#, "principal.name == \"x\""),
            (r#"User::"nobody""#, "principal has name"),
            (r#"User::"nobody""#, "principal has nick"),
            (
                r#"User::"nobody""#,
                r#"principal.hasTag("t") && principal.getTag("t") == 1"#,
            ),
            (r#"User::"nobody""#, "principal in Group::\"g\""),
            // a nested receiver: `a` exists, its boss does not
            (r#"User::"a""#, r#"principal.boss.name == "x""#),
            (r#"User::"a""#, "principal.boss has name"),
            (
                r#"User::"a""#,
                "iferror(principal.boss.name == \"x\", false)",
            ),
            // phantom values: `iferror` coalesces only symbolically, a
            // nested required `has` is literally true in the term
            (
                r#"User::"a""#,
                "iferror(principal.boss.name == principal.boss.name, false)",
            ),
            (r#"User::"nobody""#, "(principal has name) == false"),
            (
                r#"User::"nobody""#,
                "iferror(principal has name, true) == true",
            ),
            (
                r#"User::"a""#,
                r#"(if principal.boss has name then principal.boss else principal).name == "a""#,
            ),
            // closed-store controls
            (r#"User::"b""#, r#"principal.boss.name == "a""#),
            (
                r#"User::"a""#,
                r#"principal.hasTag("t") && principal.getTag("t") == 1"#,
            ),
            (r#"User::"b""#, "principal has name && context.who has nick"),
        ];
        for (principal, text) in cases {
            let expr = cedar_policy::Expression::from_str(text)
                .unwrap()
                .as_ref()
                .clone();
            let verdict = RUNTIME.block_on(test_symbolic_vs_open(
                &schema,
                &entities,
                &request(principal),
                &expr,
            ));
            assert!(
                matches!(verdict, Verdict::Checked),
                "`{text}` with principal {principal}: {verdict:?}"
            );
        }
    }

    #[test]
    fn open_target_smoke() {
        if !have_cvc5() {
            eprintln!("cvc5 not found; skipping");
            return;
        }
        run_seeded(0x0be5_70e5, 20, 2_000, |input: ConcreteFuzzTargetInput| {
            let Ok(schema) = Schema::try_from(input.schema) else {
                return Skip::OutsideEnvelope("schema".into()).into();
            };
            let request: Request = input.request.into();
            RUNTIME.block_on(test_symbolic_vs_open(
                &schema,
                &input.entities,
                &request,
                &input.expression,
            ))
        });
    }

    #[test]
    fn concrete_target_smoke() {
        if !have_cvc5() {
            eprintln!("cvc5 not found; skipping");
            return;
        }
        run_seeded(
            0x5eed_c0ffee,
            20,
            2_000,
            |input: ConcreteFuzzTargetInput| {
                let Ok(schema) = Schema::try_from(input.schema) else {
                    return Skip::OutsideEnvelope("schema".into()).into();
                };
                let request: Request = input.request.into();
                RUNTIME.block_on(test_symbolic_vs_concrete(
                    &schema,
                    &input.entities,
                    &request,
                    &input.expression,
                ))
            },
        );
    }

    #[test]
    fn lean_replay_target_smoke() {
        if !have_cvc5() {
            eprintln!("cvc5 not found; skipping");
            return;
        }
        let ffi = CedarLeanFfi::new();
        run_seeded(0x1ea9_5eed, 10, 2_000, |input: ConcreteFuzzTargetInput| {
            let Ok(schema) = Schema::try_from(input.schema) else {
                return Skip::OutsideEnvelope("schema".into()).into();
            };
            let Ok(lean_schema) = ffi.load_lean_schema_object(&schema) else {
                return Skip::OutsideEnvelope("schema not loadable in Lean".into()).into();
            };
            let request: Request = input.request.into();
            RUNTIME.block_on(test_symbolic_vs_lean(
                &ffi,
                &lean_schema,
                &schema,
                &input.entities,
                &request,
                &input.expression,
            ))
        });
    }

    #[test]
    fn tpe_target_smoke() {
        if !have_cvc5() {
            eprintln!("cvc5 not found; skipping");
            return;
        }
        run_seeded(0x7e5e_ed, 10, 2_000, |input: TpeFuzzTargetInput| {
            let Ok(schema) = Schema::try_from(input.abac_input.schema) else {
                return Skip::OutsideEnvelope("schema".into()).into();
            };
            let policies = input.abac_input.policy.into_policy_set();
            let mut verdict = Verdict::Skipped(Skip::OutsideEnvelope("no requests".into()));
            for partial_request in &input.partial_requests {
                verdict = RUNTIME.block_on(test_symbolic_vs_tpe(
                    &schema,
                    &policies,
                    partial_request,
                    &input.partial_entities,
                ));
                if matches!(verdict, Verdict::Checked) {
                    break;
                }
            }
            verdict
        });
    }
}
