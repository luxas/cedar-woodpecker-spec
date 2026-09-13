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

//! The `cedar-sql` differential tests: `cedar-sql`'s authorizer (entities
//! loaded into Postgres, policies partially evaluated and compiled to one
//! query) against `cedar-policy`'s authorizer.
//!
//! Inputs are the type-directed ABAC inputs without extension types (which
//! `cedar-sql` does not store yet). Policies that do not validate strictly
//! and requests that do not validate are outside the envelope (the compiler
//! relies on typing); constructs the compiler does not handle yet are
//! benign skips, so the target lands before every operator is compiled and
//! the skip counts show what is left.

use std::collections::{BTreeMap, BTreeSet};

use cedar_drt::sql_impl::SqlTestImpl;
use cedar_drt::tests::drop_some_entities;
use cedar_policy::{
    Authorizer, Decision, Entities, EntityUid, PolicyId, PolicySet, PrincipalQueryRequest, Request,
    ResourceQueryRequest, Schema, ValidationMode, Validator,
};
use cedar_policy_generators::abac::{ABACPolicy, ABACRequest};
use cedar_policy_generators::hierarchy::HierarchyGenerator;
use cedar_policy_generators::schema;
use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::settings::ABACSettings;
use cedar_sql::Error as SqlError;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Error, MaxRecursionReached, Unstructured};

use crate::schemas;
pub use crate::symeval::{Skip, Verdict};

/// The generator settings: type-directed, small, and no extension types
/// (not stored yet).
pub const SETTINGS: ABACSettings = ABACSettings {
    max_depth: 3,
    max_width: 3,
    enable_extensions: false,
    ..ABACSettings::type_directed()
};

/// An ABAC schema, entities, policy and eight requests, generated with
/// [`SETTINGS`] (the shape of `abac::FuzzTargetInput`).
#[derive(Debug, Clone)]
pub struct SqlFuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated entities, some dropped so that references dangle
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try
    pub requests: [ABACRequest; 8],
    /// whether `in` uses the closed hierarchy table or the recursive CTE
    pub hierarchy_closed: bool,
}

impl<'a> Arbitrary<'a> for SqlFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS, u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let cedar_schema = Schema::try_from(schema.clone()).map_err(|_| Error::IncorrectFormat)?;
        let entities = drop_some_entities(all_entities, u)?;
        let entities = schemas::add_actions_to_entities(&cedar_schema, entities)?;
        let hierarchy_closed = u.arbitrary()?;
        Ok(Self {
            schema,
            entities,
            policy,
            requests,
            hierarchy_closed,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

/// The `sql-is-authorized-drt` check on one generated input.
pub fn check_is_authorized(input: &SqlFuzzTargetInput) -> Verdict {
    let Ok(schema) = Schema::try_from(input.schema.clone()) else {
        return Skip::OutsideEnvelope("the schema does not convert".into()).into();
    };
    // Partial evaluation takes static policies: a generated template is linked.
    let mut policies = PolicySet::new();
    policies
        .add(input.policy.clone().link_to_static())
        .expect("a fresh policy set accepts one policy");
    let requests: Vec<Request> = input.requests.iter().cloned().map(Into::into).collect();
    compare(
        &schema,
        &policies,
        &input.entities,
        &requests,
        input.hierarchy_closed,
    )
}

/// `cedar-policy`'s answer for one concrete request: decision, determining
/// policies, erroring policies.
fn expected(
    authorizer: &Authorizer,
    request: &Request,
    policies: &PolicySet,
    entities: &Entities,
) -> (Decision, BTreeSet<PolicyId>, BTreeSet<PolicyId>) {
    let response = authorizer.is_authorized(request, policies, entities);
    (
        response.decision(),
        response.diagnostics().reason().cloned().collect(),
        response
            .diagnostics()
            .errors()
            .map(|e| match e {
                cedar_policy::AuthorizationError::PolicyEvaluationError(e) => e.policy_id().clone(),
            })
            .collect(),
    )
}

/// What to do with a `cedar-sql` error on one request: skip the request
/// (`Ok(Some(skip))`), skip the input (`Err`), or panic on a real failure.
fn classify(
    error: SqlError,
    request: &Request,
    policies: &PolicySet,
    entities: &Entities,
) -> Result<Skip, Skip> {
    match error {
        SqlError::Unsupported(what) => Ok(Skip::Benign(what.to_owned())),
        // Postgres `text` cannot hold NUL: a documented limitation, skipped.
        SqlError::Load(message) if message.contains("NUL") => Ok(Skip::Benign(message)),
        e if e.is_timeout() => Err(Skip::Timeout),
        e => panic!(
            "cedar-sql failed for {request}\nPolicies:\n{policies}\nEntities:\n{}\nError: {e}",
            entities.as_ref()
        ),
    }
}

/// The verdict of a batch of per-request outcomes: checked if any request
/// was, else the first skip.
fn verdict(checked: usize, skips: Vec<Skip>) -> Verdict {
    if checked > 0 {
        return Verdict::Checked;
    }
    let benign = skips.iter().position(|s| matches!(s, Skip::Benign(_)));
    let mut skips = skips;
    match benign {
        Some(i) => skips.swap_remove(i).into(),
        None => skips
            .into_iter()
            .next()
            .unwrap_or_else(|| Skip::OutsideEnvelope("no request".to_owned()))
            .into(),
    }
}

/// The schema and the test implementation for an input, or why it is skipped.
fn setup(
    schema: &Schema,
    policies: &PolicySet,
    hierarchy_closed: bool,
) -> Result<SqlTestImpl, Skip> {
    let validator = Validator::new(schema.clone());
    if !validator
        .validate(policies, ValidationMode::Strict)
        .validation_passed()
    {
        return Err(Skip::NotWellTyped(
            "the policies do not validate strictly".into(),
        ));
    }
    match SqlTestImpl::new(schema.clone(), hierarchy_closed) {
        Ok(sql) => Ok(sql),
        Err(SqlError::Unsupported(what)) => Err(Skip::Benign(what.into())),
        Err(SqlError::Schema(message)) => Err(Skip::Benign(message)),
        Err(e) => panic!("cannot set up the database: {e}"),
    }
}

/// Authorizes every valid request of `requests` through `cedar-sql` and
/// through `cedar-policy`, and panics on any disagreement in the decision,
/// the determining policies or the erroring policies.
pub fn compare(
    schema: &Schema,
    policies: &PolicySet,
    entities: &Entities,
    requests: &[Request],
    hierarchy_closed: bool,
) -> Verdict {
    let sql = match setup(schema, policies, hierarchy_closed) {
        Ok(sql) => sql,
        Err(skip) => return skip.into(),
    };
    let validator = Validator::new(schema.clone());
    let authorizer = Authorizer::new();
    let mut checked = 0;
    let mut skips = Vec::new();
    for request in requests {
        if !crate::tpe::passes_request_validation(&validator, request) {
            skips.push(Skip::OutsideEnvelope(
                "the request does not validate".into(),
            ));
            continue;
        }
        let actual = match sql.authorize(request, policies, entities) {
            Ok(response) => response,
            Err(e) => match classify(e, request, policies, entities) {
                Ok(skip) => {
                    skips.push(skip);
                    continue;
                }
                Err(skip) => return skip.into(),
            },
        };
        let (decision, reason, errors) = expected(&authorizer, request, policies, entities);
        assert_eq!(
            (actual.decision, &actual.reason, &actual.errors),
            (decision, &reason, &errors),
            "cedar-sql disagrees with cedar-policy for {request}\nPolicies:\n{policies}\nEntities:\n{}",
            entities.as_ref()
        );
        checked += 1;
    }
    verdict(checked, skips)
}

/// Which request variables a partial request leaves unknown.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unknowns {
    /// The principal.
    Principal,
    /// The resource.
    Resource,
    /// Both.
    Both,
}

impl Unknowns {
    fn flags(self) -> (bool, bool) {
        match self {
            Unknowns::Principal => (true, false),
            Unknowns::Resource => (false, true),
            Unknowns::Both => (true, true),
        }
    }
}

/// The input of `sql-query-drt`: the ABAC input, with which variables each
/// request leaves unknown.
#[derive(Debug, Clone)]
pub struct SqlQueryFuzzTargetInput {
    /// The schema, entities, policy and requests.
    pub base: SqlFuzzTargetInput,
    /// Per request, the unknown variables.
    pub unknowns: [Unknowns; 8],
}

impl<'a> Arbitrary<'a> for SqlQueryFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let base = SqlFuzzTargetInput::arbitrary(u)?;
        let mut unknowns = [Unknowns::Resource; 8];
        for unknown in &mut unknowns {
            *unknown = *u.choose(&[Unknowns::Principal, Unknowns::Resource, Unknowns::Both])?;
        }
        Ok(Self { base, unknowns })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and(
            SqlFuzzTargetInput::try_size_hint(depth)?,
            (8, Some(8)),
        ))
    }
}

/// The `sql-query-drt` check on one generated input.
pub fn check_query(input: &SqlQueryFuzzTargetInput) -> Verdict {
    let Ok(schema) = Schema::try_from(input.base.schema.clone()) else {
        return Skip::OutsideEnvelope("the schema does not convert".into()).into();
    };
    let mut policies = PolicySet::new();
    policies
        .add(input.base.policy.clone().link_to_static())
        .expect("a fresh policy set accepts one policy");
    let requests: Vec<(Request, Unknowns)> = input
        .base
        .requests
        .iter()
        .cloned()
        .map(Into::into)
        .zip(input.unknowns)
        .collect();
    compare_query(
        &schema,
        &policies,
        &input.base.entities,
        &requests,
        input.base.hierarchy_closed,
    )
}

/// Runs every valid partial request through `cedar-sql` and checks each
/// returned row against `cedar-policy`'s authorizer on the concrete
/// candidate, that the rows are exactly the candidates (the entities of the
/// unknown types), and that the allowed set agrees with
/// `PolicySet::query_resource`/`query_principal` when one variable is unknown.
pub fn compare_query(
    schema: &Schema,
    policies: &PolicySet,
    entities: &Entities,
    requests: &[(Request, Unknowns)],
    hierarchy_closed: bool,
) -> Verdict {
    let sql = match setup(schema, policies, hierarchy_closed) {
        Ok(sql) => sql,
        Err(skip) => return skip.into(),
    };
    let validator = Validator::new(schema.clone());
    let authorizer = Authorizer::new();
    let mut checked = 0;
    let mut skips = Vec::new();
    for (request, unknowns) in requests {
        if !crate::tpe::passes_request_validation(&validator, request) {
            skips.push(Skip::OutsideEnvelope(
                "the request does not validate".into(),
            ));
            continue;
        }
        let (unknown_principal, unknown_resource) = unknowns.flags();
        let rows = match sql.query(
            request,
            unknown_principal,
            unknown_resource,
            policies,
            entities,
        ) {
            Ok(rows) => rows,
            Err(e) => match classify(e, request, policies, entities) {
                Ok(skip) => {
                    skips.push(skip);
                    continue;
                }
                Err(skip) => return skip.into(),
            },
        };
        let principal = request.principal().expect("concrete");
        let resource = request.resource().expect("concrete");
        let action = request.action().expect("concrete");
        let context = request.context().expect("concrete");
        let candidates = |unknown: bool, uid: &EntityUid| -> Vec<EntityUid> {
            if unknown {
                entities
                    .iter()
                    .map(|e| e.uid())
                    .filter(|u| u.type_name() == uid.type_name())
                    .collect()
            } else {
                vec![uid.clone()]
            }
        };
        let mut expected_rows = BTreeMap::new();
        for p in candidates(unknown_principal, principal) {
            for r in candidates(unknown_resource, resource) {
                let concrete =
                    Request::new(p.clone(), action.clone(), r.clone(), context.clone(), None)
                        .expect("a request without validation");
                expected_rows.insert(
                    (p.to_string(), r.to_string()),
                    expected(&authorizer, &concrete, policies, entities),
                );
            }
        }
        let actual_rows: BTreeMap<
            (String, String),
            (Decision, BTreeSet<PolicyId>, BTreeSet<PolicyId>),
        > = rows
            .iter()
            .map(|row| {
                let p = row.principal.clone().unwrap_or_else(|| principal.clone());
                let r = row.resource.clone().unwrap_or_else(|| resource.clone());
                (
                    (p.to_string(), r.to_string()),
                    (
                        row.response.decision,
                        row.response.reason.clone(),
                        row.response.errors.clone(),
                    ),
                )
            })
            .collect();
        assert_eq!(
            actual_rows.len(),
            rows.len(),
            "duplicate rows for {request} with {unknowns:?}\nPolicies:\n{policies}"
        );
        assert_eq!(
            actual_rows,
            expected_rows,
            "cedar-sql disagrees with cedar-policy for {request} with {unknowns:?}\nPolicies:\n{policies}\nEntities:\n{}",
            entities.as_ref()
        );
        // The allowed set against the permission queries.
        let allowed: BTreeSet<String> = actual_rows
            .iter()
            .filter(|(_, (decision, _, _))| *decision == Decision::Allow)
            .map(|((p, r), _)| {
                if unknown_principal {
                    p.clone()
                } else {
                    r.clone()
                }
            })
            .collect();
        let query_allowed: Option<BTreeSet<String>> = match unknowns {
            Unknowns::Resource => ResourceQueryRequest::new(
                principal.clone(),
                action.clone(),
                resource.type_name().clone(),
                context.clone(),
                validator.schema(),
            )
            .ok()
            .and_then(|q| {
                policies
                    .query_resource(&q, entities, validator.schema())
                    .ok()
            })
            .map(|uids| uids.map(|u| u.to_string()).collect()),
            Unknowns::Principal => PrincipalQueryRequest::new(
                principal.type_name().clone(),
                action.clone(),
                resource.clone(),
                context.clone(),
                validator.schema(),
            )
            .ok()
            .and_then(|q| {
                policies
                    .query_principal(&q, entities, validator.schema())
                    .ok()
            })
            .map(|uids| uids.map(|u| u.to_string()).collect()),
            Unknowns::Both => None,
        };
        if let Some(query_allowed) = query_allowed {
            assert_eq!(
                allowed, query_allowed,
                "cedar-sql's allowed set disagrees with the permission query for {request} with {unknowns:?}\nPolicies:\n{policies}"
            );
        }
        checked += 1;
    }
    verdict(checked, skips)
}

/// The skip reasons of a batch of verdicts (kind and message), for smoke tests.
pub fn tally(verdicts: impl IntoIterator<Item = Verdict>) -> (usize, BTreeMap<String, usize>) {
    let mut checked = 0;
    let mut skipped: BTreeMap<String, usize> = BTreeMap::new();
    for verdict in verdicts {
        match verdict {
            Verdict::Checked => checked += 1,
            Verdict::Skipped(skip) => {
                let key = match skip {
                    Skip::OutsideEnvelope(m) => format!("outside envelope: {m}"),
                    Skip::NotWellTyped(m) => format!("not well typed: {m}"),
                    Skip::Benign(m) => format!("benign: {m}"),
                    Skip::Timeout => "timeout".to_owned(),
                    Skip::Unknown => "unknown".to_owned(),
                };
                *skipped.entry(key).or_default() += 1;
            }
        }
    }
    (checked, skipped)
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use cedar_policy::{Context, EntityUid};
    use rand::{Rng, SeedableRng};

    use super::*;

    const SCHEMA: &str = r#"
        entity User = { firstName: String, groups: Set<String> };
        entity Folder = { confidential: Bool };
        entity Document in [Folder] = { parent: Folder };
        action "get" appliesTo { principal: [User], resource: [Document] };
    "#;

    const ENTITIES: &str = r#"[
        {"uid": {"type": "User", "id": "luxas"}, "attrs": {"firstName": "Lucas", "groups": ["a"]}, "parents": []},
        {"uid": {"type": "User", "id": "other"}, "attrs": {"firstName": "Other", "groups": []}, "parents": []},
        {"uid": {"type": "Folder", "id": "foo"}, "attrs": {"confidential": false}, "parents": []},
        {"uid": {"type": "Folder", "id": "secret"}, "attrs": {"confidential": true}, "parents": []},
        {"uid": {"type": "Document", "id": "d1"}, "attrs": {"parent": {"__entity": {"type": "Folder", "id": "foo"}}}, "parents": [{"type": "Folder", "id": "foo"}]},
        {"uid": {"type": "Document", "id": "d2"}, "attrs": {"parent": {"__entity": {"type": "Folder", "id": "secret"}}}, "parents": [{"type": "Folder", "id": "secret"}]},
        {"uid": {"type": "Document", "id": "d3"}, "attrs": {"parent": {"__entity": {"type": "Folder", "id": "gone"}}}, "parents": []}
    ]"#;

    fn request(principal: &str, resource: &str) -> Request {
        Request::new(
            EntityUid::from_str(principal).unwrap(),
            EntityUid::from_str("Action::\"get\"").unwrap(),
            EntityUid::from_str(resource).unwrap(),
            Context::empty(),
            None,
        )
        .unwrap()
    }

    /// The README's example, over existing, confidential, dangling and
    /// missing entities: every request is checked.
    #[test]
    fn readme_example() {
        let schema = Schema::from_cedarschema_str(SCHEMA).unwrap().0;
        let entities = Entities::from_json_str(ENTITIES, Some(&schema)).unwrap();
        let policies = PolicySet::from_str(
            r#"permit(principal is User, action == Action::"get", resource is Document in Folder::"foo")
               when { principal.firstName == "Lucas" && !resource.parent.confidential };
               forbid(principal, action, resource) when { resource.parent.confidential };"#,
        )
        .unwrap();
        let requests = [
            request("User::\"luxas\"", "Document::\"d1\""),
            request("User::\"luxas\"", "Document::\"d2\""),
            request("User::\"luxas\"", "Document::\"d3\""),
            request("User::\"other\"", "Document::\"d1\""),
            request("User::\"nobody\"", "Document::\"d1\""),
            request("User::\"luxas\"", "Document::\"nope\""),
        ];
        for closed in [true, false] {
            assert!(matches!(
                compare(&schema, &policies, &entities, &requests, closed),
                Verdict::Checked
            ));
        }
    }

    /// A construct `cedar-sql` does not support (an extension type) is a
    /// benign skip, not a failure.
    #[test]
    fn unsupported_is_benign() {
        let schema = Schema::from_cedarschema_str(
            r#"entity User = { ip: ipaddr }; action "get" appliesTo { principal: [User], resource: [User] };"#,
        )
        .unwrap()
        .0;
        let entities = Entities::from_json_str("[]", Some(&schema)).unwrap();
        let policies = PolicySet::from_str(
            r#"permit(principal, action, resource) when { principal.ip.isLoopback() };"#,
        )
        .unwrap();
        let requests = [request("User::\"luxas\"", "User::\"luxas\"")];
        match compare(&schema, &policies, &entities, &requests, true) {
            Verdict::Skipped(Skip::Benign(what)) => assert_eq!(what, "extension types"),
            other => panic!("expected a benign skip, got {other:?}"),
        }
    }

    /// The README's example with the resource unknown, and both unknown.
    #[test]
    fn readme_query() {
        let schema = Schema::from_cedarschema_str(SCHEMA).unwrap().0;
        let entities = Entities::from_json_str(ENTITIES, Some(&schema)).unwrap();
        let policies = PolicySet::from_str(
            r#"permit(principal is User, action == Action::"get", resource is Document in Folder::"foo")
               when { principal.firstName == "Lucas" && !resource.parent.confidential };
               forbid(principal, action, resource) when { resource.parent.confidential };"#,
        )
        .unwrap();
        let requests = [
            (
                request("User::\"luxas\"", "Document::\"d1\""),
                Unknowns::Resource,
            ),
            (
                request("User::\"other\"", "Document::\"d1\""),
                Unknowns::Principal,
            ),
            (
                request("User::\"nobody\"", "Document::\"nope\""),
                Unknowns::Both,
            ),
        ];
        for closed in [true, false] {
            assert!(matches!(
                compare_query(&schema, &policies, &entities, &requests, closed),
                Verdict::Checked
            ));
        }
    }

    /// Generated partial requests through the whole query target.
    #[test]
    fn query_target_smoke() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x5091_a0f1);
        let (wanted, max_attempts) = (25, 4_000);
        let mut verdicts = Vec::new();
        let mut not_generated = 0;
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = SqlQueryFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes))
            else {
                not_generated += 1;
                continue;
            };
            verdicts.push(check_query(&input));
            if verdicts
                .iter()
                .filter(|v| matches!(v, Verdict::Checked))
                .count()
                >= wanted
            {
                break;
            }
        }
        let (checked, skipped) = tally(verdicts);
        eprintln!("checked {checked} inputs; skipped: {skipped:?}; not generated: {not_generated}");
        assert!(
            checked >= wanted,
            "only {checked} of {wanted}; skipped: {skipped:?}"
        );
        assert!(
            !skipped
                .keys()
                .any(|k| k.starts_with("benign") && !k.contains("NUL")),
            "benign skips remain: {skipped:?}"
        );
    }

    /// Generated inputs through the whole target, with the skip counts printed.
    #[test]
    fn target_smoke() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x5091_a0f0);
        let (wanted, max_attempts) = (25, 4_000);
        let mut verdicts = Vec::new();
        let mut not_generated = 0;
        for _ in 0..max_attempts {
            let mut bytes = vec![0u8; 1 << 14];
            rng.fill_bytes(&mut bytes);
            let Ok(input) = SqlFuzzTargetInput::arbitrary(&mut Unstructured::new(&bytes)) else {
                not_generated += 1;
                continue;
            };
            verdicts.push(check_is_authorized(&input));
            let checked = verdicts
                .iter()
                .filter(|v| matches!(v, Verdict::Checked))
                .count();
            if checked >= wanted {
                break;
            }
        }
        let (checked, skipped) = tally(verdicts);
        eprintln!("checked {checked} inputs; skipped: {skipped:?}; not generated: {not_generated}");
        assert!(
            checked >= wanted,
            "only {checked} of {wanted} wanted inputs were checked; skipped: {skipped:?}"
        );
        // Every construct the generators produce without extensions compiles;
        // only strings with NUL characters (which Postgres cannot store) are skipped.
        assert!(
            !skipped
                .keys()
                .any(|k| k.starts_with("benign") && !k.contains("NUL")),
            "benign skips remain: {skipped:?}"
        );
    }
}
