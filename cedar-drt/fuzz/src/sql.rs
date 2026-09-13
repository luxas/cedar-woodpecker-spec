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

use std::collections::{BTreeSet, HashMap};

use cedar_drt::sql_impl::SqlTestImpl;
use cedar_drt::tests::drop_some_entities;
use cedar_policy::{
    Authorizer, Entities, PolicyId, PolicySet, Request, Schema, ValidationMode, Validator,
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

/// The generator settings: type-directed, small, no extension types (not
/// stored yet) and no `like` (compiled since Plan 3, exercised from Plan 4).
pub const SETTINGS: ABACSettings = ABACSettings {
    max_depth: 3,
    max_width: 3,
    enable_extensions: false,
    enable_like: false,
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
        Ok(Self {
            schema,
            entities,
            policy,
            requests,
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
    compare(&schema, &policies, &input.entities, &requests)
}

/// Authorizes every valid request of `requests` through `cedar-sql` and
/// through `cedar-policy`, and panics on any disagreement in the decision,
/// the determining policies or the erroring policies.
pub fn compare(
    schema: &Schema,
    policies: &PolicySet,
    entities: &Entities,
    requests: &[Request],
) -> Verdict {
    let validator = Validator::new(schema.clone());
    if !validator
        .validate(policies, ValidationMode::Strict)
        .validation_passed()
    {
        return Skip::NotWellTyped("the policies do not validate strictly".into()).into();
    }
    let sql = match SqlTestImpl::new(schema.clone()) {
        Ok(sql) => sql,
        Err(SqlError::Unsupported(what)) => return Skip::Benign(what.into()).into(),
        Err(SqlError::Schema(message)) => return Skip::Benign(message).into(),
        Err(e) => panic!("cannot set up the database: {e}"),
    };
    let authorizer = Authorizer::new();
    let mut checked = 0;
    let mut benign = None;
    let mut outside = None;
    for request in requests {
        if !crate::tpe::passes_request_validation(&validator, request) {
            outside.get_or_insert_with(|| "no request validates".to_owned());
            continue;
        }
        let actual = match sql.authorize(request, policies, entities) {
            Ok(response) => response,
            Err(SqlError::Unsupported(what)) => {
                benign = Some(what.to_owned());
                continue;
            }
            Err(SqlError::Load(message)) => {
                benign = Some(message);
                continue;
            }
            Err(e) if e.is_timeout() => return Skip::Timeout.into(),
            Err(SqlError::Request(message) | SqlError::Tpe(message)) => {
                outside = Some(message);
                continue;
            }
            Err(e) => panic!(
                "cedar-sql failed for {request}\nPolicies:\n{policies}\nEntities:\n{}\nError: {e}",
                entities.as_ref()
            ),
        };
        let expected = authorizer.is_authorized(request, policies, entities);
        let reason: BTreeSet<PolicyId> = expected.diagnostics().reason().cloned().collect();
        let errors: BTreeSet<PolicyId> = expected
            .diagnostics()
            .errors()
            .map(|e| match e {
                cedar_policy::AuthorizationError::PolicyEvaluationError(e) => e.policy_id().clone(),
            })
            .collect();
        assert_eq!(
            (actual.decision, &actual.reason, &actual.errors),
            (expected.decision(), &reason, &errors),
            "cedar-sql disagrees with cedar-policy for {request}\nPolicies:\n{policies}\nEntities:\n{}",
            entities.as_ref()
        );
        checked += 1;
    }
    if checked > 0 {
        Verdict::Checked
    } else if let Some(what) = benign {
        Skip::Benign(what).into()
    } else {
        Skip::OutsideEnvelope(outside.unwrap_or_else(|| "no request".to_owned())).into()
    }
}

/// The skip kinds of a batch of verdicts, for smoke tests.
pub fn tally(verdicts: impl IntoIterator<Item = Verdict>) -> (usize, HashMap<&'static str, usize>) {
    let mut checked = 0;
    let mut skipped: HashMap<&'static str, usize> = HashMap::new();
    for verdict in verdicts {
        match verdict {
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
        assert!(matches!(
            compare(&schema, &policies, &entities, &requests),
            Verdict::Checked
        ));
    }

    /// A set operation is not compiled yet: a benign skip, not a failure.
    #[test]
    fn unsupported_is_benign() {
        let schema = Schema::from_cedarschema_str(SCHEMA).unwrap().0;
        let entities = Entities::from_json_str(ENTITIES, Some(&schema)).unwrap();
        let policies = PolicySet::from_str(
            r#"permit(principal, action, resource) when { principal.groups.contains("a") };"#,
        )
        .unwrap();
        let requests = [request("User::\"luxas\"", "Document::\"d1\"")];
        match compare(&schema, &policies, &entities, &requests) {
            Verdict::Skipped(Skip::Benign(what)) => assert_eq!(what, "set operations"),
            other => panic!("expected a benign skip, got {other:?}"),
        }
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
    }
}
