/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module

public import Cedar.DNF.Elim
public import Cedar.Spec

/-!
This file models the policy splitter implemented in Rust in
`cedar-policy-symcc/src/dnf/policy.rs` (the `cedar-spec/cedar/` checkout,
branch `split-conjunct-policies`, Phase 3 Step 3). A policy's `when`
condition is piped through `split_atoms` and `Dnf::of(·, |_| false, ·)`, and
every cube that can be true becomes its own policy with the same effect and
scope and the cube as its condition.

The definitions mirror the Rust pipeline. Differences by design, as for the
Step 1/2 models: no cube/node budget; `Spec.Policy` carries structured
scopes (`principalScope`/`actionScope`/`resourceScope`) where Rust's core
`Policy` carries constraint objects — the split copies them verbatim either
way.

The decision and satisfaction theorems are in `Cedar.Thm.DNF`.
-/

namespace Cedar.DNF

open Cedar.Spec

@[expose] public section

/-- The condition expressions of the split policies: the normalization
pipeline (`normalize`: split the atoms, eliminate record and set literals,
split again) then the DNF with `can_error ≡ false` (so every never-true cube
is pruned), each remaining (true) cube rendered as an expression. Mirrors
the Rust `normalize_atoms → Dnf::of(·, |_| false, ·) → true_cubes().map(to_expr)`
(the Rust side validates the policy first; the theorems carry typing as a
hypothesis). -/
def splitCondExprs (c : Expr) : List Expr :=
  (prune (paths (normalize c)) (fun _ => false)).map Cube.toExpr

/-- Splits a policy into one policy per condition cube: same effect and
scopes, id `{id}.cube{i}`, the cube as the sole `when` condition (Rust
`split_policy`). -/
def splitPolicy (p : Policy) : List Policy :=
  (splitCondExprs (Conditions.toExpr p.condition)).mapIdx fun i cond =>
    { p with
      id := s!"{p.id}.cube{i}",
      condition := [⟨.when, cond⟩] }

/-- `splitPolicy` applied to every policy of the set (Rust
`split_policy_set`). -/
def splitPolicySet (ps : Policies) : Policies :=
  ps.flatMap splitPolicy

end

end Cedar.DNF
