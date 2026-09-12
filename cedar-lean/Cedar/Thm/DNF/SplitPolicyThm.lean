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

import Cedar.Thm.DNF.SplitCond
import Cedar.Thm.Data

/-!
The policy- and set-level Step 3 theorems: a policy is satisfied exactly when
one of its split policies is (`policy_satisfied_iff`), and the authorization
decision of a policy set is unchanged by replacing every policy with its
split (`splitPolicySet_decision`). The decision depends only on which policies
are satisfied — the `determiningPolicies` and `erroringPolicies` diagnostics
are *not* preserved (ids differ; erroring cubes differ), matching the Rust
README's documented decision-only envelope.
-/

namespace Cedar.DNF

open Cedar.Spec
open Cedar.Data

/-- `.and`'s satisfaction: `a && b` is `.ok true` iff both are — the primitive
that threads a policy's scope conjunctions. -/
theorem evaluate_and_ok_true {a b : Expr} {req : Request} {es : Entities} :
  evaluate (.and a b) req es = .ok true ↔
    evaluate a req es = .ok true ∧ evaluate b req es = .ok true := by
  cases ha : evaluate a req es with
  | error e => simp [evaluate, ha, Result.as]
  | ok v =>
    match v with
    | .prim (.bool true) =>
      cases hb : evaluate b req es with
      | error e => simp [evaluate, ha, hb, Result.as, Coe.coe, Value.asBool]
      | ok w =>
        match w with
        | .prim (.bool wb) =>
          cases wb <;> simp [evaluate, ha, hb, Result.as, Coe.coe, Value.asBool]
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, ha, hb, Result.as, Coe.coe, Value.asBool]
    | .prim (.bool false) =>
      simp [evaluate, ha, Result.as, Coe.coe, Value.asBool]
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, ha, Result.as, Coe.coe, Value.asBool]

/-- A policy is satisfied iff its scopes all hold and its condition does. -/
theorem satisfied_iff_scopes_cond (p : Policy) (req : Request) (es : Entities) :
  satisfied p req es ↔
    evaluate p.principalScope.toExpr req es = .ok true ∧
    evaluate p.actionScope.toExpr req es = .ok true ∧
    evaluate p.resourceScope.toExpr req es = .ok true ∧
    evaluate (Conditions.toExpr p.condition) req es = .ok true := by
  simp only [satisfied, decide_eq_true_eq, Policy.toExpr, evaluate_and_ok_true]

/-- Every split policy carries `p`'s effect and scopes and a cube condition. -/
theorem splitPolicy_spec {p q : Policy} (h : q ∈ splitPolicy p) :
  q.effect = p.effect ∧
  q.principalScope = p.principalScope ∧
  q.actionScope = p.actionScope ∧
  q.resourceScope = p.resourceScope ∧
  Conditions.toExpr q.condition ∈ splitCondExprs (Conditions.toExpr p.condition) := by
  simp only [splitPolicy, List.mem_mapIdx] at h
  obtain ⟨i, hi, heq⟩ := h
  subst heq
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  have hred : Conditions.toExpr
      [(⟨.when, (splitCondExprs (Conditions.toExpr p.condition))[i]⟩ : Condition)] =
      (splitCondExprs (Conditions.toExpr p.condition))[i] := rfl
  rw [hred]
  exact List.getElem_mem hi

/-- Conversely, every cube condition is realized by a split policy. -/
theorem splitPolicy_complete {p : Policy}
  {cond : Expr} (h : cond ∈ splitCondExprs (Conditions.toExpr p.condition)) :
  ∃ q ∈ splitPolicy p,
    q.effect = p.effect ∧
    q.principalScope = p.principalScope ∧
    q.actionScope = p.actionScope ∧
    q.resourceScope = p.resourceScope ∧
    Conditions.toExpr q.condition = cond := by
  obtain ⟨i, hi, hcond⟩ := List.mem_iff_getElem.mp h
  refine ⟨_, List.mem_mapIdx.mpr ⟨i, hi, rfl⟩, rfl, rfl, rfl, rfl, ?_⟩
  show (splitCondExprs (Conditions.toExpr p.condition))[i] = cond
  exact hcond

/-- The elimination's typing hypothesis, for a policy: its split condition
is `Typed`. -/
def TypedPolicy (p : Policy) (req : Request) (es : Entities) : Prop :=
  Typed req es (splitAtoms (Conditions.toExpr p.condition))

/-- **Policy satisfaction**: a policy is satisfied exactly when one of its
split policies is, on every input on which the policy is `TypedPolicy` (a
validated policy without ill-typed dead code is; see `Cedar.Thm.DNF.ElimSound`). -/
theorem policy_satisfied_iff (p : Policy) (req : Request) (es : Entities)
  (hty : TypedPolicy p req es) :
  satisfied p req es ↔ ∃ q ∈ splitPolicy p, satisfied q req es := by
  rw [satisfied_iff_scopes_cond]
  constructor
  · rintro ⟨hpr, hac, hre, hcond⟩
    obtain ⟨cond, hmem, hok⟩ := (cond_satisfied_iff _ req es hty).mp hcond
    obtain ⟨q, hq, he, hp, ha, hr, hqc⟩ := splitPolicy_complete hmem
    refine ⟨q, hq, (satisfied_iff_scopes_cond q req es).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hp]; exact hpr
    · rw [ha]; exact hac
    · rw [hr]; exact hre
    · rw [hqc]; exact hok
  · rintro ⟨q, hq, hsat⟩
    obtain ⟨he, hp, ha, hr, hcmem⟩ := splitPolicy_spec hq
    obtain ⟨hqpr, hqac, hqre, hqcond⟩ := (satisfied_iff_scopes_cond q req es).mp hsat
    refine ⟨?_, ?_, ?_, (cond_satisfied_iff _ req es hty).mpr ⟨_, hcmem, hqcond⟩⟩
    · rw [← hp]; exact hqpr
    · rw [← ha]; exact hqac
    · rw [← hr]; exact hqre

/-- **Policy-satisfaction uniqueness**: at most one split policy is ever
satisfied (from `cond_satisfied_unique`; the split policies share the scopes,
so two satisfied ones would have two satisfied cube conditions). -/
theorem policy_satisfied_unique (p : Policy) (req : Request) (es : Entities) :
  (splitPolicy p).Pairwise fun q₁ q₂ => ¬(satisfied q₁ req es ∧ satisfied q₂ req es) := by
  have hu := cond_satisfied_unique (Conditions.toExpr p.condition) req es
  rw [List.pairwise_iff_getElem] at hu ⊢
  intro i j hi hj hij
  simp only [splitPolicy, List.length_mapIdx] at hi hj
  simp only [splitPolicy, List.getElem_mapIdx]
  intro ⟨h₁, h₂⟩
  exact hu i j hi hj hij
    ⟨((satisfied_iff_scopes_cond _ req es).mp h₁).2.2.2,
     ((satisfied_iff_scopes_cond _ req es).mp h₂).2.2.2⟩

/-! ### The decision theorem -/

/-- `satisfiedPolicies` of the split set is empty exactly when the original's
is, for each effect: the decision depends only on whether *something* with
that effect is satisfied, which `policy_satisfied_iff` preserves. -/
theorem satisfiedPolicies_split_isEmpty (eff : Effect) (ps : Policies)
  (req : Request) (es : Entities) (hty : ∀ p ∈ ps, TypedPolicy p req es) :
  (satisfiedPolicies eff (splitPolicySet ps) req es).isEmpty =
  (satisfiedPolicies eff ps req es).isEmpty := by
  simp only [satisfiedPolicies]
  rw [Bool.eq_iff_iff, Set.isEmpty_make, Set.isEmpty_make,
      List.filterMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  constructor
  · intro h p hp
    -- `p` satisfied with effect `eff`; then some split policy is too
    by_contra hne
    have hsat : (p.effect == eff && satisfied p req es) = true := by
      by_contra hc
      rw [Bool.not_eq_true] at hc
      exact hne (by simp [satisfiedWithEffect, hc])
    rw [Bool.and_eq_true, beq_iff_eq] at hsat
    obtain ⟨q, hq, hqsat⟩ := (policy_satisfied_iff p req es (hty p hp)).mp hsat.2
    have hqeff : q.effect = eff := (splitPolicy_spec hq).1.trans hsat.1
    have hqmem : q ∈ splitPolicySet ps :=
      List.mem_flatMap.mpr ⟨p, hp, hq⟩
    have := h q hqmem
    simp [satisfiedWithEffect, hqeff, hqsat] at this
  · intro h q hq
    -- `q` satisfied with effect `eff`; then its source policy is too
    obtain ⟨p, hp, hqmem⟩ := List.mem_flatMap.mp hq
    by_contra hne
    have hqsat : (q.effect == eff && satisfied q req es) = true := by
      by_contra hc
      rw [Bool.not_eq_true] at hc
      exact hne (by simp [satisfiedWithEffect, hc])
    rw [Bool.and_eq_true, beq_iff_eq] at hqsat
    have hpeff : p.effect = eff := (splitPolicy_spec hqmem).1.symm.trans hqsat.1
    have hpsat : satisfied p req es :=
      (policy_satisfied_iff p req es (hty p hp)).mpr ⟨q, hqmem, hqsat.2⟩
    have := h p hp
    simp [satisfiedWithEffect, hpeff, hpsat] at this

/-- **Decision equivalence**: replacing every policy in a set with its split
preserves the authorization decision on every input on which every policy
is `TypedPolicy` (a validated set without ill-typed dead code is). -/
theorem splitPolicySet_decision (ps : Policies) (req : Request) (es : Entities)
  (hty : ∀ p ∈ ps, TypedPolicy p req es) :
  (isAuthorized req es (splitPolicySet ps)).decision =
  (isAuthorized req es ps).decision := by
  simp only [isAuthorized]
  rw [satisfiedPolicies_split_isEmpty Effect.forbid ps req es hty,
      satisfiedPolicies_split_isEmpty Effect.permit ps req es hty,
      apply_ite Response.decision, apply_ite Response.decision]

end Cedar.DNF
