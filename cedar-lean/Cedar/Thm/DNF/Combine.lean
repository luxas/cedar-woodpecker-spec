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

import Cedar.DNF.Combine
import Cedar.Thm.DNF.IfError
import Cedar.Thm.DNF.SplitPolicyThm

/-!
The Step 4 (part 2) theorems: combining a policy set's allow and deny
policies into allow policies only preserves the authorization decision
(`combineAllowDeny_decision`), and so does splitting the result into its DNF
cubes (`allowCubes_decision`). The one hypothesis is Step 1's: every conjunct
of every forbid evaluates to a boolean or an error — for a non-boolean
conjunct both the forbid and its witness fail to be `true`, which is why it
is necessary. Everything that validates satisfies it.
-/

namespace Cedar.DNF

open Cedar.Spec
open Cedar.Data

/-! ### The `&&`-chain of the conjuncts is the expression -/

theorem outcome_andChain_append (xs ys : List Expr) (req : Request) (es : Entities) :
  outcome (evaluate (andChain (xs ++ ys)) req es) =
    (outcome (evaluate (andChain xs) req es)).and (outcome (evaluate (andChain ys) req es)) := by
  have htrue : outcome (evaluate (boolLit true) req es) = .tt := by
    simp [boolLit, evaluate, outcome]
  induction xs with
  | nil =>
    simp only [List.nil_append, andChain, htrue]
    generalize outcome (evaluate (andChain ys) req es) = o
    cases o <;> rfl
  | cons x rest ih =>
    cases rest with
    | nil =>
      cases ys with
      | nil =>
        simp only [andChain, List.append_nil, htrue]
        generalize outcome (evaluate x req es) = o
        cases o <;> rfl
      | cons y ys' =>
        simp only [List.singleton_append, andChain, outcome_and]
    | cons r rest' =>
      simp only [List.cons_append] at ih
      simp only [List.cons_append, andChain, outcome_and, ih]
      generalize outcome (evaluate x req es) = o
      cases o <;> rfl

/-- The chain of an expression's conjuncts has the expression's outcome —
`&&` is associative in three-valued logic, and `true && x` is `x`. -/
theorem outcome_andChain_conjuncts (e : Expr) (req : Request) (es : Entities) :
  outcome (evaluate (andChain (conjuncts e)) req es) = outcome (evaluate e req es) := by
  match e with
  | .and x₁ x₂ =>
    have ih₁ := outcome_andChain_conjuncts x₁ req es
    have ih₂ := outcome_andChain_conjuncts x₂ req es
    simp only [conjuncts, outcome_andChain_append, ih₁, ih₂, outcome_and]
  | .lit (.bool true) => simp [conjuncts, andChain, boolLit, evaluate, outcome]
  | .lit (.bool false) => simp [conjuncts, andChain]
  | .lit (.int _) | .lit (.string _) | .lit (.entityUID _) | .var _ | .ite _ _ _ | .or _ _
  | .unaryApp _ _ | .binaryApp _ _ _ | .getAttr _ _ | .hasAttr _ _ | .set _ | .record _
  | .call _ _ => simp [conjuncts, andChain]

/-! ### The deny witness -/

/-- The outcome of `!iferror(d, false)` for a boolean-or-error `d`: the
negation of "`d` is `tt`", never an error. -/
theorem outcome_notTrue {d : Expr} {req : Request} {es : Entities}
  (hb : Boolish (evaluate d req es)) :
  outcome (evaluate (notTrue d) req es) =
    (if outcome (evaluate d req es) = .tt then .ff else .tt) := by
  simp only [notTrue]
  rw [outcome_not, outcome_ifError hb]
  cases outcome (evaluate d req es) <;> simp [boolLit, evaluate, outcome, Outcome.negated]

/-- **The deny witness**: for a chain of boolean-or-error conjuncts, the
witness is `tt` exactly when the chain is not `tt`, and never an error. -/
theorem outcome_denyWitness (ds : List Expr) (req : Request) (es : Entities)
  (hb : ∀ d ∈ ds, Boolish (evaluate d req es)) :
  outcome (evaluate (denyWitness ds) req es) =
    (if outcome (evaluate (andChain ds) req es) = .tt then .ff else .tt) := by
  match ds with
  | [] => simp [denyWitness, andChain, boolLit, evaluate, outcome]
  | [d] =>
    simp only [denyWitness, andChain]
    exact outcome_notTrue (hb d (by simp))
  | d :: r :: rest =>
    have ih := outcome_denyWitness (r :: rest) req es (fun x hx => hb x (by simp [hx]))
    have hd := outcome_notTrue (hb d (by simp))
    simp only [denyWitness, andChain, outcome_or, outcome_and, hd, ih]
    cases outcome (evaluate d req es) <;>
    cases outcome (evaluate (andChain (r :: rest)) req es) <;> rfl

theorem denyWitness_ok_true_iff (ds : List Expr) (req : Request) (es : Entities)
  (hb : ∀ d ∈ ds, Boolish (evaluate d req es)) :
  evaluate (denyWitness ds) req es = .ok true ↔ evaluate (andChain ds) req es ≠ .ok true := by
  rw [evaluate_ok_true_iff_outcome, outcome_denyWitness ds req es hb, ne_eq,
    evaluate_ok_true_iff_outcome]
  generalize outcome (evaluate (andChain ds) req es) = o
  cases o <;> simp

/-! ### Combined permits -/

/-- A condition list is `true` iff each of its conditions is. -/
theorem conditions_ok_true_iff (cs : Conditions) (req : Request) (es : Entities) :
  evaluate (Conditions.toExpr cs) req es = .ok true ↔
    ∀ c ∈ cs, evaluate c.toExpr req es = .ok true := by
  have hfold : ∀ (l : List Condition) (init : Expr),
      evaluate (l.foldl (fun expr c => .and c.toExpr expr) init) req es = .ok true ↔
        (evaluate init req es = .ok true ∧ ∀ c ∈ l, evaluate c.toExpr req es = .ok true) := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons c l ih =>
      intro init
      simp only [List.foldl_cons, ih, evaluate_and_ok_true, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨hc, hi⟩, hl⟩; exact ⟨hi, hc, hl⟩
      · rintro ⟨hi, hc, hl⟩; exact ⟨⟨hc, hi⟩, hl⟩
  simp only [Conditions.toExpr]
  split
  next hrev =>
    have hnil : cs = [] := by simpa using congrArg List.reverse hrev
    subst hnil
    simp [evaluate]
  next c l hrev =>
    rw [hfold]
    have hmem : ∀ x, x ∈ cs ↔ x ∈ c :: l := by
      intro x
      rw [← List.mem_reverse, hrev]
    simp only [hmem, List.mem_cons, forall_eq_or_imp]

/-- A combined permit is satisfied iff the permit is and every forbid's
witness is `true`. -/
theorem combinePermit_satisfied_iff (fs : Policies) (p : Policy) (req : Request) (es : Entities) :
  satisfied (combinePermit fs p) req es ↔
    satisfied p req es ∧
    ∀ f ∈ fs, evaluate (denyWitness (conjuncts f.toExpr)) req es = .ok true := by
  simp only [satisfied_iff_scopes_cond, combinePermit, conditions_ok_true_iff, List.mem_append,
    List.mem_map]
  constructor
  · rintro ⟨hp, ha, hr, hc⟩
    refine ⟨⟨hp, ha, hr, fun c hc' => hc c (Or.inl hc')⟩, fun f hf => ?_⟩
    exact hc ⟨.when, denyWitness (conjuncts f.toExpr)⟩ (Or.inr ⟨f, hf, rfl⟩)
  · rintro ⟨⟨hp, ha, hr, hc⟩, hw⟩
    refine ⟨hp, ha, hr, fun c hc' => ?_⟩
    rcases hc' with hc' | ⟨f, hf, hcf⟩
    · exact hc c hc'
    · subst hcf
      exact hw f hf

/-- Under the boolean-conjuncts hypothesis, the witness is `true` iff the
forbid is not satisfied. -/
theorem witness_iff_not_satisfied (f : Policy) (req : Request) (es : Entities)
  (hb : ∀ d ∈ conjuncts f.toExpr, Boolish (evaluate d req es)) :
  evaluate (denyWitness (conjuncts f.toExpr)) req es = .ok true ↔ ¬ satisfied f req es := by
  rw [denyWitness_ok_true_iff _ _ _ hb]
  simp only [satisfied, decide_eq_true_eq, ne_eq]
  rw [evaluate_ok_true_iff_outcome, evaluate_ok_true_iff_outcome, outcome_andChain_conjuncts]

/-! ### The decision theorem -/

/-- The combined set has no forbids. -/
theorem combineAllowDeny_no_forbid (ps : Policies) (req : Request) (es : Entities) :
  (satisfiedPolicies .forbid (combineAllowDeny ps) req es).isEmpty = true := by
  simp only [satisfiedPolicies, Set.isEmpty_make, List.filterMap_eq_nil_iff]
  intro q hq
  simp only [combineAllowDeny, List.mem_map, List.mem_filter] at hq
  obtain ⟨p, ⟨_, hperm⟩, hq⟩ := hq
  subst hq
  simp only [beq_iff_eq] at hperm
  simp [satisfiedWithEffect, combinePermit, hperm]

/-- Membership in the sorted forbids is membership among the forbids. -/
theorem mem_forbidsOf {ps : Policies} {f : Policy} :
  f ∈ forbidsOf ps ↔ f ∈ ps ∧ f.effect = .forbid := by
  simp only [forbidsOf, (List.mergeSort_perm _ _).mem_iff, List.mem_filter, beq_iff_eq]

/-- Something with an effect is satisfied iff the set of satisfied policies
with that effect is nonempty. -/
theorem satisfiedPolicies_nonempty_iff (eff : Effect) (ps : Policies) (req : Request) (es : Entities) :
  (satisfiedPolicies eff ps req es).isEmpty = false ↔
    ∃ p ∈ ps, p.effect = eff ∧ satisfied p req es := by
  simp only [satisfiedPolicies, Set.isEmpty_make_eq_false, ne_eq, List.filterMap_eq_nil_iff]
  constructor
  · intro h
    by_contra hc
    apply h
    intro p hp
    simp only [satisfiedWithEffect]
    rw [if_neg]
    intro hsat
    simp only [Bool.and_eq_true, beq_iff_eq] at hsat
    exact hc ⟨p, hp, hsat.1, hsat.2⟩
  · rintro ⟨p, hp, heff, hsat⟩ h
    have := h p hp
    simp [satisfiedWithEffect, heff, hsat] at this

/-- **Decision equivalence**: the allow-only combination of a policy set has
its authorization decision on every input on which every conjunct of every
forbid is boolean-or-error. -/
theorem combineAllowDeny_decision (ps : Policies) (req : Request) (es : Entities)
  (hb : ∀ f ∈ ps, f.effect = .forbid → ∀ d ∈ conjuncts f.toExpr, Boolish (evaluate d req es)) :
  (isAuthorized req es (combineAllowDeny ps)).decision = (isAuthorized req es ps).decision := by
  -- the combined set's allow condition is the original's
  have hkey : ((satisfiedPolicies .forbid (combineAllowDeny ps) req es).isEmpty &&
      !(satisfiedPolicies .permit (combineAllowDeny ps) req es).isEmpty) =
      ((satisfiedPolicies .forbid ps req es).isEmpty &&
      !(satisfiedPolicies .permit ps req es).isEmpty) := by
    rw [combineAllowDeny_no_forbid, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    rw [satisfiedPolicies_nonempty_iff, satisfiedPolicies_nonempty_iff]
    have hforbid : (satisfiedPolicies .forbid ps req es).isEmpty = true ↔
        ∀ f ∈ ps, f.effect = .forbid → ¬ satisfied f req es := by
      constructor
      · intro h f hf heff hsat
        have : (satisfiedPolicies .forbid ps req es).isEmpty = false :=
          (satisfiedPolicies_nonempty_iff _ _ _ _).mpr ⟨f, hf, heff, hsat⟩
        rw [h] at this
        cases this
      · intro h
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        obtain ⟨f, hf, heff, hsat⟩ := (satisfiedPolicies_nonempty_iff _ _ _ _).mp hc
        exact h f hf heff hsat
    rw [hforbid]
    constructor
    · rintro ⟨q, hq, _, hsat⟩
      simp only [combineAllowDeny, List.mem_map, List.mem_filter, beq_iff_eq] at hq
      obtain ⟨p, ⟨hp, hperm⟩, hq⟩ := hq
      subst hq
      rw [combinePermit_satisfied_iff] at hsat
      obtain ⟨hpsat, hw⟩ := hsat
      refine ⟨fun f hf heff => ?_, p, hp, hperm, hpsat⟩
      have hfw := hw f (mem_forbidsOf.mpr ⟨hf, heff⟩)
      exact (witness_iff_not_satisfied f req es (hb f hf heff)).mp hfw
    · rintro ⟨hnf, p, hp, hperm, hpsat⟩
      refine ⟨combinePermit (forbidsOf ps) p, ?_, by simp [combinePermit, hperm], ?_⟩
      · simp only [combineAllowDeny, List.mem_map, List.mem_filter, beq_iff_eq]
        exact ⟨p, ⟨hp, hperm⟩, rfl⟩
      · rw [combinePermit_satisfied_iff]
        refine ⟨hpsat, fun f hf => ?_⟩
        obtain ⟨hf', heff⟩ := mem_forbidsOf.mp hf
        exact (witness_iff_not_satisfied f req es (hb f hf' heff)).mpr (hnf f hf' heff)
  simp only [isAuthorized]
  rw [hkey, apply_ite Response.decision, apply_ite Response.decision]

/-- **The allow-only cubes** keep the decision too, on every input on which
the combined permits are `TypedPolicy` (the Rust side validates them). -/
theorem allowCubes_decision (ps : Policies) (req : Request) (es : Entities)
  (hb : ∀ f ∈ ps, f.effect = .forbid → ∀ d ∈ conjuncts f.toExpr, Boolish (evaluate d req es))
  (hty : ∀ p ∈ combineAllowDeny ps, TypedPolicy p req es) :
  (isAuthorized req es (allowCubes ps)).decision = (isAuthorized req es ps).decision := by
  simp only [allowCubes]
  rw [splitPolicySet_decision _ req es hty, combineAllowDeny_decision ps req es hb]

end Cedar.DNF
