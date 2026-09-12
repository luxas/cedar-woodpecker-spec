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

import Cedar.Thm.DNF.Pruning
import Cedar.Thm.Data.Control

/-!
The concrete equivalence: `dnf e canError` evaluates like `e` under
`Cedar.Spec.evaluate` — the same boolean value, or errors on both sides — for
every request and entity store on which the `canError` answers are correct
and every atom of `e` evaluates to a boolean or an error (`evaluate_dnf`;
unconditional in `canError` for `dnfOfExpr`, `evaluate_dnfOfExpr`).

The boolean-atoms hypothesis is necessary, not an artifact: literal dedup
rewrites `a || a` to the single cube `a`, and for an atom of non-boolean type
the original errs (`.as Bool`) where the cube returns the value. Anything
that typechecks satisfies the hypothesis.

The bridge is `interp_evaluate`: over the valuation that evaluates an atom
and classifies its result (`outcome`), the abstract `interp` agrees with
`evaluate` on *every* expression — Cedar's `&&`/`||`/`!`/`if` coerce with
`.as Bool`, so a non-boolean operand and an error collapse to the same
`Outcome.err` on both sides.
-/

namespace Cedar.DNF

open Cedar.Spec

/-- Classifies an evaluation result: `true`, `false`, or anything else
(an error, or a non-boolean value). -/
def outcome : Result Value → Outcome
  | .ok (.prim (.bool true))  => .tt
  | .ok (.prim (.bool false)) => .ff
  | _                         => .err

theorem outcome_tt_inv {r : Result Value} (h : outcome r = .tt) :
  r = .ok (.prim (.bool true))
:= by
  match r with
  | .ok (.prim (.bool true)) => rfl
  | .ok (.prim (.bool false)) => cases h
  | .ok (.prim (.int _)) | .ok (.prim (.string _)) | .ok (.prim (.entityUID _)) => cases h
  | .ok (.set _) | .ok (.record _) | .ok (.ext _) => cases h
  | .error _ => cases h

theorem outcome_ff_inv {r : Result Value} (h : outcome r = .ff) :
  r = .ok (.prim (.bool false))
:= by
  match r with
  | .ok (.prim (.bool true)) => cases h
  | .ok (.prim (.bool false)) => rfl
  | .ok (.prim (.int _)) | .ok (.prim (.string _)) | .ok (.prim (.entityUID _)) => cases h
  | .ok (.set _) | .ok (.record _) | .ok (.ext _) => cases h
  | .error _ => cases h

/-! ### The boolean structure of `evaluate`, at the `outcome` level -/

theorem outcome_and (l r : Expr) (req : Request) (es : Entities) :
  outcome (evaluate (.and l r) req es) =
    (outcome (evaluate l req es)).and (outcome (evaluate r req es))
:= by
  cases hl : evaluate l req es with
  | error e => simp [evaluate, hl, Result.as, outcome, Outcome.and]
  | ok v =>
    match v with
    | .prim (.bool true) =>
      cases hr : evaluate r req es with
      | error e =>
        simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.and]
      | ok w =>
        match w with
        | .prim (.bool true) =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.and]
        | .prim (.bool false) =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.and]
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.and]
    | .prim (.bool false) =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool, outcome, Outcome.and]
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool, outcome, Outcome.and]

theorem outcome_or (l r : Expr) (req : Request) (es : Entities) :
  outcome (evaluate (.or l r) req es) =
    (outcome (evaluate l req es)).or (outcome (evaluate r req es))
:= by
  cases hl : evaluate l req es with
  | error e => simp [evaluate, hl, Result.as, outcome, Outcome.or]
  | ok v =>
    match v with
    | .prim (.bool true) =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool, outcome, Outcome.or]
    | .prim (.bool false) =>
      cases hr : evaluate r req es with
      | error e =>
        simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.or]
      | ok w =>
        match w with
        | .prim (.bool true) =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.or]
        | .prim (.bool false) =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.or]
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, outcome, Outcome.or]
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool, outcome, Outcome.or]

theorem outcome_not (x : Expr) (req : Request) (es : Entities) :
  outcome (evaluate (.unaryApp .not x) req es) =
    (outcome (evaluate x req es)).negated
:= by
  cases hx : evaluate x req es with
  | error e => simp [evaluate, hx, outcome, Outcome.negated]
  | ok v =>
    match v with
    | .prim (.bool true) => simp [evaluate, hx, apply₁, outcome, Outcome.negated]
    | .prim (.bool false) => simp [evaluate, hx, apply₁, outcome, Outcome.negated]
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hx, apply₁, outcome, Outcome.negated]

theorem outcome_ite (c t e' : Expr) (req : Request) (es : Entities) :
  outcome (evaluate (.ite c t e') req es) =
    match outcome (evaluate c req es) with
    | .tt  => outcome (evaluate t req es)
    | .ff  => outcome (evaluate e' req es)
    | .err => .err
:= by
  cases hc : evaluate c req es with
  | error e => simp [evaluate, hc, Result.as, outcome]
  | ok v =>
    match v with
    | .prim (.bool true) =>
      simp [evaluate, hc, Result.as, Coe.coe, Value.asBool, outcome]
    | .prim (.bool false) =>
      simp [evaluate, hc, Result.as, Coe.coe, Value.asBool, outcome]
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hc, Result.as, Coe.coe, Value.asBool, outcome]

/-- Over the valuation that evaluates the atom, `interp` agrees with
`evaluate` on every expression — no side conditions. -/
theorem interp_evaluate (e : Expr) (req : Request) (es : Entities) :
  interp (fun a => outcome (evaluate a req es)) e = outcome (evaluate e req es)
:= by
  match e with
  | .lit (.bool b) => cases b <;> simp [interp, evaluate, outcome]
  | .unaryApp .not x =>
    have ih := interp_evaluate x req es
    show (interp _ x).negated = _
    rw [ih, outcome_not]
  | .and l r =>
    have ihl := interp_evaluate l req es
    have ihr := interp_evaluate r req es
    rw [interp_and, ihl, ihr, outcome_and]
  | .or l r =>
    have ihl := interp_evaluate l req es
    have ihr := interp_evaluate r req es
    rw [interp_or, ihl, ihr, outcome_or]
  | .ite c t e' =>
    have ihc := interp_evaluate c req es
    have iht := interp_evaluate t req es
    have ihe := interp_evaluate e' req es
    show (match interp (fun a => outcome (evaluate a req es)) c with
      | .tt => interp (fun a => outcome (evaluate a req es)) t
      | .ff => interp (fun a => outcome (evaluate a req es)) e'
      | .err => .err) = _
    rw [ihc, iht, ihe, outcome_ite]
  | .lit (.int _) => rfl
  | .lit (.string _) => rfl
  | .lit (.entityUID _) => rfl
  | .var _ => rfl
  | .unaryApp .neg _ => rfl
  | .unaryApp .isEmpty _ => rfl
  | .unaryApp (.like _) _ => rfl
  | .unaryApp (.is _) _ => rfl
  | .binaryApp _ _ _ => rfl
  | .getAttr _ _ => rfl
  | .hasAttr _ _ => rfl
  | .set _ => rfl
  | .record _ => rfl
  | .call _ _ => rfl
termination_by sizeOf e

/-! ### Members of `atoms` are genuine atoms -/

theorem atoms_mem_spec {e : Expr} :
  ∀ a ∈ atoms e, atoms a = [a] ∧ ∀ (v : Expr → Outcome), interp v a = v a
:= by
  match e with
  | .lit (.bool b) => intro a ha; cases ha
  | .unaryApp .not x =>
    intro a ha
    exact atoms_mem_spec (e := x) a ha
  | .and l r =>
    intro a ha
    cases List.mem_append.mp ha with
    | inl h => exact atoms_mem_spec (e := l) a h
    | inr h => exact atoms_mem_spec (e := r) a h
  | .or l r =>
    intro a ha
    cases List.mem_append.mp ha with
    | inl h => exact atoms_mem_spec (e := l) a h
    | inr h => exact atoms_mem_spec (e := r) a h
  | .ite c t e' =>
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · cases List.mem_append.mp h with
      | inl h' => exact atoms_mem_spec (e := c) a h'
      | inr h' => exact atoms_mem_spec (e := t) a h'
    · exact atoms_mem_spec (e := e') a h
  | .lit (.int _) => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .lit (.string _) => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .lit (.entityUID _) => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .var _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .unaryApp .neg _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .unaryApp .isEmpty _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .unaryApp (.like _) _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .unaryApp (.is _) _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .binaryApp _ _ _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .getAttr _ _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .hasAttr _ _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .set _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .record _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
  | .call _ _ => intro a ha; simp [atoms] at ha; subst ha; exact ⟨rfl, fun _ => rfl⟩
termination_by sizeOf e

/-! ### The atoms of the DNF are atoms of the input -/

theorem atoms_literal_toExpr (l : Literal) :
  atoms l.toExpr = atoms l.atom
:= by cases hn : l.negated <;> simp [Literal.toExpr, hn, atoms]

theorem atoms_and_chain (ls : List Literal) (init : Expr) :
  atoms (ls.foldl (fun acc l => .and acc l.toExpr) init) =
    atoms init ++ ls.flatMap (fun l => atoms l.toExpr)
:= by
  induction ls generalizing init with
  | nil => simp
  | cons l rest ih =>
    simp only [List.foldl, List.flatMap_cons]
    rw [ih]
    show atoms init ++ atoms l.toExpr ++ _ = _
    simp [List.append_assoc]

theorem atoms_cube_toExpr {c : Cube} {a : Expr} (h : a ∈ atoms c.toExpr) :
  ∃ l ∈ c.literals, a ∈ atoms l.atom
:= by
  match c with
  | ⟨[], nt⟩ =>
    exfalso
    cases nt <;> simp [Cube.toExpr, boolLit, atoms] at h
  | ⟨l :: rest, nt⟩ =>
    have hchain := atoms_and_chain rest l.toExpr
    have hmain : a ∈ atoms (rest.foldl (fun acc l' => .and acc l'.toExpr) l.toExpr) →
        ∃ l' ∈ (⟨l :: rest, nt⟩ : Cube).literals, a ∈ atoms l'.atom := by
      intro h'
      rw [hchain] at h'
      cases List.mem_append.mp h' with
      | inl h'' =>
        rw [atoms_literal_toExpr] at h''
        exact ⟨l, by simp, h''⟩
      | inr h'' =>
        have ⟨l', hl', ha⟩ := List.mem_flatMap.mp h''
        rw [atoms_literal_toExpr] at ha
        exact ⟨l', by simp [hl'], ha⟩
    cases nt with
    | false =>
      apply hmain
      simpa [Cube.toExpr] using h
    | true =>
      apply hmain
      have h' : a ∈ atoms
          ((rest.foldl (fun acc l' => .and acc l'.toExpr) l.toExpr).and (boolLit false)) := by
        simpa [Cube.toExpr] using h
      simpa [atoms, boolLit] using h'

theorem atoms_or_chain (cs : List Cube) (init : Expr) :
  atoms (cs.foldl (fun acc c => .or acc c.toExpr) init) =
    atoms init ++ cs.flatMap (fun c => atoms c.toExpr)
:= by
  induction cs generalizing init with
  | nil => simp
  | cons c rest ih =>
    simp only [List.foldl, List.flatMap_cons]
    rw [ih]
    show atoms init ++ atoms c.toExpr ++ _ = _
    simp [List.append_assoc]

theorem atoms_toExpr_sub {cs : List Cube} {a : Expr} (h : a ∈ atoms (toExpr cs)) :
  ∃ c ∈ cs, ∃ l ∈ c.literals, a ∈ atoms l.atom
:= by
  match cs with
  | [] => simp [toExpr, boolLit, atoms] at h
  | c :: rest =>
    simp only [toExpr] at h
    rw [atoms_or_chain] at h
    cases List.mem_append.mp h with
    | inl h' =>
      have ⟨l, hl, ha⟩ := atoms_cube_toExpr h'
      exact ⟨c, by simp, l, hl, ha⟩
    | inr h' =>
      have ⟨c', hc', ha⟩ := List.mem_flatMap.mp h'
      have ⟨l, hl, ha'⟩ := atoms_cube_toExpr ha
      exact ⟨c', by simp [hc'], l, hl, ha'⟩

/-- Every atom of the DNF is an atom of the input. -/
theorem atoms_dnf_sub {e : Expr} {canError : Expr → Bool} :
  ∀ a ∈ atoms (dnf e canError), a ∈ atoms e
:= by
  intro a ha
  rw [dnf] at ha
  have ⟨c, hc, l, hl, hla⟩ := atoms_toExpr_sub ha
  have ⟨p, hp, hcp⟩ := prune_shape hc
  subst hcp
  have hmem : l.atom ∈ atoms e := paths_atoms_sub hp hl
  have := (atoms_mem_spec l.atom hmem).1
  rw [this] at hla
  simp at hla
  subst hla
  exact hmem

/-! ### Structure nodes evaluate to booleans or errors -/

theorem and_ok_bool {l r : Expr} {req : Request} {es : Entities} {v : Value}
  (h : evaluate (.and l r) req es = .ok v) :
  ∃ b, v = .prim (.bool b)
:= by
  cases hl : evaluate l req es with
  | error e => simp [evaluate, hl, Result.as] at h
  | ok w =>
    match w with
    | .prim (.bool false) =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h
      exact ⟨false, h.symm⟩
    | .prim (.bool true) =>
      cases hr : evaluate r req es with
      | error e => simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
      | ok u =>
        match u with
        | .prim (.bool c) =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
          exact ⟨c, h.symm⟩
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h

theorem or_ok_bool {l r : Expr} {req : Request} {es : Entities} {v : Value}
  (h : evaluate (.or l r) req es = .ok v) :
  ∃ b, v = .prim (.bool b)
:= by
  cases hl : evaluate l req es with
  | error e => simp [evaluate, hl, Result.as] at h
  | ok w =>
    match w with
    | .prim (.bool true) =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h
      exact ⟨true, h.symm⟩
    | .prim (.bool false) =>
      cases hr : evaluate r req es with
      | error e => simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
      | ok u =>
        match u with
        | .prim (.bool c) =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
          exact ⟨c, h.symm⟩
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h

theorem not_ok_bool {x : Expr} {req : Request} {es : Entities} {v : Value}
  (h : evaluate (.unaryApp .not x) req es = .ok v) :
  ∃ b, v = .prim (.bool b)
:= by
  cases hx : evaluate x req es with
  | error e => simp [evaluate, hx] at h
  | ok w =>
    match w with
    | .prim (.bool c) =>
      simp [evaluate, hx, apply₁] at h
      exact ⟨!c, h.symm⟩
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hx, apply₁] at h

/-- With boolean atoms, evaluation only ever produces booleans or errors. -/
theorem evaluate_ok_bool {e : Expr} {req : Request} {es : Entities}
  (hb : ∀ a ∈ atoms e, ∀ v, evaluate a req es = .ok v → ∃ b, v = .prim (.bool b))
  {v : Value} (h : evaluate e req es = .ok v) :
  ∃ b, v = .prim (.bool b)
:= by
  match e with
  | .lit (.bool b) =>
    simp [evaluate] at h
    exact ⟨b, h.symm⟩
  | .and l r => exact and_ok_bool h
  | .or l r => exact or_ok_bool h
  | .unaryApp .not x => exact not_ok_bool h
  | .ite c t e' =>
    cases hc : evaluate c req es with
    | error e => simp [evaluate, hc, Result.as] at h
    | ok w =>
      match w with
      | .prim (.bool true) =>
        have ht : evaluate t req es = .ok v := by
          simpa [evaluate, hc, Result.as, Coe.coe, Value.asBool] using h
        refine evaluate_ok_bool (fun a ha => hb a ?_) ht
        show a ∈ atoms c ++ atoms t ++ atoms e'
        rw [List.append_assoc, List.mem_append]
        exact .inr (List.mem_append.mpr (.inl ha))
      | .prim (.bool false) =>
        have he : evaluate e' req es = .ok v := by
          simpa [evaluate, hc, Result.as, Coe.coe, Value.asBool] using h
        refine evaluate_ok_bool (fun a ha => hb a ?_) he
        show a ∈ atoms c ++ atoms t ++ atoms e'
        rw [List.append_assoc, List.mem_append]
        exact .inr (List.mem_append.mpr (.inr ha))
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, hc, Result.as, Coe.coe, Value.asBool] at h
  | .lit (.int i) => exact hb _ (by simp [atoms]) v h
  | .lit (.string s) => exact hb _ (by simp [atoms]) v h
  | .lit (.entityUID u) => exact hb _ (by simp [atoms]) v h
  | .var x => exact hb _ (by simp [atoms]) v h
  | .unaryApp .neg x => exact hb _ (by simp [atoms]) v h
  | .unaryApp .isEmpty x => exact hb _ (by simp [atoms]) v h
  | .unaryApp (.like p) x => exact hb _ (by simp [atoms]) v h
  | .unaryApp (.is ty) x => exact hb _ (by simp [atoms]) v h
  | .binaryApp op x y => exact hb _ (by simp [atoms]) v h
  | .getAttr x attr => exact hb _ (by simp [atoms]) v h
  | .hasAttr x attr => exact hb _ (by simp [atoms]) v h
  | .set xs => exact hb _ (by simp [atoms]) v h
  | .record axs => exact hb _ (by simp [atoms]) v h
  | .call f xs => exact hb _ (by simp [atoms]) v h
termination_by sizeOf e

/-- **Equivalence, concrete**: the DNF evaluates like the input — the same
boolean value, or an error on both sides — wherever the `canError` answers
are correct and every atom evaluates to a boolean or an error. -/
theorem evaluate_dnf {e : Expr} {canError : Expr → Bool} {req : Request} {es : Entities}
  (hbool : ∀ a ∈ atoms e, ∀ v, evaluate a req es = .ok v → ∃ b, v = .prim (.bool b))
  (herr : ∀ a ∈ atoms e, canError a = false → ∀ err, evaluate a req es ≠ .error err) :
  (∃ b, evaluate (dnf e canError) req es = .ok (.prim (.bool b)) ∧
        evaluate e req es = .ok (.prim (.bool b))) ∨
  ((∃ err, evaluate (dnf e canError) req es = .error err) ∧
   (∃ err, evaluate e req es = .error err))
:= by
  have habs : ∀ a ∈ atoms e, canError a = false →
      interp (fun a' => outcome (evaluate a' req es)) a ≠ .err := by
    intro a ha hce
    rw [(atoms_mem_spec a ha).2]
    intro hout
    cases hv : evaluate a req es with
    | error err => exact herr a ha hce err hv
    | ok v =>
      have ⟨b, hb⟩ := hbool a ha v hv
      subst hb
      rw [hv] at hout
      cases b <;> simp [outcome] at hout
  have key : outcome (evaluate (dnf e canError) req es) = outcome (evaluate e req es) := by
    rw [← interp_evaluate (dnf e canError) req es, ← interp_evaluate e req es]
    exact interp_dnf habs
  cases ho : outcome (evaluate e req es) with
  | tt =>
    exact .inl ⟨true, outcome_tt_inv (key.trans ho), outcome_tt_inv ho⟩
  | ff =>
    exact .inl ⟨false, outcome_ff_inv (key.trans ho), outcome_ff_inv ho⟩
  | err =>
    refine .inr ⟨?_, ?_⟩
    · cases hv : evaluate (dnf e canError) req es with
      | error err => exact ⟨err, rfl⟩
      | ok v =>
        have ⟨b, hb⟩ := evaluate_ok_bool
          (fun a ha => hbool a (atoms_dnf_sub a ha)) hv
        subst hb
        have := key.trans ho
        rw [hv] at this
        cases b <;> simp [outcome] at this
    · cases hv : evaluate e req es with
      | error err => exact ⟨err, rfl⟩
      | ok v =>
        have ⟨b, hb⟩ := evaluate_ok_bool hbool hv
        subst hb
        rw [hv] at ho
        cases b <;> simp [outcome] at ho

/-- `dnfOfExpr` evaluates like the input whenever every atom evaluates to a
boolean or an error. -/
theorem evaluate_dnfOfExpr {e : Expr} {req : Request} {es : Entities}
  (hbool : ∀ a ∈ atoms e, ∀ v, evaluate a req es = .ok v → ∃ b, v = .prim (.bool b)) :
  (∃ b, evaluate (dnfOfExpr e) req es = .ok (.prim (.bool b)) ∧
        evaluate e req es = .ok (.prim (.bool b))) ∨
  ((∃ err, evaluate (dnfOfExpr e) req es = .error err) ∧
   (∃ err, evaluate e req es = .error err))
:= evaluate_dnf hbool (by simp)

end Cedar.DNF
