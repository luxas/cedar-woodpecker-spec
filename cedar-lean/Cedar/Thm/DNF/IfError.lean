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

import Cedar.Thm.DNF.SplitEquiv

/-!
The `iferror` operator (Phase 3 Step 4, part 1): `iferror(e, d)` coalesces
`e`'s error into `d`'s boolean. Its semantics is the `.call .ifError [e, d]`
arm of `evaluate`; the theorems here state it as the three-valued table the
README documents, over the `outcome` classification of the DNF development:

| `outcome e` | `outcome (iferror e d)`   |
| ----------- | ------------------------- |
| `tt`        | `tt` (`d` not evaluated)  |
| `ff`        | `ff` (`d` not evaluated)  |
| `err`       | `outcome d`, coerced      |

for `e` boolean-or-error (`Boolish`), and the two facts part 2 of Step 4 rests
on: `iferror(e, false)` never errors, and it is `.ok true` exactly when `e` is
(`ifError_false_ok_true_iff`, hypothesis-free).
-/

namespace Cedar.DNF

open Cedar.Spec

/-- The `iferror` call, for readability. -/
abbrev ifError (e d : Expr) : Expr := .call .ifError [e, d]

/-- Row 1/2: a boolean `e` passes through; `d` is not evaluated. -/
theorem evaluate_ifError_ok {e d : Expr} {req : Request} {es : Entities} {b : Bool}
  (h : evaluate e req es = .ok (.prim (.bool b))) :
  evaluate (ifError e d) req es = .ok (.prim (.bool b)) := by
  simp [ifError, evaluate, h, Result.as, Coe.coe, Value.asBool]

/-- Row 3: a non-boolean `e` is a type error, not coalesced. -/
theorem evaluate_ifError_nonbool {e d : Expr} {req : Request} {es : Entities} {v : Value}
  (h : evaluate e req es = .ok v) (hnb : ∀ b, v ≠ .prim (.bool b)) :
  evaluate (ifError e d) req es = .error .typeError := by
  simp only [ifError, evaluate, h]
  match v, hnb with
  | .prim (.bool b), hnb => exact absurd rfl (hnb b)
  | .prim (.int _), _ | .prim (.string _), _ | .prim (.entityUID _), _
  | .set _, _ | .record _, _ | .ext _, _ =>
    simp [Result.as, Coe.coe, Value.asBool]

/-- Row 4: an erring `e` yields `d` coerced to a boolean — `d`'s boolean, or
`d`'s own error, or a type error when `d` is not boolean. -/
theorem evaluate_ifError_err {e d : Expr} {req : Request} {es : Entities} {err : Error}
  (h : evaluate e req es = .error err) :
  evaluate (ifError e d) req es =
    (do let b ← (evaluate d req es).as Bool; .ok (Value.prim (Prim.bool b))) := by
  simp only [ifError, evaluate, h, bind_assoc, pure_bind]

/-- The three-valued table over `outcome`, for a boolean-or-error `e`: `.tt`
and `.ff` pass through and `.err` becomes `d`'s outcome (with `d` coerced to
a boolean, so a non-boolean `d` is `.err`). -/
theorem outcome_ifError {e d : Expr} {req : Request} {es : Entities}
  (hb : Boolish (evaluate e req es)) :
  outcome (evaluate (ifError e d) req es) =
    match outcome (evaluate e req es) with
    | .err => outcome (evaluate d req es)
    | o => o := by
  cases he : evaluate e req es with
  | error err =>
    rw [evaluate_ifError_err he]
    cases hd : evaluate d req es with
    | error e' => simp [outcome, Result.as]
    | ok v =>
      match v with
      | .prim (.bool true) | .prim (.bool false) => simp [outcome, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ => simp [outcome, Result.as, Coe.coe, Value.asBool]
  | ok v =>
    have ⟨b, hv⟩ := hb v he
    subst hv
    rw [evaluate_ifError_ok he]
    cases b <;> simp [outcome]

/-- **Never errors**: `iferror(e, false)` errs on no input on which `e` is
boolean-or-error (everything that validates). -/
theorem outcome_ifError_false_ne_err {e : Expr} {req : Request} {es : Entities}
  (hb : Boolish (evaluate e req es)) :
  outcome (evaluate (ifError e (boolLit false)) req es) ≠ .err := by
  rw [outcome_ifError hb]
  cases outcome (evaluate e req es) <;> simp [boolLit, evaluate, outcome]

/-- **The Step 4 rule**: `iferror(e, false)` is `true` exactly when `e` is —
the "`eval e = .some true`" test as a Cedar boolean. No hypotheses. -/
theorem ifError_false_ok_true_iff {e : Expr} {req : Request} {es : Entities} :
  evaluate (ifError e (boolLit false)) req es = .ok (.prim (.bool true)) ↔
    evaluate e req es = .ok (.prim (.bool true)) := by
  constructor
  · intro h
    cases he : evaluate e req es with
    | error err =>
      rw [evaluate_ifError_err he] at h
      simp [boolLit, evaluate, Result.as, Coe.coe, Value.asBool] at h
    | ok v =>
      match v with
      | .prim (.bool true) => rfl
      | .prim (.bool false) =>
        rw [evaluate_ifError_ok he] at h
        cases h
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        rw [evaluate_ifError_nonbool he (by intro b h; cases h)] at h
        cases h
  · intro h
    exact evaluate_ifError_ok h

/-- Consequently the negated form `!iferror(e, false)` — the shape Step 4 moves
into allow policies — is `true` exactly when `e` is not `true` (false or
erring), and never errs for boolean-or-error `e`. -/
theorem not_ifError_false_ok_true_iff {e : Expr} {req : Request} {es : Entities}
  (hb : Boolish (evaluate e req es)) :
  evaluate (.unaryApp .not (ifError e (boolLit false))) req es = .ok (.prim (.bool true)) ↔
    evaluate e req es ≠ .ok (.prim (.bool true)) := by
  have hne := outcome_ifError_false_ne_err hb
  cases ho : outcome (evaluate (ifError e (boolLit false)) req es) with
  | err => exact absurd ho hne
  | tt =>
    have h := outcome_tt_inv ho
    rw [ifError_false_ok_true_iff] at h
    simp only [h, ne_eq, not_true_eq_false, iff_false]
    intro hn
    have := (ifError_false_ok_true_iff (e := e) (req := req) (es := es)).mpr h
    simp [evaluate, this, apply₁] at hn
  | ff =>
    have h := outcome_ff_inv ho
    have hnt : evaluate e req es ≠ .ok (.prim (.bool true)) := by
      intro ht
      rw [(ifError_false_ok_true_iff).mpr ht] at h
      cases h
    simp only [hnt, ne_eq, not_false_eq_true, iff_true]
    simp [evaluate, h, apply₁]

end Cedar.DNF
