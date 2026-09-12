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
The hoisting specification: when `hoist` finds an offending node inside a
non-offender expression and produces `(guards, cond, when_true, when_false)`,
then on every input the expression evaluates *exactly* like
`if cond then when_true else when_false` under the guards — once every guard
(a left sibling of the offending node, evaluated before it) evaluates without
error, and to the first guard's error otherwise. Congruence does the work:
every node inside an atom is strict, so its evaluation is a `do`-chain over
its children in order, into which the child's specification is substituted
and the bind pushed under the guards and into the branches (`underGuards_bind`,
`iteRes_bind`). The `isOffender e = false` hypothesis matters: `hoist`'s
`and`/`or`/`ite` arms are dead code at every call site, and for them the
clause is false — `&&`/`||` short-circuit their second operand, and `if`
branches are not strict.
-/

namespace Cedar.DNF

open Cedar.Spec

mutual

theorem hoistStep_spec {c cond t f : Expr} {gs : List Expr}
  (h : hoistStep c = some (gs, cond, t, f)) (req : Request) (es : Entities) :
  evaluate c req es =
    underGuards gs req es (iteRes (evaluate cond req es) (evaluate t req es) (evaluate f req es))
:= by
  match c with
  | .ite cc tt ee =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hg, hc, ht, hf⟩ := h
    subst hg hc ht hf
    rw [underGuards_nil]
    exact evaluate_ite cc tt ee req es
  | .and x₁ x₂ =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hg, hc, ht, hf⟩ := h
    subst hg hc ht hf
    rw [underGuards_nil]
    cases hv : evaluate (.and x₁ x₂) req es with
    | error err => simp [iteRes_error]
    | ok v =>
      have ⟨b, hb⟩ := and_ok_bool hv
      subst hb
      cases b <;> simp [iteRes, Result.as, Coe.coe, Value.asBool, boolLit, evaluate]
  | .or x₁ x₂ =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hg, hc, ht, hf⟩ := h
    subst hg hc ht hf
    rw [underGuards_nil]
    cases hv : evaluate (.or x₁ x₂) req es with
    | error err => simp [iteRes_error]
    | ok v =>
      have ⟨b, hb⟩ := or_ok_bool hv
      subst hb
      cases b <;> simp [iteRes, Result.as, Coe.coe, Value.asBool, boolLit, evaluate]
  | .unaryApp .not x =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hg, hc, ht, hf⟩ := h
    subst hg hc ht hf
    rw [underGuards_nil]
    cases hv : evaluate (.unaryApp .not x) req es with
    | error err => simp [iteRes_error]
    | ok v =>
      have ⟨b, hb⟩ := not_ok_bool hv
      subst hb
      cases b <;> simp [iteRes, Result.as, Coe.coe, Value.asBool, boolLit, evaluate]
  | .lit p => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .var v => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .unaryApp .neg x => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .unaryApp .isEmpty x => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .unaryApp (.like _) x => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .unaryApp (.is _) x => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .binaryApp _ _ _ => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .getAttr _ _ => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .hasAttr _ _ => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .set _ => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .record _ => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
  | .call _ _ => exact hoist_spec rfl (by simpa [hoistStep] using h) req es
termination_by (sizeOf c, 1)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; omega)

theorem hoist_spec {e cond t f : Expr} {gs : List Expr} (hno : isOffender e = false)
  (h : hoist e = some (gs, cond, t, f)) (req : Request) (es : Entities) :
  evaluate e req es =
    underGuards gs req es (iteRes (evaluate cond req es) (evaluate t req es) (evaluate f req es))
:= by
  match e with
  | .lit _ => simp [hoist] at h
  | .var _ => simp [hoist] at h
  | .and _ _ => simp [isOffender] at hno
  | .or _ _ => simp [isOffender] at hno
  | .ite _ _ _ => simp [isOffender] at hno
  | .unaryApp op x =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistStep_spec heq req es
      simp only [evaluate, ih, underGuards_bind, iteRes_bind]
    next => simp at h
  | .binaryApp op x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistStep_spec heq req es
      simp only [evaluate, ih, underGuards_bind, iteRes_bind]
    next =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have ih := hoistStep_spec heq req es
        rw [underGuards_addGuard]
        cases h₁ : evaluate x₁ req es with
        | error e₁ => simp only [evaluate, h₁, Except.bind_err]
        | ok v₁ => simp only [evaluate, h₁, Except.bind_ok, ih, underGuards_bind, iteRes_bind]
      next => simp at h
  | .getAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistStep_spec heq req es
      simp only [evaluate, ih, underGuards_bind, iteRes_bind]
    next => simp at h
  | .hasAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistStep_spec heq req es
      simp only [evaluate, ih, underGuards_bind, iteRes_bind]
    next => simp at h
  | .set xs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistList_spec heq req es
      simp only [evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es), ih,
        underGuards_bind, iteRes_bind]
    next => simp at h
  | .record axs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistRecord_spec heq req es
      simp only [evaluate,
        List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)), ih,
        underGuards_bind, iteRes_bind]
    next => simp at h
  | .call xfn xs =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next hne =>
      split at h
      next gs' cond' ts fs heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have ih := hoistList_spec heq req es
        rw [evaluate_call_ne xs req es hne, evaluate_call_ne ts req es hne,
          evaluate_call_ne fs req es hne]
        simp only [List.mapM₁_eq_mapM (fun x => evaluate x req es), ih,
          underGuards_bind, iteRes_bind]
      next => simp at h
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem hoistList_spec {xs : List Expr} {cond : Expr} {ts fs gs : List Expr}
  (h : hoistList xs = some (gs, cond, ts, fs)) (req : Request) (es : Entities) :
  xs.mapM (fun x => evaluate x req es) =
    underGuards gs req es (iteRes (evaluate cond req es)
      (ts.mapM (fun x => evaluate x req es)) (fs.mapM (fun x => evaluate x req es)))
:= by
  match xs with
  | [] => simp [hoistList] at h
  | x :: rest =>
    simp only [hoistList] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistStep_spec heq req es
      simp only [List.mapM_cons, ih, underGuards_bind, iteRes_bind]
    next =>
      split at h
      next gs' cond' ts' fs' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have ih := hoistList_spec heq req es
        rw [underGuards_addGuard]
        cases hx : evaluate x req es with
        | error e₁ => simp only [List.mapM_cons, hx, Except.bind_err]
        | ok v => simp only [List.mapM_cons, hx, Except.bind_ok, ih, underGuards_bind, iteRes_bind]
      next => simp at h
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem hoistRecord_spec {axs : List (Attr × Expr)} {cond : Expr} {gs : List Expr}
  {ts fs : List (Attr × Expr)}
  (h : hoistRecord axs = some (gs, cond, ts, fs)) (req : Request) (es : Entities) :
  axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) =
    underGuards gs req es (iteRes (evaluate cond req es)
      (ts.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)))
      (fs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es))))
:= by
  match axs with
  | [] => simp [hoistRecord] at h
  | (a, x) :: rest =>
    simp only [hoistRecord] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have ih := hoistStep_spec heq req es
      simp only [List.mapM_cons, bindAttr, ih, underGuards_bind, iteRes_bind]
    next =>
      split at h
      next gs' cond' ts' fs' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have ih := hoistRecord_spec heq req es
        rw [underGuards_addGuard]
        cases hx : evaluate x req es with
        | error e₁ => simp only [List.mapM_cons, hx, bindAttr_error, Except.bind_err]
        | ok v =>
          simp only [List.mapM_cons, hx, bindAttr_ok, Except.bind_ok, ih, underGuards_bind, iteRes_bind]
      next => simp at h
termination_by (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

end

end Cedar.DNF
