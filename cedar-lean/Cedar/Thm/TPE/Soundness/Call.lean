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


import Cedar.TPE
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

import Cedar.Thm.TPE.Soundness.Basic

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

/-- Coercing to a boolean respects `toOption`-equality of the results. -/
private theorem as_bool_to_option_congr {r₁ r₂ : Spec.Result Value}
  (h : r₁.toOption = r₂.toOption) :
  (Result.as Bool r₁).toOption = (Result.as Bool r₂).toOption
:= by
  cases r₁ <;> cases r₂ <;> simp only [Except.toOption, reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (subst h ; rfl)
    | simp [Result.as, Except.toOption]

/-- `iferror`'s "use the fallback on error" step respects `toOption`-equality
of its first argument. -/
private theorem ifError_fallback_congr {a a' f : Spec.Result Value}
  (h : a.toOption = a'.toOption) :
  (match a with | .error _ => f | r => r).toOption =
  (match a' with | .error _ => f | r => r).toOption
:= by
  cases a <;> cases a' <;> simp only [Except.toOption, reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (subst h ; rfl)
    | rfl

/-- A value residual evaluates to its value; an error residual errs. -/
private theorem val_evaluate_to_option {v : Value} {ty : CedarType} {req : Request} {es : Entities} :
  ((Residual.val v ty).evaluate req es).toOption = some v
:= by simp [Residual.evaluate, Except.toOption]

private theorem error_evaluate_to_option {ty : CedarType} {req : Request} {es : Entities} :
  ((Residual.error ty).evaluate req es).toOption = none
:= by simp [Residual.evaluate, Except.toOption]

theorem partial_evaluate_is_sound_call
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{xfn : ExtFun}
{args : List Residual}
{ty : CedarType}
(hᵢ₁ : ∀ (x : Residual),
  x ∈ args →
    Except.toOption (x.evaluate req es) = Except.toOption ((TPE.evaluate x preq pes).evaluate req es)) :
  Except.toOption ((Residual.call xfn args ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.call xfn args ty) preq pes).evaluate req es)
:= by
  by_cases hif : xfn = .ifError ∧ ∃ x₁ x₂, args = [x₁, x₂]
  · -- `iferror`: the lazy evaluation on both sides agrees `toOption`-wise
    obtain ⟨hxfn, x₁, x₂, hxs⟩ := hif
    subst hxfn hxs
    have h₁ := hᵢ₁ x₁ (by simp)
    have h₂ := hᵢ₁ x₂ (by simp)
    generalize hr₁ : TPE.evaluate x₁ preq pes = r₁ at h₁
    generalize hr₂ : TPE.evaluate x₂ preq pes = r₂ at h₂
    simp only [TPE.evaluate, hr₁, hr₂]
    split
    next =>
      -- `x₁` is a value
      rw [val_evaluate_to_option] at h₁
      replace h₁ := to_option_some.mp h₁
      split
      · simp [Residual.evaluate, h₁, Result.as, Coe.coe, Value.asBool, Except.toOption]
      · rw [error_evaluate_to_option]
        simp only [Residual.evaluate, h₁, Result.as, Coe.coe, Value.asBool]
        simp [Except.toOption]
    next =>
      -- `x₁` errs: the fallback decides
      rw [error_evaluate_to_option] at h₁
      obtain ⟨e₁, he₁⟩ := to_option_none.mp h₁
      split
      next =>
        rw [val_evaluate_to_option] at h₂
        replace h₂ := to_option_some.mp h₂
        split
        · simp [Residual.evaluate, he₁, h₂, Result.as, Coe.coe, Value.asBool, Except.toOption]
        · rw [error_evaluate_to_option]
          simp only [Residual.evaluate, he₁, h₂, Result.as, Coe.coe, Value.asBool]
          simp [Except.toOption]
      next =>
        rw [error_evaluate_to_option] at h₂
        obtain ⟨e₂, he₂⟩ := to_option_none.mp h₂
        rw [error_evaluate_to_option]
        simp [Residual.evaluate, he₁, he₂, Result.as, Except.toOption]
      next =>
        -- both sides coalesce into the fallback
        simp only [Residual.evaluate, he₁]
        apply to_option_eq_do₁
        apply to_option_eq_do₁
        apply as_bool_to_option_congr
        exact h₂
    next =>
      -- `x₁` stays a residual: the call stays, and `x₂` is untouched
      simp only [Residual.evaluate]
      apply to_option_eq_do₁
      apply to_option_eq_do₁
      apply as_bool_to_option_congr
      exact ifError_fallback_congr h₁
  have hshape : ∀ (f : Residual → Residual) (y₁ y₂ : Residual), args.map f = [y₁, y₂] →
      ∃ a b, args = [a, b] := by
    intro f y₁ y₂ h
    match args, h with
    | [a, b], _ => exact ⟨a, b, rfl⟩
    | [], h => simp at h
    | [_], h => simp at h
    | _ :: _ :: _ :: _, h => simp at h
  have hmapped : ∀ (x₁ x₂ : Residual), xfn = ExtFun.ifError →
      List.map (fun x => TPE.evaluate x preq pes) args = [x₁, x₂] → False := by
    intro y₁ y₂ h₁ h₂
    obtain ⟨a, b, hab⟩ := hshape _ y₁ y₂ h₂
    exact hif ⟨h₁, a, b, hab⟩
  rw [Cedar.TPE.evaluate.eq_14 _ _ _ _ _ (fun x₁ x₂ h₁ h₂ => hif ⟨h₁, x₁, x₂, h₂⟩),
    Residual.evaluate.eq_16 _ _ _ _ _ (fun x₁ x₂ h₁ h₂ => hif ⟨h₁, x₁, x₂, h₂⟩)]
  simp only [TPE.call, List.map₁, List.map_subtype, List.unattach_attach,
    List.mapM_map, Function.comp_def, List.any_map, List.any_eq_true]
  split
  case _ vs heq =>
    simp only [List.mapM₁_eq_mapM (Residual.evaluate · req es), someOrError]
    simp only [List.mapM_some_iff_forall₂] at heq
    have h_tpe_ok : List.mapM (λ x => (TPE.evaluate x preq pes).evaluate req es) args = .ok vs := by
      rw [List.mapM_ok_iff_forall₂]
      exact List.Forall₂.imp (fun _ _ h => asValue_evaluate_val h req es) heq
    have h₅ : List.mapM (λ x => x.evaluate req es) args = .ok vs := by
      have h₅ := List.mapM_to_option_congr hᵢ₁
      simp only [h_tpe_ok] at h₅
      exact to_option_left_ok' h₅.symm
    simp only [h₅, Except.bind_ok]
    split
    case _ heq₁ =>
      simp only [to_option_some] at heq₁
      simp only [heq₁, Residual.evaluate]
    case _ heq₁ =>
      rcases to_option_none.mp heq₁ with ⟨_, heq₁⟩
      simp [heq₁, Residual.evaluate, Except.toOption]
  split
  case _ heq₁ =>
    rcases heq₁ with ⟨x, heq₂, heq₃⟩
    have ⟨_, he⟩ := isError_evaluate_err heq₃ req es
    have h_none : (x.evaluate req es).toOption = none := by
      rw [hᵢ₁ x heq₂]
      simp [he, Except.toOption]
    have heq₄ := List.element_to_option_none_implies_mapM_none (f := (Residual.evaluate · req es)) heq₂
      (by rw [hᵢ₁ x heq₂]; simp [he, Except.toOption])
    simp only [Residual.evaluate, List.mapM₁_eq_mapM (Residual.evaluate · req es), do_to_option_none heq₄,]
    simp [Except.toOption]
  case _ =>
    rw [Residual.evaluate.eq_16 _ _ _ _ _ hmapped]
    simp only [List.mapM₁_eq_mapM (Residual.evaluate · req es)]
    apply to_option_eq_do₁ (λ (x : List Value) => Spec.call xfn x)
    rw [List.mapM_to_option_congr hᵢ₁]
    rw [List.mapM_map]
    unfold Function.comp
    simp

end Cedar.Thm
