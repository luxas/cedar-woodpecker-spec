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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Validation.Levels.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem level_based_slicing_is_sound_call {xs : List Expr} {n : Nat} {c₀ c₁: Capabilities} {env : TypeEnv} {request : Request} {entities : Entities}
  (hc : CapabilitiesInvariant c₀ request entities)
  (hr : InstanceOfWellFormedEnvironment request entities env)
  (ht : typeOf (.call xfn xs) c₀ env = Except.ok (tx, c₁))
  (hl : tx.AtLevel env n)
  (ih : ∀ x ∈ xs, TypedAtLevelIsSound x) :
  evaluate (.call xfn xs) request entities = evaluate (.call xfn xs) request (entities.sliceAtLevel request n)
:= by
  replace ⟨ txs, ⟨ty, hty⟩, ht ⟩ := type_of_call_inversion ht
  subst tx
  cases hl ; rename_i hl

  have he : ∀ x ∈ xs, evaluate x request entities = evaluate x request (entities.sliceAtLevel request n) := by
    intros x hx
    replace ⟨ tx, htxs, c', htx ⟩ := List.forall₂_implies_all_left ht x hx
    specialize hl tx htxs
    exact ih x hx hc hr htx hl

  by_cases hif : xfn = .ifError ∧ ∃ x₁ x₂, xs = [x₁, x₂]
  · -- `iferror` is lazy: rewrite each argument's evaluation directly
    obtain ⟨hxfn, x₁, x₂, hxs⟩ := hif
    subst hxfn hxs
    simp only [evaluate, he x₁ (by simp), he x₂ (by simp)]
  rw [evaluate.eq_16 _ _ _ _ (fun x₁ x₂ h₁ h₂ => hif ⟨h₁, x₁, x₂, h₂⟩),
    evaluate.eq_16 _ _ _ _ (fun x₁ x₂ h₁ h₂ => hif ⟨h₁, x₁, x₂, h₂⟩)]
  simp only [xs.mapM₁_eq_mapM (evaluate · request entities)]
  simp only [xs.mapM₁_eq_mapM (evaluate · request (entities.sliceAtLevel request n))]
  rw [List.mapM_congr he]
