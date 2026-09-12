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

import Cedar.DNF.SplitPolicy
import Cedar.Thm.DNF.ElimSound

/-!
The cube-satisfaction lemma: a condition expression evaluates to `.ok true`
exactly when *one* of its split cube-conditions does, and at most one ever
does. Both facts are hypothesis-free — everything lands on `outcome = .tt`,
which `outcome_tt_inv` turns into `.ok true` with no side conditions — because
`.ok true` is the only outcome that matters for policy satisfaction, and an
erroring input simply satisfies neither side.
-/

namespace Cedar.DNF

open Cedar.Spec

theorem outcome_ok_true : outcome (.ok true) = .tt := rfl

/-- `evaluate e = .ok true` in terms of the classifying valuation. -/
theorem evaluate_ok_true_iff_outcome {e : Expr} {req : Request} {es : Entities} :
  evaluate e req es = .ok true ↔ outcome (evaluate e req es) = .tt := by
  constructor
  · intro h; rw [h]; exact outcome_ok_true
  · intro h; exact outcome_tt_inv h

/-- A cube's rendered expression evaluates to `.ok true` exactly when the
cube interprets `.tt` under the classifying valuation. -/
theorem cube_toExpr_ok_true {c : Cube} {req : Request} {es : Entities} :
  evaluate c.toExpr req es = .ok true ↔
    c.interp (fun a => outcome (evaluate a req es)) = .tt := by
  rw [evaluate_ok_true_iff_outcome, ← interp_evaluate c.toExpr req es,
      interp_cube_toExpr]

/-- The pruned cubes contain a `.tt` cube exactly when the interpretation of
the whole (structure) expression is `.tt`. Independent of `canError`, since
true-cubes are always kept. -/
theorem cube_interp_eq_pathInterp (v : Expr → Outcome) (p : Path) :
  p.cube.interp v = pathInterp v p := rfl

theorem exists_tt_cube_iff {s : Expr} {v : Expr → Outcome} {cf : Expr → Bool} :
  (∃ c ∈ prune (paths s) cf, c.interp v = .tt) ↔ interp v s = .tt := by
  constructor
  · rintro ⟨c, hc, htt⟩
    have ⟨p, hp, hcp⟩ := prune_shape hc
    subst hcp
    rw [cube_interp_eq_pathInterp] at htt
    obtain ⟨hlits, hleaf⟩ := pathInterp_tt_inv htt
    obtain ⟨_, mF, mE⟩ := master s v
    cases ho : interp v s with
    | tt => rfl
    | ff =>
      obtain ⟨_, hB, _⟩ := mF ho
      exact absurd hlits (hB p hp (by simp [leafOf, hleaf]))
    | err =>
      obtain ⟨hnopass, _⟩ := mE ho
      exact absurd hlits (hnopass p hp (.inl hleaf))
  · intro h
    obtain ⟨mT, _, _⟩ := master s v
    obtain ⟨⟨p, hp, hpleaf, hpass⟩, _, _⟩ := mT h
    have hleaf : p.leaf = .tt := by simpa [leafOf] using hpleaf
    refine ⟨p.cube, prune_keeps_tt hp hleaf, ?_⟩
    rw [cube_interp_eq_pathInterp]
    exact pathInterp_of_pass_tt hpass hleaf

/-- **Cube satisfaction**: the condition evaluates to `.ok true` iff exactly
one of its split cube-conditions does (existence here; uniqueness is
`cond_satisfied_unique`), on every input on which the split condition is
`Typed` (the elimination's hypothesis; a validated condition without ill-typed
dead code satisfies it). -/
theorem cond_satisfied_iff (c : Expr) (req : Request) (es : Entities)
  (hty : Typed req es (splitAtoms c)) :
  evaluate c req es = .ok true ↔
    ∃ cond ∈ splitCondExprs c, evaluate cond req es = .ok true := by
  rw [evaluate_ok_true_iff_outcome, ← evaluate_normalize c req es hty,
      ← interp_evaluate (normalize c) req es,
      ← exists_tt_cube_iff (cf := fun _ => false)]
  simp only [splitCondExprs, List.mem_map]
  constructor
  · rintro ⟨cube, hmem, htt⟩
    exact ⟨cube.toExpr, ⟨cube, hmem, rfl⟩, cube_toExpr_ok_true.mpr htt⟩
  · rintro ⟨cond, ⟨cube, hmem, hceq⟩, hok⟩
    subst hceq
    exact ⟨cube, hmem, cube_toExpr_ok_true.mp hok⟩

/-- **Cube-satisfaction uniqueness**: at most one split cube-condition
evaluates to `.ok true`. -/
theorem cond_satisfied_unique (c : Expr) (req : Request) (es : Entities) :
  (splitCondExprs c).Pairwise fun c₁ c₂ =>
    ¬(evaluate c₁ req es = .ok true ∧ evaluate c₂ req es = .ok true) := by
  have hpair := dnf_cubes_exclusive (normalize c) (fun _ => false)
  simp only [splitCondExprs]
  refine List.Pairwise.map _ ?_ hpair
  intro c₁ c₂ h ⟨h₁, h₂⟩
  exact h (fun a => outcome (evaluate a req es))
    ⟨cube_toExpr_ok_true.mp h₁, cube_toExpr_ok_true.mp h₂⟩

end Cedar.DNF
