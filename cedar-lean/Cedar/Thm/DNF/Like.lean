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

import Cedar.DNF.Like
import Cedar.Thm.DNF.Wildcard
import Cedar.Thm.DNF.Equivalence
import Cedar.Thm.DNF.SplitEquiv
import Cedar.Thm.Data

/-!
Phase 4 Step 1: `x like p` with a wildcard-free `p` is `x == "<p>"`.

* `evaluate_rewriteLike` — **soundness**: the rewrite evaluates like its input
  wherever every operand of a wildcard-free `like` evaluates to a string or an
  error. Validation ensures this by its typing rules (the connection to the
  typechecker is not made here); on a non-string *value* `like` is a type
  error while `==` is `false`, so the hypothesis is necessary.
* `rewriteLike_complete` — **completeness**: every `like` left has a wildcard,
  and (`rewriteLike_matches_two`) is matched by at least two strings.
-/

namespace Cedar.DNF

open Cedar.Spec
open Cedar.Thm

/-- `x` evaluates to a string, or errors. -/
def Stringish (x : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ v, evaluate x req es = .ok v → ∃ s, v = .prim (.string s)

/-! ### Patterns -/

/-- A wildcard-free pattern is its characters. -/
theorem noStar_eq_map {p : Pattern} (h : hasStar p = false) :
  p = (patternChars p).map .justChar := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    cases e with
    | star => simp [hasStar] at h
    | justChar c =>
      simp only [hasStar, List.any_cons, beq_self_eq_true, Bool.false_or, reduceCtorEq,
        beq_iff_eq] at h ih ⊢
      simp only [patternChars, List.filterMap_cons, List.map_cons, List.cons.injEq, true_and]
      exact ih h

/-- On a wildcard-free pattern, `like` is equality with `patternString`. -/
theorem wildcardMatch_noStar {p : Pattern} (h : hasStar p = false) (s : String) :
  wildcardMatch s p = (s == patternString p) := by
  rw [wildcardMatch_eq_matchB]
  conv => lhs ; rw [noStar_eq_map h]
  rw [matchB_noStar]
  simp only [patternString]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro heq
    rw [String.ext_iff, String.toList_ofList]
    exact heq
  · intro heq
    rw [heq, String.toList_ofList]

/-! ### Soundness -/

/-- `x like p` with a wildcard-free `p` evaluates like `x == "<p>"` when `x`
is a string or errors. -/
theorem evaluate_like_eq {x : Expr} {p : Pattern} {req : Request} {es : Entities}
  (hp : hasStar p = false) (hx : Stringish x req es) :
  evaluate (.binaryApp .eq x (.lit (.string (patternString p)))) req es =
    evaluate (.unaryApp (.like p) x) req es := by
  simp only [evaluate]
  cases hv : evaluate x req es with
  | error e => simp [Except.bind_err]
  | ok v =>
    obtain ⟨s, rfl⟩ := hx v hv
    have hbeq : (Value.prim (.string s) == Value.prim (.string (patternString p))) =
        (s == patternString p) := by
      rw [value_prim_beq]
      apply Bool.eq_iff_iff.mpr
      simp
    simp only [Except.bind_ok, apply₁, apply₂, wildcardMatch_noStar hp, hbeq]

mutual

theorem evaluate_rewriteLike (e : Expr) (req : Request) (es : Entities)
  (h : ∀ x ∈ likeOperands e, Stringish x req es) :
  evaluate (rewriteLike e) req es = evaluate e req es := by
  match e with
  | .lit p => simp only [rewriteLike]
  | .var v => simp only [rewriteLike]
  | .ite x₁ x₂ x₃ =>
    simp only [likeOperands, List.mem_append] at h
    have ih₁ := evaluate_rewriteLike x₁ req es (fun x hx => h x (Or.inl (Or.inl hx)))
    have ih₂ := evaluate_rewriteLike x₂ req es (fun x hx => h x (Or.inl (Or.inr hx)))
    have ih₃ := evaluate_rewriteLike x₃ req es (fun x hx => h x (Or.inr hx))
    simp only [rewriteLike, evaluate, ih₁, ih₂, ih₃]
  | .and x₁ x₂ =>
    simp only [likeOperands, List.mem_append] at h
    have ih₁ := evaluate_rewriteLike x₁ req es (fun x hx => h x (Or.inl hx))
    have ih₂ := evaluate_rewriteLike x₂ req es (fun x hx => h x (Or.inr hx))
    simp only [rewriteLike, evaluate, ih₁, ih₂]
  | .or x₁ x₂ =>
    simp only [likeOperands, List.mem_append] at h
    have ih₁ := evaluate_rewriteLike x₁ req es (fun x hx => h x (Or.inl hx))
    have ih₂ := evaluate_rewriteLike x₂ req es (fun x hx => h x (Or.inr hx))
    simp only [rewriteLike, evaluate, ih₁, ih₂]
  | .unaryApp (.like p) x =>
    simp only [likeOperands] at h
    simp only [rewriteLike]
    split
    · rename_i hp
      rw [if_pos hp] at h
      have ih := evaluate_rewriteLike x req es h
      simp only [evaluate, ih]
    · rename_i hp
      rw [if_neg hp] at h
      simp only [List.mem_cons] at h
      have ih := evaluate_rewriteLike x req es (fun y hy => h y (Or.inr hy))
      have hx : Stringish x req es := h x (Or.inl rfl)
      have hx' : Stringish (rewriteLike x) req es := by
        intro v hv ; rw [ih] at hv ; exact hx v hv
      rw [evaluate_like_eq (by simpa using hp) hx']
      simp only [evaluate, ih]
  | .unaryApp .not x =>
    simp only [likeOperands] at h
    have ih := evaluate_rewriteLike x req es h
    simp only [rewriteLike, evaluate, ih]
  | .unaryApp .neg x =>
    simp only [likeOperands] at h
    have ih := evaluate_rewriteLike x req es h
    simp only [rewriteLike, evaluate, ih]
  | .unaryApp (.is ety) x =>
    simp only [likeOperands] at h
    have ih := evaluate_rewriteLike x req es h
    simp only [rewriteLike, evaluate, ih]
  | .unaryApp .isEmpty x =>
    simp only [likeOperands] at h
    have ih := evaluate_rewriteLike x req es h
    simp only [rewriteLike, evaluate, ih]
  | .binaryApp op x₁ x₂ =>
    simp only [likeOperands, List.mem_append] at h
    have ih₁ := evaluate_rewriteLike x₁ req es (fun x hx => h x (Or.inl hx))
    have ih₂ := evaluate_rewriteLike x₂ req es (fun x hx => h x (Or.inr hx))
    simp only [rewriteLike, evaluate, ih₁, ih₂]
  | .getAttr x a =>
    simp only [likeOperands] at h
    have ih := evaluate_rewriteLike x req es h
    simp only [rewriteLike, evaluate, ih]
  | .hasAttr x a =>
    simp only [likeOperands] at h
    have ih := evaluate_rewriteLike x req es h
    simp only [rewriteLike, evaluate, ih]
  | .set xs =>
    simp only [likeOperands, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
      exists_prop] at h
    have ih := evaluate_rewriteLike_list xs req es (fun y hy x hx => h x ⟨y, hy, hx⟩)
    simp only [rewriteLike, evaluate, List.map₁_eq_map,
      List.mapM₁_eq_mapM (fun x => evaluate x req es), List.mapM_map,
      Function.comp_def, ih]
  | .record axs =>
    simp only [likeOperands, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
      exists_prop] at h
    have ih := evaluate_rewriteLike_record axs req es
      (fun a y hy x hx => h x ⟨(a, y), hy, hx⟩)
    simp only [rewriteLike, evaluate, List.map₂_eq_map_snd,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)),
      List.mapM_map, Function.comp_def, ih]
  | .call xfn xs =>
    simp only [likeOperands, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists,
      exists_prop] at h
    by_cases hif : xfn = .ifError ∧ ∃ x₁ x₂, xs = [x₁, x₂]
    · obtain ⟨hxfn, x₁, x₂, hxs⟩ := hif
      subst hxfn hxs
      have ih₁ := evaluate_rewriteLike x₁ req es (fun x hx => h x ⟨x₁, by simp, hx⟩)
      have ih₂ := evaluate_rewriteLike x₂ req es (fun x hx => h x ⟨x₂, by simp, hx⟩)
      simp only [rewriteLike, List.map₁_eq_map, List.map_cons, List.map_nil, evaluate, ih₁, ih₂]
    · have ih := evaluate_rewriteLike_list xs req es (fun y hy x hx => h x ⟨y, hy, hx⟩)
      have hshape : ∀ y₁ y₂, xs.map rewriteLike = [y₁, y₂] → ∃ a b, xs = [a, b] := by
        intro y₁ y₂ h
        match xs, h with
        | [a, b], _ => exact ⟨a, b, rfl⟩
        | [], h => simp at h
        | [_], h => simp at h
        | _ :: _ :: _ :: _, h => simp at h
      simp only [rewriteLike, List.map₁_eq_map]
      rw [evaluate.eq_16 _ _ _ _ (fun y₁ y₂ h₁ h₂ => by
            obtain ⟨a, b, hab⟩ := hshape y₁ y₂ h₂
            exact hif ⟨h₁, a, b, hab⟩),
          evaluate.eq_16 _ _ _ _ (fun y₁ y₂ h₁ h₂ => hif ⟨h₁, y₁, y₂, h₂⟩)]
      simp only [List.mapM₁_eq_mapM (fun x => evaluate x req es), List.mapM_map,
        Function.comp_def, ih]
termination_by (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp +arith; done)
    | (apply Prod.Lex.left; subst_vars; simp +arith; done)

theorem evaluate_rewriteLike_list (xs : List Expr) (req : Request) (es : Entities)
  (h : ∀ y ∈ xs, ∀ x ∈ likeOperands y, Stringish x req es) :
  xs.mapM (fun x => evaluate (rewriteLike x) req es) =
    xs.mapM (fun x => evaluate x req es) := by
  match xs with
  | [] => rfl
  | x :: rest =>
    have hx := evaluate_rewriteLike x req es (h x (by simp))
    have hrest := evaluate_rewriteLike_list rest req es (fun y hy => h y (by simp [hy]))
    simp only [List.mapM_cons, hx, hrest]
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem evaluate_rewriteLike_record (axs : List (Attr × Expr)) (req : Request) (es : Entities)
  (h : ∀ a y, (a, y) ∈ axs → ∀ x ∈ likeOperands y, Stringish x req es) :
  axs.mapM (fun ax => bindAttr ax.1 (evaluate (rewriteLike ax.2) req es)) =
    axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) := by
  match axs with
  | [] => rfl
  | (a, x) :: rest =>
    have hx := evaluate_rewriteLike x req es (h a x (by simp))
    have hrest := evaluate_rewriteLike_record rest req es (fun a y hy => h a y (by simp [hy]))
    simp only [List.mapM_cons, hx, hrest]
termination_by (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

end

/-! ### Completeness -/

/-- Every `like` left by the rewrite has a wildcard. -/
theorem rewriteLike_complete (e : Expr) :
  ∀ p ∈ likePatterns (rewriteLike e), hasStar p = true := by
  match e with
  | .lit _ | .var _ => simp [rewriteLike, likePatterns]
  | .ite x₁ x₂ x₃ =>
    have ih₁ := rewriteLike_complete x₁
    have ih₂ := rewriteLike_complete x₂
    have ih₃ := rewriteLike_complete x₃
    simp only [rewriteLike, likePatterns, List.mem_append]
    rintro p ((h | h) | h)
    · exact ih₁ p h
    · exact ih₂ p h
    · exact ih₃ p h
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ =>
    have ih₁ := rewriteLike_complete x₁
    have ih₂ := rewriteLike_complete x₂
    simp only [rewriteLike, likePatterns, List.mem_append]
    rintro p (h | h)
    · exact ih₁ p h
    · exact ih₂ p h
  | .unaryApp (.like p) x =>
    have ih := rewriteLike_complete x
    simp only [rewriteLike]
    split
    · rename_i hp
      simp only [likePatterns, List.mem_cons]
      rintro q (rfl | h)
      · exact hp
      · exact ih q h
    · simp only [likePatterns, List.mem_append, List.not_mem_nil, or_false]
      exact ih
  | .unaryApp .not x | .unaryApp .neg x | .unaryApp (.is _) x | .unaryApp .isEmpty x
  | .getAttr x _ | .hasAttr x _ =>
    have ih := rewriteLike_complete x
    simpa [rewriteLike, likePatterns] using ih
  | .set xs =>
    simp only [rewriteLike, likePatterns, List.map₁_eq_map, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists, exists_prop, List.mem_map]
    rintro p ⟨y, ⟨x, hx, hxy⟩, hp⟩
    subst hxy
    exact rewriteLike_complete x p hp
  | .record axs =>
    simp only [rewriteLike, likePatterns, List.map₂_eq_map_snd, List.mem_flatMap,
      List.mem_attach, true_and, Subtype.exists, exists_prop, List.mem_map, Prod.exists]
    rintro p ⟨a, y, ⟨b, x, hx, hax⟩, hp⟩
    simp only [Prod.mk.injEq] at hax
    obtain ⟨hab, hxy⟩ := hax
    subst hab hxy
    exact rewriteLike_complete x p hp
  | .call _ xs =>
    simp only [rewriteLike, likePatterns, List.map₁_eq_map, List.mem_flatMap, List.mem_attach,
      true_and, Subtype.exists, exists_prop, List.mem_map]
    rintro p ⟨y, ⟨x, hx, hxy⟩, hp⟩
    subst hxy
    exact rewriteLike_complete x p hp
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (have := List.sizeOf_lt_of_mem hx; simp +arith; omega)
    | (have := List.sizeOf_lt_of_mem hx
       simp +arith at this
       omega))

/-- Every `like` left by the rewrite is matched by at least two strings. -/
theorem rewriteLike_matches_two (e : Expr) :
  ∀ p ∈ likePatterns (rewriteLike e),
    ∃ s₁ s₂ : String, s₁ ≠ s₂ ∧ wildcardMatch s₁ p = true ∧ wildcardMatch s₂ p = true := by
  intro p hp
  have hstar : PatElem.star ∈ p := by
    have h := rewriteLike_complete e p hp
    simp only [hasStar, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨e, he, rfl⟩ := h
    exact he
  obtain ⟨s₁, s₂, hne, h₁, h₂⟩ := star_matches_two p hstar
  refine ⟨String.ofList s₁, String.ofList s₂, ?_, ?_, ?_⟩
  · intro heq ; apply hne ; simpa using congrArg String.toList heq
  · rw [wildcardMatch_eq_matchB, String.toList_ofList] ; exact h₁
  · rw [wildcardMatch_eq_matchB, String.toList_ofList] ; exact h₂

end Cedar.DNF
