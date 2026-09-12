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

public import Cedar.Spec
import all Cedar.Spec.Wildcard

/-!
A relational specification of Cedar's `like` matcher. `Cedar.Spec.wildcardMatch`
is a memoized dynamic program over string and pattern indices
(`wildcardMatchIdx`); this file gives the structural matcher `matchB` and
proves the dynamic program computes it (`wildcardMatch_eq_matchB`, through a
cache invariant), then the two facts Phase 4 Step 1 needs: a wildcard-free
pattern matches exactly its characters (`matchB_noStar`), and a pattern with
a wildcard is matched by at least two strings (`star_matches_two`).
-/

namespace Cedar.Thm

open Cedar.Spec

/-- The structural matcher: a wildcard matches any (possibly empty) prefix. -/
@[expose] public def matchB : List Char → Pattern → Bool
  | [], [] => true
  | [], .star :: p => matchB [] p
  | [], .justChar _ :: _ => false
  | _ :: _, [] => false
  | c :: cs, .justChar d :: p => c == d && matchB cs p
  | c :: cs, .star :: p => matchB (c :: cs) p || matchB cs (.star :: p)
termination_by cs p => (cs.length, p.length)

/-! ### The dynamic program computes `matchB` -/

/-- Every cached answer is the specified one. -/
def CacheOk (text : List Char) (pattern : Pattern) (cache : Cache) : Prop :=
  ∀ i j b, cache.get? (i, j) = some b → b = matchB (text.drop i) (pattern.drop j)

theorem cacheOk_empty {text : List Char} {pattern : Pattern} : CacheOk text pattern {} := by
  intro i j b h
  simp at h

theorem cacheOk_insert {text : List Char} {pattern : Pattern} {cache : Cache} {i j : Nat} {b : Bool}
  (hc : CacheOk text pattern cache) (hb : b = matchB (text.drop i) (pattern.drop j)) :
  CacheOk text pattern (cache.insert (i, j) b) := by
  intro i' j' b' h
  rw [Std.HashMap.get?_insert] at h
  split at h
  · rename_i heq
    simp only [beq_iff_eq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    injection h with h ; subst h
    exact hb
  · exact hc i' j' b' h

private theorem matchB_nil_cons (e : PatElem) (p : Pattern) :
  matchB [] (e :: p) = (wildcard e && matchB [] p) := by
  cases e <;> simp [matchB, wildcard]

private theorem matchB_cons_cons (c : Char) (cs : List Char) (e : PatElem) (p : Pattern) :
  matchB (c :: cs) (e :: p) =
    if wildcard e then matchB (c :: cs) p || matchB cs (e :: p)
    else charMatch c e && matchB cs p := by
  cases e <;> simp [matchB, wildcard, charMatch]

/-- The dynamic program computes `matchB` and keeps the cache correct. -/
theorem wildcardMatchIdx_spec (text : List Char) (pattern : Pattern) :
  ∀ (i j : Nat) (h₁ : i ≤ text.length) (h₂ : j ≤ pattern.length) (cache : Cache),
    CacheOk text pattern cache →
    ((wildcardMatchIdx text pattern i j h₁ h₂).run cache).1 =
        matchB (text.drop i) (pattern.drop j) ∧
    CacheOk text pattern ((wildcardMatchIdx text pattern i j h₁ h₂).run cache).2 := by
  intro i j h₁ h₂
  induction i, j, h₁, h₂ using wildcardMatchIdx.induct text pattern with
  | _ i j h₁ h₂ ih₁ ih₂ ih₃ ih₄ =>
  intro cache hc
  unfold wildcardMatchIdx
  simp only [bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  cases hget : cache.get? (i, j) with
  | some b =>
    simp only [hget]
    exact ⟨(hc i j b hget).symm ▸ rfl, hc⟩
  | none =>
    simp only [hget]
    by_cases hj : j = pattern.length
    · rw [dif_pos hj]
      subst hj
      have hspec : decide (i = text.length) =
          matchB (text.drop i) (pattern.drop pattern.length) := by
        rw [List.drop_length]
        cases hd : text.drop i with
        | nil =>
          rw [List.drop_eq_nil_iff] at hd
          simp only [matchB, decide_eq_true_eq]
          omega
        | cons c cs =>
          have hlt : ¬ text.length ≤ i := by
            intro hle ; rw [← List.drop_eq_nil_iff] at hle ; simp [hle] at hd
          simp only [matchB, decide_eq_false_iff_not]
          omega
      exact ⟨hspec, cacheOk_insert hc hspec⟩
    · rw [dif_neg hj]
      have hjlt : j < pattern.length := by omega
      have hdropp : pattern.drop j = pattern[j] :: pattern.drop (j + 1) :=
        List.drop_eq_getElem_cons hjlt
      by_cases hi : i = text.length
      · rw [dif_pos hi]
        obtain ⟨hr, hc'⟩ := ih₁ hj cache hc
        simp only [StateT.run] at hr hc'
        rcases hrun : wildcardMatchIdx text pattern i (j + 1) h₁ (by omega) cache with ⟨r, c'⟩
        rw [hrun] at hr hc'
        simp only at hr hc'
        subst hr
        simp only [StateT.bind, StateT.modifyGet]
        rw [hrun]
        simp only [bind, pure]
        have hspec : (wildcard (pattern.get ⟨j, hjlt⟩) &&
            matchB (text.drop i) (pattern.drop (j + 1))) =
            matchB (text.drop i) (pattern.drop j) := by
          rw [hdropp, List.get_eq_getElem]
          have : text.drop i = [] := by rw [List.drop_eq_nil_iff] ; omega
          rw [this, matchB_nil_cons]
        exact ⟨hspec, cacheOk_insert hc' hspec⟩
      · rw [dif_neg hi]
        have hilt : i < text.length := by omega
        have hdropt : text.drop i = text[i] :: text.drop (i + 1) :=
          List.drop_eq_getElem_cons hilt
        by_cases hw : wildcard (pattern.get ⟨j, hjlt⟩) = true
        · rw [if_pos hw]
          obtain ⟨hr₁, hc₁⟩ := ih₂ hj hi cache hc
          simp only [StateT.run] at hr₁ hc₁
          rcases hrun₁ : wildcardMatchIdx text pattern i (j + 1) h₁ (by omega) cache with ⟨r₁, c₁⟩
          rw [hrun₁] at hr₁ hc₁
          simp only at hr₁ hc₁
          subst hr₁
          obtain ⟨hr₂, hc₂⟩ := ih₃ hi c₁ hc₁
          simp only [StateT.run] at hr₂ hc₂
          rcases hrun₂ : wildcardMatchIdx text pattern (i + 1) j (by omega) h₂ c₁ with ⟨r₂, c₂⟩
          rw [hrun₂] at hr₂ hc₂
          simp only at hr₂ hc₂
          subst hr₂
          simp only [StateT.bind, StateT.modifyGet]
          rw [hrun₁]
          simp only [bind, pure]
          rw [hrun₂]
          simp only [bind, pure]
          have hspec : (matchB (text.drop i) (pattern.drop (j + 1)) ||
              matchB (text.drop (i + 1)) (pattern.drop j)) =
              matchB (text.drop i) (pattern.drop j) := by
            rw [hdropp, hdropt, matchB_cons_cons]
            rw [List.get_eq_getElem] at hw
            rw [if_pos hw, ← hdropt]
          exact ⟨hspec, cacheOk_insert hc₂ hspec⟩
        · rw [if_neg hw]
          obtain ⟨hr, hc'⟩ := ih₄ hj hi cache hc
          simp only [StateT.run] at hr hc'
          rcases hrun : wildcardMatchIdx text pattern (i + 1) (j + 1) (by omega) (by omega) cache
            with ⟨r, c'⟩
          rw [hrun] at hr hc'
          simp only at hr hc'
          subst hr
          simp only [StateT.bind, StateT.modifyGet]
          rw [hrun]
          simp only [bind, pure]
          have hspec : (charMatch (text.get ⟨i, hilt⟩) (pattern.get ⟨j, hjlt⟩) &&
              matchB (text.drop (i + 1)) (pattern.drop (j + 1))) =
              matchB (text.drop i) (pattern.drop j) := by
            rw [hdropp, hdropt, matchB_cons_cons, List.get_eq_getElem, List.get_eq_getElem]
            rw [List.get_eq_getElem] at hw
            rw [if_neg (by simpa using hw)]
          exact ⟨hspec, cacheOk_insert hc' hspec⟩

public theorem wildcardMatch_eq_matchB (s : String) (p : Pattern) :
  wildcardMatch s p = matchB s.toList p := by
  have h := (wildcardMatchIdx_spec s.toList p 0 0 (by simp) (by simp) {}
    (cacheOk_empty (text := s.toList) (pattern := p))).left
  simp only [List.drop_zero] at h
  unfold wildcardMatch
  exact h

/-! ### Wildcard-free patterns match exactly their characters -/

public theorem matchB_noStar (cs ds : List Char) :
  matchB cs (ds.map .justChar) = (cs == ds) := by
  induction ds generalizing cs with
  | nil => cases cs <;> simp [matchB]
  | cons d ds ih =>
    cases cs with
    | nil => simp [matchB]
    | cons c cs => simp [matchB, ih]

/-! ### A wildcard admits at least two strings -/

/-- The pattern with every wildcard replaced by `fill`. -/
@[expose] public def render (fill : List Char) : Pattern → List Char
  | [] => []
  | .justChar c :: p => c :: render fill p
  | .star :: p => fill ++ render fill p

private theorem matchB_star_append (fill rest : List Char) (p : Pattern)
  (h : matchB rest p = true) : matchB (fill ++ rest) (.star :: p) = true := by
  induction fill with
  | nil =>
    cases rest with
    | nil => simpa [matchB] using h
    | cons c cs => simp [matchB, h]
  | cons f fs ih => simp [matchB, ih]

public theorem matchB_render (fill : List Char) (p : Pattern) : matchB (render fill p) p = true := by
  induction p with
  | nil => simp [render, matchB]
  | cons e p ih =>
    cases e with
    | justChar c => simp [render, matchB, ih]
    | star => exact matchB_star_append fill _ p ih

/-- The number of wildcards. -/
def stars : Pattern → Nat
  | [] => 0
  | .star :: p => stars p + 1
  | .justChar _ :: p => stars p

theorem stars_pos_of_mem {p : Pattern} (h : PatElem.star ∈ p) : 0 < stars p := by
  induction p with
  | nil => simp at h
  | cons e p ih =>
    cases e with
    | star => simp [stars]
    | justChar c =>
      simp only [List.mem_cons, reduceCtorEq, false_or] at h
      simp [stars, ih h]

/-- Filling every wildcard with one character adds one character per wildcard. -/
theorem render_length_one (p : Pattern) :
  (render ['a'] p).length = (render [] p).length + stars p := by
  induction p with
  | nil => simp [render, stars]
  | cons e p ih =>
    cases e with
    | justChar c => simp [render, stars, ih] ; omega
    | star => simp [render, stars, ih] ; omega

/-- A pattern with a wildcard is matched by at least two strings. -/
public theorem star_matches_two (p : Pattern) (h : PatElem.star ∈ p) :
  ∃ s₁ s₂ : List Char, s₁ ≠ s₂ ∧ matchB s₁ p = true ∧ matchB s₂ p = true := by
  refine ⟨render [] p, render ['a'] p, ?_, matchB_render [] p, matchB_render ['a'] p⟩
  intro heq
  have hlen := congrArg List.length heq
  rw [render_length_one] at hlen
  have hstar := stars_pos_of_mem h
  omega

end Cedar.Thm
