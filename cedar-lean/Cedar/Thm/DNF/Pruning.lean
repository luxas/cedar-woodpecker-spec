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

import Cedar.Thm.DNF.Master

/-!
Pruning is sound, and the abstract equivalence follows: `prune` keeps every
may-be-true cube and at least one cube through any erring node whose atom
`canError`, so the pruned disjunction interprets exactly like the input
expression wherever the `canError` answers are correct (`interp_dnf`). The
cubes of the DNF are also pairwise exclusive — at most one is ever true, in
any valuation and any order (`dnf_cubes_exclusive`).
-/

namespace Cedar.DNF

open Cedar.Spec

/-! ### What `prune` keeps -/

theorem cube_nodes_eq (p : Path) : nodesFrom [] p.cube.literals = p.nodes := rfl

theorem cubeInterp_of_err {v : Expr → Outcome} {c : Cube}
  (h : litsInterp v c.literals = .err) :
  c.interp v = .err
:= by simp [Cube.interp, h]

/-- The uncovered `canError` nodes of a never-true path. -/
def uncoveredOf (ce : Expr → Bool) (covered : List Node) (p : Path) : List Node :=
  (p.nodes.filter fun (n, l) => !covered.contains n && ce l.atom).map Prod.fst

theorem pruneGo_cons_tt {ce : Expr → Bool} {covered : List Node} {p : Path}
  {rest : List Path} (h : p.leaf = .tt) :
  pruneGo ce covered (p :: rest) = p.cube :: pruneGo ce covered rest
:= by
  simp only [pruneGo]
  rw [if_pos (by simp [h])]

theorem pruneGo_cons_drop {ce : Expr → Bool} {covered : List Node} {p : Path}
  {rest : List Path} (h : p.leaf ≠ .tt)
  (hemp : (uncoveredOf ce covered p).isEmpty = true) :
  pruneGo ce covered (p :: rest) = pruneGo ce covered rest
:= by
  have hemp' : ((p.nodes.filter fun (n, l) =>
      !covered.contains n && ce l.atom).map Prod.fst).isEmpty = true := hemp
  simp only [pruneGo]
  rw [if_neg (by simp [h]), if_pos hemp']

theorem pruneGo_cons_keep {ce : Expr → Bool} {covered : List Node} {p : Path}
  {rest : List Path} (h : p.leaf ≠ .tt)
  (hemp : ¬ (uncoveredOf ce covered p).isEmpty = true) :
  pruneGo ce covered (p :: rest) =
    p.cube :: pruneGo ce (covered ++ uncoveredOf ce covered p) rest
:= by
  have hemp' : ¬ ((p.nodes.filter fun (n, l) =>
      !covered.contains n && ce l.atom).map Prod.fst).isEmpty = true := hemp
  simp only [pruneGo]
  rw [if_neg (by simp [h]), if_neg hemp']
  rfl

theorem uncoveredOf_sub {ce : Expr → Bool} {covered : List Node} {p : Path}
  {n : Node} (h : n ∈ uncoveredOf ce covered p) :
  ∃ l, (n, l) ∈ p.nodes
:= by
  have ⟨nl, hnl, hfst⟩ := List.mem_map.mp h
  exact ⟨nl.2, by rw [← hfst] at *; exact (List.mem_filter.mp hnl).1⟩


theorem pruneGo_keeps_tt {ce : Expr → Bool} {p : Path} :
  ∀ (ps : List Path) (covered : List Node), p ∈ ps → p.leaf = .tt →
    p.cube ∈ pruneGo ce covered ps
:= by
  intro ps
  induction ps with
  | nil => intro covered h; cases h
  | cons q rest ih =>
    intro covered hmem hleaf
    cases List.mem_cons.mp hmem with
    | inl heq =>
      subst heq
      rw [pruneGo_cons_tt hleaf]
      simp
    | inr hrest =>
      by_cases hq : q.leaf = .tt
      · rw [pruneGo_cons_tt hq]
        exact List.mem_cons.mpr (.inr (ih covered hrest hleaf))
      · by_cases hemp : (uncoveredOf ce covered q).isEmpty = true
        · rw [pruneGo_cons_drop hq hemp]
          exact ih covered hrest hleaf
        · rw [pruneGo_cons_keep hq hemp]
          exact List.mem_cons.mpr (.inr (ih _ hrest hleaf))

theorem prune_keeps_tt {ce : Expr → Bool} {ps : List Path} {p : Path}
  (hmem : p ∈ ps) (hleaf : p.leaf = .tt) :
  p.cube ∈ prune ps ce
:= pruneGo_keeps_tt ps _ hmem hleaf

theorem pruneGo_shape {ce : Expr → Bool} {c : Cube} :
  ∀ (ps : List Path) (covered : List Node), c ∈ pruneGo ce covered ps →
    ∃ p ∈ ps, c = p.cube
:= by
  intro ps
  induction ps with
  | nil => intro covered h; cases h
  | cons q rest ih =>
    intro covered hmem
    by_cases hq : q.leaf = .tt
    · rw [pruneGo_cons_tt hq] at hmem
      cases List.mem_cons.mp hmem with
      | inl heq => exact ⟨q, by simp, heq⟩
      | inr hrest =>
        have ⟨p, hp, hc⟩ := ih covered hrest
        exact ⟨p, by simp [hp], hc⟩
    · by_cases hemp : (uncoveredOf ce covered q).isEmpty = true
      · rw [pruneGo_cons_drop hq hemp] at hmem
        have ⟨p, hp, hc⟩ := ih covered hmem
        exact ⟨p, by simp [hp], hc⟩
      · rw [pruneGo_cons_keep hq hemp] at hmem
        cases List.mem_cons.mp hmem with
        | inl heq => exact ⟨q, by simp, heq⟩
        | inr hrest =>
          have ⟨p, hp, hc⟩ := ih _ hrest
          exact ⟨p, by simp [hp], hc⟩

theorem prune_shape {ce : Expr → Bool} {ps : List Path} {c : Cube}
  (hmem : c ∈ prune ps ce) :
  ∃ p ∈ ps, c = p.cube
:= pruneGo_shape ps _ hmem

/-- The pruned cubes are a sublist of all the cubes, in order. -/
theorem pruneGo_sublist {ce : Expr → Bool} :
  ∀ (ps : List Path) (covered : List Node),
    (pruneGo ce covered ps).Sublist (ps.map Path.cube)
:= by
  intro ps
  induction ps with
  | nil => intro covered; simp [pruneGo]
  | cons q rest ih =>
    intro covered
    by_cases hq : q.leaf = .tt
    · rw [pruneGo_cons_tt hq, List.map_cons]
      exact (ih covered).cons_cons q.cube
    · by_cases hemp : (uncoveredOf ce covered q).isEmpty = true
      · rw [pruneGo_cons_drop hq hemp, List.map_cons]
        exact (ih covered).cons q.cube
      · rw [pruneGo_cons_keep hq hemp, List.map_cons]
        exact (ih _).cons_cons q.cube

/-- A node with a `canError` atom that lies on some path lies on some kept
cube, provided it is not already covered. -/
theorem pruneGo_covers {ce : Expr → Bool} {n : Node} (hce : ce n.atom = true) :
  ∀ (ps : List Path) (covered : List Node),
    (∃ p ∈ ps, ∃ l, (n, l) ∈ p.nodes) → n ∉ covered →
    ∃ c ∈ pruneGo ce covered ps, ∃ l, (n, l) ∈ nodesFrom [] c.literals
:= by
  intro ps
  induction ps with
  | nil =>
    intro covered h
    obtain ⟨p, hp, _⟩ := h
    cases hp
  | cons q rest ih =>
    intro covered hex hnc
    by_cases hq : q.leaf = .tt
    · rw [pruneGo_cons_tt hq]
      obtain ⟨p, hp, l, hl⟩ := hex
      cases List.mem_cons.mp hp with
      | inl heq =>
        subst heq
        exact ⟨p.cube, by simp, l, by rw [cube_nodes_eq]; exact hl⟩
      | inr hrest =>
        have ⟨c, hc, hcn⟩ := ih covered ⟨p, hrest, l, hl⟩ hnc
        exact ⟨c, List.mem_cons.mpr (.inr hc), hcn⟩
    · by_cases hqn : ∃ l, (n, l) ∈ q.nodes
      · obtain ⟨l, hl⟩ := hqn
        have hfilter : (n, l) ∈ q.nodes.filter
            (fun (n', l') => !covered.contains n' && ce l'.atom) := by
          apply List.mem_filter.mpr
          refine ⟨hl, ?_⟩
          show (!covered.contains n && ce l.atom) = true
          have h₁ : covered.contains n = false := by
            simp only [List.contains_eq_mem, decide_eq_false_iff_not]
            exact hnc
          have h₂ : ce l.atom = true := by
            rw [← node_atom_of_mem hl]
            exact hce
          rw [h₁, h₂]
          rfl
        have hemp : ¬ (uncoveredOf ce covered q).isEmpty = true := by
          intro hnil
          rw [List.isEmpty_iff] at hnil
          have : n ∈ uncoveredOf ce covered q :=
            List.mem_map.mpr ⟨(n, l), hfilter, rfl⟩
          rw [hnil] at this
          cases this
        rw [pruneGo_cons_keep hq hemp]
        exact ⟨q.cube, by simp, l, by rw [cube_nodes_eq]; exact hl⟩
      · obtain ⟨p, hp, l, hl⟩ := hex
        have hprest : p ∈ rest := by
          cases List.mem_cons.mp hp with
          | inl heq => exact absurd ⟨l, heq ▸ hl⟩ hqn
          | inr h => exact h
        by_cases hemp : (uncoveredOf ce covered q).isEmpty = true
        · rw [pruneGo_cons_drop hq hemp]
          exact ih covered ⟨p, hprest, l, hl⟩ hnc
        · rw [pruneGo_cons_keep hq hemp]
          have hnc' : n ∉ covered ++ uncoveredOf ce covered q := by
            intro hmem
            cases List.mem_append.mp hmem with
            | inl h => exact hnc h
            | inr h => exact hqn (uncoveredOf_sub h)
          have ⟨c, hc, hcn⟩ := ih _ ⟨p, hprest, l, hl⟩ hnc'
          exact ⟨c, List.mem_cons.mpr (.inr hc), hcn⟩

/-- Top-level coverage: a `canError` node on some path lies on some kept
cube. -/
theorem prune_covers {ce : Expr → Bool} {ps : List Path} {n : Node}
  (hce : ce n.atom = true)
  (hex : ∃ p ∈ ps, ∃ l, (n, l) ∈ p.nodes) :
  ∃ c ∈ prune ps ce, ∃ l, (n, l) ∈ nodesFrom [] c.literals
:= by
  by_cases hcov : n ∈ (ps.filter fun p => p.leaf == .tt).flatMap fun p => p.nodes.map Prod.fst
  · have ⟨p, hp, hn⟩ := List.mem_flatMap.mp hcov
    have hpmem := (List.mem_filter.mp hp).1
    have hpleaf : p.leaf = .tt := by
      have := (List.mem_filter.mp hp).2
      simpa using this
    have ⟨nl, hnl, hfst⟩ := List.mem_map.mp hn
    refine ⟨p.cube, prune_keeps_tt hpmem hpleaf, nl.2, ?_⟩
    rw [cube_nodes_eq, ← hfst]
    simpa using hnl
  · exact pruneGo_covers hce ps _ hex hcov

/-! ### The pruned disjunction interprets like the expression -/

/-- A literal of a node of a path is a literal of the path. -/
theorem lit_of_node_mem {pre : List (Expr × Bool)} {ls : List Literal}
  {n : Node} {l : Literal} (h : (n, l) ∈ nodesFrom pre ls) :
  l ∈ ls
:= by
  have ⟨xs, ys, hsplit, _⟩ := mem_nodesFrom h
  rw [hsplit]
  simp

theorem orInterp_prune_eq_interp {e : Expr} {v : Expr → Outcome}
  {ce : Expr → Bool}
  (h : ∀ a ∈ atoms e, ce a = false → interp v a ≠ .err) :
  orInterp v (prune (paths e) ce) = interp v e
:= by
  obtain ⟨mT, mF, mE⟩ := master e v
  cases hi : interp v e with
  | tt =>
    obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, _, hnoerr⟩ := mT hi
    apply orInterp_eq_tt (prune_keeps_tt hp₀ (by simpa [leafOf] using hp₀leaf))
      (pathInterp_of_pass_tt hp₀pass (by simpa [leafOf] using hp₀leaf))
    intro c hc herr
    have ⟨p, hp, hcp⟩ := prune_shape hc
    subst hcp
    exact hnoerr p hp (pathInterp_err_inv herr)
  | ff =>
    obtain ⟨_, hB, hnoerr⟩ := mF hi
    apply orInterp_eq_ff
    intro c hc
    have ⟨p, hp, hcp⟩ := prune_shape hc
    subst hcp
    cases hpi : litsInterp v p.literals with
    | err => exact absurd hpi (hnoerr p hp)
    | ff => exact pathInterp_of_ff hpi
    | tt =>
      apply pathInterp_of_pass_ne_tt hpi
      intro htt
      exact hB p hp (by simpa [leafOf] using htt) hpi
  | err =>
    obtain ⟨hnopass, n, hnpre, hnerr, hex, _⟩ := mE hi
    have hce : ce n.atom = true := by
      by_contra hcef
      obtain ⟨p₁, hp₁, l₁, hn₁⟩ := hex
      have hatom : n.atom ∈ atoms e := by
        rw [node_atom_of_mem hn₁]
        exact paths_atoms_sub hp₁ (lit_of_node_mem hn₁)
      exact h n.atom hatom (by simpa using hcef) hnerr
    obtain ⟨c, hc, l', hl'⟩ := prune_covers hce hex
    apply orInterp_eq_err hc (cubeInterp_of_err (litsInterp_err_of_node hl' hnpre hnerr))
    intro c' hc' htt
    have ⟨p, hp, hcp⟩ := prune_shape hc'
    subst hcp
    have ⟨hpass, hleaf⟩ := pathInterp_tt_inv htt
    exact hnopass p hp (.inl hleaf) hpass

/-- The unpruned disjunction — every path as a cube — also interprets like
the expression. -/
theorem orInterp_paths_eq_interp (e : Expr) (v : Expr → Outcome) :
  orInterp v ((paths e).map Path.cube) = interp v e
:= by
  obtain ⟨mT, mF, mE⟩ := master e v
  cases hi : interp v e with
  | tt =>
    obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, _, hnoerr⟩ := mT hi
    apply orInterp_eq_tt (List.mem_map.mpr ⟨p₀, hp₀, rfl⟩)
      (pathInterp_of_pass_tt hp₀pass (by simpa [leafOf] using hp₀leaf))
    intro c hc herr
    have ⟨p, hp, hcp⟩ := List.mem_map.mp hc
    subst hcp
    exact hnoerr p hp (pathInterp_err_inv herr)
  | ff =>
    obtain ⟨_, hB, hnoerr⟩ := mF hi
    apply orInterp_eq_ff
    intro c hc
    have ⟨p, hp, hcp⟩ := List.mem_map.mp hc
    subst hcp
    cases hpi : litsInterp v p.literals with
    | err => exact absurd hpi (hnoerr p hp)
    | ff => exact pathInterp_of_ff hpi
    | tt =>
      apply pathInterp_of_pass_ne_tt hpi
      intro htt
      exact hB p hp (by simpa [leafOf] using htt) hpi
  | err =>
    obtain ⟨hnopass, n, hnpre, hnerr, ⟨p₁, hp₁, l₁, hn₁⟩, _⟩ := mE hi
    apply orInterp_eq_err (List.mem_map.mpr ⟨p₁, hp₁, rfl⟩)
      (cubeInterp_of_err (litsInterp_err_of_node hn₁ hnpre hnerr))
    intro c' hc' htt
    have ⟨p, hp, hcp⟩ := List.mem_map.mp hc'
    subst hcp
    have ⟨hpass, hleaf⟩ := pathInterp_tt_inv htt
    exact hnopass p hp (.inl hleaf) hpass

/-- **Equivalence, abstract**: the DNF of `e` interprets exactly like `e`
under every valuation on which the `canError` answers are correct. -/
theorem interp_dnf {e : Expr} {v : Expr → Outcome} {canError : Expr → Bool}
  (h : ∀ a ∈ atoms e, canError a = false → interp v a ≠ .err) :
  interp v (dnf e canError) = interp v e
:= by
  rw [dnf, interp_toExpr]
  exact orInterp_prune_eq_interp h

/-- `dnfOfExpr` interprets exactly like `e` under every valuation. -/
theorem interp_dnfOfExpr (e : Expr) (v : Expr → Outcome) :
  interp v (dnfOfExpr e) = interp v e
:= interp_dnf (by simp)

/-- **At most one cube is ever true**: the cubes of the DNF are pairwise
exclusive, under every valuation — cube order is irrelevant. -/
theorem dnf_cubes_exclusive (e : Expr) (canError : Expr → Bool) :
  (prune (paths e) canError).Pairwise
    fun c₁ c₂ => ∀ v, ¬(c₁.interp v = .tt ∧ c₂.interp v = .tt)
:= by
  have hcubes : ((paths e).map Path.cube).Pairwise
      (fun c₁ c₂ => ∀ v, ¬(c₁.interp v = .tt ∧ c₂.interp v = .tt)) := by
    refine List.Pairwise.map _ ?_ (paths_exclusive e)
    intro p q hpq v ⟨hp, hq⟩
    have ⟨hppass, hpleaf⟩ := pathInterp_tt_inv (p := p) hp
    have ⟨hqpass, hqleaf⟩ := pathInterp_tt_inv (p := q) hq
    exact conflict_not_both_pass (hpq (.inl hpleaf) (.inl hqleaf)) ⟨hppass, hqpass⟩
  exact List.Pairwise.sublist (pruneGo_sublist _ _) hcubes

end Cedar.DNF
