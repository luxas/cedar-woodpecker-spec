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

import Cedar.Thm.DNF.Extend

/-!
Structural invariants of `paths`: the list is never empty, every path's
literals have distinct atoms drawn from the expression's atoms, and — the
*exclusivity* invariant — any two distinct paths with real (`tt`/`ff`) leaves
contradict each other on some atom, so no valuation can pass both. The file
also packages the shifted erring node of `Cedar.Thm.DNF.Extend` at the path
level, and characterizes membership in grafted path lists.
-/

namespace Cedar.DNF

open Cedar.Spec

/-! ### Membership in grafted lists -/

theorem mem_graft_iff {ls sub : List Path} {at_ : Leaf} {q : Path} :
  q ∈ graft ls at_ sub ↔
    (q ∈ ls ∧ q.leaf ≠ at_) ∨
    (∃ p ∈ ls, p.leaf = at_ ∧ ∃ s ∈ sub, q = p.extended s)
:= by
  simp only [graft, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hq⟩
    by_cases hleaf : p.leaf = at_
    · rw [if_pos (by simp [hleaf])] at hq
      have ⟨s, hs, hqs⟩ := List.mem_map.mp hq
      exact .inr ⟨p, hp, hleaf, s, hs, hqs.symm⟩
    · rw [if_neg (by simp [hleaf])] at hq
      simp at hq
      subst hq
      exact .inl ⟨hp, hleaf⟩
  · rintro (⟨hq, hleaf⟩ | ⟨p, hp, hleaf, s, hs, hqs⟩)
    · exact ⟨q, hq, by rw [if_neg (by simp [hleaf])]; simp⟩
    · exact ⟨p, hp, by
        rw [if_pos (by simp [hleaf])]
        exact List.mem_map.mpr ⟨s, hs, hqs.symm⟩⟩

/-- The `ite` arm of `paths`, as its own function so membership can be
characterized. -/
def itePaths (pc pt pe : List Path) : List Path :=
  pc.flatMap fun p =>
    match p.leaf with
    | .tt            => pt.map p.extended
    | .ff            => pe.map p.extended
    | .contradiction => [p]

theorem paths_ite_def (c t e : Expr) :
  paths (.ite c t e) = itePaths (paths c) (paths t) (paths e)
:= rfl

theorem mem_itePaths_iff {pc pt pe : List Path} {q : Path} :
  q ∈ itePaths pc pt pe ↔
    (∃ p ∈ pc, p.leaf = .tt ∧ ∃ s ∈ pt, q = p.extended s) ∨
    (∃ p ∈ pc, p.leaf = .ff ∧ ∃ s ∈ pe, q = p.extended s) ∨
    (q ∈ pc ∧ q.leaf = .contradiction)
:= by
  simp only [itePaths, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hq⟩
    cases hleaf : p.leaf <;> rw [hleaf] at hq
    · have ⟨s, hs, hqs⟩ := List.mem_map.mp hq
      exact .inl ⟨p, hp, hleaf, s, hs, hqs.symm⟩
    · have ⟨s, hs, hqs⟩ := List.mem_map.mp hq
      exact .inr (.inl ⟨p, hp, hleaf, s, hs, hqs.symm⟩)
    · simp at hq
      subst hq
      exact .inr (.inr ⟨hp, hleaf⟩)
  · rintro (⟨p, hp, hleaf, s, hs, hqs⟩ | ⟨p, hp, hleaf, s, hs, hqs⟩ | ⟨hq, hleaf⟩)
    · exact ⟨p, hp, by rw [hleaf]; exact List.mem_map.mpr ⟨s, hs, hqs.symm⟩⟩
    · exact ⟨p, hp, by rw [hleaf]; exact List.mem_map.mpr ⟨s, hs, hqs.symm⟩⟩
    · exact ⟨q, hq, by rw [hleaf]; simp⟩

/-! ### Basic structural invariants -/

theorem paths_ne_nil (e : Expr) : paths e ≠ []
:= by
  match e with
  | .lit (.bool b) => simp [paths]
  | .unaryApp .not x =>
    have := paths_ne_nil x
    simp [paths, this]
  | .and l r =>
    have hl := paths_ne_nil l
    intro h
    simp only [paths, graft] at h
    rw [List.flatMap_eq_nil_iff] at h
    match hps : paths l with
    | [] => exact hl hps
    | p :: _ =>
      have := h p (by rw [hps]; simp)
      by_cases hleaf : p.leaf = .tt
      · rw [if_pos (by simp [hleaf])] at this
        rw [List.map_eq_nil_iff] at this
        exact paths_ne_nil r this
      · rw [if_neg (by simp [hleaf])] at this
        cases this
  | .or l r =>
    have hl := paths_ne_nil l
    intro h
    simp only [paths, graft] at h
    rw [List.flatMap_eq_nil_iff] at h
    match hps : paths l with
    | [] => exact hl hps
    | p :: _ =>
      have := h p (by rw [hps]; simp)
      by_cases hleaf : p.leaf = .ff
      · rw [if_pos (by simp [hleaf])] at this
        rw [List.map_eq_nil_iff] at this
        exact paths_ne_nil r this
      · rw [if_neg (by simp [hleaf])] at this
        cases this
  | .ite c t e' =>
    have hc := paths_ne_nil c
    intro h
    rw [paths_ite_def] at h
    simp only [itePaths] at h
    rw [List.flatMap_eq_nil_iff] at h
    match hps : paths c with
    | [] => exact hc hps
    | p :: _ =>
      have := h p (by rw [hps]; simp)
      cases hleaf : p.leaf <;> rw [hleaf] at this
      · rw [List.map_eq_nil_iff] at this
        exact paths_ne_nil t this
      · rw [List.map_eq_nil_iff] at this
        exact paths_ne_nil e' this
      · cases this
  | .lit (.int _) => simp [paths]
  | .lit (.string _) => simp [paths]
  | .lit (.entityUID _) => simp [paths]
  | .var _ => simp [paths]
  | .unaryApp .neg _ => simp [paths]
  | .unaryApp .isEmpty _ => simp [paths]
  | .unaryApp (.like _) _ => simp [paths]
  | .unaryApp (.is _) _ => simp [paths]
  | .binaryApp _ _ _ => simp [paths]
  | .getAttr _ _ => simp [paths]
  | .hasAttr _ _ => simp [paths]
  | .set _ => simp [paths]
  | .record _ => simp [paths]
  | .call _ _ => simp [paths]

/-- Every path's literals have pairwise-distinct atoms. -/
theorem paths_nodup {e : Expr} {p : Path} (hp : p ∈ paths e) :
  (p.literals.map (·.atom)).Nodup
:= by
  match e with
  | .lit (.bool b) =>
    simp [paths, Path.ofLeaf] at hp
    subst hp
    simp
  | .unaryApp .not x =>
    simp only [paths] at hp
    have ⟨q, hq, hqp⟩ := List.mem_map.mp hp
    subst hqp
    show ((q.literals).map (·.atom)).Nodup
    exact paths_nodup (e := x) hq
  | .and l r =>
    rw [(rfl : paths (.and l r) = graft (paths l) .tt (paths r))] at hp
    cases mem_graft_iff.mp hp with
    | inl h => exact paths_nodup h.1
    | inr h =>
      have ⟨q, hq, _, s, _, hqs⟩ := h
      subst hqs
      exact extendLits_nodup (paths_nodup hq)
  | .or l r =>
    rw [(rfl : paths (.or l r) = graft (paths l) .ff (paths r))] at hp
    cases mem_graft_iff.mp hp with
    | inl h => exact paths_nodup h.1
    | inr h =>
      have ⟨q, hq, _, s, _, hqs⟩ := h
      subst hqs
      exact extendLits_nodup (paths_nodup hq)
  | .ite c t e' =>
    rw [paths_ite_def] at hp
    rcases mem_itePaths_iff.mp hp with ⟨q, hq, _, s, _, hqs⟩ | ⟨q, hq, _, s, _, hqs⟩ | ⟨hq, _⟩
    · subst hqs; exact extendLits_nodup (paths_nodup hq)
    · subst hqs; exact extendLits_nodup (paths_nodup hq)
    · exact paths_nodup hq
  | .lit (.int _) => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .lit (.string _) => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .lit (.entityUID _) => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .var _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .unaryApp .neg _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .unaryApp .isEmpty _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .unaryApp (.like _) _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .unaryApp (.is _) _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .binaryApp _ _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .getAttr _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .hasAttr _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .set _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .record _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)
  | .call _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp)

/-- Every literal's atom of every path is an atom of the expression. -/
theorem paths_atoms_sub {e : Expr} {p : Path} {l : Literal}
  (hp : p ∈ paths e) (hl : l ∈ p.literals) :
  l.atom ∈ atoms e
:= by
  match e with
  | .lit (.bool b) =>
    simp [paths, Path.ofLeaf] at hp
    subst hp
    cases hl
  | .unaryApp .not x =>
    simp only [paths] at hp
    have ⟨q, hq, hqp⟩ := List.mem_map.mp hp
    subst hqp
    exact paths_atoms_sub (e := x) hq hl
  | .and l' r =>
    rw [(rfl : paths (.and l' r) = graft (paths l') .tt (paths r))] at hp
    show l.atom ∈ atoms l' ++ atoms r
    rw [List.mem_append]
    cases mem_graft_iff.mp hp with
    | inl h => exact .inl (paths_atoms_sub h.1 hl)
    | inr h =>
      have ⟨q, hq, _, s, hs, hqs⟩ := h
      subst hqs
      have ⟨t, ht, hmem⟩ := extendLits_prefix q.literals s.leaf s.literals
      simp only [Path.extended] at hl
      rw [ht] at hl
      cases List.mem_append.mp hl with
      | inl h' => exact .inl (paths_atoms_sub hq h')
      | inr h' => exact .inr (paths_atoms_sub hs (hmem l h'))
  | .or l' r =>
    rw [(rfl : paths (.or l' r) = graft (paths l') .ff (paths r))] at hp
    show l.atom ∈ atoms l' ++ atoms r
    rw [List.mem_append]
    cases mem_graft_iff.mp hp with
    | inl h => exact .inl (paths_atoms_sub h.1 hl)
    | inr h =>
      have ⟨q, hq, _, s, hs, hqs⟩ := h
      subst hqs
      have ⟨t, ht, hmem⟩ := extendLits_prefix q.literals s.leaf s.literals
      simp only [Path.extended] at hl
      rw [ht] at hl
      cases List.mem_append.mp hl with
      | inl h' => exact .inl (paths_atoms_sub hq h')
      | inr h' => exact .inr (paths_atoms_sub hs (hmem l h'))
  | .ite c t e' =>
    rw [paths_ite_def] at hp
    show l.atom ∈ atoms c ++ atoms t ++ atoms e'
    rcases mem_itePaths_iff.mp hp with ⟨q, hq, _, s, hs, hqs⟩ | ⟨q, hq, _, s, hs, hqs⟩ | ⟨hq, _⟩
    · subst hqs
      have ⟨t', ht', hmem⟩ := extendLits_prefix q.literals s.leaf s.literals
      simp only [Path.extended] at hl
      rw [ht'] at hl
      rw [List.append_assoc, List.mem_append]
      cases List.mem_append.mp hl with
      | inl h' => exact .inl (paths_atoms_sub hq h')
      | inr h' => exact .inr (by rw [List.mem_append]; exact .inl (paths_atoms_sub hs (hmem l h')))
    · subst hqs
      have ⟨t', ht', hmem⟩ := extendLits_prefix q.literals s.leaf s.literals
      simp only [Path.extended] at hl
      rw [ht'] at hl
      rw [List.append_assoc, List.mem_append]
      cases List.mem_append.mp hl with
      | inl h' => exact .inl (paths_atoms_sub hq h')
      | inr h' => exact .inr (by rw [List.mem_append]; exact .inr (paths_atoms_sub hs (hmem l h')))
    · rw [List.append_assoc, List.mem_append]
      exact .inl (paths_atoms_sub hq hl)
  | .lit (.int _) => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .lit (.string _) => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .lit (.entityUID _) => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .var _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .unaryApp .neg _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .unaryApp .isEmpty _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .unaryApp (.like _) _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .unaryApp (.is _) _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .binaryApp _ _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .getAttr _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .hasAttr _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .set _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .record _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])
  | .call _ _ => simp [paths] at hp; rcases hp with h | h <;> (subst h; simp_all [atoms])

/-! ### Both parts passing: extension passes with the suffix's leaf -/

theorem extendLits_pass_pass {v : Expr → Outcome} {acc : List Literal}
  {leaf : Leaf} {rest : List Literal}
  (hacc : litsInterp v acc = .tt) (hrest : litsInterp v rest = .tt) :
  litsInterp v (extendLits acc leaf rest).literals = .tt ∧
  (extendLits acc leaf rest).leaf = leaf
:= by
  induction rest generalizing acc with
  | nil => exact ⟨hacc, rfl⟩
  | cons l rest' ih =>
    have hl : l.holds v = .tt := by
      simp only [litsInterp] at hrest
      exact (Outcome.and_eq_tt.mp hrest).1
    have hrest' : litsInterp v rest' = .tt := by
      simp only [litsInterp] at hrest
      exact (Outcome.and_eq_tt.mp hrest).2
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf]
      apply ih ?_ hrest'
      rw [litsInterp_append]
      simp [hacc, litsInterp, hl, Outcome.and]
    | some seen =>
      have ⟨hseen_mem, hseen_atom⟩ := find?_atom_spec hf
      have hseen_tt : seen.holds v = .tt := litsInterp_eq_tt.mp hacc seen hseen_mem
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn]
        exact ih hacc hrest'
      · exfalso
        have hflip := holds_flip (v := v) (l := l) (l' := seen)
          hseen_atom.symm (fun h => hn h.symm)
        rw [hflip, hseen_tt] at hl
        cases hl

theorem extended_pass_pass {v : Expr → Outcome} {p s : Path}
  (hp : litsInterp v p.literals = .tt) (hs : litsInterp v s.literals = .tt) :
  litsInterp v (p.extended s).literals = .tt ∧ (p.extended s).leaf = s.leaf
:= extendLits_pass_pass hp hs

/-! ### The shifted erring node, at the path level -/

/-- The node at which an erring node `n` of a suffix reappears after
extension by `p`; depends only on `p` and `n`. -/
def shiftNode (p : Path) (n : Node) : Node :=
  ⟨pairs p.literals ++ n.pre.filter (fun pr => !(p.literals.map (·.atom)).contains pr.1),
   n.atom⟩

theorem pairs_filter_atoms (xs : List Literal) (f : Expr → Bool) :
  pairs (xs.filter fun x => f x.atom) = (pairs xs).filter fun pr => f pr.1
:= by
  simp only [pairs, List.filter_map]
  rfl

theorem holds_of_pairs_pass {v : Expr → Outcome} {xs : List Literal}
  (h : pairsPass v (pairs xs)) :
  ∀ x ∈ xs, x.holds v = .tt
:= by
  intro x hx
  apply holds_eq_tt.mpr
  exact h (x.atom, x.negated) (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem shiftNode_atom (p : Path) (n : Node) : (shiftNode p n).atom = n.atom := rfl

theorem shiftNode_pairsPass {v : Expr → Outcome} {p : Path} {n : Node}
  (hp : litsInterp v p.literals = .tt) (hpre : pairsPass v n.pre) :
  pairsPass v (shiftNode p n).pre
:= pairsPass_append (pairsPass_of_litsInterp_tt hp) (pairsPass_filter hpre)

/-- If `p` passes and `s` (with distinct atoms) contains the erring node `n`,
the extension contains `shiftNode p n`. -/
theorem extended_shift_node {v : Expr → Outcome} {p s : Path} {n : Node} {l : Literal}
  (hp : litsInterp v p.literals = .tt)
  (hnodup : (s.literals.map (·.atom)).Nodup)
  (hmem : (n, l) ∈ s.nodes)
  (hpre : pairsPass v n.pre) (herr : interp v n.atom = .err) :
  (shiftNode p n, l) ∈ (p.extended s).nodes
:= by
  have ⟨xs, ys, hsplit, hn⟩ := mem_nodesFrom hmem
  have hnpre : n.pre = pairs xs := by rw [hn]; simp
  have hnatom : n.atom = l.atom := by rw [hn]
  have hxs : ∀ x ∈ xs, x.holds v = .tt :=
    holds_of_pairs_pass (hnpre ▸ hpre)
  have hlerr : l.holds v = .err := holds_eq_err.mpr (hnatom ▸ herr)
  have hshift := extendLits_shift (leaf := s.leaf) (ys := ys) hlerr
    xs p.literals (litsInterp_eq_tt.mp hp) hxs (by rw [← hsplit]; exact hnodup)
  show (shiftNode p n, l) ∈ nodesFrom []
    (extendLits p.literals s.leaf s.literals).literals
  rw [hsplit]
  have hpre_eq : (shiftNode p n).pre =
      pairs p.literals ++
        pairs (xs.filter fun x => !(p.literals.map (·.atom)).contains x.atom) := by
    simp only [shiftNode, hnpre]
    rw [pairs_filter_atoms xs (fun a => !(p.literals.map (·.atom)).contains a)]
  have : shiftNode p n =
      ⟨pairs p.literals ++
        pairs (xs.filter fun x => !(p.literals.map (·.atom)).contains x.atom), l.atom⟩ := by
    cases hs : shiftNode p n
    simp only [Node.mk.injEq]
    constructor
    · have := hpre_eq
      rw [hs] at this
      exact this
    · have := shiftNode_atom p n
      rw [hs] at this
      simp at this
      rw [this, hnatom]
  rw [this]
  exact hshift

/-- Nodes survive extension (path level). -/
theorem extended_nodes_mono {p s : Path} {n : Node} {l : Literal}
  (h : (n, l) ∈ p.nodes) :
  (n, l) ∈ (p.extended s).nodes
:= extendLits_nodes_mono h

/-! ### Exclusivity: distinct real-leaf paths conflict -/

/-- Two paths contradict each other on some atom. -/
def Conflict (p q : Path) : Prop :=
  ∃ x b, (⟨x, b⟩ : Literal) ∈ p.literals ∧ (⟨x, !b⟩ : Literal) ∈ q.literals

/-- The path ends in a real (`tt`/`ff`) leaf. -/
def RealLeaf (p : Path) : Prop :=
  p.leaf = .tt ∨ p.leaf = .ff

theorem RealLeaf.ne_contradiction {p : Path} (h : RealLeaf p) :
  p.leaf ≠ .contradiction
:= by cases h <;> simp_all

theorem realLeaf_flipped {p : Path} : RealLeaf p.flipped ↔ RealLeaf p
:= by
  cases hl : p.leaf <;> simp [RealLeaf, Path.flipped, hl]

theorem conflict_symm {p q : Path} (h : Conflict p q) : Conflict q p
:= by
  have ⟨x, b, hp, hq⟩ := h
  exact ⟨x, !b, hq, by simpa using hp⟩

/-- Conflicting paths cannot both pass. -/
theorem conflict_not_both_pass {v : Expr → Outcome} {p q : Path}
  (h : Conflict p q) :
  ¬(litsInterp v p.literals = .tt ∧ litsInterp v q.literals = .tt)
:= by
  rintro ⟨hp, hq⟩
  have ⟨x, b, hxp, hxq⟩ := h
  have h₁ := litsInterp_eq_tt.mp hp _ hxp
  have h₂ := litsInterp_eq_tt.mp hq _ hxq
  have hflip := holds_flip (v := v) (l := (⟨x, !b⟩ : Literal)) (l' := (⟨x, b⟩ : Literal))
    rfl (by simp)
  rw [h₂, h₁] at hflip
  cases hflip

/-- Invariant X: any two distinct real-leaf paths conflict. -/
def Exclusive (ps : List Path) : Prop :=
  ps.Pairwise fun p q => RealLeaf p → RealLeaf q → Conflict p q

theorem pairwise_of_mem_ne {α : Type} {R : α → α → Prop}
  (hsymm : ∀ a b, R a b → R b a) {l : List α}
  (h : l.Pairwise R) {a b : α}
  (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
  R a b
:= by
  induction l with
  | nil => cases ha
  | cons x rest ih =>
    have ⟨hx, hrest⟩ := List.pairwise_cons.mp h
    cases List.mem_cons.mp ha with
    | inl haeq =>
      cases List.mem_cons.mp hb with
      | inl hbeq => exact absurd (haeq.trans hbeq.symm) hne
      | inr hbrest => exact haeq ▸ hx b hbrest
    | inr harest =>
      cases List.mem_cons.mp hb with
      | inl hbeq => exact hbeq ▸ hsymm _ _ (hx a harest)
      | inr hbrest => exact ih hrest harest hbrest

/-- Two distinct real-leaf members of an exclusive list cannot both pass;
equivalently, real-leaf passers are unique as values. -/
theorem exclusive_eq_of_pass {v : Expr → Outcome} {ps : List Path}
  (hX : Exclusive ps) {p q : Path}
  (hp : p ∈ ps) (hq : q ∈ ps)
  (hpr : RealLeaf p) (hqr : RealLeaf q)
  (hpp : litsInterp v p.literals = .tt) (hqp : litsInterp v q.literals = .tt) :
  p = q
:= by
  by_contra hne
  have hR := pairwise_of_mem_ne
    (fun a b hab hbr har => conflict_symm (hab har hbr)) hX hp hq hne
  exact conflict_not_both_pass (hR hpr hqr) ⟨hpp, hqp⟩

theorem pairwise_flatMap {α β : Type} {R : β → β → Prop} {f : α → List β}
  {l : List α}
  (hin : ∀ a ∈ l, (f a).Pairwise R)
  (hcross : l.Pairwise fun a b => ∀ x ∈ f a, ∀ y ∈ f b, R x y) :
  (l.flatMap f).Pairwise R
:= by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have ⟨hc, hrest⟩ := List.pairwise_cons.mp hcross
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨hin a (by simp), ih (fun b hb => hin b (by simp [hb])) hrest, ?_⟩
    intro x hx y hy
    have ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
    exact hc b hb x hx y hyb

/-- Conflicts lift through extension on the left. -/
theorem conflict_extended_left {p q s : Path} (h : Conflict p q) :
  Conflict (p.extended s) q
:= by
  have ⟨x, b, hp, hq⟩ := h
  exact ⟨x, b, extendLits_mem_of_acc hp, hq⟩

theorem conflict_extended_right {p q s : Path} (h : Conflict p q) :
  Conflict p (q.extended s)
:= by
  have ⟨x, b, hp, hq⟩ := h
  exact ⟨x, b, hp, extendLits_mem_of_acc hq⟩

/-- A conflict between suffixes survives extension by the same prefix, unless
one side truncated. -/
theorem conflict_extended_both {p s₁ s₂ : Path} (h : Conflict s₁ s₂) :
  Conflict (p.extended s₁) (p.extended s₂) ∨
  (p.extended s₁).leaf = .contradiction ∨
  (p.extended s₂).leaf = .contradiction
:= by
  have ⟨x, b, h₁, h₂⟩ := h
  cases extendLits_lit_survives (acc := p.literals) (leaf := s₁.leaf) h₁ with
  | inr hc => exact .inr (.inl hc)
  | inl hm₁ =>
    cases extendLits_lit_survives (acc := p.literals) (leaf := s₂.leaf) h₂ with
    | inr hc => exact .inr (.inr hc)
    | inl hm₂ => exact .inl ⟨x, b, hm₁, hm₂⟩

/-- A real-leafed extension has the suffix's (real) leaf. -/
theorem extended_leaf_real {p s : Path} (h : RealLeaf (p.extended s)) :
  RealLeaf s ∧ (p.extended s).leaf = s.leaf
:= by
  cases extendLits_leaf p.literals s.leaf s.literals with
  | inl heq =>
    have hleaf : (p.extended s).leaf = s.leaf := heq
    refine ⟨?_, hleaf⟩
    rw [RealLeaf, ← hleaf]
    exact h
  | inr hC => exact absurd hC h.ne_contradiction

theorem atom_paths_exclusive (x : Expr) :
  Exclusive [⟨[⟨x, false⟩], .tt⟩, ⟨[⟨x, true⟩], .ff⟩]
:= by
  refine .cons ?_ (.cons (by intro q hq; cases hq) .nil)
  intro q hq _ _
  simp at hq
  subst hq
  exact ⟨x, false, by simp, by simp⟩

/-- Extending every path of an exclusive list by the same prefix keeps it
exclusive. -/
theorem extended_map_exclusive {p : Path} {sub : List Path}
  (hsub : Exclusive sub) :
  (sub.map p.extended).Pairwise fun x y => RealLeaf x → RealLeaf y → Conflict x y
:= by
  refine List.Pairwise.map _ ?_ hsub
  intro s₁ s₂ hs hr₁ hr₂
  have hr₁' := (extended_leaf_real hr₁).1
  have hr₂' := (extended_leaf_real hr₂).1
  cases conflict_extended_both (p := p) (hs hr₁' hr₂') with
  | inl h => exact h
  | inr h =>
    cases h with
    | inl h => exact absurd h hr₁.ne_contradiction
    | inr h => exact absurd h hr₂.ne_contradiction

theorem graft_exclusive {ls sub : List Path} {at_ : Leaf}
  (hat : at_ = .tt ∨ at_ = .ff)
  (hls : Exclusive ls) (hsub : Exclusive sub) :
  Exclusive (graft ls at_ sub)
:= by
  apply pairwise_flatMap
  · intro p _
    by_cases hleaf : p.leaf = at_
    · rw [if_pos (by simp [hleaf])]
      exact extended_map_exclusive hsub
    · rw [if_neg (by simp [hleaf])]
      simp
  · apply List.Pairwise.imp ?_ hls
    intro p₁ p₂ h12 x hx y hy hxr hyr
    have split : ∀ {p : Path} {z : Path},
        z ∈ (if p.leaf == at_ then sub.map p.extended else [p]) →
        z = p ∨ (p.leaf = at_ ∧ ∃ s ∈ sub, z = p.extended s) := by
      intro p z hz
      by_cases hleaf : p.leaf = at_
      · rw [if_pos (by simp [hleaf])] at hz
        have ⟨s, hs, hzs⟩ := List.mem_map.mp hz
        exact .inr ⟨hleaf, s, hs, hzs.symm⟩
      · rw [if_neg (by simp [hleaf])] at hz
        simp at hz
        exact .inl hz
    have realOfAt : ∀ {p : Path}, p.leaf = at_ → RealLeaf p := by
      intro p hleaf
      cases hat with
      | inl h => exact .inl (h ▸ hleaf)
      | inr h => exact .inr (h ▸ hleaf)
    have hp₁r : RealLeaf p₁ := by
      cases split hx with
      | inl h => exact h ▸ hxr
      | inr h => exact realOfAt h.1
    have hp₂r : RealLeaf p₂ := by
      cases split hy with
      | inl h => exact h ▸ hyr
      | inr h => exact realOfAt h.1
    have hconf := h12 hp₁r hp₂r
    have hconf₁ : Conflict x p₂ := by
      cases split hx with
      | inl h => exact h ▸ hconf
      | inr h =>
        have ⟨_, s, _, hxs⟩ := h
        exact hxs ▸ conflict_extended_left hconf
    cases split hy with
    | inl h => exact h ▸ hconf₁
    | inr h =>
      have ⟨_, s, _, hys⟩ := h
      exact hys ▸ conflict_extended_right hconf₁

theorem itePaths_exclusive {pc pt pe : List Path}
  (hc : Exclusive pc) (ht : Exclusive pt) (he : Exclusive pe) :
  Exclusive (itePaths pc pt pe)
:= by
  apply pairwise_flatMap
  · intro p _
    cases hleaf : p.leaf with
    | tt => exact extended_map_exclusive ht
    | ff => exact extended_map_exclusive he
    | contradiction => simp
  · apply List.Pairwise.imp ?_ hc
    intro p₁ p₂ h12 x hx y hy hxr hyr
    have split : ∀ {p : Path} {z : Path},
        z ∈ (match p.leaf with
             | .tt => pt.map p.extended
             | .ff => pe.map p.extended
             | .contradiction => [p]) →
        (RealLeaf p ∧ (z = p ∨ ∃ s, z = p.extended s)) ∨ z = p := by
      intro p z hz
      cases hleaf : p.leaf <;> rw [hleaf] at hz
      · have ⟨s, _, hzs⟩ := List.mem_map.mp hz
        exact .inl ⟨.inl hleaf, .inr ⟨s, hzs.symm⟩⟩
      · have ⟨s, _, hzs⟩ := List.mem_map.mp hz
        exact .inl ⟨.inr hleaf, .inr ⟨s, hzs.symm⟩⟩
      · simp at hz
        exact .inr hz
    have hp₁ : RealLeaf p₁ := by
      cases split hx with
      | inl h => exact h.1
      | inr h => exact h ▸ hxr
    have hp₂ : RealLeaf p₂ := by
      cases split hy with
      | inl h => exact h.1
      | inr h => exact h ▸ hyr
    have hconf := h12 hp₁ hp₂
    have hconf₁ : Conflict x p₂ := by
      cases split hx with
      | inl h =>
        cases h.2 with
        | inl heq => exact heq ▸ hconf
        | inr hex =>
          have ⟨s, hxs⟩ := hex
          exact hxs ▸ conflict_extended_left hconf
      | inr h => exact h ▸ hconf
    cases split hy with
    | inl h =>
      cases h.2 with
      | inl heq => exact heq ▸ hconf₁
      | inr hex =>
        have ⟨s, hys⟩ := hex
        exact hys ▸ conflict_extended_right hconf₁
    | inr h => exact h ▸ hconf₁

/-- Invariant X for `paths`: any two distinct real-leaf paths conflict, so at
most one real-leaf path can pass under any valuation. -/
theorem paths_exclusive (e : Expr) : Exclusive (paths e)
:= by
  match e with
  | .lit (.bool b) => simp [paths, Exclusive]
  | .unaryApp .not x =>
    have ih := paths_exclusive x
    simp only [paths]
    refine List.Pairwise.map _ ?_ ih
    intro p q hpq hpr hqr
    exact hpq (realLeaf_flipped.mp hpr) (realLeaf_flipped.mp hqr)
  | .and l r =>
    exact graft_exclusive (.inl rfl) (paths_exclusive l) (paths_exclusive r)
  | .or l r =>
    exact graft_exclusive (.inr rfl) (paths_exclusive l) (paths_exclusive r)
  | .ite c t e' =>
    exact itePaths_exclusive (paths_exclusive c) (paths_exclusive t) (paths_exclusive e')
  | .lit (.int _) => exact atom_paths_exclusive _
  | .lit (.string _) => exact atom_paths_exclusive _
  | .lit (.entityUID _) => exact atom_paths_exclusive _
  | .var _ => exact atom_paths_exclusive _
  | .unaryApp .neg _ => exact atom_paths_exclusive _
  | .unaryApp .isEmpty _ => exact atom_paths_exclusive _
  | .unaryApp (.like _) _ => exact atom_paths_exclusive _
  | .unaryApp (.is _) _ => exact atom_paths_exclusive _
  | .binaryApp _ _ _ => exact atom_paths_exclusive _
  | .getAttr _ _ => exact atom_paths_exclusive _
  | .hasAttr _ _ => exact atom_paths_exclusive _
  | .set _ => exact atom_paths_exclusive _
  | .record _ => exact atom_paths_exclusive _
  | .call _ _ => exact atom_paths_exclusive _
termination_by sizeOf e

end Cedar.DNF
