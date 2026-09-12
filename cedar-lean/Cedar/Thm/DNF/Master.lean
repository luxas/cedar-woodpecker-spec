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

import Cedar.Thm.DNF.Invariant

/-!
The master invariant of `paths`, by structural induction: for every valuation,

* if the expression interprets `tt`, some `tt`-leaf path passes, no `ff`-leaf
  path passes, and no path errs;
* if it interprets `ff`, the same with `tt` and `ff` swapped;
* if it errs, no real-leaf path passes and there is an *erring node* — a node
  with a passing prefix and an erring atom that lies on some path, such that
  every path either contains the node (and so errs) or has cube outcome `ff`.

The `tt`/`ff` cases are stated once over a boolean polarity (`MasterB`); the
erring node moves through grafting via `shiftNode`, pinned to the unique
passing prefix by the exclusivity invariant.
-/

namespace Cedar.DNF

open Cedar.Spec

/-- The leaf of polarity `b`. -/
def leafOf (b : Bool) : Leaf :=
  if b then .tt else .ff

theorem leafOf_real (b : Bool) : RealLeaf ⟨[], leafOf b⟩ := by
  cases b <;> simp [RealLeaf, leafOf]

theorem leafOf_realLeaf {p : Path} {b : Bool} (h : p.leaf = leafOf b) :
  RealLeaf p := by
  cases b <;> simp [leafOf] at h <;> simp [RealLeaf, h]

theorem leafOf_ne_contradiction (b : Bool) : leafOf b ≠ .contradiction := by
  cases b <;> simp [leafOf]

theorem leafOf_inj {a b : Bool} (h : leafOf a = leafOf b) : a = b := by
  cases a <;> cases b <;> simp_all [leafOf]

theorem leaf_real_cases {l : Leaf} (h : l = .tt ∨ l = .ff) :
  ∃ b, l = leafOf b := by
  cases h with
  | inl h => exact ⟨true, by simp [leafOf, h]⟩
  | inr h => exact ⟨false, by simp [leafOf, h]⟩

/-- The `tt`/`ff` halves of the master invariant, over the polarity `b` of
the interpreted outcome: some `b`-leaf path passes, no `!b`-leaf path passes,
and no path errs. -/
def MasterB (v : Expr → Outcome) (b : Bool) (ps : List Path) : Prop :=
  (∃ p ∈ ps, p.leaf = leafOf b ∧ litsInterp v p.literals = .tt) ∧
  (∀ p ∈ ps, p.leaf = leafOf (!b) → litsInterp v p.literals ≠ .tt) ∧
  (∀ p ∈ ps, litsInterp v p.literals ≠ .err)

/-- The erring node of the `err` half: a node with a passing prefix and an
erring atom, on some path, such that every path contains it or is `ff`. -/
def ErrWitness (v : Expr → Outcome) (ps : List Path) : Prop :=
  ∃ n : Node, pairsPass v n.pre ∧ interp v n.atom = .err ∧
    (∃ p ∈ ps, ∃ l, (n, l) ∈ p.nodes) ∧
    (∀ p ∈ ps, (∃ l, (n, l) ∈ p.nodes) ∨ pathInterp v p = .ff)

/-- The `err` half of the master invariant. -/
def MasterE (v : Expr → Outcome) (ps : List Path) : Prop :=
  (∀ p ∈ ps, RealLeaf p → litsInterp v p.literals ≠ .tt) ∧
  ErrWitness v ps

/-- The outcome of the interpreted expression selects the master clause. -/
def MasterProp (v : Expr → Outcome) (ps : List Path) : Outcome → Prop
  | .tt  => MasterB v true ps
  | .ff  => MasterB v false ps
  | .err => MasterE v ps

/-! ### Small consequences and helpers -/

/-- A path containing the erring node errs. -/
theorem litsInterp_err_of_errNode {v : Expr → Outcome} {p : Path} {n : Node}
  {l : Literal}
  (hmem : (n, l) ∈ p.nodes) (hpre : pairsPass v n.pre)
  (herr : interp v n.atom = .err) :
  litsInterp v p.literals = .err
:= litsInterp_err_of_node hmem hpre herr

/-- A never-true path with non-erring literals is `ff`. -/
theorem pathInterp_ff_of_ne_tt {v : Expr → Outcome} {p : Path}
  (hleaf : p.leaf ≠ .tt) (hnoerr : litsInterp v p.literals ≠ .err) :
  pathInterp v p = .ff
:= by
  cases hl : litsInterp v p.literals with
  | tt => exact pathInterp_of_pass_ne_tt hl hleaf
  | ff => exact pathInterp_of_ff hl
  | err => exact absurd hl hnoerr

/-- An extension whose prefix fails is `ff`. -/
theorem extended_ff_of_prefix {v : Expr → Outcome} {p s : Path}
  (hff : litsInterp v p.literals = .ff) :
  pathInterp v (p.extended s) = .ff
:= by
  apply pathInterp_of_ff
  show litsInterp v (extendLits p.literals s.leaf s.literals).literals = .ff
  rw [litsInterp_extendLits_of_ne_tt (by simp [hff])]
  exact hff

/-- An extension by a passing prefix has the suffix's outcome (path level). -/
theorem extended_pass {v : Expr → Outcome} {p s : Path}
  (hp : litsInterp v p.literals = .tt) :
  pathInterp v (p.extended s) = pathInterp v s
:= by
  have h := extendLits_pass (v := v) (acc := p.literals)
    (leaf := s.leaf) (rest := s.literals) hp
  exact h

theorem extended_passback {v : Expr → Outcome} {p s : Path}
  (hnc : (p.extended s).leaf ≠ .contradiction)
  (h : litsInterp v (p.extended s).literals = .tt) :
  litsInterp v p.literals = .tt ∧ litsInterp v s.literals = .tt
:= extendLits_passback hnc h

theorem extended_errback {v : Expr → Outcome} {p s : Path}
  (h : litsInterp v (p.extended s).literals = .err) :
  litsInterp v p.literals = .err ∨
  (litsInterp v p.literals = .tt ∧ litsInterp v s.literals = .err)
:= extendLits_errback h

/-! ### Grafting the master invariant -/

section Graft

variable {v : Expr → Outcome} {ls sub : List Path}

/-- Graft membership, split by origin. -/
theorem graft_cases {a : Bool} {q : Path} (hq : q ∈ graft ls (leafOf a) sub) :
  (q ∈ ls ∧ q.leaf ≠ leafOf a) ∨
  (∃ p ∈ ls, p.leaf = leafOf a ∧ ∃ s ∈ sub, q = p.extended s)
:= mem_graft_iff.mp hq

theorem graft_mem_kept {a : Bool} {q : Path} (hq : q ∈ ls)
  (hleaf : q.leaf ≠ leafOf a) :
  q ∈ graft ls (leafOf a) sub
:= mem_graft_iff.mpr (.inl ⟨hq, hleaf⟩)

theorem graft_mem_extended {a : Bool} {p s : Path} (hp : p ∈ ls)
  (hleaf : p.leaf = leafOf a) (hs : s ∈ sub) :
  p.extended s ∈ graft ls (leafOf a) sub
:= mem_graft_iff.mpr (.inr ⟨p, hp, hleaf, s, hs, rfl⟩)

/-- G1: prefix polarity matches the graft; the result follows the suffix. -/
theorem graft_masterB {a b : Bool}
  (hls : MasterB v a ls) (hsub : MasterB v b sub) :
  MasterB v b (graft ls (leafOf a) sub)
:= by
  obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, hlsB, hlsE⟩ := hls
  obtain ⟨⟨s₀, hs₀, hs₀leaf, hs₀pass⟩, hsubB, hsubE⟩ := hsub
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨p₀.extended s₀, graft_mem_extended hp₀ hp₀leaf hs₀, ?_, ?_⟩
    · rw [(extended_pass_pass hp₀pass hs₀pass).2]
      exact hs₀leaf
    · exact (extended_pass_pass hp₀pass hs₀pass).1
  · intro q hq hqleaf hqpass
    cases graft_cases hq with
    | inl h =>
      by_cases hab : a = !b
      · exact absurd hqleaf (by rw [← hab]; exact h.2)
      · have : (!b) = !a := by
          cases a <;> cases b <;> simp_all
        rw [this] at hqleaf
        exact hlsB q h.1 hqleaf hqpass
    | inr h =>
      obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
      subst hqs
      have hreal : RealLeaf (p.extended s) := leafOf_realLeaf hqleaf
      have ⟨hpp, hsp⟩ := extended_passback hreal.ne_contradiction hqpass
      have hsleaf : (p.extended s).leaf = s.leaf := (extended_leaf_real hreal).2
      exact hsubB s hs (by rw [← hsleaf]; exact hqleaf) hsp
  · intro q hq hqerr
    cases graft_cases hq with
    | inl h => exact hlsE q h.1 hqerr
    | inr h =>
      obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
      subst hqs
      cases extended_errback hqerr with
      | inl herr => exact hlsE p hp herr
      | inr herr => exact hsubE s hs herr.2

/-- G2: prefix polarity opposite to the graft; the prefix decides. -/
theorem graft_masterB_opp {a : Bool}
  (hls : MasterB v (!a) ls) :
  MasterB v (!a) (graft ls (leafOf a) sub)
:= by
  obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, hlsB, hlsE⟩ := hls
  have hne : leafOf (!a) ≠ leafOf a := by
    intro h
    have := leafOf_inj h
    simp at this
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨p₀, graft_mem_kept hp₀ (by rw [hp₀leaf]; exact hne), hp₀leaf, hp₀pass⟩
  · intro q hq hqleaf hqpass
    simp only [Bool.not_not] at hqleaf
    cases graft_cases hq with
    | inl h => exact hlsB q h.1 (by simpa [leafOf] using hqleaf) hqpass
    | inr h =>
      obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
      subst hqs
      have hreal : RealLeaf (p.extended s) := leafOf_realLeaf hqleaf
      have ⟨hpp, _⟩ := extended_passback hreal.ne_contradiction hqpass
      exact hlsB p hp (by simpa [leafOf] using hpleaf) hpp
  · intro q hq hqerr
    cases graft_cases hq with
    | inl h => exact hlsE q h.1 hqerr
    | inr h =>
      obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
      subst hqs
      cases extended_errback hqerr with
      | inl herr => exact hlsE p hp herr
      | inr herr => exact hlsB p hp (by simpa [leafOf] using hpleaf) herr.1

/-- G3: prefix polarity matches and the suffix errs; the erring node shifts
by the unique passing prefix. -/
theorem graft_masterE {a : Bool}
  (hX : Exclusive ls)
  (hnodup : ∀ s ∈ sub, (s.literals.map (·.atom)).Nodup)
  (hls : MasterB v a ls) (hsub : MasterE v sub) :
  MasterE v (graft ls (leafOf a) sub)
:= by
  obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, hlsB, hlsE⟩ := hls
  obtain ⟨hsubB, n, hnpre, hnerr, ⟨s₁, hs₁, l₁, hn₁⟩, hncover⟩ := hsub
  refine ⟨?_, ?_⟩
  · intro q hq hqreal hqpass
    cases graft_cases hq with
    | inl h =>
      cases hqreal with
      | inl htt =>
        by_cases ha : a = true
        · exact h.2 (by simp [ha, leafOf, htt])
        · have : a = false := by simpa using ha
          exact hlsB q h.1 (by simp [this, leafOf, htt]) hqpass
      | inr hff =>
        by_cases ha : a = false
        · exact h.2 (by simp [ha, leafOf, hff])
        · have : a = true := by simpa using ha
          exact hlsB q h.1 (by simp [this, leafOf, hff]) hqpass
    | inr h =>
      obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
      subst hqs
      have ⟨hpp, hsp⟩ := extended_passback hqreal.ne_contradiction hqpass
      have hsreal := (extended_leaf_real hqreal).1
      exact hsubB s hs hsreal hsp
  · refine ⟨shiftNode p₀ n, shiftNode_pairsPass hp₀pass hnpre, ?_, ?_, ?_⟩
    · rw [shiftNode_atom]
      exact hnerr
    · exact ⟨p₀.extended s₁, graft_mem_extended hp₀ hp₀leaf hs₁, l₁,
        extended_shift_node hp₀pass (hnodup s₁ hs₁) hn₁ hnpre hnerr⟩
    · intro q hq
      cases graft_cases hq with
      | inl h =>
        refine .inr ?_
        cases hqi : litsInterp v q.literals with
        | err => exact absurd hqi (hlsE q h.1)
        | ff => exact pathInterp_of_ff hqi
        | tt =>
          apply pathInterp_of_pass_ne_tt hqi
          intro htt
          by_cases ha : a = true
          · exact h.2 (by simp [ha, leafOf, htt])
          · have haf : a = false := by simpa using ha
            exact hlsB q h.1 (by simp [haf, leafOf, htt]) hqi
      | inr h =>
        obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
        subst hqs
        cases hpi : litsInterp v p.literals with
        | err => exact absurd hpi (hlsE p hp)
        | ff => exact .inr (extended_ff_of_prefix hpi)
        | tt =>
          have hpeq : p = p₀ := exclusive_eq_of_pass hX hp hp₀
            (leafOf_realLeaf hpleaf) (leafOf_realLeaf hp₀leaf) hpi hp₀pass
          subst hpeq
          cases hncover s hs with
          | inl hcon =>
            obtain ⟨l', hl'⟩ := hcon
            exact .inl ⟨l', extended_shift_node hpi (hnodup s hs) hl' hnpre hnerr⟩
          | inr hff =>
            rw [extended_pass hpi]
            exact .inr hff

/-- G4: the prefix errs; its erring node persists. -/
theorem graft_masterE_pre {a : Bool}
  (hsub_ne : sub ≠ [])
  (hls : MasterE v ls) :
  MasterE v (graft ls (leafOf a) sub)
:= by
  obtain ⟨hlsB, n, hnpre, hnerr, ⟨p₁, hp₁, l₁, hn₁⟩, hncover⟩ := hls
  refine ⟨?_, ?_⟩
  · intro q hq hqreal hqpass
    cases graft_cases hq with
    | inl h => exact hlsB q h.1 hqreal hqpass
    | inr h =>
      obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
      subst hqs
      have ⟨hpp, _⟩ := extended_passback hqreal.ne_contradiction hqpass
      exact hlsB p hp (leafOf_realLeaf hpleaf) hpp
  · refine ⟨n, hnpre, hnerr, ?_, ?_⟩
    · by_cases hleaf : p₁.leaf = leafOf a
      · match hsub : sub with
        | s :: _ =>
          exact ⟨p₁.extended s, graft_mem_extended hp₁ hleaf (by simp),
            l₁, extended_nodes_mono hn₁⟩
      · exact ⟨p₁, graft_mem_kept hp₁ hleaf, l₁, hn₁⟩
    · intro q hq
      cases graft_cases hq with
      | inl h => exact hncover q h.1
      | inr h =>
        obtain ⟨p, hp, hpleaf, s, hs, hqs⟩ := h
        subst hqs
        cases hncover p hp with
        | inl hcon =>
          obtain ⟨l', hl'⟩ := hcon
          exact .inl ⟨l', extended_nodes_mono hl'⟩
        | inr hff =>
          have hpreal : RealLeaf p := leafOf_realLeaf hpleaf
          have hnp : litsInterp v p.literals ≠ .tt := hlsB p hp hpreal
          have hne : litsInterp v p.literals ≠ .err := by
            intro herr
            rw [pathInterp_of_err herr] at hff
            cases hff
          cases hpi : litsInterp v p.literals with
          | tt => exact absurd hpi hnp
          | err => exact absurd hpi hne
          | ff => exact .inr (extended_ff_of_prefix hpi)

end Graft

theorem leafOf_true : leafOf true = .tt := rfl
theorem leafOf_false : leafOf false = .ff := rfl

/-! ### `ite` and the master invariant -/

section Ite

variable {v : Expr → Outcome} {pc pt pe : List Path}

theorem itePaths_mem_tt {p s : Path} (hp : p ∈ pc) (hleaf : p.leaf = .tt)
  (hs : s ∈ pt) : p.extended s ∈ itePaths pc pt pe
:= mem_itePaths_iff.mpr (.inl ⟨p, hp, hleaf, s, hs, rfl⟩)

theorem itePaths_mem_ff {p s : Path} (hp : p ∈ pc) (hleaf : p.leaf = .ff)
  (hs : s ∈ pe) : p.extended s ∈ itePaths pc pt pe
:= mem_itePaths_iff.mpr (.inr (.inl ⟨p, hp, hleaf, s, hs, rfl⟩))

theorem itePaths_mem_c {q : Path} (hq : q ∈ pc)
  (hleaf : q.leaf = .contradiction) : q ∈ itePaths pc pt pe
:= mem_itePaths_iff.mpr (.inr (.inr ⟨hq, hleaf⟩))

/-- I1: the test is real; the result follows the taken branch. -/
theorem itePaths_masterB {a b : Bool}
  (hc : MasterB v a pc)
  (hact : MasterB v b (if a then pt else pe)) :
  MasterB v b (itePaths pc pt pe)
:= by
  obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, hcB, hcE⟩ := hc
  obtain ⟨⟨s₀, hs₀, hs₀leaf, hs₀pass⟩, hactB, hactE⟩ := hact
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨p₀.extended s₀, ?_, ?_, (extended_pass_pass hp₀pass hs₀pass).1⟩
    · cases a with
      | true => exact itePaths_mem_tt hp₀ (by simpa [leafOf] using hp₀leaf) (by simpa [leafOf] using hs₀)
      | false => exact itePaths_mem_ff hp₀ (by simpa [leafOf] using hp₀leaf) (by simpa [leafOf] using hs₀)
    · rw [(extended_pass_pass hp₀pass hs₀pass).2]
      exact hs₀leaf
  · intro q hq hqleaf hqpass
    rcases mem_itePaths_iff.mp hq with
      ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨_, hqc⟩
    · subst hqs
      have hreal : RealLeaf (p.extended s) := leafOf_realLeaf hqleaf
      have ⟨hpp, hsp⟩ := extended_passback hreal.ne_contradiction hqpass
      cases a with
      | true =>
        have hsleaf : (p.extended s).leaf = s.leaf := (extended_leaf_real hreal).2
        exact hactB s (by simpa [leafOf] using hs) (by rw [← hsleaf]; exact hqleaf) hsp
      | false =>
        exact hcB p hp (by simpa [leafOf] using hpleaf) hpp
    · subst hqs
      have hreal : RealLeaf (p.extended s) := leafOf_realLeaf hqleaf
      have ⟨hpp, hsp⟩ := extended_passback hreal.ne_contradiction hqpass
      cases a with
      | true =>
        exact hcB p hp (by simpa [leafOf] using hpleaf) hpp
      | false =>
        have hsleaf : (p.extended s).leaf = s.leaf := (extended_leaf_real hreal).2
        exact hactB s (by simpa [leafOf] using hs) (by rw [← hsleaf]; exact hqleaf) hsp
    · rw [hqc] at hqleaf
      exact absurd hqleaf.symm (leafOf_ne_contradiction _)
  · intro q hq hqerr
    rcases mem_itePaths_iff.mp hq with
      ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨hqc, _⟩
    · subst hqs
      cases extended_errback hqerr with
      | inl herr => exact hcE p hp herr
      | inr herr =>
        cases a with
        | true => exact hactE s (by simpa [leafOf] using hs) herr.2
        | false => exact hcB p hp (by simpa [leafOf] using hpleaf) herr.1
    · subst hqs
      cases extended_errback hqerr with
      | inl herr => exact hcE p hp herr
      | inr herr =>
        cases a with
        | true => exact hcB p hp (by simpa [leafOf] using hpleaf) herr.1
        | false => exact hactE s (by simpa [leafOf] using hs) herr.2
    · exact hcE q hqc hqerr

/-- I3: the test is real and the taken branch errs. -/
theorem itePaths_masterE {a : Bool}
  (hX : Exclusive pc)
  (hnodup : ∀ s ∈ (if a then pt else pe), (s.literals.map (·.atom)).Nodup)
  (hc : MasterB v a pc) (hact : MasterE v (if a then pt else pe)) :
  MasterE v (itePaths pc pt pe)
:= by
  obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, hcB, hcE⟩ := hc
  obtain ⟨hactB, n, hnpre, hnerr, ⟨s₁, hs₁, l₁, hn₁⟩, hncover⟩ := hact
  refine ⟨?_, ?_⟩
  · intro q hq hqreal hqpass
    rcases mem_itePaths_iff.mp hq with
      ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨_, hqc⟩
    · subst hqs
      have ⟨hpp, hsp⟩ := extended_passback hqreal.ne_contradiction hqpass
      have hsreal := (extended_leaf_real hqreal).1
      cases a with
      | true => exact hactB s (by simpa [leafOf] using hs) hsreal hsp
      | false => exact hcB p hp (by simpa [leafOf] using hpleaf) hpp
    · subst hqs
      have ⟨hpp, hsp⟩ := extended_passback hqreal.ne_contradiction hqpass
      have hsreal := (extended_leaf_real hqreal).1
      cases a with
      | true => exact hcB p hp (by simpa [leafOf] using hpleaf) hpp
      | false => exact hactB s (by simpa [leafOf] using hs) hsreal hsp
    · exact absurd hqc hqreal.ne_contradiction
  · refine ⟨shiftNode p₀ n, shiftNode_pairsPass hp₀pass hnpre, ?_, ?_, ?_⟩
    · rw [shiftNode_atom]
      exact hnerr
    · refine ⟨p₀.extended s₁, ?_, l₁,
        extended_shift_node hp₀pass (hnodup s₁ hs₁) hn₁ hnpre hnerr⟩
      cases a with
      | true => exact itePaths_mem_tt hp₀ (by simpa [leafOf] using hp₀leaf) (by simpa [leafOf] using hs₁)
      | false => exact itePaths_mem_ff hp₀ (by simpa [leafOf] using hp₀leaf) (by simpa [leafOf] using hs₁)
    · intro q hq
      have handle_active : ∀ (p s : Path), p ∈ pc → p.leaf = leafOf a →
          s ∈ (if a then pt else pe) →
          (∃ l', (shiftNode p₀ n, l') ∈ (p.extended s).nodes) ∨
            pathInterp v (p.extended s) = .ff := by
        intro p s hp hpleaf hs
        cases hpi : litsInterp v p.literals with
        | err => exact absurd hpi (hcE p hp)
        | ff => exact .inr (extended_ff_of_prefix hpi)
        | tt =>
          have hpeq : p = p₀ := exclusive_eq_of_pass hX hp hp₀
            (leafOf_realLeaf hpleaf) (leafOf_realLeaf hp₀leaf) hpi hp₀pass
          subst hpeq
          cases hncover s hs with
          | inl hcon =>
            obtain ⟨l', hl'⟩ := hcon
            exact .inl ⟨l', extended_shift_node hpi (hnodup s hs) hl' hnpre hnerr⟩
          | inr hff =>
            rw [extended_pass hpi]
            exact .inr hff
      have handle_inactive : ∀ (p s : Path), p ∈ pc → p.leaf = leafOf (!a) →
          (∃ l', (shiftNode p₀ n, l') ∈ (p.extended s).nodes) ∨
            pathInterp v (p.extended s) = .ff := by
        intro p s hp hpleaf
        cases hpi : litsInterp v p.literals with
        | err => exact absurd hpi (hcE p hp)
        | ff => exact .inr (extended_ff_of_prefix hpi)
        | tt => exact absurd hpi (hcB p hp hpleaf)
      rcases mem_itePaths_iff.mp hq with
        ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨hqc, hqleaf⟩
      · subst hqs
        cases a with
        | true => exact handle_active p s hp hpleaf (by simpa [leafOf] using hs)
        | false => exact handle_inactive p s hp (by simpa [leafOf] using hpleaf)
      · subst hqs
        cases a with
        | true => exact handle_inactive p s hp (by simpa [leafOf] using hpleaf)
        | false => exact handle_active p s hp hpleaf (by simpa [leafOf] using hs)
      · refine .inr (pathInterp_ff_of_ne_tt (by simp [hqleaf]) (hcE q hqc))

/-- I2: the test errs; its erring node persists into both branches. -/
theorem itePaths_masterE_pre
  (htne : pt ≠ []) (hene : pe ≠ [])
  (hc : MasterE v pc) :
  MasterE v (itePaths pc pt pe)
:= by
  obtain ⟨hcB, n, hnpre, hnerr, ⟨p₁, hp₁, l₁, hn₁⟩, hncover⟩ := hc
  refine ⟨?_, ?_⟩
  · intro q hq hqreal hqpass
    rcases mem_itePaths_iff.mp hq with
      ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨hqc, hqleaf⟩
    · subst hqs
      have ⟨hpp, _⟩ := extended_passback hqreal.ne_contradiction hqpass
      exact hcB p hp (.inl hpleaf) hpp
    · subst hqs
      have ⟨hpp, _⟩ := extended_passback hqreal.ne_contradiction hqpass
      exact hcB p hp (.inr hpleaf) hpp
    · exact absurd hqleaf hqreal.ne_contradiction
  · refine ⟨n, hnpre, hnerr, ?_, ?_⟩
    · cases hleaf : p₁.leaf with
      | tt =>
        match hpt : pt with
        | s :: _ =>
          exact ⟨p₁.extended s, itePaths_mem_tt hp₁ hleaf (by simp),
            l₁, extended_nodes_mono hn₁⟩
      | ff =>
        match hpe : pe with
        | s :: _ =>
          exact ⟨p₁.extended s, itePaths_mem_ff hp₁ hleaf (by simp),
            l₁, extended_nodes_mono hn₁⟩
      | contradiction =>
        exact ⟨p₁, itePaths_mem_c hp₁ hleaf, l₁, hn₁⟩
    · intro q hq
      have handle : ∀ (p s : Path), p ∈ pc → RealLeaf p →
          (∃ l', (n, l') ∈ (p.extended s).nodes) ∨
            pathInterp v (p.extended s) = .ff := by
        intro p s hp hpreal
        cases hncover p hp with
        | inl hcon =>
          obtain ⟨l', hl'⟩ := hcon
          exact .inl ⟨l', extended_nodes_mono hl'⟩
        | inr hff =>
          have hne : litsInterp v p.literals ≠ .err := by
            intro herr
            rw [pathInterp_of_err herr] at hff
            cases hff
          cases hpi : litsInterp v p.literals with
          | tt => exact absurd hpi (hcB p hp hpreal)
          | err => exact absurd hpi hne
          | ff => exact .inr (extended_ff_of_prefix hpi)
      rcases mem_itePaths_iff.mp hq with
        ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨p, hp, hpleaf, s, hs, hqs⟩ | ⟨hqc, hqleaf⟩
      · subst hqs
        exact handle p s hp (.inl hpleaf)
      · subst hqs
        exact handle p s hp (.inr hpleaf)
      · exact hncover q hqc

end Ite

/-! ### Flipping and atoms -/

theorem flipped_leaf_eq {p : Path} {b : Bool} :
  p.flipped.leaf = leafOf b ↔ p.leaf = leafOf (!b)
:= by
  cases hl : p.leaf <;> cases b <;> simp [Path.flipped, hl, leafOf]

theorem flipped_literals (p : Path) : p.flipped.literals = p.literals := rfl

theorem flipped_nodes (p : Path) : p.flipped.nodes = p.nodes := rfl

theorem flipped_realLeaf {p : Path} : RealLeaf p.flipped ↔ RealLeaf p :=
  realLeaf_flipped

theorem flipped_masterB {v : Expr → Outcome} {b : Bool} {ps : List Path}
  (h : MasterB v b ps) :
  MasterB v (!b) (ps.map .flipped)
:= by
  obtain ⟨⟨p₀, hp₀, hp₀leaf, hp₀pass⟩, hB, hE⟩ := h
  refine ⟨⟨p₀.flipped, List.mem_map.mpr ⟨p₀, hp₀, rfl⟩, ?_, hp₀pass⟩, ?_, ?_⟩
  · rw [flipped_leaf_eq, Bool.not_not]
    exact hp₀leaf
  · intro q hq hqleaf hqpass
    have ⟨p, hp, hqp⟩ := List.mem_map.mp hq
    subst hqp
    rw [flipped_leaf_eq, Bool.not_not] at hqleaf
    exact hB p hp hqleaf hqpass
  · intro q hq hqerr
    have ⟨p, hp, hqp⟩ := List.mem_map.mp hq
    subst hqp
    exact hE p hp hqerr

theorem flipped_masterE {v : Expr → Outcome} {ps : List Path}
  (h : MasterE v ps) :
  MasterE v (ps.map .flipped)
:= by
  obtain ⟨hB, n, hnpre, hnerr, ⟨p₁, hp₁, l₁, hn₁⟩, hncover⟩ := h
  refine ⟨?_, n, hnpre, hnerr,
    ⟨p₁.flipped, List.mem_map.mpr ⟨p₁, hp₁, rfl⟩, l₁, by rw [flipped_nodes]; exact hn₁⟩, ?_⟩
  · intro q hq hqreal hqpass
    have ⟨p, hp, hqp⟩ := List.mem_map.mp hq
    subst hqp
    exact hB p hp (flipped_realLeaf.mp hqreal) hqpass
  · intro q hq
    have ⟨p, hp, hqp⟩ := List.mem_map.mp hq
    subst hqp
    cases hncover p hp with
    | inl hcon =>
      obtain ⟨l', hl'⟩ := hcon
      exact .inl ⟨l', by rw [flipped_nodes]; exact hl'⟩
    | inr hff =>
      refine .inr ?_
      have hne : litsInterp v p.literals ≠ .err := by
        intro herr
        rw [pathInterp_of_err herr] at hff
        cases hff
      cases hpi : litsInterp v p.literals with
      | err => exact absurd hpi hne
      | ff => exact pathInterp_of_ff hpi
      | tt =>
        apply pathInterp_of_pass_ne_tt (p := p.flipped) hpi
        intro htt
        have hpleaf : p.leaf = .ff := by
          cases hpl : p.leaf with
          | tt =>
            rw [pathInterp_of_pass_tt hpi hpl] at hff
            cases hff
          | ff => rfl
          | contradiction =>
            rw [Path.flipped] at htt
            simp [hpl] at htt
        exact absurd hpi (hB p hp (.inr hpleaf) )

/-- The master invariant for a bare atom. -/
theorem atom_master {x : Expr} {v : Expr → Outcome} :
  (interp v x = .tt → MasterB v true [⟨[⟨x, false⟩], .tt⟩, ⟨[⟨x, true⟩], .ff⟩]) ∧
  (interp v x = .ff → MasterB v false [⟨[⟨x, false⟩], .tt⟩, ⟨[⟨x, true⟩], .ff⟩]) ∧
  (interp v x = .err → MasterE v [⟨[⟨x, false⟩], .tt⟩, ⟨[⟨x, true⟩], .ff⟩])
:= by
  have hpos : litsInterp v [(⟨x, false⟩ : Literal)] = interp v x := by
    simp [litsInterp, Literal.holds]
    cases h : interp v x <;> simp [Outcome.and]
  have hneg : litsInterp v [(⟨x, true⟩ : Literal)] = (interp v x).negated := by
    simp [litsInterp, Literal.holds]
    cases h : interp v x <;> simp [Outcome.and, Outcome.negated]
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · refine ⟨⟨⟨[⟨x, false⟩], .tt⟩, by simp, rfl, by rw [hpos, h]⟩, ?_, ?_⟩
    · intro p hp hleaf hpass
      simp at hp
      rcases hp with hp | hp <;> subst hp
      · cases hleaf
      · rw [hneg, h] at hpass
        cases hpass
    · intro p hp herr
      simp at hp
      rcases hp with hp | hp <;> subst hp
      · rw [hpos, h] at herr
        cases herr
      · rw [hneg, h] at herr
        cases herr
  · refine ⟨⟨⟨[⟨x, true⟩], .ff⟩, by simp, rfl, by rw [hneg, h]; rfl⟩, ?_, ?_⟩
    · intro p hp hleaf hpass
      simp at hp
      rcases hp with hp | hp <;> subst hp
      · rw [hpos, h] at hpass
        cases hpass
      · cases hleaf
    · intro p hp herr
      simp at hp
      rcases hp with hp | hp <;> subst hp
      · rw [hpos, h] at herr
        cases herr
      · rw [hneg, h] at herr
        cases herr
  · refine ⟨?_, (⟨[], x⟩ : Node), ?_, h, ?_, ?_⟩
    · intro p hp _ hpass
      simp at hp
      rcases hp with hp | hp <;> subst hp
      · rw [hpos, h] at hpass
        cases hpass
      · rw [hneg, h] at hpass
        cases hpass
    · intro pr hpr
      cases hpr
    · exact ⟨⟨[⟨x, false⟩], .tt⟩, by simp, ⟨x, false⟩, by simp [Path.nodes, nodesFrom]⟩
    · intro p hp
      simp at hp
      rcases hp with hp | hp <;> subst hp
      · exact .inl ⟨⟨x, false⟩, by simp [Path.nodes, nodesFrom]⟩
      · exact .inl ⟨⟨x, true⟩, by simp [Path.nodes, nodesFrom]⟩

/-! ### The master invariant -/

theorem master (e : Expr) (v : Expr → Outcome) :
  (interp v e = .tt → MasterB v true (paths e)) ∧
  (interp v e = .ff → MasterB v false (paths e)) ∧
  (interp v e = .err → MasterE v (paths e))
:= by
  match e with
  | .lit (.bool true) =>
    refine ⟨fun _ => ⟨⟨⟨[], .tt⟩, by simp [paths, Path.ofLeaf], rfl, rfl⟩, ?_, ?_⟩, ?_, ?_⟩
    · intro p hp hleaf
      simp [paths, Path.ofLeaf] at hp
      subst hp
      cases hleaf
    · intro p hp
      simp [paths, Path.ofLeaf] at hp
      subst hp
      simp [litsInterp]
    · intro h
      simp [interp] at h
    · intro h
      simp [interp] at h
  | .lit (.bool false) =>
    refine ⟨?_, fun _ => ⟨⟨⟨[], .ff⟩, by simp [paths, Path.ofLeaf], rfl, rfl⟩, ?_, ?_⟩, ?_⟩
    · intro h
      simp [interp] at h
    · intro p hp hleaf
      simp [paths, Path.ofLeaf] at hp
      subst hp
      cases hleaf
    · intro p hp
      simp [paths, Path.ofLeaf] at hp
      subst hp
      simp [litsInterp]
    · intro h
      simp [interp] at h
  | .unaryApp .not x =>
    obtain ⟨ihT, ihF, ihE⟩ := master x v
    have hpaths : paths (.unaryApp .not x) = (paths x).map .flipped := rfl
    have hinterp : interp v (.unaryApp .not x) = (interp v x).negated := rfl
    rw [hpaths, hinterp]
    refine ⟨?_, ?_, ?_⟩ <;> intro h
    · have hx : interp v x = .ff := by
        cases hi : interp v x <;> rw [hi] at h <;> simp [Outcome.negated] at h
      exact flipped_masterB (b := false) (ihF hx)
    · have hx : interp v x = .tt := by
        cases hi : interp v x <;> rw [hi] at h <;> simp [Outcome.negated] at h
      exact flipped_masterB (b := true) (ihT hx)
    · have hx : interp v x = .err := by
        cases hi : interp v x <;> rw [hi] at h <;> simp [Outcome.negated] at h
      exact flipped_masterE (ihE hx)
  | .and l r =>
    obtain ⟨lT, lF, lE⟩ := master l v
    obtain ⟨rT, rF, rE⟩ := master r v
    have hpaths : paths (.and l r) = graft (paths l) (leafOf true) (paths r) := rfl
    rw [hpaths]
    refine ⟨?_, ?_, ?_⟩ <;> (intro h; rw [interp_and] at h)
    · cases hl : interp v l <;> rw [hl] at h <;> simp only [Outcome.and] at h
      · exact graft_masterB (lT hl) (rT h)
      · cases h
      · cases h
    · cases hl : interp v l <;> rw [hl] at h <;> simp only [Outcome.and] at h
      · exact graft_masterB (lT hl) (rF h)
      · exact graft_masterB_opp (a := true) (lF hl)
      · cases h
    · cases hl : interp v l <;> rw [hl] at h <;> simp only [Outcome.and] at h
      · exact graft_masterE (paths_exclusive l) (fun s hs => paths_nodup hs)
          (lT hl) (rE h)
      · cases h
      · exact graft_masterE_pre (paths_ne_nil r) (lE hl)
  | .or l r =>
    obtain ⟨lT, lF, lE⟩ := master l v
    obtain ⟨rT, rF, rE⟩ := master r v
    have hpaths : paths (.or l r) = graft (paths l) (leafOf false) (paths r) := rfl
    rw [hpaths]
    refine ⟨?_, ?_, ?_⟩ <;> (intro h; rw [interp_or] at h)
    · cases hl : interp v l <;> rw [hl] at h <;> simp only [Outcome.or] at h
      · exact graft_masterB_opp (a := false) (lT hl)
      · exact graft_masterB (lF hl) (rT h)
      · cases h
    · cases hl : interp v l <;> rw [hl] at h <;> simp only [Outcome.or] at h
      · cases h
      · exact graft_masterB (lF hl) (rF h)
      · cases h
    · cases hl : interp v l <;> rw [hl] at h <;> simp only [Outcome.or] at h
      · cases h
      · exact graft_masterE (paths_exclusive l) (fun s hs => paths_nodup hs)
          (lF hl) (rE h)
      · exact graft_masterE_pre (paths_ne_nil r) (lE hl)
  | .ite c t e' =>
    obtain ⟨cT, cF, cE⟩ := master c v
    obtain ⟨tT, tF, tE⟩ := master t v
    obtain ⟨eT, eF, eE⟩ := master e' v
    rw [paths_ite_def]
    have hinterp : interp v (.ite c t e') =
        match interp v c with
        | .tt => interp v t
        | .ff => interp v e'
        | .err => .err := rfl
    refine ⟨?_, ?_, ?_⟩ <;> (intro h; rw [hinterp] at h)
    · cases hc : interp v c <;> rw [hc] at h
      · exact itePaths_masterB (a := true) (cT hc) (by simpa [leafOf] using tT h)
      · exact itePaths_masterB (a := false) (cF hc) (by simpa [leafOf] using eT h)
      · cases h
    · cases hc : interp v c <;> rw [hc] at h
      · exact itePaths_masterB (a := true) (cT hc) (by simpa [leafOf] using tF h)
      · exact itePaths_masterB (a := false) (cF hc) (by simpa [leafOf] using eF h)
      · cases h
    · cases hc : interp v c <;> rw [hc] at h
      · exact itePaths_masterE (a := true) (paths_exclusive c)
          (by simpa [leafOf] using fun s hs => paths_nodup (e := t) hs)
          (cT hc) (by simpa [leafOf] using tE h)
      · exact itePaths_masterE (a := false) (paths_exclusive c)
          (by simpa [leafOf] using fun s hs => paths_nodup (e := e') hs)
          (cF hc) (by simpa [leafOf] using eE h)
      · exact itePaths_masterE_pre (paths_ne_nil t) (paths_ne_nil e') (cE hc)
  | .lit (.int _) => exact atom_master
  | .lit (.string _) => exact atom_master
  | .lit (.entityUID _) => exact atom_master
  | .var _ => exact atom_master
  | .unaryApp .neg _ => exact atom_master
  | .unaryApp .isEmpty _ => exact atom_master
  | .unaryApp (.like _) _ => exact atom_master
  | .unaryApp (.is _) _ => exact atom_master
  | .binaryApp _ _ _ => exact atom_master
  | .getAttr _ _ => exact atom_master
  | .hasAttr _ _ => exact atom_master
  | .set _ => exact atom_master
  | .record _ => exact atom_master
  | .call _ _ => exact atom_master
termination_by sizeOf e

end Cedar.DNF
