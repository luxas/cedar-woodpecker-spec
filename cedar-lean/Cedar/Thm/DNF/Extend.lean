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

import Cedar.Thm.DNF.Interp

/-!
How `Path.extended` — appending with literal dedup and contradiction
truncation (`extendLits`) — behaves, syntactically and semantically. The
central facts: extension preserves the prefix and its nodes; under a passing
prefix, the extension's cube outcome is exactly the suffix path's (dedup is
sound because a valuation is a function, and truncation matches the
short-circuit at the contradicting literal); a passing extension passes both
parts back; an erring extension pinpoints the erring part; and an erring node
of the suffix survives at a shifted node of the extension that does not
depend on the suffix.
-/

namespace Cedar.DNF

open Cedar.Spec

/-- The (atom, polarity) pairs of a literal list. -/
def pairs (ls : List Literal) : List (Expr × Bool) :=
  ls.map fun l => (l.atom, l.negated)

/-- The cube outcome of a path. -/
def pathInterp (v : Expr → Outcome) (p : Path) : Outcome :=
  p.cube.interp v

theorem pairs_append (xs ys : List Literal) :
  pairs (xs ++ ys) = pairs xs ++ pairs ys
:= by simp [pairs]

/-! ### Path outcomes -/

theorem pathInterp_of_ff {v : Expr → Outcome} {p : Path}
  (h : litsInterp v p.literals = .ff) :
  pathInterp v p = .ff
:= by simp [pathInterp, Path.cube, Cube.interp, h]

theorem pathInterp_of_err {v : Expr → Outcome} {p : Path}
  (h : litsInterp v p.literals = .err) :
  pathInterp v p = .err
:= by simp [pathInterp, Path.cube, Cube.interp, h]

theorem pathInterp_of_pass_tt {v : Expr → Outcome} {p : Path}
  (h : litsInterp v p.literals = .tt) (hleaf : p.leaf = .tt) :
  pathInterp v p = .tt
:= by simp [pathInterp, Path.cube, Cube.interp, h, hleaf]

theorem pathInterp_of_pass_ne_tt {v : Expr → Outcome} {p : Path}
  (h : litsInterp v p.literals = .tt) (hleaf : p.leaf ≠ .tt) :
  pathInterp v p = .ff
:= by
  have hnt : (p.leaf != Leaf.tt) = true := by
    cases hl : p.leaf <;> simp_all
  simp [pathInterp, Path.cube, Cube.interp, h, hnt]

theorem pathInterp_tt_inv {v : Expr → Outcome} {p : Path}
  (h : pathInterp v p = .tt) :
  litsInterp v p.literals = .tt ∧ p.leaf = .tt
:= by
  cases hl : litsInterp v p.literals with
  | tt =>
    refine ⟨rfl, ?_⟩
    by_contra hne
    rw [pathInterp_of_pass_ne_tt hl hne] at h
    cases h
  | ff => rw [pathInterp_of_ff hl] at h; cases h
  | err => rw [pathInterp_of_err hl] at h; cases h

theorem pathInterp_err_inv {v : Expr → Outcome} {p : Path}
  (h : pathInterp v p = .err) :
  litsInterp v p.literals = .err
:= by
  cases hl : litsInterp v p.literals with
  | tt =>
    by_cases hlf : p.leaf = .tt
    · rw [pathInterp_of_pass_tt hl hlf] at h; cases h
    · rw [pathInterp_of_pass_ne_tt hl hlf] at h; cases h
  | ff => rw [pathInterp_of_ff hl] at h; cases h
  | err => rfl

theorem pathInterp_ne_tt_of_contradiction {v : Expr → Outcome} {p : Path}
  (h : p.leaf = .contradiction) :
  pathInterp v p ≠ .tt
:= by
  intro htt
  exact absurd (pathInterp_tt_inv htt).2 (by simp [h])

/-! ### Equations for `extendLits` -/

theorem extendLits_cons_none {acc : List Literal} {l : Literal}
  (leaf : Leaf) (rest : List Literal)
  (hf : acc.find? (fun l' => l'.atom == l.atom) = none) :
  extendLits acc leaf (l :: rest) = extendLits (acc ++ [l]) leaf rest
:= by simp only [extendLits, hf]

theorem extendLits_cons_same {acc : List Literal} {l seen : Literal}
  (leaf : Leaf) (rest : List Literal)
  (hf : acc.find? (fun l' => l'.atom == l.atom) = some seen)
  (hn : seen.negated = l.negated) :
  extendLits acc leaf (l :: rest) = extendLits acc leaf rest
:= by
  simp only [extendLits, hf]
  rw [if_pos (by simp [hn])]

theorem extendLits_cons_opp {acc : List Literal} {l seen : Literal}
  (leaf : Leaf) (rest : List Literal)
  (hf : acc.find? (fun l' => l'.atom == l.atom) = some seen)
  (hn : seen.negated ≠ l.negated) :
  extendLits acc leaf (l :: rest) = ⟨acc, .contradiction⟩
:= by
  simp only [extendLits, hf]
  rw [if_neg (by simp [hn])]

/-- What a `find?` hit on the dedup predicate means. -/
theorem find?_atom_spec {acc : List Literal} {l seen : Literal}
  (hf : acc.find? (fun l' => l'.atom == l.atom) = some seen) :
  seen ∈ acc ∧ seen.atom = l.atom
:= ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem find?_atom_none {acc : List Literal} {l : Literal}
  (hf : acc.find? (fun l' => l'.atom == l.atom) = none) :
  l.atom ∉ acc.map (·.atom)
:= by
  intro hmem
  have ⟨la, hla, hlaa⟩ := List.mem_map.mp hmem
  have := List.find?_eq_none.mp hf la hla
  simp [hlaa] at this

/-- Same atom, opposite polarity: the outcomes are negations of each other. -/
theorem holds_flip {v : Expr → Outcome} {l l' : Literal}
  (ha : l.atom = l'.atom) (hn : l.negated ≠ l'.negated) :
  l.holds v = (l'.holds v).negated
:= by
  simp only [Literal.holds, ha]
  cases hln : l.negated <;> cases hl'n : l'.negated <;> simp_all
  all_goals (cases hi : interp v l'.atom <;> simp [Outcome.negated])

/-! ### Syntactic facts about `extendLits` -/

theorem extendLits_prefix (acc : List Literal) (leaf : Leaf) (rest : List Literal) :
  ∃ t, (extendLits acc leaf rest).literals = acc ++ t ∧ ∀ l ∈ t, l ∈ rest
:= by
  induction rest generalizing acc with
  | nil => exact ⟨[], by simp [extendLits], by simp⟩
  | cons l rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf]
      have ⟨t, ht, hmem⟩ := ih (acc ++ [l])
      refine ⟨l :: t, by simp [ht], ?_⟩
      intro x hx
      cases List.mem_cons.mp hx with
      | inl h => simp [h]
      | inr h => simp [hmem x h]
    | some seen =>
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn]
        have ⟨t, ht, hmem⟩ := ih acc
        exact ⟨t, ht, fun x hx => by simp [hmem x hx]⟩
      · rw [extendLits_cons_opp leaf rest' hf hn]
        exact ⟨[], by simp, by simp⟩

theorem extendLits_leaf (acc : List Literal) (leaf : Leaf) (rest : List Literal) :
  (extendLits acc leaf rest).leaf = leaf ∨
  (extendLits acc leaf rest).leaf = .contradiction
:= by
  induction rest generalizing acc with
  | nil => simp [extendLits]
  | cons l rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none => rw [extendLits_cons_none leaf rest' hf]; exact ih (acc ++ [l])
    | some seen =>
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn]; exact ih acc
      · rw [extendLits_cons_opp leaf rest' hf hn]; simp

theorem extendLits_nodup {acc : List Literal} {leaf : Leaf} {rest : List Literal}
  (h : (acc.map (·.atom)).Nodup) :
  (((extendLits acc leaf rest).literals).map (·.atom)).Nodup
:= by
  induction rest generalizing acc with
  | nil => simpa [extendLits] using h
  | cons l rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf]
      apply ih
      rw [List.map_append, List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      intro heq
      exact absurd (heq ▸ ha) (find?_atom_none hf)
    | some seen =>
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn]; exact ih h
      · rw [extendLits_cons_opp leaf rest' hf hn]; simpa using h

/-- Literals already in the prefix survive extension. -/
theorem extendLits_mem_of_acc {acc : List Literal} {leaf : Leaf}
  {rest : List Literal} {l : Literal} (h : l ∈ acc) :
  l ∈ (extendLits acc leaf rest).literals
:= by
  have ⟨t, ht, _⟩ := extendLits_prefix acc leaf rest
  rw [ht]
  exact List.mem_append.mpr (.inl h)

/-- A suffix literal survives extension, unless the extension truncated. -/
theorem extendLits_lit_survives {acc : List Literal} {leaf : Leaf}
  {rest : List Literal} {l : Literal} (h : l ∈ rest) :
  l ∈ (extendLits acc leaf rest).literals ∨
  (extendLits acc leaf rest).leaf = .contradiction
:= by
  induction rest generalizing acc with
  | nil => cases h
  | cons x rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == x.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf]
      cases List.mem_cons.mp h with
      | inl heq =>
        subst heq
        exact .inl (extendLits_mem_of_acc (by simp))
      | inr hrest => exact ih hrest
    | some seen =>
      by_cases hn : seen.negated = x.negated
      · rw [extendLits_cons_same leaf rest' hf hn]
        cases List.mem_cons.mp h with
        | inl heq =>
          subst heq
          have ⟨hmem, hatom⟩ := find?_atom_spec hf
          have : seen = l := by
            cases seen; cases l
            simp_all
          exact .inl (extendLits_mem_of_acc (this ▸ hmem))
        | inr hrest => exact ih hrest
      · rw [extendLits_cons_opp leaf rest' hf hn]
        exact .inr rfl

/-! ### Semantic facts about `extendLits` -/

theorem litsInterp_extendLits_of_ne_tt {v : Expr → Outcome} {acc : List Literal}
  {leaf : Leaf} {rest : List Literal}
  (h : litsInterp v acc ≠ .tt) :
  litsInterp v (extendLits acc leaf rest).literals = litsInterp v acc
:= by
  have ⟨t, ht, _⟩ := extendLits_prefix acc leaf rest
  rw [ht]
  exact litsInterp_prefix_ne_tt h

/-- A leading literal that holds does not change a path's outcome. -/
theorem pathInterp_cons_tt {v : Expr → Outcome} {l : Literal} {rest : List Literal}
  (leaf : Leaf) (hl : l.holds v = .tt) :
  pathInterp v ⟨l :: rest, leaf⟩ = pathInterp v ⟨rest, leaf⟩
:= by
  simp [pathInterp, Path.cube, Cube.interp, litsInterp, hl, Outcome.and]

/-- Under a passing prefix, extension has exactly the suffix's cube outcome:
dropped literals are determined by the prefix, and truncation matches the
short-circuit at the contradicting literal. -/
theorem extendLits_pass {v : Expr → Outcome} {acc : List Literal}
  {leaf : Leaf} {rest : List Literal}
  (hacc : litsInterp v acc = .tt) :
  pathInterp v (extendLits acc leaf rest) = pathInterp v ⟨rest, leaf⟩
:= by
  induction rest generalizing acc with
  | nil =>
    show pathInterp v ⟨acc, leaf⟩ = _
    by_cases hlf : leaf = .tt
    · rw [pathInterp_of_pass_tt hacc hlf, pathInterp_of_pass_tt rfl hlf]
    · rw [pathInterp_of_pass_ne_tt hacc hlf, pathInterp_of_pass_ne_tt rfl hlf]
  | cons l rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf]
      cases hl : l.holds v with
      | tt =>
        have hacc' : litsInterp v (acc ++ [l]) = .tt := by
          rw [litsInterp_append]
          simp [hacc, litsInterp, hl, Outcome.and]
        rw [ih hacc']
        rw [pathInterp_cons_tt leaf hl]
      | ff =>
        have hacc' : litsInterp v (acc ++ [l]) = .ff := by
          rw [litsInterp_append]
          simp [hacc, litsInterp, hl, Outcome.and]
        have hext : litsInterp v (extendLits (acc ++ [l]) leaf rest').literals = .ff := by
          rw [litsInterp_extendLits_of_ne_tt (by simp [hacc'])]
          exact hacc'
        rw [pathInterp_of_ff hext,
            pathInterp_of_ff (p := ⟨l :: rest', leaf⟩) (by simp [litsInterp, hl, Outcome.and])]
      | err =>
        have hacc' : litsInterp v (acc ++ [l]) = .err := by
          rw [litsInterp_append]
          simp [hacc, litsInterp, hl, Outcome.and]
        have hext : litsInterp v (extendLits (acc ++ [l]) leaf rest').literals = .err := by
          rw [litsInterp_extendLits_of_ne_tt (by simp [hacc'])]
          exact hacc'
        rw [pathInterp_of_err hext,
            pathInterp_of_err (p := ⟨l :: rest', leaf⟩) (by simp [litsInterp, hl, Outcome.and])]
    | some seen =>
      have ⟨hseen_mem, hseen_atom⟩ := find?_atom_spec hf
      have hseen_tt : seen.holds v = .tt := litsInterp_eq_tt.mp hacc seen hseen_mem
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn, ih hacc]
        have hl : l.holds v = .tt := by
          rw [holds_congr (l := l) (l' := seen) hseen_atom.symm hn.symm]
          exact hseen_tt
        rw [pathInterp_cons_tt leaf hl]
      · rw [extendLits_cons_opp leaf rest' hf hn]
        have hl : l.holds v = .ff := by
          have hflip := holds_flip (v := v) (l := l) (l' := seen) hseen_atom.symm (fun h => hn h.symm)
          rw [hflip, hseen_tt]
          rfl
        rw [pathInterp_of_pass_ne_tt (p := ⟨acc, .contradiction⟩) hacc (by simp),
            pathInterp_of_ff (p := ⟨l :: rest', leaf⟩) (by simp [litsInterp, hl, Outcome.and])]

/-- A passing, non-truncated extension passes both its parts back. -/
theorem extendLits_passback {v : Expr → Outcome} {acc : List Literal}
  {leaf : Leaf} {rest : List Literal}
  (hnc : (extendLits acc leaf rest).leaf ≠ .contradiction)
  (h : litsInterp v (extendLits acc leaf rest).literals = .tt) :
  litsInterp v acc = .tt ∧ litsInterp v rest = .tt
:= by
  induction rest generalizing acc with
  | nil =>
    simp only [extendLits] at h
    exact ⟨h, rfl⟩
  | cons l rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf] at hnc h
      have ⟨hacc', hrest'⟩ := ih hnc h
      rw [litsInterp_append] at hacc'
      have ⟨hacc, hl⟩ := Outcome.and_eq_tt.mp hacc'
      have hltt : l.holds v = .tt := by
        simp only [litsInterp] at hl
        exact (Outcome.and_eq_tt.mp hl).1
      exact ⟨hacc, by simp [litsInterp, hltt, hrest', Outcome.and]⟩
    | some seen =>
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn] at hnc h
        have ⟨hacc, hrest'⟩ := ih hnc h
        have ⟨hseen_mem, hseen_atom⟩ := find?_atom_spec hf
        have hl : l.holds v = .tt := by
          rw [holds_congr (l := l) (l' := seen) hseen_atom.symm hn.symm]
          exact litsInterp_eq_tt.mp hacc seen hseen_mem
        exact ⟨hacc, by simp [litsInterp, hl, hrest', Outcome.and]⟩
      · rw [extendLits_cons_opp leaf rest' hf hn] at hnc
        simp at hnc

/-- An erring extension errs in the prefix, or passes the prefix and errs in
the suffix. -/
theorem extendLits_errback {v : Expr → Outcome} {acc : List Literal}
  {leaf : Leaf} {rest : List Literal}
  (h : litsInterp v (extendLits acc leaf rest).literals = .err) :
  litsInterp v acc = .err ∨
  (litsInterp v acc = .tt ∧ litsInterp v rest = .err)
:= by
  induction rest generalizing acc with
  | nil =>
    simp only [extendLits] at h
    exact .inl h
  | cons l rest' ih =>
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | none =>
      rw [extendLits_cons_none leaf rest' hf] at h
      cases ih h with
      | inl happ =>
        rw [litsInterp_append] at happ
        cases Outcome.and_eq_err.mp happ with
        | inl hacc => exact .inl hacc
        | inr hboth =>
          refine .inr ⟨hboth.1, ?_⟩
          have hl : l.holds v = .err := by
            have h2 := hboth.2
            simp only [litsInterp] at h2
            cases hlh : l.holds v <;> rw [hlh] at h2 <;> first | rfl | cases h2
          simp [litsInterp, hl, Outcome.and]
      | inr hboth =>
        rw [litsInterp_append] at hboth
        have ⟨hacc, hl⟩ := Outcome.and_eq_tt.mp hboth.1
        have hltt : l.holds v = .tt := by
          simp only [litsInterp] at hl
          exact (Outcome.and_eq_tt.mp hl).1
        exact .inr ⟨hacc, by simp [litsInterp, hltt, hboth.2, Outcome.and]⟩
    | some seen =>
      by_cases hn : seen.negated = l.negated
      · rw [extendLits_cons_same leaf rest' hf hn] at h
        cases ih h with
        | inl hacc => exact .inl hacc
        | inr hboth =>
          have ⟨hseen_mem, hseen_atom⟩ := find?_atom_spec hf
          have hl : l.holds v = .tt := by
            rw [holds_congr (l := l) (l' := seen) hseen_atom.symm hn.symm]
            exact litsInterp_eq_tt.mp hboth.1 seen hseen_mem
          exact .inr ⟨hboth.1, by simp [litsInterp, hl, hboth.2, Outcome.and]⟩
      · rw [extendLits_cons_opp leaf rest' hf hn] at h
        exact .inl h

/-! ### Nodes through extension -/

theorem nodesFrom_append (pre : List (Expr × Bool)) (xs ys : List Literal) :
  nodesFrom pre (xs ++ ys) = nodesFrom pre xs ++ nodesFrom (pre ++ pairs xs) ys
:= by
  induction xs generalizing pre with
  | nil => simp [nodesFrom, pairs]
  | cons l rest ih =>
    simp only [List.cons_append, nodesFrom, ih, pairs, List.map_cons]
    simp [List.append_assoc]

theorem nodesFrom_mem_of_split {ls xs ys : List Literal} {l : Literal}
  (pre : List (Expr × Bool)) (h : ls = xs ++ l :: ys) :
  (⟨pre ++ pairs xs, l.atom⟩, l) ∈ nodesFrom pre ls
:= by
  subst h
  rw [nodesFrom_append]
  apply List.mem_append.mpr (.inr ?_)
  simp [nodesFrom]

theorem mem_nodesFrom {pre : List (Expr × Bool)} {ls : List Literal}
  {n : Node} {l : Literal} (h : (n, l) ∈ nodesFrom pre ls) :
  ∃ xs ys, ls = xs ++ l :: ys ∧ n = ⟨pre ++ pairs xs, l.atom⟩
:= by
  induction ls generalizing pre with
  | nil => cases h
  | cons x rest ih =>
    simp only [nodesFrom] at h
    cases List.mem_cons.mp h with
    | inl heq =>
      have h₁ : n = ⟨pre, x.atom⟩ := congrArg Prod.fst heq
      have h₂ : l = x := congrArg Prod.snd heq
      exact ⟨[], rest, by simp [h₂], by simp [h₁, h₂, pairs]⟩
    | inr hrest =>
      have ⟨xs, ys, hsplit, hn⟩ := ih hrest
      exact ⟨x :: xs, ys, by simp [hsplit], by simp [hn, pairs, List.append_assoc]⟩

theorem node_atom_of_mem {pre : List (Expr × Bool)} {ls : List Literal}
  {n : Node} {l : Literal} (h : (n, l) ∈ nodesFrom pre ls) :
  n.atom = l.atom
:= by
  have ⟨_, _, _, hn⟩ := mem_nodesFrom h
  simp [hn]

/-- Nodes of the prefix are nodes of the extension. -/
theorem extendLits_nodes_mono {acc : List Literal} {leaf : Leaf}
  {rest : List Literal} {n : Node} {l : Literal}
  (h : (n, l) ∈ nodesFrom [] acc) :
  (n, l) ∈ nodesFrom [] (extendLits acc leaf rest).literals
:= by
  have ⟨t, ht, _⟩ := extendLits_prefix acc leaf rest
  rw [ht, nodesFrom_append]
  exact List.mem_append.mpr (.inl h)

/-- An erring node of a path makes its literals err, given that the node's
prefix holds. -/
theorem litsInterp_err_of_node {v : Expr → Outcome} {ls : List Literal}
  {n : Node} {l : Literal}
  (hmem : (n, l) ∈ nodesFrom [] ls)
  (hpre : pairsPass v n.pre) (herr : interp v n.atom = .err) :
  litsInterp v ls = .err
:= by
  have ⟨xs, ys, hsplit, hn⟩ := mem_nodesFrom hmem
  subst hn
  apply litsInterp_eq_err.mpr
  refine ⟨xs, l, ys, hsplit, ?_, ?_⟩
  · apply litsInterp_eq_tt.mpr
    intro x hx
    apply holds_eq_tt.mpr
    have := hpre (x.atom, x.negated) (by
      simp only [List.nil_append]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using this
  · exact holds_eq_err.mpr (by simpa using herr)

theorem pairsPass_of_litsInterp_tt {v : Expr → Outcome} {ls : List Literal}
  (h : litsInterp v ls = .tt) :
  pairsPass v (pairs ls)
:= by
  intro pr hpr
  have ⟨l, hl, hpr'⟩ := List.mem_map.mp hpr
  have := litsInterp_eq_tt.mp h l hl
  rw [holds_eq_tt] at this
  rw [← hpr']
  exact this

theorem pairsPass_append {v : Expr → Outcome} {xs ys : List (Expr × Bool)}
  (hx : pairsPass v xs) (hy : pairsPass v ys) :
  pairsPass v (xs ++ ys)
:= by
  intro pr hpr
  cases List.mem_append.mp hpr with
  | inl h => exact hx pr h
  | inr h => exact hy pr h

theorem pairsPass_filter {v : Expr → Outcome} {xs : List (Expr × Bool)}
  {p : Expr × Bool → Bool} (h : pairsPass v xs) :
  pairsPass v (xs.filter p)
:= fun pr hpr => h pr (List.mem_filter.mp hpr).1

/-- The shifted node at which an erring node of the suffix reappears in any
extension by a passing prefix; the node depends only on the prefix literals
and the erring node. -/
theorem extendLits_shift {v : Expr → Outcome}
  {leaf : Leaf} {ys : List Literal} {l : Literal}
  (herr : l.holds v = .err) :
  ∀ (xs acc : List Literal),
    (∀ x ∈ acc, x.holds v = .tt) →
    (∀ x ∈ xs, x.holds v = .tt) →
    ((xs ++ l :: ys).map (·.atom)).Nodup →
    (⟨pairs acc ++ pairs (xs.filter fun x => !(acc.map (·.atom)).contains x.atom), l.atom⟩, l)
      ∈ nodesFrom [] (extendLits acc leaf (xs ++ l :: ys)).literals
:= by
  intro xs
  induction xs with
  | nil =>
    intro acc hacc _ _
    simp only [List.nil_append]
    cases hf : acc.find? (fun l' => l'.atom == l.atom) with
    | some seen =>
      exfalso
      have ⟨hseen_mem, hseen_atom⟩ := find?_atom_spec hf
      have hseen_tt := hacc seen hseen_mem
      rw [holds_eq_tt] at hseen_tt
      rw [holds_eq_err, ← hseen_atom] at herr
      rw [herr] at hseen_tt
      cases hsn : seen.negated <;> rw [hsn] at hseen_tt <;> cases hseen_tt
    | none =>
      rw [extendLits_cons_none leaf ys hf]
      have ⟨t, ht, _⟩ := extendLits_prefix (acc ++ [l]) leaf ys
      rw [ht]
      have hsplit : acc ++ [l] ++ t = acc ++ l :: t := by simp
      rw [hsplit]
      have hmem := nodesFrom_mem_of_split (ls := acc ++ l :: t)
        (xs := acc) (ys := t) (l := l) [] rfl
      simpa [pairs] using hmem
  | cons x xs' ih =>
    intro acc hacc hxs hnodup
    have hx := hxs x (by simp)
    have hxs' : ∀ x' ∈ xs', x'.holds v = .tt := fun x' hx' => hxs x' (by simp [hx'])
    have hnodup' : ((xs' ++ l :: ys).map (·.atom)).Nodup := by
      simp only [List.cons_append, List.map_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).2
    have hxatom_notin : x.atom ∉ (xs' ++ l :: ys).map (·.atom) := by
      simp only [List.cons_append, List.map_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    have hxatom_ne : ∀ x' ∈ xs', x'.atom ≠ x.atom := by
      intro x' hx' heq
      exact hxatom_notin (heq ▸ List.mem_map.mpr ⟨x', by simp [hx'], rfl⟩)
    rw [List.cons_append]
    cases hf : acc.find? (fun l' => l'.atom == x.atom) with
    | none =>
      rw [extendLits_cons_none leaf (xs' ++ l :: ys) hf]
      have haccx : ∀ y ∈ acc ++ [x], y.holds v = .tt := by
        intro y hy
        cases List.mem_append.mp hy with
        | inl h => exact hacc y h
        | inr h => simp at h; subst h; exact hx
      have hres := ih (acc ++ [x]) haccx hxs' hnodup'
      have hfilter :
          xs'.filter (fun x' => !((acc ++ [x]).map (·.atom)).contains x'.atom) =
          xs'.filter (fun x' => !(acc.map (·.atom)).contains x'.atom) := by
        apply List.filter_congr
        intro x' hx'
        have hne := hxatom_ne x' hx'
        simp [List.contains_eq_mem, hne]
      rw [hfilter] at hres
      have hxnotacc : ((acc.map (·.atom)).contains x.atom) = false := by
        rw [List.contains_eq_mem]
        exact decide_eq_false (find?_atom_none (l := x) hf)
      have hkeep : (!(acc.map (·.atom)).contains x.atom) = true := by
        rw [hxnotacc]
        rfl
      rw [List.filter_cons_of_pos
        (p := fun x' => !(acc.map (·.atom)).contains x'.atom) (a := x) hkeep]
      have hpairs_acc : pairs (acc ++ [x]) = pairs acc ++ [(x.atom, x.negated)] := by
        simp [pairs]
      rw [hpairs_acc] at hres
      have hpairs_cons :
          pairs (x :: xs'.filter (fun x' => !(acc.map (·.atom)).contains x'.atom)) =
          (x.atom, x.negated) :: pairs (xs'.filter (fun x' => !(acc.map (·.atom)).contains x'.atom)) := by
        simp [pairs]
      rw [hpairs_cons]
      simpa [List.append_assoc] using hres
    | some seen =>
      have ⟨hseen_mem, hseen_atom⟩ := find?_atom_spec hf
      have hseen_tt := hacc seen hseen_mem
      have hsame : seen.negated = x.negated := by
        by_contra hne
        have hflip := holds_flip (v := v) (l := x) (l' := seen)
          hseen_atom.symm (fun h => hne h.symm)
        rw [hflip, hseen_tt] at hx
        cases hx
      rw [extendLits_cons_same leaf (xs' ++ l :: ys) hf hsame]
      have hres := ih acc hacc hxs' hnodup'
      have hxinacc : ((acc.map (·.atom)).contains x.atom) = true := by
        rw [List.contains_eq_mem]
        exact decide_eq_true (List.mem_map.mpr ⟨seen, hseen_mem, hseen_atom⟩)
      have hdrop : ¬ ((!(acc.map (·.atom)).contains x.atom) = true) := by
        rw [hxinacc]
        simp
      rw [List.filter_cons_of_neg
        (p := fun x' => !(acc.map (·.atom)).contains x'.atom) (a := x) hdrop]
      exact hres

end Cedar.DNF
