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

import Cedar.DNF

/-!
Semantic apparatus for the DNF proofs: the three-valued outcome of a literal,
of a literal list read as a conjunction, and of a cube list read as a
disjunction — plus the lemmas connecting them to `interp` of the rendered
expressions (`Cube.toExpr`, `toExpr`). Everything is stated over an arbitrary
valuation `v : Expr → Outcome`; a literal's outcome goes through `interp` of
its atom, so no "the atom is not boolean structure" side conditions are
needed anywhere in the abstract development.
-/

namespace Cedar.DNF

open Cedar.Spec

/-- The outcome of a literal: its atom's outcome, negated for negated
literals. -/
def Literal.holds (v : Expr → Outcome) (l : Literal) : Outcome :=
  if l.negated then (interp v l.atom).negated else interp v l.atom

/-- Sequential three-valued conjunction (the `&&` of two outcomes). -/
def Outcome.and : Outcome → Outcome → Outcome
  | .tt,  o => o
  | .ff,  _ => .ff
  | .err, _ => .err

/-- Sequential three-valued disjunction (the `||` of two outcomes). -/
def Outcome.or : Outcome → Outcome → Outcome
  | .tt,  _ => .tt
  | .ff,  o => o
  | .err, _ => .err

/-- The literals of a cube, evaluated left to right: `.tt` iff all hold. -/
def litsInterp (v : Expr → Outcome) : List Literal → Outcome
  | []        => .tt
  | l :: rest => (l.holds v).and (litsInterp v rest)

/-- The outcome of a cube: that of its literals, capped to `.ff` for a
never-true cube. -/
def Cube.interp (v : Expr → Outcome) (c : Cube) : Outcome :=
  match litsInterp v c.literals with
  | .tt => if c.neverTrue then .ff else .tt
  | o   => o

/-- The outcome of a cube list read as a left-to-right disjunction. -/
def orInterp (v : Expr → Outcome) : List Cube → Outcome
  | []        => .ff
  | c :: rest => (c.interp v).or (orInterp v rest)

/-- A prefix of literal decisions holds: each atom has exactly the recorded
polarity's outcome. -/
def pairsPass (v : Expr → Outcome) (pre : List (Expr × Bool)) : Prop :=
  ∀ pr ∈ pre, interp v pr.1 = (if pr.2 then Outcome.ff else Outcome.tt)

/-! ### Outcome algebra -/

theorem Outcome.and_assoc (o₁ o₂ o₃ : Outcome) :
  (o₁.and o₂).and o₃ = o₁.and (o₂.and o₃)
:= by cases o₁ <;> cases o₂ <;> rfl

theorem Outcome.or_assoc (o₁ o₂ o₃ : Outcome) :
  (o₁.or o₂).or o₃ = o₁.or (o₂.or o₃)
:= by cases o₁ <;> cases o₂ <;> rfl

theorem Outcome.and_eq_tt {o₁ o₂ : Outcome} :
  o₁.and o₂ = .tt ↔ o₁ = .tt ∧ o₂ = .tt
:= by cases o₁ <;> cases o₂ <;> simp [Outcome.and]

theorem Outcome.and_eq_err {o₁ o₂ : Outcome} :
  o₁.and o₂ = .err ↔ o₁ = .err ∨ (o₁ = .tt ∧ o₂ = .err)
:= by cases o₁ <;> cases o₂ <;> simp [Outcome.and]

theorem Outcome.ff_and (o : Outcome) : Outcome.ff.and o = .ff := rfl

theorem Outcome.err_and (o : Outcome) : Outcome.err.and o = .err := rfl

/-! ### Literal and literal-list semantics -/

theorem holds_eq_tt {v : Expr → Outcome} {l : Literal} :
  l.holds v = .tt ↔ interp v l.atom = (if l.negated then Outcome.ff else Outcome.tt)
:= by
  cases h : interp v l.atom <;> cases hn : l.negated <;>
    simp [Literal.holds, hn, h, Outcome.negated]

theorem holds_eq_err {v : Expr → Outcome} {l : Literal} :
  l.holds v = .err ↔ interp v l.atom = .err
:= by
  cases h : interp v l.atom <;> cases hn : l.negated <;>
    simp [Literal.holds, hn, h, Outcome.negated]

/-- Two literals on the same atom with opposite polarity cannot both hold. -/
theorem holds_opposite {v : Expr → Outcome} {l l' : Literal}
  (ha : l.atom = l'.atom) (hn : l.negated = !l'.negated) :
  ¬ (l.holds v = .tt ∧ l'.holds v = .tt)
:= by
  rintro ⟨h₁, h₂⟩
  rw [holds_eq_tt] at h₁ h₂
  rw [ha] at h₁
  cases hb : l'.negated <;> rw [hb] at h₂ <;> simp [hb] at hn <;>
    rw [hn] at h₁ <;> simp at h₁ <;> simp at h₂ <;> simp [h₂] at h₁

/-- Two literals on the same atom with the same polarity have the same
outcome. -/
theorem holds_congr {v : Expr → Outcome} {l l' : Literal}
  (ha : l.atom = l'.atom) (hn : l.negated = l'.negated) :
  l.holds v = l'.holds v
:= by simp [Literal.holds, ha, hn]

theorem litsInterp_append (v : Expr → Outcome) (xs ys : List Literal) :
  litsInterp v (xs ++ ys) = (litsInterp v xs).and (litsInterp v ys)
:= by
  induction xs with
  | nil => simp [litsInterp, Outcome.and]
  | cons l rest ih => simp [litsInterp, ih, Outcome.and_assoc]

theorem litsInterp_eq_tt {v : Expr → Outcome} {ls : List Literal} :
  litsInterp v ls = .tt ↔ ∀ l ∈ ls, l.holds v = .tt
:= by
  induction ls with
  | nil => simp [litsInterp]
  | cons l rest ih => simp [litsInterp, Outcome.and_eq_tt, ih]

/-- If the literals err, the first erring literal has a passing prefix. -/
theorem litsInterp_eq_err {v : Expr → Outcome} {ls : List Literal} :
  litsInterp v ls = .err ↔
    ∃ xs l ys, ls = xs ++ l :: ys ∧ litsInterp v xs = .tt ∧ l.holds v = .err
:= by
  induction ls with
  | nil => simp [litsInterp]
  | cons l rest ih =>
    simp only [litsInterp, Outcome.and_eq_err]
    constructor
    · rintro (h | ⟨hl, hrest⟩)
      · exact ⟨[], l, rest, rfl, rfl, h⟩
      · have ⟨xs, l', ys, hsplit, hxs, hl'⟩ := ih.mp hrest
        exact ⟨l :: xs, l', ys, by simp [hsplit],
               by simp [litsInterp, hl, hxs, Outcome.and], hl'⟩
    · rintro ⟨xs, l', ys, hsplit, hxs, hl'⟩
      cases xs with
      | nil =>
        simp at hsplit
        exact .inl (by rw [hsplit.1]; exact hl')
      | cons x xs' =>
        simp at hsplit
        obtain ⟨hlx, hrest⟩ := hsplit
        rw [litsInterp] at hxs
        have ⟨hx, hxs'⟩ := Outcome.and_eq_tt.mp hxs
        subst hlx
        exact .inr ⟨hx, ih.mpr ⟨xs', l', ys, hrest, hxs', hl'⟩⟩

/-- A prefix that fails or errs decides the whole list. -/
theorem litsInterp_prefix_ne_tt {v : Expr → Outcome} {xs ys : List Literal}
  (h : litsInterp v xs ≠ .tt) :
  litsInterp v (xs ++ ys) = litsInterp v xs
:= by
  rw [litsInterp_append]
  cases hx : litsInterp v xs
  · exact absurd hx h
  · rfl
  · rfl

/-! ### The rendered expressions interpret as the cube semantics -/

theorem interp_boolLit (v : Expr → Outcome) (b : Bool) :
  interp v (boolLit b) = if b then .tt else .ff
:= by cases b <;> rfl

theorem interp_literal_toExpr (v : Expr → Outcome) (l : Literal) :
  interp v l.toExpr = l.holds v
:= by
  cases hn : l.negated <;> simp [Literal.toExpr, Literal.holds, hn, interp]

theorem interp_and (v : Expr → Outcome) (l r : Expr) :
  interp v (.and l r) = (interp v l).and (interp v r)
:= by cases h : interp v l <;> simp [interp, h, Outcome.and]

theorem interp_or (v : Expr → Outcome) (l r : Expr) :
  interp v (.or l r) = (interp v l).or (interp v r)
:= by cases h : interp v l <;> simp [interp, h, Outcome.or]

theorem interp_and_chain (v : Expr → Outcome) (ls : List Literal) (init : Expr) :
  interp v (ls.foldl (fun acc l => .and acc l.toExpr) init) =
    (interp v init).and (litsInterp v ls)
:= by
  induction ls generalizing init with
  | nil => cases h : interp v init <;> simp [litsInterp, h, Outcome.and]
  | cons l rest ih =>
    simp only [List.foldl, litsInterp]
    rw [ih, interp_and, interp_literal_toExpr, Outcome.and_assoc]

theorem interp_cube_toExpr (v : Expr → Outcome) (c : Cube) :
  interp v c.toExpr = c.interp v
:= by
  have hconj : ∀ (l : Literal) (rest : List Literal),
      interp v (rest.foldl (fun acc l' => .and acc l'.toExpr) l.toExpr) =
        litsInterp v (l :: rest) := by
    intro l rest
    rw [interp_and_chain, interp_literal_toExpr]
    rfl
  match c with
  | ⟨[], false⟩ => simp [Cube.toExpr, Cube.interp, litsInterp, interp_boolLit]
  | ⟨[], true⟩  => simp [Cube.toExpr, Cube.interp, litsInterp, interp_boolLit]
  | ⟨l :: rest, false⟩ =>
    show interp v (rest.foldl (fun acc l' => .and acc l'.toExpr) l.toExpr) = _
    rw [hconj]
    unfold Cube.interp
    cases h : litsInterp v (l :: rest) <;> simp
  | ⟨l :: rest, true⟩ =>
    show interp v (.and (rest.foldl (fun acc l' => .and acc l'.toExpr) l.toExpr) (boolLit false)) = _
    rw [interp_and, hconj, interp_boolLit]
    unfold Cube.interp
    cases h : litsInterp v (l :: rest) <;> simp [Outcome.and]

theorem interp_or_chain (v : Expr → Outcome) (cs : List Cube) (init : Expr) :
  interp v (cs.foldl (fun acc c => .or acc c.toExpr) init) =
    (interp v init).or (orInterp v cs)
:= by
  induction cs generalizing init with
  | nil => cases h : interp v init <;> simp [orInterp, h, Outcome.or]
  | cons c rest ih =>
    simp only [List.foldl, orInterp]
    rw [ih, interp_or, interp_cube_toExpr, Outcome.or_assoc]

theorem interp_toExpr (v : Expr → Outcome) (cs : List Cube) :
  interp v (toExpr cs) = orInterp v cs
:= by
  match cs with
  | [] => simp [toExpr, orInterp, interp_boolLit]
  | c :: rest =>
    simp only [toExpr, orInterp]
    rw [interp_or_chain, interp_cube_toExpr]

/-! ### Disjunction outcomes from cube outcomes -/

theorem orInterp_eq_ff {v : Expr → Outcome} {cs : List Cube}
  (h : ∀ c ∈ cs, c.interp v = .ff) :
  orInterp v cs = .ff
:= by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [orInterp, h c (by simp)]
    exact ih (fun c' hc' => h c' (by simp [hc']))

theorem orInterp_eq_tt {v : Expr → Outcome} {cs : List Cube} {c : Cube}
  (hmem : c ∈ cs) (htt : c.interp v = .tt)
  (hnoerr : ∀ c' ∈ cs, c'.interp v ≠ .err) :
  orInterp v cs = .tt
:= by
  induction cs with
  | nil => cases hmem
  | cons c' rest ih =>
    simp only [orInterp]
    cases h : c'.interp v
    · rfl
    · cases List.mem_cons.mp hmem with
      | inl heq => subst heq; rw [htt] at h; cases h
      | inr hrest => exact ih hrest (fun c'' hc'' => hnoerr c'' (by simp [hc'']))
    · exact absurd h (hnoerr c' (by simp))

theorem orInterp_eq_err {v : Expr → Outcome} {cs : List Cube} {c : Cube}
  (hmem : c ∈ cs) (herr : c.interp v = .err)
  (hnott : ∀ c' ∈ cs, c'.interp v ≠ .tt) :
  orInterp v cs = .err
:= by
  induction cs with
  | nil => cases hmem
  | cons c' rest ih =>
    simp only [orInterp]
    cases h : c'.interp v
    · exact absurd h (hnott c' (by simp))
    · cases List.mem_cons.mp hmem with
      | inl heq => subst heq; rw [herr] at h; cases h
      | inr hrest => exact ih hrest (fun c'' hc'' => hnott c'' (by simp [hc'']))
    · rfl

end Cedar.DNF
