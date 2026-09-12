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

import Cedar.Thm.SymCC.Evaluator.Outcomes
import Cedar.Thm.SymCC.Opt.Compiler

/-!
Invariants of the symbolic evaluator's tree builder
(`Cedar.SymCC.Opt.buildTree`): every node's term is exactly what the
(unoptimized) symbolic compiler produces for that node's expression, which is
what lets the soundness proofs apply `compile_bisimulation` at every node.
-/

namespace Cedar.Thm

open Cedar Data Spec SymCC
open Cedar.SymCC.Opt

/--
The term component of `Opt.compileAnd` ignores footprints and mirrors
`SymCC.compileAnd`.
-/
theorem opt_compileAnd_term (t₁ : Term) (fp₁ : Data.Set Term)
    (r : SymCC.Result CompileResult) :
  (Opt.compileAnd ⟨t₁, fp₁⟩ r).map CompileResult.term
    = SymCC.compileAnd t₁ (r.map CompileResult.term)
:= by
  cases r <;>
    (unfold Opt.compileAnd SymCC.compileAnd
     split <;> (try split) <;>
       simp_all [Except.map, Except.bind_ok, Except.bind_err] <;>
       (try (split <;> rename_i heq <;> split at heq <;> (try cases heq) <;>
             simp_all [Except.map, Factory.ite, Factory.option.get])))

/--
The term component of `Opt.compileOr` ignores footprints and mirrors
`SymCC.compileOr`.
-/
theorem opt_compileOr_term (t₁ : Term) (fp₁ : Data.Set Term)
    (r : SymCC.Result CompileResult) :
  (Opt.compileOr ⟨t₁, fp₁⟩ r).map CompileResult.term
    = SymCC.compileOr t₁ (r.map CompileResult.term)
:= by
  cases r <;>
    (unfold Opt.compileOr SymCC.compileOr
     split <;> (try split) <;>
       simp_all [Except.map, Except.bind_ok, Except.bind_err] <;>
       (try (split <;> rename_i heq <;> split at heq <;> (try cases heq) <;>
             simp_all [Except.map, Factory.ite, Factory.option.get])))

/--
The term component of `Opt.compileIf` ignores footprints and mirrors
`SymCC.compileIf`.
-/
theorem opt_compileIf_term (t₁ : Term) (fp₁ : Data.Set Term)
    (r₂ r₃ : SymCC.Result CompileResult) :
  (Opt.compileIf ⟨t₁, fp₁⟩ r₂ r₃).map CompileResult.term
    = SymCC.compileIf t₁ (r₂.map CompileResult.term) (r₃.map CompileResult.term)
:= by
  cases r₂ <;> cases r₃ <;>
    (unfold Opt.compileIf SymCC.compileIf
     split <;> (try split) <;>
       simp_all [Except.map, Except.bind_ok, Except.bind_err] <;>
       (try (split <;> rename_i heq <;> split at heq <;> (try cases heq) <;>
             simp_all [Except.map, Factory.ite, Factory.option.get])))

/--
The term component of `Opt.compileNot` mirrors the `unaryApp .not` slice of
`SymCC.compile`.
-/
theorem opt_compileNot_term (t : Term) (fp : Data.Set Term) :
  (Opt.compileNot ⟨t, fp⟩).map CompileResult.term
    = (do
        let t' ← SymCC.compileApp₁ .not (Factory.option.get t)
        .ok (Factory.ifSome t t'))
:= by
  unfold Opt.compileNot Opt.compileApp₁ SymCC.compileApp₁ CompileResult.mapTerm
  split <;> (try split) <;>
    simp_all [Except.map, Except.bind_ok, Except.bind_err, CompileResult.mapTerm]

/--
Result equivalence up to the error *value*: same success value, and failure
implies failure (with a possibly different error). `buildTree` reports a
child's own compilation error where `SymCC.compile` may report the node
compiler's (mirroring the Rust `sub_err` choice), so this — not equality — is
the correspondence that holds.
-/
def ErrEquiv (r r' : SymCC.Result α) : Prop :=
  (∀ v, r = .ok v → r' = .ok v) ∧ (∀ e, r = .error e → ∃ e', r' = .error e')

theorem errEquiv_refl (r : SymCC.Result α) : ErrEquiv r r :=
  ⟨λ _ h => h, λ e h => ⟨e, h⟩⟩

theorem errEquiv_of_eq {r r' : SymCC.Result α} : r = r' → ErrEquiv r r' :=
  λ h => h ▸ errEquiv_refl r

theorem errEquiv_error {e e' : SymCC.Error} :
  ErrEquiv (α := α) (.error e) (.error e')
:= ⟨by simp, λ _ _ => ⟨e', rfl⟩⟩

theorem errEquiv_trans {r₁ r₂ r₃ : SymCC.Result α} :
  ErrEquiv r₁ r₂ → ErrEquiv r₂ r₃ → ErrEquiv r₁ r₃
:= by
  intro ⟨hok₁, herr₁⟩ ⟨hok₂, herr₂⟩
  refine ⟨λ v h => hok₂ v (hok₁ v h), λ e h => ?_⟩
  obtain ⟨e', he'⟩ := herr₁ e h
  exact herr₂ e' he'

/-- `SymCC.compileAnd` preserves `ErrEquiv` of its second argument. -/
theorem compileAnd_erreq {t : Term} {r r' : SymCC.Result Term} :
  ErrEquiv r r' → ErrEquiv (SymCC.compileAnd t r) (SymCC.compileAnd t r')
:= by
  intro ⟨hok, herr⟩
  unfold SymCC.compileAnd
  split
  · exact errEquiv_refl _
  · cases hr : r
    case error e =>
      obtain ⟨e', he'⟩ := herr e hr
      simp [he', ErrEquiv]
    case ok v =>
      have := hok v hr
      simp [this]
      exact errEquiv_refl _
  · exact errEquiv_refl _

/-- `SymCC.compileOr` preserves `ErrEquiv` of its second argument. -/
theorem compileOr_erreq {t : Term} {r r' : SymCC.Result Term} :
  ErrEquiv r r' → ErrEquiv (SymCC.compileOr t r) (SymCC.compileOr t r')
:= by
  intro ⟨hok, herr⟩
  unfold SymCC.compileOr
  split
  · exact errEquiv_refl _
  · cases hr : r
    case error e =>
      obtain ⟨e', he'⟩ := herr e hr
      simp [he', ErrEquiv]
    case ok v =>
      have := hok v hr
      simp [this]
      exact errEquiv_refl _
  · exact errEquiv_refl _

/-- `SymCC.compileIf` preserves `ErrEquiv` of its branch arguments. -/
theorem compileIf_erreq {t : Term} {r₂ r₂' r₃ r₃' : SymCC.Result Term} :
  ErrEquiv r₂ r₂' → ErrEquiv r₃ r₃' →
  ErrEquiv (SymCC.compileIf t r₂ r₃) (SymCC.compileIf t r₂' r₃')
:= by
  intro h₂ h₃
  unfold SymCC.compileIf
  split
  · exact h₂
  · exact h₃
  · obtain ⟨hok₂, herr₂⟩ := h₂
    obtain ⟨hok₃, herr₃⟩ := h₃
    cases hr₂ : r₂
    case error e =>
      obtain ⟨e', he'⟩ := herr₂ e hr₂
      simp [he', ErrEquiv]
    case ok v₂ =>
      have hv₂ := hok₂ v₂ hr₂
      cases hr₃ : r₃
      case error e =>
        obtain ⟨e', he'⟩ := herr₃ e hr₃
        simp [hv₂, he', ErrEquiv]
      case ok v₃ =>
        have hv₃ := hok₃ v₃ hr₃
        simp [hv₂, hv₃]
        exact errEquiv_refl _
  · exact errEquiv_refl _

/--
Every node's term equals what the symbolic compiler produces for its
expression, up to the identity of compilation errors (`buildTree` prefers a
child's error where the compiler reports the node's).
-/
theorem buildTree_erreq (x : Expr) (εnv : SymEnv) :
  ErrEquiv ((Opt.buildTree x εnv).map (λ (p : SENode × Data.Set Term) => p.1.term))
           (SymCC.compile x εnv)
:= by
  induction x using Opt.buildTree.induct with
  | case1 x₁ x₂ ihl ihr =>
    cases hB₁ : Opt.buildTree x₁ εnv with
    | error e =>
      obtain ⟨e', he'⟩ := ihl.right e (by simp [hB₁, Except.map])
      have hL : (Opt.buildTree (.and x₁ x₂) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
          = .error e := by
        simp [Opt.buildTree, hB₁, Except.map]
      have hR : SymCC.compile (.and x₁ x₂) εnv = .error e' := by
        simp [SymCC.compile, he']
      rw [hL, hR] ; exact errEquiv_error
    | ok p =>
      obtain ⟨l, fp₁⟩ := p
      have hC₁ : SymCC.compile x₁ εnv = .ok l.term := ihl.left l.term (by simp [hB₁, Except.map])
      have hRmap : ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
            (⟨p.1.term, ∅⟩ : CompileResult))).map CompileResult.term
          = (Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) => p.1.term) := by
        cases Opt.buildTree x₂ εnv <;> simp [Except.map]
      have hmatch : ErrEquiv
          ((Opt.buildTree (.and x₁ x₂) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term))
          ((Opt.compileAnd ⟨l.term, ∅⟩ ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
            (⟨p.1.term, ∅⟩ : CompileResult)))).map CompileResult.term) := by
        simp only [Opt.buildTree, hB₁, Except.bind_ok]
        cases hca : Opt.compileAnd ⟨l.term, ∅⟩ ((Opt.buildTree x₂ εnv).map
            (λ (p : SENode × Data.Set Term) => (⟨p.1.term, ∅⟩ : CompileResult))) with
        | error e => simp [Except.map] ; exact errEquiv_error
        | ok res => simp [Except.map] ; exact errEquiv_refl _
      have hR : SymCC.compile (.and x₁ x₂) εnv
          = SymCC.compileAnd l.term (SymCC.compile x₂ εnv) := by
        simp [SymCC.compile, hC₁]
      rw [hR]
      exact errEquiv_trans hmatch
        (errEquiv_trans (errEquiv_of_eq (opt_compileAnd_term l.term ∅ _))
          (compileAnd_erreq (hRmap ▸ ihr)))
  | case2 x₁ x₂ ihl ihr =>
    cases hB₁ : Opt.buildTree x₁ εnv with
    | error e =>
      obtain ⟨e', he'⟩ := ihl.right e (by simp [hB₁, Except.map])
      have hL : (Opt.buildTree (.or x₁ x₂) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
          = .error e := by
        simp [Opt.buildTree, hB₁, Except.map]
      have hR : SymCC.compile (.or x₁ x₂) εnv = .error e' := by
        simp [SymCC.compile, he']
      rw [hL, hR] ; exact errEquiv_error
    | ok p =>
      obtain ⟨l, fp₁⟩ := p
      have hC₁ : SymCC.compile x₁ εnv = .ok l.term := ihl.left l.term (by simp [hB₁, Except.map])
      have hRmap : ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
            (⟨p.1.term, ∅⟩ : CompileResult))).map CompileResult.term
          = (Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) => p.1.term) := by
        cases Opt.buildTree x₂ εnv <;> simp [Except.map]
      have hmatch : ErrEquiv
          ((Opt.buildTree (.or x₁ x₂) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term))
          ((Opt.compileOr ⟨l.term, ∅⟩ ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
            (⟨p.1.term, ∅⟩ : CompileResult)))).map CompileResult.term) := by
        simp only [Opt.buildTree, hB₁, Except.bind_ok]
        cases hca : Opt.compileOr ⟨l.term, ∅⟩ ((Opt.buildTree x₂ εnv).map
            (λ (p : SENode × Data.Set Term) => (⟨p.1.term, ∅⟩ : CompileResult))) with
        | error e => simp [Except.map] ; exact errEquiv_error
        | ok res => simp [Except.map] ; exact errEquiv_refl _
      have hR : SymCC.compile (.or x₁ x₂) εnv
          = SymCC.compileOr l.term (SymCC.compile x₂ εnv) := by
        simp [SymCC.compile, hC₁]
      rw [hR]
      exact errEquiv_trans hmatch
        (errEquiv_trans (errEquiv_of_eq (opt_compileOr_term l.term ∅ _))
          (compileOr_erreq (hRmap ▸ ihr)))
  | case3 x₁ x₂ x₃ ihc iha ihb =>
    cases hcr : Opt.compile (.ite x₁ x₂ x₃) εnv with
    | error e =>
      have hL : (Opt.buildTree (.ite x₁ x₂ x₃) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
          = .error e := by
        simp [Opt.buildTree, hcr, Except.map]
      have hR : SymCC.compile (.ite x₁ x₂ x₃) εnv = .error e := by
        have h := Opt.compile.correctness (.ite x₁ x₂ x₃) εnv
        rw [hcr] at h
        cases hc : SymCC.compile (.ite x₁ x₂ x₃) εnv <;> simp [hc] at h <;> simp_all
      rw [hL, hR] ; exact errEquiv_error
    | ok cr =>
      have hcompile : SymCC.compile (.ite x₁ x₂ x₃) εnv = .ok cr.term := by
        have h := Opt.compile.correctness (.ite x₁ x₂ x₃) εnv
        rw [hcr] at h
        cases hc : SymCC.compile (.ite x₁ x₂ x₃) εnv <;> rw [hc] at h <;> simp_all
      by_cases hty : cr.term.typeOf = .option .bool
      case neg =>
        have hL : (Opt.buildTree (.ite x₁ x₂ x₃) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
            = .ok cr.term := by
          simp [Opt.buildTree, hcr, hty, Except.map, SENode.term]
        rw [hL, hcompile] ; exact errEquiv_refl _
      case pos =>
        cases hB₁ : Opt.buildTree x₁ εnv with
        | error e =>
          obtain ⟨e', he'⟩ := ihc.right e (by simp [hB₁, Except.map])
          have hL : (Opt.buildTree (.ite x₁ x₂ x₃) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
              = .error e := by
            simp [Opt.buildTree, hcr, hty, hB₁, Except.map]
          have hR : SymCC.compile (.ite x₁ x₂ x₃) εnv = .error e' := by
            simp [SymCC.compile, he']
          rw [hL, hR] ; exact errEquiv_error
        | ok p =>
          obtain ⟨c, fpc⟩ := p
          have hC₁ : SymCC.compile x₁ εnv = .ok c.term := ihc.left c.term (by simp [hB₁, Except.map])
          have hRmap₂ : ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
                (⟨p.1.term, ∅⟩ : CompileResult))).map CompileResult.term
              = (Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) => p.1.term) := by
            cases Opt.buildTree x₂ εnv <;> simp [Except.map]
          have hRmap₃ : ((Opt.buildTree x₃ εnv).map (λ (p : SENode × Data.Set Term) =>
                (⟨p.1.term, ∅⟩ : CompileResult))).map CompileResult.term
              = (Opt.buildTree x₃ εnv).map (λ (p : SENode × Data.Set Term) => p.1.term) := by
            cases Opt.buildTree x₃ εnv <;> simp [Except.map]
          have hmatch : ErrEquiv
              ((Opt.buildTree (.ite x₁ x₂ x₃) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term))
              ((Opt.compileIf ⟨c.term, ∅⟩
                ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
                  (⟨p.1.term, ∅⟩ : CompileResult)))
                ((Opt.buildTree x₃ εnv).map (λ (p : SENode × Data.Set Term) =>
                  (⟨p.1.term, ∅⟩ : CompileResult)))).map CompileResult.term) := by
            simp only [Opt.buildTree, hcr, hty, hB₁, Except.bind_ok, if_pos]
            cases hca : Opt.compileIf ⟨c.term, ∅⟩
                ((Opt.buildTree x₂ εnv).map (λ (p : SENode × Data.Set Term) =>
                  (⟨p.1.term, ∅⟩ : CompileResult)))
                ((Opt.buildTree x₃ εnv).map (λ (p : SENode × Data.Set Term) =>
                  (⟨p.1.term, ∅⟩ : CompileResult))) with
            | error e => simp [Except.map] ; exact errEquiv_error
            | ok res => simp [Except.map] ; exact errEquiv_refl _
          have hR : SymCC.compile (.ite x₁ x₂ x₃) εnv
              = SymCC.compileIf c.term (SymCC.compile x₂ εnv) (SymCC.compile x₃ εnv) := by
            simp [SymCC.compile, hC₁]
          rw [hR]
          exact errEquiv_trans hmatch
            (errEquiv_trans (errEquiv_of_eq (opt_compileIf_term c.term ∅ _ _))
              (compileIf_erreq (hRmap₂ ▸ iha) (hRmap₃ ▸ ihb)))
  | case4 x₁ ihc =>
    cases hB₁ : Opt.buildTree x₁ εnv with
    | error e =>
      obtain ⟨e', he'⟩ := ihc.right e (by simp [hB₁, Except.map])
      have hL : (Opt.buildTree (.unaryApp .not x₁) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
          = .error e := by
        simp [Opt.buildTree, hB₁, Except.map]
      have hR : SymCC.compile (.unaryApp .not x₁) εnv = .error e' := by
        simp [SymCC.compile, he']
      rw [hL, hR] ; exact errEquiv_error
    | ok p =>
      obtain ⟨c, fp⟩ := p
      have hC₁ : SymCC.compile x₁ εnv = .ok c.term := ihc.left c.term (by simp [hB₁, Except.map])
      have hnot := opt_compileNot_term c.term ∅
      have hR : SymCC.compile (.unaryApp .not x₁) εnv
          = (do
              let t' ← SymCC.compileApp₁ .not (Factory.option.get c.term)
              .ok (Factory.ifSome c.term t')) := by
        simp only [SymCC.compile, hC₁, Except.bind_ok]
      have hL : (Opt.buildTree (.unaryApp .not x₁) εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
          = (Opt.compileNot ⟨c.term, ∅⟩).map CompileResult.term := by
        simp only [Opt.buildTree, hB₁, Except.bind_ok]
        cases hcn : Opt.compileNot ⟨c.term, ∅⟩ <;> simp [Except.map, SENode.term]
      rw [hL, hR, hnot]
      exact errEquiv_refl _
  | case5 x hne₁ hne₂ hne₃ hne₄ =>
    have hL : (Opt.buildTree x εnv).map (λ (p : SENode × Data.Set Term) => p.1.term)
        = (Opt.compile x εnv).map CompileResult.term := by
      unfold Opt.buildTree
      split
      case h_1 => simp_all
      case h_2 => simp_all
      case h_3 => simp_all
      case h_4 => simp_all
      case h_5 =>
        cases hc : Opt.compile x εnv <;> simp [Except.map, SENode.term]
    have hR : (Opt.compile x εnv).map CompileResult.term = SymCC.compile x εnv := by
      have h := Opt.compile.correctness x εnv
      rw [h]
      cases hc : SymCC.compile x εnv <;> simp [Except.map]
    rw [hL, hR]
    exact errEquiv_refl _

/-- A successful `buildTree` yields the compiler's term for the expression. -/
theorem buildTree_term {x : Expr} {εnv : SymEnv} {n : SENode} {fp : Data.Set Term} :
  Opt.buildTree x εnv = .ok (n, fp) → SymCC.compile x εnv = .ok n.term
:= by
  intro h
  exact (buildTree_erreq x εnv).left n.term (by simp [h, Except.map])

/--
The structural invariant of a built tree: every node carries its own
expression and the compiler's term for it, and present children are
themselves well-built for the corresponding sub-expressions.
-/
inductive SENode.WellBuilt (εnv : SymEnv) : SENode → Expr → Prop where
  | atom {x : Expr} {t : Term} {cs ft ff fn : List Existence} {keep : Bool} :
      SymCC.compile x εnv = .ok t →
      WellBuilt εnv (.atom x t cs ft ff fn keep) x
  | not {x₁ : Expr} {t : Term} {c : SENode} :
      WellBuilt εnv c x₁ →
      SymCC.compile (.unaryApp .not x₁) εnv = .ok t →
      WellBuilt εnv (.not (.unaryApp .not x₁) t c) (.unaryApp .not x₁)
  | and {x₁ x₂ : Expr} {t : Term} {l : SENode} {r : Option SENode} :
      WellBuilt εnv l x₁ →
      (∀ n, r = .some n → WellBuilt εnv n x₂) →
      SymCC.compile (.and x₁ x₂) εnv = .ok t →
      WellBuilt εnv (.and (.and x₁ x₂) t l r) (.and x₁ x₂)
  | or {x₁ x₂ : Expr} {t : Term} {l : SENode} {r : Option SENode} :
      WellBuilt εnv l x₁ →
      (∀ n, r = .some n → WellBuilt εnv n x₂) →
      SymCC.compile (.or x₁ x₂) εnv = .ok t →
      WellBuilt εnv (.or (.or x₁ x₂) t l r) (.or x₁ x₂)
  | ite {x₁ x₂ x₃ : Expr} {t : Term} {c : SENode} {a b : Option SENode} :
      WellBuilt εnv c x₁ →
      (∀ n, a = .some n → WellBuilt εnv n x₂) →
      (∀ n, b = .some n → WellBuilt εnv n x₃) →
      SymCC.compile (.ite x₁ x₂ x₃) εnv = .ok t →
      WellBuilt εnv (.ite (.ite x₁ x₂ x₃) t c a b) (.ite x₁ x₂ x₃)

/-- A well-built node carries the compiler's term for its expression. -/
theorem wellBuilt_compile {εnv : SymEnv} {n : SENode} {x : Expr} :
  SENode.WellBuilt εnv n x → SymCC.compile x εnv = .ok n.term ∧ n.expr = x
:= by
  intro h
  cases h <;> simp_all [SENode.term, SENode.expr]

/-- A successful `buildTree` produces a well-built tree. -/
theorem buildTree_wellBuilt {x : Expr} {εnv : SymEnv} {n : SENode} {fp : Data.Set Term} :
  Opt.buildTree x εnv = .ok (n, fp) → SENode.WellBuilt εnv n x
:= by
  induction x using Opt.buildTree.induct generalizing n fp with
  | case1 x₁ x₂ ihl ihr =>
    intro h
    have hterm := buildTree_term h
    simp only [Opt.buildTree] at h
    cases hB₁ : Opt.buildTree x₁ εnv <;> rw [hB₁] at h <;>
      simp only [Except.bind_ok, Except.bind_err] at h
    case error => exact absurd h (by simp)
    case ok p =>
      obtain ⟨l, fp₁⟩ := p
      cases hB₂ : Opt.buildTree x₂ εnv <;> rw [hB₂] at h <;>
        cases hca : Opt.compileAnd ⟨l.term, ∅⟩ _ <;> rw [hca] at h <;>
        simp only [Opt.buildTree.childErr, Opt.buildTree.childParts] at h
      all_goals simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      all_goals (obtain ⟨hn, hfp⟩ := h ; subst hn)
      · exact .and (ihl hB₁) (λ _ hnn => nomatch hnn) hterm
      · exact .and (ihl hB₁)
          (λ nn hnn => by injection hnn with h₂ ; subst h₂ ; exact ihr hB₂) hterm
  | case2 x₁ x₂ ihl ihr =>
    intro h
    have hterm := buildTree_term h
    simp only [Opt.buildTree] at h
    cases hB₁ : Opt.buildTree x₁ εnv <;> rw [hB₁] at h <;>
      simp only [Except.bind_ok, Except.bind_err] at h
    case error => exact absurd h (by simp)
    case ok p =>
      obtain ⟨l, fp₁⟩ := p
      cases hB₂ : Opt.buildTree x₂ εnv <;> rw [hB₂] at h <;>
        cases hca : Opt.compileOr ⟨l.term, ∅⟩ _ <;> rw [hca] at h <;>
        simp only [Opt.buildTree.childErr, Opt.buildTree.childParts] at h
      all_goals simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      all_goals (obtain ⟨hn, hfp⟩ := h ; subst hn)
      · exact .or (ihl hB₁) (λ _ hnn => nomatch hnn) hterm
      · exact .or (ihl hB₁)
          (λ nn hnn => by injection hnn with h₂ ; subst h₂ ; exact ihr hB₂) hterm
  | case3 x₁ x₂ x₃ ihc iha ihb =>
    intro h
    have hterm := buildTree_term h
    simp only [Opt.buildTree] at h
    cases hcr : Opt.compile (.ite x₁ x₂ x₃) εnv <;> rw [hcr] at h <;>
      simp only [Except.bind_ok, Except.bind_err] at h
    case error => exact absurd h (by simp)
    case ok cr =>
      by_cases hty : cr.term.typeOf = .option .bool
      case neg =>
        rw [if_neg hty] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hn, hfp⟩ := h ; subst hn
        exact .atom hterm
      case pos =>
        rw [if_pos hty] at h
        cases hB₁ : Opt.buildTree x₁ εnv <;> rw [hB₁] at h <;>
          simp only [Except.bind_ok, Except.bind_err] at h
        case error => exact absurd h (by simp)
        case ok p =>
          obtain ⟨c, fpc⟩ := p
          cases hB₂ : Opt.buildTree x₂ εnv <;> rw [hB₂] at h <;>
            cases hB₃ : Opt.buildTree x₃ εnv <;> rw [hB₃] at h <;>
            cases hca : Opt.compileIf ⟨c.term, ∅⟩ _ _ <;> rw [hca] at h <;>
            simp only [Opt.buildTree.childErr, Opt.buildTree.childParts] at h
          all_goals simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
          all_goals (obtain ⟨hn, hfp⟩ := h ; subst hn)
          · exact .ite (ihc hB₁) (λ _ hnn => nomatch hnn) (λ _ hnn => nomatch hnn) hterm
          · exact .ite (ihc hB₁) (λ _ hnn => nomatch hnn)
              (λ nn hnn => by injection hnn with h₂ ; subst h₂ ; exact ihb hB₃) hterm
          · exact .ite (ihc hB₁)
              (λ nn hnn => by injection hnn with h₂ ; subst h₂ ; exact iha hB₂)
              (λ _ hnn => nomatch hnn) hterm
          · exact .ite (ihc hB₁)
              (λ nn hnn => by injection hnn with h₂ ; subst h₂ ; exact iha hB₂)
              (λ nn hnn => by injection hnn with h₂ ; subst h₂ ; exact ihb hB₃) hterm
  | case4 x₁ ihc =>
    intro h
    have hterm := buildTree_term h
    simp only [Opt.buildTree] at h
    cases hB₁ : Opt.buildTree x₁ εnv <;> rw [hB₁] at h <;>
      simp only [Except.bind_ok, Except.bind_err] at h
    case error => exact absurd h (by simp)
    case ok p =>
      obtain ⟨c, fp₁⟩ := p
      cases hcn : Opt.compileNot ⟨c.term, ∅⟩ <;> rw [hcn] at h <;>
        simp only [Except.bind_ok, Except.bind_err] at h
      case error => exact absurd h (by simp)
      case ok res =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hn, hfp⟩ := h ; subst hn
        exact .not (ihc hB₁) hterm
  | case5 x hne₁ hne₂ hne₃ hne₄ =>
    intro h
    have hterm := buildTree_term h
    unfold Opt.buildTree at h
    split at h
    case h_1 => simp_all
    case h_2 => simp_all
    case h_3 => simp_all
    case h_4 => simp_all
    case h_5 =>
      cases hc : Opt.compile x εnv <;> rw [hc] at h <;>
        simp only [Except.bind_ok, Except.bind_err] at h
      case error => exact absurd h (by simp)
      case ok cr =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨hn, hfp⟩ := h ; subst hn
        exact .atom hterm

/-! ### Marking the kept guards (plan 5) preserves terms and well-builtness -/

theorem markKept_term (ks : List Expr) (n : SENode) :
  (markKept ks n).term = n.term
:= by
  cases n <;> (unfold markKept ; rfl)

theorem markKept_wellBuilt {εnv : SymEnv} {ks : List Expr} {n : SENode} {x : Expr}
    (h : SENode.WellBuilt εnv n x) :
  SENode.WellBuilt εnv (markKept ks n) x
:= by
  induction h with
  | atom hok => unfold markKept ; exact .atom hok
  | not _ hok ih => unfold markKept ; exact .not ih hok
  | @and _ _ _ _ r _ _ hok ihl ihr =>
    unfold markKept
    refine .and ihl ?_ hok
    intro n hn
    cases r with
    | none => try dsimp only at hn ; cases hn
    | some m => try dsimp only at hn ; injection hn with hn ; subst hn ; exact ihr m rfl
  | @or _ _ _ _ r _ _ hok ihl ihr =>
    unfold markKept
    refine .or ihl ?_ hok
    intro n hn
    cases r with
    | none => try dsimp only at hn ; cases hn
    | some m => try dsimp only at hn ; injection hn with hn ; subst hn ; exact ihr m rfl
  | @ite _ _ _ _ _ a b _ _ _ hok ihc iha ihb =>
    unfold markKept
    refine .ite ihc ?_ ?_ hok
    · intro n hn
      cases a with
      | none => try dsimp only at hn ; cases hn
      | some m => try dsimp only at hn ; injection hn with hn ; subst hn ; exact iha m rfl
    · intro n hn
      cases b with
      | none => try dsimp only at hn ; cases hn
      | some m => try dsimp only at hn ; injection hn with hn ; subst hn ; exact ihb m rfl

end Cedar.Thm
