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

import Cedar.Thm.SymCC.Evaluator.Tree
import Cedar.Thm.SymCC.Compiler
import Cedar.Thm.SymCC.Verifier

/-!
Soundness of the symbolic evaluator model (`Cedar.SymCC.Opt.symEvaluate`)
with respect to Cedar's concrete semantics, given an oracle whose
`unsat? = true` answers are correct.

The theorems are stated for strongly well-formed (closed) stores, where
every referenced entity exists; there the evaluator's existence questions
(`atomOutcomes`, `addMissing`) only ever add outcomes, and its existence
facts hold under any interpretation reading `exists[E]` as true everywhere
(`ExistsTrue`), which every theorem below assumes of `I`. The open-store
guarantee — the concrete outcome stays in the set when a referenced entity
is missing — is what the existence questions are for; it is tested
differentially (`symcc-evaluator-open-drt`) and its proof is a follow-up.
-/

namespace Cedar.Thm

open Data Spec SymCC Factory
open Cedar.SymCC.Opt

/--
The only obligation on the oracle: a `true` answer really means the asserts
are unsatisfiable over well-formed interpretations of `εnv`. Nothing is
assumed about `false` answers, so an incomplete oracle (a solver answering
`unknown`, mapped to `false`) only makes results less folded, never wrong.
-/
def UnsatSound (unsat? : Asserts → Bool) (εnv : SymEnv) : Prop :=
  ∀ ts, unsat? ts = true → εnv ⊭ ts

/-- The outcome of a concrete evaluation, when it is a boolean one. -/
def outcomeOf : Spec.Result Value → Option EvalOutcome
  | .ok (.prim (.bool true))  => .some .tt
  | .ok (.prim (.bool false)) => .some .ff
  | .error _                  => .some .err
  | .ok _                     => .none

/--
Characterization of `termOutcomes` at `m := Id`: either the term is a
literal and the result is its singleton, or the three flags record the
oracle's answers (with the error question skipped when `isNone` folds).
-/
theorem termOutcomes_id_spec {unsat? : Asserts → Bool} {base : Asserts}
    {t : Term} {trail : List Term} {o : Outcomes} :
  termOutcomes (m := Id) unsat? base t trail = .ok o →
  (∃ u, termLit t = .some u ∧ o = Outcomes.single u) ∨
  (termLit t = .none ∧
    o.canTrue = !unsat? (base ++ trail ++ [eq t (⊙ true)]) ∧
    o.canFalse = !unsat? (base ++ trail ++ [eq t (⊙ false)]) ∧
    ((isNone t = Term.bool false ∧ o.canError = false) ∨
     (isNone t ≠ Term.bool false ∧
       o.canError = !unsat? (base ++ trail ++ [isNone t]))))
:= by
  intro h
  simp only [termOutcomes, ExceptT.run, pure, ExceptT.pure, bind, ExceptT.bind,
    ExceptT.bindCont, Functor.map, ExceptT.map, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, Except.map, Except.pure, Except.bind, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  case h_1 u heq =>
    left
    injection h with h'
    exact ⟨u, heq, h'.symm⟩
  case h_2 heq =>
    right
    refine ⟨heq, ?_⟩
    split at h
    case isTrue hno =>
      split at h
      next => simp at h
      next hcond =>
        injection h with h'
        subst h'
        exact ⟨rfl, rfl, Or.inl ⟨hno, rfl⟩⟩
    case isFalse hno =>
      split at h
      next => simp at h
      next hcond =>
        injection h with h'
        subst h'
        exact ⟨rfl, rfl, Or.inr ⟨hno, rfl⟩⟩

/-- Adding outcomes keeps the others. -/
private theorem outcomes_mem_union {o o' : Outcomes} {u : EvalOutcome} :
  o.mem u = true → (o.union o').mem u = true := by
  intro h
  cases u <;> simp_all [Outcomes.mem, Outcomes.union]

/-- `addMissing` at `m := Id` only ever adds outcomes. -/
theorem addMissing_id_mem {unsat? : Asserts → Bool} {base : Asserts} {trail : List Term}
    {cs : List Existence} {o : Outcomes} {u : EvalOutcome} :
  o.mem u = true → (addMissing (m := Id) unsat? base trail cs o).mem u = true := by
  induction cs generalizing o with
  | nil => intro h ; simp only [addMissing] ; exact h
  | cons c cs ih =>
    intro h
    simp only [addMissing]
    split
    · exact ih h
    · show (addMissing (m := Id) unsat? base trail cs
        (if unsat? (base ++ trail ++ [c.missing]) then o else o.union c.adds)).mem u = true
      split
      · exact ih h
      · exact ih (outcomes_mem_union h)

/--
Characterization of `atomOutcomes` at `m := Id`: the term's outcomes, then
the existence questions.
-/
theorem atomOutcomes_id_spec {unsat? : Asserts → Bool} {base : Asserts}
    {t : Term} {cs : List Existence} {trail : List Term} {o : Outcomes} :
  atomOutcomes (m := Id) unsat? base t cs trail = .ok o →
  ∃ o₀, termOutcomes (m := Id) unsat? base t trail = .ok o₀ ∧
    addMissing (m := Id) unsat? base trail cs o₀ = o := by
  intro h
  simp only [atomOutcomes, bind, ExceptT.bind, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, pure, Except.pure,
    Functor.map, Except.map] at h
  cases ht : termOutcomes (m := Id) unsat? base t trail with
  | error e => rw [ht] at h ; simp at h
  | ok o₀ =>
    rw [ht] at h
    exact ⟨o₀, rfl, Except.ok.inj h⟩


private theorem satisfiedBy_snoc {ts : Asserts} {t : Term} {I : Interpretation} :
  ts.satisfiedBy I → t.interpret I = true → (ts ++ [t]).satisfiedBy I
:= by
  intro h₁ h₂
  rw [asserts_satisfiedBy_true] at *
  intro a ha
  simp only [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | ha
  · exact h₁ a ha
  · subst ha ; exact h₂

/-- A query whose asserts `I` satisfies cannot soundly be answered unsat. -/
private theorem unsat_absurd {unsat? : Asserts → Bool} {εnv : SymEnv} {I : Interpretation}
    {ts : Asserts} :
  UnsatSound unsat? εnv → I.WellFormed εnv.entities → ts.satisfiedBy I →
  unsat? ts = false
:= by
  intro hsound hwI hsat
  by_contra hcon
  simp only [Bool.not_eq_false] at hcon
  obtain ⟨a, ha, hne⟩ := (asserts_unsatisfiable_def.mp (hsound ts hcon)) I hwI
  rw [asserts_satisfiedBy_true] at hsat
  exact hne (hsat a ha)

/-- A literal term interprets to itself. -/
private theorem termLit_interpret {t : Term} {I : Interpretation} {u : EvalOutcome} :
  termLit t = .some u → t.interpret I = t
:= by
  unfold termLit
  intro h
  split at h
  case h_4 => simp at h
  all_goals simp [interpret_term_some, interpret_term_prim, interpret_term_none]

/-- The outcome of a result matching a literal term is the literal's. -/
private theorem termLit_same {t : Term} {I : Interpretation} {w u : EvalOutcome}
    {res : Spec.Result Value} :
  termLit t = .some w →
  SameResults res (t.interpret I) →
  outcomeOf res = .some u →
  u = w
:= by
  intro hlit hsame hout
  rw [termLit_interpret hlit] at hsame
  unfold termLit at hlit
  split at hlit <;> simp only [Option.some.injEq, reduceCtorEq] at hlit <;> subst hlit
  case h_1 =>
    cases res with
    | error e => simp only [SameResults] at hsame
    | ok v =>
      replace hsame : v ∼ Term.prim (TermPrim.bool true) := hsame
      replace hsame := same_bool_term_implies hsame
      subst hsame
      simp only [outcomeOf, Option.some.injEq] at hout
      exact hout.symm
  case h_2 =>
    cases res with
    | error e => simp only [SameResults] at hsame
    | ok v =>
      replace hsame : v ∼ Term.prim (TermPrim.bool false) := hsame
      replace hsame := same_bool_term_implies hsame
      subst hsame
      simp only [outcomeOf, Option.some.injEq] at hout
      exact hout.symm
  case h_3 =>
    cases res with
    | ok v => simp only [SameResults] at hsame
    | error e =>
      simp only [outcomeOf, Option.some.injEq] at hout
      exact hout.symm

/-- A result matching a `.none` term is an error. -/
private theorem same_error_term {t : Term} {res : Spec.Result Value} :
  SameResults res t →
  (∀ v, res ≠ .ok v) →
  ∃ ty, t = .none ty
:= by
  intro hsame hne
  cases res with
  | ok v => exact absurd rfl (hne v)
  | error e =>
    cases t <;> simp only [SameResults] at hsame
    rename_i ty
    exact ⟨ty, rfl⟩

/--
Soundness of the term decision: if `x` compiles to `t`, the concrete
evaluation outcome of `x` under any interpretation that satisfies
`base ++ trail` is in the set `termOutcomes` computes.
-/
theorem termOutcomes_sound {unsat? : Asserts → Bool} {εnv : SymEnv} {base trail : Asserts}
    {x : Expr} {t : Term} {o : Outcomes} {env : Env} {I : Interpretation} {u : EvalOutcome} :
  UnsatSound unsat? εnv →
  I.WellFormed εnv.entities →
  env ∼ εnv.interpret I →
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  SymCC.compile x εnv = .ok t →
  termOutcomes (m := Id) unsat? base t trail = .ok o →
  (base ++ trail).satisfiedBy I →
  outcomeOf (evaluate x env.request env.entities) = .some u →
  o.mem u = true
:= by
  intro hsound hwI heq hwε hwe hok hatom hsat hout
  have hrb := compile_bisimulation hwε hwe hwI heq hok
  simp only [Same.same] at hrb
  obtain ⟨hwt, ty, hty⟩ := compile_wf hwε hok
  rcases termOutcomes_id_spec hatom with ⟨w, hlit, ho⟩ | ⟨hnl, hct, hcf, hce⟩
  · subst ho
    rw [termLit_same hlit hrb hout]
    exact outcomes_mem_single w
  · unfold outcomeOf at hout
    split at hout <;> simp only [Option.some.injEq, reduceCtorEq] at hout <;> subst hout
    case h_1 heval =>
      rw [heval] at hrb
      have hti := same_ok_bool_implies hrb
      have hint : (eq t (⊙ true)).interpret I = true := by
        simp only [someOf]
        rw [interpret_eq hwI hwt (Term.WellFormed.some_wf wf_bool)]
        rw [interpret_term_some, interpret_term_prim, hti]
        exact pe_eq_same
      simp only [Outcomes.mem, hct, Bool.not_eq_true',
        unsat_absurd hsound hwI (satisfiedBy_snoc hsat hint)]
    case h_2 heval =>
      rw [heval] at hrb
      have hti := same_ok_bool_implies hrb
      have hint : (eq t (⊙ false)).interpret I = true := by
        simp only [someOf]
        rw [interpret_eq hwI hwt (Term.WellFormed.some_wf wf_bool)]
        rw [interpret_term_some, interpret_term_prim, hti]
        exact pe_eq_same
      simp only [Outcomes.mem, hcf, Bool.not_eq_true',
        unsat_absurd hsound hwI (satisfiedBy_snoc hsat hint)]
    case h_3 e heval =>
      rw [heval] at hrb
      obtain ⟨ty', hti⟩ := same_error_term hrb (by simp)
      have hint : (isNone t).interpret I = true := by
        rw [interpret_isNone hwI hwt, hti]
        rfl
      rcases hce with ⟨hno, hcefalse⟩ | ⟨hno, hcequery⟩
      · exfalso
        rw [hno, interpret_term_prim] at hint
        simp at hint
      · simp only [Outcomes.mem, hcequery, Bool.not_eq_true',
          unsat_absurd hsound hwI (satisfiedBy_snoc hsat hint)]

/--
Soundness of the atom decision: the existence questions only add outcomes,
so the concrete outcome stays in the set (a closed store never makes an
access miss, and an open store only adds outcomes the questions cover).
-/
theorem atomOutcomes_sound {unsat? : Asserts → Bool} {εnv : SymEnv} {base trail : Asserts}
    {x : Expr} {t : Term} {cs : List Existence} {o : Outcomes} {env : Env}
    {I : Interpretation} {u : EvalOutcome} :
  UnsatSound unsat? εnv →
  I.WellFormed εnv.entities →
  env ∼ εnv.interpret I →
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  SymCC.compile x εnv = .ok t →
  atomOutcomes (m := Id) unsat? base t cs trail = .ok o →
  (base ++ trail).satisfiedBy I →
  outcomeOf (evaluate x env.request env.entities) = .some u →
  o.mem u = true
:= by
  intro hsound hwI heq hwε hwe hok hatom hsat hout
  obtain ⟨o₀, ht, hadd⟩ := atomOutcomes_id_spec hatom
  subst hadd
  exact addMissing_id_mem (termOutcomes_sound hsound hwI heq hwε hwe hok ht hsat hout)

/--
The evaluator's existence predicate holds everywhere under `I` — the
intended reading of `exists[E]` on a closed store, where every referenced
entity exists. The predicate is the evaluator's own symbol, absent from
`εnv`, so any well-formed interpretation can be adjusted to satisfy this
without changing how `εnv` is interpreted; that adjustment is not carried
out here (see the plan's follow-up).
-/
def ExistsTrue (I : Interpretation) : Prop :=
  ∀ (ety : EntityType) (t : Term), (app (existsUUF ety) t).interpret I = Term.bool true

/-- Under `ExistsTrue`, a node's existence facts are satisfied. -/
private theorem satisfiedBy_facts {ts : Asserts} {I : Interpretation} {n : SENode} {b : Bool} :
  ExistsTrue I → ts.satisfiedBy I → (ts ++ n.factTerms b).satisfiedBy I := by
  intro hex hsat
  rw [asserts_satisfiedBy_true] at *
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hsat t h
  · simp only [SENode.factTerms, List.mem_map] at h
    obtain ⟨e, _, rfl⟩ := h
    exact hex e.ety (option.get e.receiver)


/-! ### Characterizations of `evalNode` at `m := Id` -/

theorem evalNode_atom_id_spec {unsat? : Asserts → Bool} {base : Asserts} {x : Expr}
    {t : Term} {cs ft ff fn : List Existence} {keep : Bool} {trail : List Term} {r : SEExpr} :
  evalNode (m := Id) unsat? base (.atom x t cs ft ff fn keep) trail = .ok r →
  ∃ o, atomOutcomes (m := Id) unsat? base t cs trail = .ok o ∧
    ((o = Outcomes.lit true ∧ keep = false ∧ r = .lit true) ∨
     (o = Outcomes.lit false ∧ r = .lit false) ∨
     (¬(o = Outcomes.lit true ∧ keep = false) ∧ o ≠ Outcomes.lit false ∧ r = .atom x o))
:= by
  intro h
  simp only [evalNode, pure, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    Except.pure] at h
  cases hatom : atomOutcomes (m := Id) unsat? base t cs trail with
  | error e => rw [hatom] at h ; simp [ExceptT.mk, Except.bind] at h
  | ok o =>
    rw [hatom] at h
    simp only [Except.bind] at h
    refine ⟨o, rfl, ?_⟩
    split at h
    next heq => injection h with h' ; exact Or.inl ⟨heq.1, heq.2, h'.symm⟩
    next hne =>
      split at h
      next heq => injection h with h' ; exact Or.inr (Or.inl ⟨heq, h'.symm⟩)
      next hne' => injection h with h' ; exact Or.inr (Or.inr ⟨hne, hne', h'.symm⟩)

theorem evalNode_not_id_spec {unsat? : Asserts → Bool} {base : Asserts} {x : Expr}
    {t : Term} {c : SENode} {trail : List Term} {r : SEExpr} :
  evalNode (m := Id) unsat? base (.not x t c) trail = .ok r →
  ∃ cv, evalNode (m := Id) unsat? base c trail = .ok cv ∧
    ((∃ b, cv.asLit = .some b ∧ r = .lit !b) ∨
     (cv.asLit = .none ∧ cv.outcomes.isOnlyError = true ∧ r = cv) ∨
     (cv.asLit = .none ∧ cv.outcomes.isOnlyError = false ∧
       r = .not cv cv.outcomes.negated))
:= by
  intro h
  simp only [evalNode, pure, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    Except.pure] at h
  cases hcv : evalNode (m := Id) unsat? base c trail with
  | error e => rw [hcv] at h ; simp [ExceptT.mk, Except.bind] at h
  | ok cv =>
    rw [hcv] at h
    simp only [Except.bind] at h
    refine ⟨cv, rfl, ?_⟩
    split at h
    next b heq => injection h with h' ; exact Or.inl ⟨b, heq, h'.symm⟩
    next hne =>
      split at h
      next heq => injection h with h' ; exact Or.inr (Or.inl ⟨hne, heq, h'.symm⟩)
      next hne' =>
        injection h with h'
        simp only [Bool.not_eq_true] at hne'
        exact Or.inr (Or.inr ⟨hne, hne', h'.symm⟩)


theorem evalNode_and_id_spec {unsat? : Asserts → Bool} {base : Asserts} {x : Expr}
    {t : Term} {l : SENode} {ro : Option SENode} {trail : List Term} {r : SEExpr} :
  evalNode (m := Id) unsat? base (.and x t l ro) trail = .ok r →
  ∃ lv, evalNode (m := Id) unsat? base l trail = .ok lv ∧
    ((lv.outcomes.isOnlyError = true ∧ r = lv) ∨
     (lv.outcomes.isOnlyError = false ∧
      ((lv.asLit = .some false ∧ r = .lit false) ∨
       (lv.asLit = .some true ∧ ∃ rn, ro = .some rn ∧
         evalNode (m := Id) unsat? base rn trail = .ok r) ∨
       (lv.asLit = .none ∧ lv.outcomes.canTrue = false ∧ r = lv) ∨
       (lv.asLit = .none ∧ lv.outcomes.canTrue = true ∧
        ∃ rn rv, ro = .some rn ∧
          evalNode (m := Id) unsat? base rn (trail ++ [eq l.term (⊙ true)] ++ l.factTerms true) = .ok rv ∧
          ((rv.asLit = .some true ∧ r = lv.unguard) ∨
           (rv.asLit = .some false ∧ lv.outcomes.isErrorFree = true ∧ r = .lit false) ∨
           (((rv.asLit = .some false ∧ lv.outcomes.isErrorFree = false) ∨ rv.asLit = .none) ∧
            r = .and lv rv (lv.outcomes.and rv.outcomes)))))))
:= by
  intro h
  rw [evalNode.eq_def] at h
  simp only [pure, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure] at h
  cases hlv : evalNode (m := Id) unsat? base l trail with
  | error e => rw [hlv] at h ; simp [ExceptT.mk, Except.bind] at h
  | ok lv =>
    rw [hlv] at h
    try simp only [Except.bind] at h
    refine ⟨lv, rfl, ?_⟩
    split at h
    next honly => injection h with h' ; exact Or.inl ⟨honly, h'.symm⟩
    next honly =>
      simp only [Bool.not_eq_true] at honly
      refine Or.inr ⟨honly, ?_⟩
      split at h
      next heq => injection h with h' ; exact Or.inl ⟨heq, h'.symm⟩
      next heq =>
        cases ro with
        | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
        | some rn => exact Or.inr (Or.inl ⟨heq, rn, rfl, h⟩)
      next hnl =>
        split at h
        next hng =>
          injection h with h'
          simp only [Bool.not_eq_true'] at hng
          exact Or.inr (Or.inr (Or.inl ⟨hnl, hng, h'.symm⟩))
        next hng =>
          simp at hng
          cases ro with
          | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
          | some rn =>
            simp only [] at h
            cases hrv : evalNode (m := Id) unsat? base rn (trail ++ [eq l.term (⊙ true)] ++ l.factTerms true) with
            | error e => rw [hrv] at h ; simp [ExceptT.mk, Except.bind] at h
            | ok rv =>
              rw [hrv] at h
              simp only [Except.bind] at h
              refine Or.inr (Or.inr (Or.inr ⟨hnl, hng, rn, rv, rfl, hrv, ?_⟩))
              split at h
              next heqr => injection h with h' ; exact Or.inl ⟨heqr, h'.symm⟩
              next heqr =>
                split at h
                next hef => injection h with h' ; exact Or.inr (Or.inl ⟨heqr, hef, h'.symm⟩)
                next hef =>
                  injection h with h'
                  simp only [Bool.not_eq_true] at hef
                  exact Or.inr (Or.inr ⟨Or.inl ⟨heqr, hef⟩, h'.symm⟩)
              next hnr =>
                injection h with h'
                exact Or.inr (Or.inr ⟨Or.inr hnr, h'.symm⟩)

theorem evalNode_or_id_spec {unsat? : Asserts → Bool} {base : Asserts} {x : Expr}
    {t : Term} {l : SENode} {ro : Option SENode} {trail : List Term} {r : SEExpr} :
  evalNode (m := Id) unsat? base (.or x t l ro) trail = .ok r →
  ∃ lv, evalNode (m := Id) unsat? base l trail = .ok lv ∧
    ((lv.outcomes.isOnlyError = true ∧ r = lv) ∨
     (lv.outcomes.isOnlyError = false ∧
      ((lv.asLit = .some true ∧ r = .lit true) ∨
       (lv.asLit = .some false ∧ ∃ rn, ro = .some rn ∧
         evalNode (m := Id) unsat? base rn trail = .ok r) ∨
       (lv.asLit = .none ∧ lv.outcomes.canFalse = false ∧ r = lv) ∨
       (lv.asLit = .none ∧ lv.outcomes.canFalse = true ∧
        ∃ rn rv, ro = .some rn ∧
          evalNode (m := Id) unsat? base rn (trail ++ [eq l.term (⊙ false)] ++ l.factTerms false) = .ok rv ∧
          ((rv.asLit = .some false ∧ r = lv) ∨
           (rv.asLit = .some true ∧ lv.outcomes.isErrorFree = true ∧ r = .lit true) ∨
           (((rv.asLit = .some true ∧ lv.outcomes.isErrorFree = false) ∨ rv.asLit = .none) ∧
            r = .or lv rv (lv.outcomes.or rv.outcomes)))))))
:= by
  intro h
  rw [evalNode.eq_def] at h
  simp only [pure, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure] at h
  cases hlv : evalNode (m := Id) unsat? base l trail with
  | error e => rw [hlv] at h ; simp [ExceptT.mk, Except.bind] at h
  | ok lv =>
    rw [hlv] at h
    try simp only [Except.bind] at h
    refine ⟨lv, rfl, ?_⟩
    split at h
    next honly => injection h with h' ; exact Or.inl ⟨honly, h'.symm⟩
    next honly =>
      simp only [Bool.not_eq_true] at honly
      refine Or.inr ⟨honly, ?_⟩
      split at h
      next heq => injection h with h' ; exact Or.inl ⟨heq, h'.symm⟩
      next heq =>
        cases ro with
        | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
        | some rn => exact Or.inr (Or.inl ⟨heq, rn, rfl, h⟩)
      next hnl =>
        split at h
        next hng =>
          injection h with h'
          simp only [Bool.not_eq_true'] at hng
          exact Or.inr (Or.inr (Or.inl ⟨hnl, hng, h'.symm⟩))
        next hng =>
          simp at hng
          cases ro with
          | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
          | some rn =>
            simp only [] at h
            cases hrv : evalNode (m := Id) unsat? base rn (trail ++ [eq l.term (⊙ false)] ++ l.factTerms false) with
            | error e => rw [hrv] at h ; simp [ExceptT.mk, Except.bind] at h
            | ok rv =>
              rw [hrv] at h
              simp only [Except.bind] at h
              refine Or.inr (Or.inr (Or.inr ⟨hnl, hng, rn, rv, rfl, hrv, ?_⟩))
              split at h
              next heqr => injection h with h' ; exact Or.inl ⟨heqr, h'.symm⟩
              next heqr =>
                split at h
                next hef => injection h with h' ; exact Or.inr (Or.inl ⟨heqr, hef, h'.symm⟩)
                next hef =>
                  injection h with h'
                  simp only [Bool.not_eq_true] at hef
                  exact Or.inr (Or.inr ⟨Or.inl ⟨heqr, hef⟩, h'.symm⟩)
              next hnr =>
                injection h with h'
                exact Or.inr (Or.inr ⟨Or.inr hnr, h'.symm⟩)


theorem evalNode_ite_id_spec {unsat? : Asserts → Bool} {base : Asserts} {x : Expr}
    {t : Term} {c : SENode} {ao bo : Option SENode} {trail : List Term} {r : SEExpr} :
  evalNode (m := Id) unsat? base (.ite x t c ao bo) trail = .ok r →
  ∃ cv, evalNode (m := Id) unsat? base c trail = .ok cv ∧
    ((cv.outcomes.isOnlyError = true ∧ r = cv) ∨
     (cv.outcomes.isOnlyError = false ∧
      ((cv.asLit = .some true ∧ ∃ an, ao = .some an ∧
         evalNode (m := Id) unsat? base an trail = .ok r) ∨
       (cv.asLit = .some false ∧ ∃ bn, bo = .some bn ∧
         evalNode (m := Id) unsat? base bn trail = .ok r) ∨
       (cv.asLit = .none ∧ ∃ (an bn : SENode) (av bv : Option SEExpr), ao = .some an ∧ bo = .some bn ∧
         ((cv.outcomes.canTrue = true ∧
            ∃ rv, evalNode (m := Id) unsat? base an (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true) = .ok rv ∧
              av = .some rv) ∨
          (cv.outcomes.canTrue = false ∧ av = .none)) ∧
         ((cv.outcomes.canFalse = true ∧
            ∃ rv, evalNode (m := Id) unsat? base bn (trail ++ [eq c.term (⊙ false)] ++ c.factTerms false) = .ok rv ∧
              bv = .some rv) ∨
          (cv.outcomes.canFalse = false ∧ bv = .none)) ∧
         r = iteResult cv av bv an.expr bn.expr))))
:= by
  intro h
  rw [evalNode.eq_def] at h
  simp only [pure, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, Functor.map,
    ExceptT.map] at h
  cases hcv : evalNode (m := Id) unsat? base c trail with
  | error e => rw [hcv] at h ; simp [ExceptT.mk, Except.bind] at h
  | ok cv =>
    rw [hcv] at h
    try simp only [Except.bind] at h
    refine ⟨cv, rfl, ?_⟩
    split at h
    next honly => injection h with h' ; exact Or.inl ⟨honly, h'.symm⟩
    next honly =>
      simp only [Bool.not_eq_true] at honly
      refine Or.inr ⟨honly, ?_⟩
      split at h
      next heq =>
        cases ao with
        | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
        | some an => exact Or.inl ⟨heq, an, rfl, h⟩
      next heq =>
        cases bo with
        | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
        | some bn => exact Or.inr (Or.inl ⟨heq, bn, rfl, h⟩)
      next hnl =>
        cases ao with
        | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
        | some an =>
          cases bo with
          | none => simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, Except.bind] at h
          | some bn =>
            simp only [] at h
            refine Or.inr (Or.inr ⟨hnl, an, bn, ?_⟩)
            split at h
            next hct =>
              cases hav : evalNode (m := Id) unsat? base an (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true) with
              | error e => rw [hav] at h ; simp [ExceptT.mk, Except.map, Except.bind] at h
              | ok rv =>
                rw [hav] at h
                simp only [ExceptT.mk, Except.map, Except.bind] at h
                split at h
                next hcf =>
                  cases hbv : evalNode (m := Id) unsat? base bn (trail ++ [eq c.term (⊙ false)] ++ c.factTerms false) with
                  | error e => rw [hbv] at h ; simp [ExceptT.mk, Except.map, Except.bind] at h
                  | ok rvb =>
                    rw [hbv] at h
                    simp only [ExceptT.mk, Except.map, Except.bind] at h
                    injection h with h'
                    exact ⟨.some rv, .some rvb, rfl, rfl,
                      Or.inl ⟨hct, rv, rfl, rfl⟩, Or.inl ⟨hcf, rvb, rfl, rfl⟩, h'.symm⟩
                next hcf =>
                  simp only [Bool.not_eq_true] at hcf
                  injection h with h'
                  exact ⟨.some rv, .none, rfl, rfl,
                    Or.inl ⟨hct, rv, rfl, rfl⟩, Or.inr ⟨hcf, rfl⟩, h'.symm⟩
            next hct =>
              simp only [Bool.not_eq_true] at hct
              try simp only [ExceptT.mk, Except.map, Except.bind] at h
              split at h
              next hcf =>
                cases hbv : evalNode (m := Id) unsat? base bn (trail ++ [eq c.term (⊙ false)] ++ c.factTerms false) with
                | error e => rw [hbv] at h ; simp [ExceptT.mk, Except.map, Except.bind] at h
                | ok rvb =>
                  rw [hbv] at h
                  simp only [ExceptT.mk, Except.map, Except.bind] at h
                  injection h with h'
                  exact ⟨.none, .some rvb, rfl, rfl,
                    Or.inr ⟨hct, rfl⟩, Or.inl ⟨hcf, rvb, rfl, rfl⟩, h'.symm⟩
              next hcf =>
                simp only [Bool.not_eq_true] at hcf
                injection h with h'
                exact ⟨.none, .none, rfl, rfl,
                  Or.inr ⟨hct, rfl⟩, Or.inr ⟨hcf, rfl⟩, h'.symm⟩


/-! ### Soundness of the evaluation loop -/

private theorem asLit_some {r : SEExpr} {b : Bool} :
  r.asLit = .some b → r = .lit b
:= by cases r <;> simp [SEExpr.asLit]

/-- `unguard` changes nothing whose outcomes contain something other than `tt`. -/
private theorem unguard_eq_of_mem {lv : SEExpr} {u : EvalOutcome} (hu : u ≠ .tt)
    (h : lv.outcomes.mem u = true) :
  lv.unguard = lv
:= by
  cases lv <;> simp only [SEExpr.unguard]
  case atom x o =>
    split
    next ho =>
      exfalso
      subst ho
      cases u
      case tt => exact hu rfl
      all_goals simp [Outcomes.lit, Outcomes.mem, SEExpr.outcomes] at h
    next => rfl

/-- `unguard` of a value that is `tt` and evaluates to `true` is still both. -/
private theorem unguard_true {lv : SEExpr} {env : Env}
    (hltt : lv.outcomes.mem .tt = true)
    (hlok : evaluate lv.toExpr env.request env.entities = .ok (.prim (.bool true))) :
  lv.unguard.outcomes.mem .tt = true ∧
  evaluate lv.unguard.toExpr env.request env.entities = .ok (.prim (.bool true))
:= by
  cases lv <;> simp only [SEExpr.unguard]
  case atom x o =>
    split
    next => exact ⟨by simp [SEExpr.outcomes, Outcomes.lit, Outcomes.mem], by simp [SEExpr.toExpr, evaluate]⟩
    next => exact ⟨hltt, hlok⟩
  all_goals exact ⟨hltt, hlok⟩

/-- The two shapes of `iteResult`. -/
private theorem iteResult_cases {cv : SEExpr} {av bv : Option SEExpr} {ax bx : Expr} {r : SEExpr} :
  r = iteResult cv av bv ax bx →
  (∃ avv, av = .some avv ∧ avv.asLit.isSome = true ∧ cv.outcomes = Outcomes.lit true ∧ r = avv) ∨
  r = .ite cv (av.getD (.unvisited ax)) (bv.getD (.unvisited bx))
        (cv.outcomes.ite (av.map SEExpr.outcomes) (bv.map SEExpr.outcomes))
:= by
  intro h
  cases av with
  | none =>
    simp only [iteResult] at h
    exact Or.inr (by simpa using h)
  | some avv =>
    simp only [iteResult] at h
    split at h
    next hc => exact Or.inl ⟨avv, rfl, hc.2, hc.1, h⟩
    next => exact Or.inr (by simpa using h)

@[simp] private theorem seexpr_outcomes_lit {b : Bool} :
  (SEExpr.lit b).outcomes = Outcomes.lit b := rfl
@[simp] private theorem seexpr_outcomes_atom {x : Expr} {o : Outcomes} :
  (SEExpr.atom x o).outcomes = o := rfl
@[simp] private theorem seexpr_outcomes_unvisited {x : Expr} :
  (SEExpr.unvisited x).outcomes = Outcomes.all := rfl
@[simp] private theorem seexpr_outcomes_not {c : SEExpr} {o : Outcomes} :
  (SEExpr.not c o).outcomes = o := rfl
@[simp] private theorem seexpr_outcomes_and {l r : SEExpr} {o : Outcomes} :
  (SEExpr.and l r o).outcomes = o := rfl
@[simp] private theorem seexpr_outcomes_or {l r : SEExpr} {o : Outcomes} :
  (SEExpr.or l r o).outcomes = o := rfl
@[simp] private theorem seexpr_outcomes_ite {c a b : SEExpr} {o : Outcomes} :
  (SEExpr.ite c a b o).outcomes = o := rfl
@[simp] private theorem seexpr_toExpr_lit {b : Bool} :
  (SEExpr.lit b).toExpr = .lit (.bool b) := rfl
@[simp] private theorem seexpr_toExpr_atom {x : Expr} {o : Outcomes} :
  (SEExpr.atom x o).toExpr = x := rfl
@[simp] private theorem seexpr_toExpr_unvisited {x : Expr} :
  (SEExpr.unvisited x).toExpr = x := rfl
@[simp] private theorem seexpr_toExpr_not {c : SEExpr} {o : Outcomes} :
  (SEExpr.not c o).toExpr = .unaryApp .not c.toExpr := rfl
@[simp] private theorem seexpr_toExpr_and {l r : SEExpr} {o : Outcomes} :
  (SEExpr.and l r o).toExpr = .and l.toExpr r.toExpr := rfl
@[simp] private theorem seexpr_toExpr_or {l r : SEExpr} {o : Outcomes} :
  (SEExpr.or l r o).toExpr = .or l.toExpr r.toExpr := rfl
@[simp] private theorem seexpr_toExpr_ite {c a b : SEExpr} {o : Outcomes} :
  (SEExpr.ite c a b o).toExpr = .ite c.toExpr a.toExpr b.toExpr := rfl

private theorem toOption_some_inv {r : Spec.Result Value} {v : Value} :
  r.toOption = .some v → r = .ok v
:= by cases r <;> simp [Except.toOption]

private theorem toOption_none_inv {r : Spec.Result Value} :
  r.toOption = .none → ∃ e, r = .error e
:= by cases r <;> simp [Except.toOption]

/--
A boolean-typed compiled expression evaluates to a boolean whenever it
evaluates successfully (under an interpretation relating the environments).
-/
private theorem eval_ok_bool {x : Expr} {εnv : SymEnv} {env : Env} {I : Interpretation}
    {t : Term} {v : Value} :
  I.WellFormed εnv.entities →
  env ∼ εnv.interpret I →
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  SymCC.compile x εnv = .ok t →
  t.typeOf = .option .bool →
  evaluate x env.request env.entities = .ok v →
  ∃ b, v = .prim (.bool b)
:= by
  intro hwI heq hwε hwe hok hty heval
  have hrb := compile_bisimulation hwε hwe hwI heq hok
  rw [heval] at hrb
  simp only [Same.same] at hrb
  have hw := interpret_term_wf hwI (compile_wf hwε hok).left
  rw [hty] at hw
  generalize hgen : t.interpret I = ti at hrb hw
  have hlit := same_ok_value_implies_lit hrb
  rcases wfl_of_type_option_is_option ⟨hw.left, hlit⟩ hw.right with hnone | ⟨t', hsome, hty'⟩
  · rw [hnone] at hrb ; simp only [SameResults] at hrb
  · subst hsome
    simp only [SameResults] at hrb
    cases hw.left ; rename_i hwt'
    replace ⟨b, hb⟩ := wfl_of_type_bool_is_bool ⟨hwt', isLiteral_some.mp hlit⟩ hty'
    subst hb
    exact ⟨b, same_bool_term_implies hrb⟩

private theorem compileApp₁_not_ok_bool {t t₂ : Term} :
  SymCC.compileApp₁ .not t = .ok t₂ → t.typeOf = .bool
:= by
  unfold SymCC.compileApp₁
  intro h
  split at h <;> simp_all

private theorem typeOf_option_get {t : Term} {ty : TermType} :
  t.typeOf = .option ty → (Factory.option.get t).typeOf = ty
:= by
  intro h
  unfold Factory.option.get
  split
  · rename_i t'
    simp only [Term.typeOf] at h
    injection h
  · rw [h] ; simp [Term.typeOf]

private theorem result_as_bool_ok {b : Bool} :
  Result.as Bool (Except.ok (Value.prim (.bool b))) = Except.ok b
:= by simp [Result.as, Coe.coe, Value.asBool]

private theorem result_as_bool_error {e : Spec.Error} :
  Result.as Bool (Except.error e : Spec.Result Value) = Except.error e
:= by simp [Result.as]

private theorem evaluate_and_error {x₁ x₂ : Expr} {req : Request} {es : Entities}
    {e : Spec.Error} :
  evaluate x₁ req es = .error e →
  evaluate (.and x₁ x₂) req es = .error e
:= by
  intro h
  simp [evaluate, h, Result.as]

private theorem evaluate_and_false {x₁ x₂ : Expr} {req : Request} {es : Entities} :
  evaluate x₁ req es = .ok (.prim (.bool false)) →
  evaluate (.and x₁ x₂) req es = .ok (.prim (.bool false))
:= by
  intro h
  simp [evaluate, h, Result.as, Coe.coe, Value.asBool]

private theorem evaluate_and_true {x₁ x₂ : Expr} {req : Request} {es : Entities} :
  evaluate x₁ req es = .ok (.prim (.bool true)) →
  evaluate (.and x₁ x₂) req es
    = (Result.as Bool (evaluate x₂ req es)).map (λ b => Value.prim (.bool b))
:= by
  intro h
  cases h₂ : evaluate x₂ req es with
  | error e => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
  | ok v =>
    cases v with
    | prim p =>
      cases p <;> simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
    | set s => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
    | record m => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
    | ext e => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]

private theorem evaluate_or_error {x₁ x₂ : Expr} {req : Request} {es : Entities}
    {e : Spec.Error} :
  evaluate x₁ req es = .error e →
  evaluate (.or x₁ x₂) req es = .error e
:= by
  intro h
  simp [evaluate, h, Result.as]

private theorem evaluate_or_true {x₁ x₂ : Expr} {req : Request} {es : Entities} :
  evaluate x₁ req es = .ok (.prim (.bool true)) →
  evaluate (.or x₁ x₂) req es = .ok (.prim (.bool true))
:= by
  intro h
  simp [evaluate, h, Result.as, Coe.coe, Value.asBool]

private theorem evaluate_or_false {x₁ x₂ : Expr} {req : Request} {es : Entities} :
  evaluate x₁ req es = .ok (.prim (.bool false)) →
  evaluate (.or x₁ x₂) req es
    = (Result.as Bool (evaluate x₂ req es)).map (λ b => Value.prim (.bool b))
:= by
  intro h
  cases h₂ : evaluate x₂ req es with
  | error e => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
  | ok v =>
    cases v with
    | prim p =>
      cases p <;> simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
    | set s => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
    | record m => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]
    | ext e => simp [evaluate, h, h₂, Result.as, Coe.coe, Value.asBool, Except.map]

private theorem evaluate_ite_error {x₁ x₂ x₃ : Expr} {req : Request} {es : Entities}
    {e : Spec.Error} :
  evaluate x₁ req es = .error e →
  evaluate (.ite x₁ x₂ x₃) req es = .error e
:= by
  intro h
  simp [evaluate, h, Result.as]

private theorem evaluate_ite_true {x₁ x₂ x₃ : Expr} {req : Request} {es : Entities} :
  evaluate x₁ req es = .ok (.prim (.bool true)) →
  evaluate (.ite x₁ x₂ x₃) req es = evaluate x₂ req es
:= by
  intro h
  simp [evaluate, h, Result.as, Coe.coe, Value.asBool]

private theorem evaluate_ite_false {x₁ x₂ x₃ : Expr} {req : Request} {es : Entities} :
  evaluate x₁ req es = .ok (.prim (.bool false)) →
  evaluate (.ite x₁ x₂ x₃) req es = evaluate x₃ req es
:= by
  intro h
  simp [evaluate, h, Result.as, Coe.coe, Value.asBool]

private theorem toOption_as_bool {r₁ r₂ : Spec.Result Value} :
  r₁.toOption = r₂.toOption →
  ((Result.as Bool r₁).map (λ b => Value.prim (.bool b))).toOption
    = ((Result.as Bool r₂).map (λ b => Value.prim (.bool b))).toOption
:= by
  intro h
  cases r₁ <;> cases r₂ <;> simp_all [Except.toOption, Except.map, Result.as]

theorem evalNode_sound {unsat? : Asserts → Bool} {εnv : SymEnv} {base : Asserts}
    {n : SENode} {x : Expr} {trail : List Term} {r : SEExpr} {env : Env} {I : Interpretation} :
  UnsatSound unsat? εnv →
  I.WellFormed εnv.entities →
  ExistsTrue I →
  env ∼ εnv.interpret I →
  SENode.WellBuilt εnv n x →
  n.term.typeOf = .option .bool →
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  evalNode (m := Id) unsat? base n trail = .ok r →
  (base ++ trail).satisfiedBy I →
  (∀ u, outcomeOf (evaluate x env.request env.entities) = .some u →
    r.outcomes.mem u = true) ∧
  (evaluate r.toExpr env.request env.entities).toOption
    = (evaluate x env.request env.entities).toOption
:= by
  intro hsound hwI hex heq hwb hty hwε hwe h hsat
  suffices H : ∀ (N : Nat) (n : SENode) (x : Expr) (trail : List Term) (r : SEExpr),
      sizeOf n ≤ N →
      SENode.WellBuilt εnv n x →
      n.term.typeOf = .option .bool →
      εnv.WellFormedFor x →
      env.WellFormedFor x →
      evalNode (m := Id) unsat? base n trail = .ok r →
      (base ++ trail).satisfiedBy I →
      (∀ u, outcomeOf (evaluate x env.request env.entities) = .some u →
        r.outcomes.mem u = true) ∧
      (evaluate r.toExpr env.request env.entities).toOption
        = (evaluate x env.request env.entities).toOption by
    exact H (sizeOf n) n x trail r (Nat.le_refl _) hwb hty hwε hwe h hsat
  clear hwb hty hwε hwe h hsat
  intro N
  induction N with
  | zero =>
    intro n x trail r hle
    cases n <;> simp at hle
  | succ N ihN =>
    intro n x trail r hle hwb hty hwε hwe h hsat
    cases n with
    | atom xa ta =>
      obtain ⟨hok, hxeq⟩ := wellBuilt_compile hwb
      simp only [SENode.expr] at hxeq
      subst hxeq
      simp only [SENode.term] at hty hok
      obtain ⟨o, hatom, ho⟩ := evalNode_atom_id_spec h
      have hS1 : ∀ u, outcomeOf (evaluate xa env.request env.entities) = .some u →
          o.mem u = true :=
        λ u hu => atomOutcomes_sound hsound hwI heq hwε hwe hok hatom hsat hu
      have hbool : ∀ v, evaluate xa env.request env.entities = .ok v →
          ∃ b, v = .prim (.bool b) :=
        λ v hv => eval_ok_bool hwI heq hwε hwe hok hty hv
      rcases ho with ⟨hoe, _, hr⟩ | ⟨hoe, hr⟩ | ⟨_, _, hr⟩ <;> subst hr
      · subst hoe
        refine ⟨λ u hu => hS1 u hu, ?_⟩
        cases heval : evaluate xa env.request env.entities with
        | error e =>
          have := hS1 .err (by rw [heval] ; rfl)
          simp [Outcomes.lit, Outcomes.mem] at this
        | ok v =>
          obtain ⟨b, hb⟩ := hbool v heval ; subst hb
          cases b
          case false =>
            have := hS1 .ff (by rw [heval] ; rfl)
            simp [Outcomes.lit, Outcomes.mem] at this
          case true =>
            simp [SEExpr.toExpr, evaluate, Except.toOption]
      · subst hoe
        refine ⟨λ u hu => hS1 u hu, ?_⟩
        cases heval : evaluate xa env.request env.entities with
        | error e =>
          have := hS1 .err (by rw [heval] ; rfl)
          simp [Outcomes.lit, Outcomes.mem] at this
        | ok v =>
          obtain ⟨b, hb⟩ := hbool v heval ; subst hb
          cases b
          case true =>
            have := hS1 .tt (by rw [heval] ; rfl)
            simp [Outcomes.lit, Outcomes.mem] at this
          case false =>
            simp [SEExpr.toExpr, evaluate, Except.toOption]
      · exact ⟨hS1, rfl⟩
    | not xn tn c =>
      cases hwb ; rename_i x₁ hok hwbc
      simp only [SENode.term] at hty
      obtain ⟨t₁, t₂, hok₁, happ, hteq⟩ := compile_unaryApp_ok_implies hok
      obtain ⟨hokc, _⟩ := wellBuilt_compile hwbc
      have ht₁ : t₁ = c.term := by
        have := hokc.symm.trans hok₁
        injection this with h' ; exact h'.symm
      subst ht₁
      obtain ⟨tyc, htyc'⟩ := (compile_wf (wf_εnv_for_unaryApp_implies hwε) hokc).right
      have htyget := compileApp₁_not_ok_bool happ
      rw [typeOf_option_get htyc'] at htyget
      subst htyget
      have hwεc := wf_εnv_for_unaryApp_implies hwε
      have hwec := wf_env_for_unaryApp_implies hwe
      have hbool : ∀ v, evaluate x₁ env.request env.entities = .ok v →
          ∃ b, v = .prim (.bool b) :=
        λ v hv => eval_ok_bool hwI heq hwεc hwec hokc htyc' hv
      obtain ⟨cv, hcv, ho⟩ := evalNode_not_id_spec h
      have hszc : sizeOf c ≤ N := by simp at hle ; omega
      have IH := ihN c x₁ trail cv hszc hwbc htyc' hwεc hwec hcv hsat
      rcases ho with ⟨b, hlit, hr⟩ | ⟨hnl, hone, hr⟩ | ⟨hnl, hone, hr⟩ <;> subst hr
      · -- child folded to a literal
        have hcvlit := asLit_some hlit ; subst hcvlit
        have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool b)) := by
          have h2 := IH.right
          simp only [SEExpr.toExpr, evaluate, Except.toOption] at h2
          exact toOption_some_inv h2.symm
        have hnoteval : evaluate (.unaryApp .not x₁) env.request env.entities
            = .ok (.prim (.bool !b)) := by
          simp [evaluate, hx₁, apply₁]
        constructor
        · intro u hu
          rw [hnoteval] at hu
          cases b <;>
            simp only [outcomeOf, Bool.not_true, Bool.not_false, Option.some.injEq] at hu <;>
            subst hu <;> rfl
        · rw [hnoteval]
          cases b <;> simp [SEExpr.toExpr, evaluate]
      · -- child necessarily errors: collapse to the child
        have herr : ∀ v, evaluate x₁ env.request env.entities ≠ .ok v := by
          intro v hv
          obtain ⟨b, hb⟩ := hbool v hv ; subst hb
          have := IH.left (if b then .tt else .ff) (by cases b <;> rw [hv] <;> rfl)
          simp only [Outcomes.isOnlyError, decide_eq_true_eq] at hone
          rw [hone] at this
          cases b <;> simp [Outcomes.mem] at this
        cases heval : evaluate x₁ env.request env.entities with
        | ok v => exact absurd heval (herr v)
        | error e =>
          constructor
          · intro u hu
            have hne : evaluate (.unaryApp .not x₁) env.request env.entities = .error e := by
              simp [evaluate, heval]
            rw [hne] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
            exact outcomes_isOnlyError_mem hone
          · have h2 := IH.right
            rw [heval] at h2
            simp only [Except.toOption] at h2
            obtain ⟨e', he'⟩ := toOption_none_inv h2
            rw [he']
            simp [evaluate, heval, Except.toOption]
      · -- kept as a Not node with flipped outcomes
        constructor
        · intro u hu
          cases heval : evaluate x₁ env.request env.entities with
          | error e =>
            rw [show evaluate (.unaryApp .not x₁) env.request env.entities = .error e from by
              simp [evaluate, heval]] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
            have := IH.left .err (by rw [heval] ; rfl)
            simp only [seexpr_outcomes_not]
            have h' := outcomes_negated_mem (o := .err) this
            simpa [EvalOutcome.negated] using h'
          | ok v =>
            obtain ⟨b, hb⟩ := hbool v heval ; subst hb
            rw [show evaluate (.unaryApp .not x₁) env.request env.entities
                = .ok (.prim (.bool !b)) from by simp [evaluate, heval, apply₁]] at hu
            have hmem := IH.left (if b then .tt else .ff)
              (by cases b <;> rw [heval] <;> rfl)
            simp only [seexpr_outcomes_not]
            cases b <;>
              simp only [outcomeOf, Option.some.injEq, Bool.not_true, Bool.not_false] at hu <;>
              subst hu <;>
              simpa [EvalOutcome.negated] using outcomes_negated_mem hmem
        · cases heval : evaluate x₁ env.request env.entities with
          | error e =>
            have h2 := IH.right
            rw [heval] at h2
            obtain ⟨e', he'⟩ := toOption_none_inv h2
            simp [SEExpr.toExpr, evaluate, he', heval, Except.toOption]
          | ok v =>
            obtain ⟨b, hb⟩ := hbool v heval ; subst hb
            have h2 := IH.right
            rw [heval] at h2
            have hcv' := toOption_some_inv h2
            simp [SEExpr.toExpr, evaluate, hcv', heval, apply₁, Except.toOption]
    | and xn tn l ro =>
      cases hwb with
      | @and x₁ x₂ t' l' ro' hwbl hwbr hok =>
      simp only [SENode.term] at hty
      obtain ⟨t₁, hok₁, hmatch⟩ := compile_and_ok_implies hok
      obtain ⟨hokl, _⟩ := wellBuilt_compile hwbl
      have ht₁ : t₁ = l.term := by
        have hh := hokl.symm.trans hok₁ ; injection hh with h' ; exact h'.symm
      subst ht₁
      obtain ⟨hwε₁, hwε₂⟩ := wf_εnv_for_and_implies hwε
      obtain ⟨hwe₁, hwe₂⟩ := wf_env_for_and_implies hwe
      obtain ⟨tyl, htyl'⟩ := (compile_wf hwε₁ hokl).right
      have htyl : l.term.typeOf = .option .bool := by
        split at hmatch
        · rename_i heqf ; rw [heqf] ; simp [typeOf_term_some, typeOf_bool]
        · exact hmatch.left
      have hbool₁ : ∀ v, evaluate x₁ env.request env.entities = .ok v →
          ∃ b, v = .prim (.bool b) :=
        λ v hv => eval_ok_bool hwI heq hwε₁ hwe₁ hokl htyl hv
      obtain ⟨lv, hlv, hcase⟩ := evalNode_and_id_spec h
      have hszl : sizeOf l ≤ N := by simp at hle ; omega
      have IHl := ihN l x₁ trail lv hszl hwbl htyl hwε₁ hwe₁ hlv hsat
      rcases hcase with ⟨hone, hr⟩ | ⟨hone, hcase⟩
      · -- left operand necessarily errors: collapse to it
        subst hr
        have herr : ∀ v, evaluate x₁ env.request env.entities ≠ .ok v := by
          intro v hv
          obtain ⟨b, hb⟩ := hbool₁ v hv ; subst hb
          have hm := IHl.left (if b then .tt else .ff) (by cases b <;> rw [hv] <;> rfl)
          simp only [Outcomes.isOnlyError, decide_eq_true_eq] at hone
          rw [hone] at hm
          cases b <;> simp [Outcomes.mem] at hm
        cases heval : evaluate x₁ env.request env.entities with
        | ok v => exact absurd heval (herr v)
        | error e =>
          have hand := evaluate_and_error (x₂ := x₂) heval
          constructor
          · intro u hu
            rw [hand] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
            exact outcomes_isOnlyError_mem hone
          · rw [hand]
            have h2 := IHl.right ; rw [heval] at h2
            obtain ⟨e', he'⟩ := toOption_none_inv h2
            rw [he'] ; simp [Except.toOption]
      · rcases hcase with ⟨hfl, hr⟩ | ⟨htl, rn, hro, hrn⟩ | ⟨hnl, hng, hr⟩ | ⟨hnl, hng, rn, rv, hro, hrv, hrvcase⟩
        · -- left folded to false: the node is false
          subst hr
          have hlvf := asLit_some hfl ; subst hlvf
          have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool false)) := by
            have h2 := IHl.right
            simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
            exact toOption_some_inv h2.symm
          have hand := evaluate_and_false (x₂ := x₂) hx₁
          constructor
          · intro u hu
            rw [hand] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu ; rfl
          · rw [hand] ; simp [evaluate, Except.toOption]
        · -- left folded to true: the node is the right operand
          have hlvt := asLit_some htl ; subst hlvt
          have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool true)) := by
            have h2 := IHl.right
            simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
            exact toOption_some_inv h2.symm
          -- the literal-false shortcut of `compileAnd` cannot apply
          have hcs : CompileAndSym tn l.term (SymCC.compile x₂ εnv) := by
            split at hmatch
            · rename_i heqf
              exfalso
              have hrb := compile_bisimulation hwε₁ hwe₁ hwI heq hokl
              rw [hx₁, heqf] at hrb
              simp only [Same.same, interpret_term_some, interpret_term_prim] at hrb
              have := same_ok_bool_term_implies hrb
              simp at this
            · exact hmatch
          obtain ⟨_, t₂, hok₂, hty₂, _⟩ := hcs
          have hwbrn := hwbr rn hro
          obtain ⟨hokr, _⟩ := wellBuilt_compile hwbrn
          have htyr : rn.term.typeOf = .option .bool := by
            have hh := hok₂.symm.trans hokr ; injection hh with h' ; rw [← h'] ; exact hty₂
          have hszr : sizeOf rn ≤ N := by subst hro ; simp at hle ; omega
          have IHr := ihN rn x₂ trail r hszr hwbrn htyr hwε₂ hwe₂ hrn hsat
          have hand := evaluate_and_true (x₂ := x₂) hx₁
          constructor
          · intro u hu
            rw [hand] at hu
            cases heval₂ : evaluate x₂ env.request env.entities with
            | error e =>
              rw [heval₂] at hu
              simp only [result_as_bool_error, Except.map, outcomeOf, Option.some.injEq] at hu
              subst hu
              exact IHr.left .err (by rw [heval₂] ; rfl)
            | ok v =>
              obtain ⟨b, hb⟩ := eval_ok_bool hwI heq hwε₂ hwe₂ hokr htyr heval₂ ; subst hb
              rw [heval₂] at hu
              simp only [result_as_bool_ok, Except.map] at hu
              have hm := IHr.left (if b then .tt else .ff) (by cases b <;> rw [heval₂] <;> rfl)
              cases b <;> simp only [outcomeOf, Option.some.injEq] at hu <;> subst hu <;>
                simpa using hm
          · rw [hand]
            have h2 := IHr.right
            calc (evaluate r.toExpr env.request env.entities).toOption
                = (evaluate x₂ env.request env.entities).toOption := h2
              _ = ((Result.as Bool (evaluate x₂ env.request env.entities)).map
                    (λ b => Value.prim (.bool b))).toOption := ?_
            cases heval₂ : evaluate x₂ env.request env.entities with
            | error e => simp [result_as_bool_error, Except.map, Except.toOption]
            | ok v =>
              obtain ⟨b, hb⟩ := eval_ok_bool hwI heq hwε₂ hwe₂ hokr htyr heval₂ ; subst hb
              simp [result_as_bool_ok, Except.map, Except.toOption]
        · -- gating: the left operand cannot be true, so `l && r ≡ l`
          subst hr
          constructor
          · intro u hu
            cases heval : evaluate x₁ env.request env.entities with
            | error e =>
              rw [evaluate_and_error (x₂ := x₂) heval] at hu
              simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
              exact IHl.left .err (by rw [heval] ; rfl)
            | ok v =>
              obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
              cases b
              case true =>
                have hm := IHl.left .tt (by rw [heval] ; rfl)
                simp only [Outcomes.mem] at hm
                simp [hm] at hng
              case false =>
                rw [evaluate_and_false (x₂ := x₂) heval] at hu
                simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                exact IHl.left .ff (by rw [heval] ; rfl)
          · cases heval : evaluate x₁ env.request env.entities with
            | error e =>
              rw [evaluate_and_error (x₂ := x₂) heval]
              have h2 := IHl.right ; rw [heval] at h2
              obtain ⟨e', he'⟩ := toOption_none_inv h2
              rw [he'] ; simp [Except.toOption]
            | ok v =>
              obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
              cases b
              case true =>
                have hm := IHl.left .tt (by rw [heval] ; rfl)
                simp only [Outcomes.mem] at hm
                simp [hm] at hng
              case false =>
                rw [evaluate_and_false (x₂ := x₂) heval]
                have h2 := IHl.right ; rw [heval] at h2
                rw [h2] ; try simp [Except.toOption]
        · -- the right operand was evaluated under the extended trail
          subst hro
          have hwbrn := hwbr rn rfl
          obtain ⟨hokr, _⟩ := wellBuilt_compile hwbrn
          have hcs : CompileAndSym tn l.term (SymCC.compile x₂ εnv) → True := λ _ => trivial
          -- typing for the right operand (the literal-false shortcut may or may
          -- not apply; if it does, the left operand is always false and the
          -- right facts are never needed — but the type is still available
          -- from the child's own compilation when required below)
          have hszr : sizeOf rn ≤ N := by simp at hle ; omega
          -- case on the concrete left operand
          cases heval : evaluate x₁ env.request env.entities with
          | error e =>
            have hand := evaluate_and_error (x₂ := x₂) heval
            have hlerr := IHl.left .err (by rw [heval] ; rfl)
            have h2l := IHl.right ; rw [heval] at h2l
            obtain ⟨e', he'⟩ := toOption_none_inv h2l
            rcases hrvcase with ⟨hrt, hr⟩ | ⟨hrf, hef, hr⟩ | ⟨hor, hr⟩ <;> subst hr
            · rw [unguard_eq_of_mem (by intro h ; cases h) hlerr]
              constructor
              · intro u hu
                rw [hand] at hu
                simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                exact hlerr
              · rw [hand, he'] ; simp [Except.toOption]
            · exfalso
              simp only [Outcomes.isErrorFree, Bool.not_eq_true'] at hef
              simp only [Outcomes.mem] at hlerr
              rw [hlerr] at hef ; cases hef
            · constructor
              · intro u hu
                rw [hand] at hu
                simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                simp only [seexpr_outcomes_and]
                exact outcomes_and_mem_err hlerr
              · rw [hand]
                simp only [seexpr_toExpr_and]
                rw [evaluate_and_error (x₂ := rv.toExpr) he']
                simp [Except.toOption]
          | ok v =>
            obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
            cases b
            case false =>
              have hand := evaluate_and_false (x₂ := x₂) heval
              have hlff := IHl.left .ff (by rw [heval] ; rfl)
              have h2l := IHl.right ; rw [heval] at h2l
              have hlok := toOption_some_inv h2l
              rcases hrvcase with ⟨hrt, hr⟩ | ⟨hrf, hef, hr⟩ | ⟨hor, hr⟩ <;> subst hr
              · rw [unguard_eq_of_mem (by intro h ; cases h) hlff]
                constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                  exact hlff
                · rw [hand, hlok] ; try simp [Except.toOption]
              · constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [outcomeOf, Option.some.injEq] at hu ; subst hu ; rfl
                · rw [hand] ; simp [evaluate, Except.toOption]
              · constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                  simp only [seexpr_outcomes_and]
                  exact outcomes_and_mem_ff hlff
                · rw [hand]
                  simp only [seexpr_toExpr_and]
                  rw [evaluate_and_false (x₂ := rv.toExpr) hlok]
                  try simp [Except.toOption]
            case true =>
              -- the extended trail is satisfied; the right IH applies
              have hltt := IHl.left .tt (by rw [heval] ; rfl)
              have hrb := compile_bisimulation hwε₁ hwe₁ hwI heq hokl
              rw [heval] at hrb
              simp only [Same.same] at hrb
              have hti := same_ok_bool_implies hrb
              have htr : (eq l.term (⊙ true)).interpret I = true := by
                simp only [someOf]
                rw [interpret_eq hwI (compile_wf hwε₁ hokl).left
                  (Term.WellFormed.some_wf wf_bool)]
                rw [interpret_term_some, interpret_term_prim, hti]
                exact pe_eq_same
              have hsat' : (base ++ (trail ++ [eq l.term (⊙ true)] ++ l.factTerms true)).satisfiedBy I := by
                simpa only [List.append_assoc] using satisfiedBy_facts hex (satisfiedBy_snoc hsat htr)
              -- the literal-false shortcut cannot apply (left is true here)
              have hcs : CompileAndSym tn l.term (SymCC.compile x₂ εnv) := by
                split at hmatch
                · rename_i heqf
                  exfalso
                  rw [heqf] at hti
                  simp only [interpret_term_some, interpret_term_prim] at hti
                  injection hti with hti' ; injection hti' with hti'' ; cases hti''
                · exact hmatch
              obtain ⟨_, t₂, hok₂, hty₂, _⟩ := hcs
              have htyr : rn.term.typeOf = .option .bool := by
                have hh := hok₂.symm.trans hokr ; injection hh with h' ; rw [← h'] ; exact hty₂
              have IHr := ihN rn x₂ (trail ++ [eq l.term (⊙ true)] ++ l.factTerms true) rv hszr hwbrn htyr
                hwε₂ hwe₂ hrv hsat'
              have hand := evaluate_and_true (x₂ := x₂) heval
              have h2l := IHl.right ; rw [heval] at h2l
              have hlok := toOption_some_inv h2l
              rcases hrvcase with ⟨hrt, hr⟩ | ⟨hrf, hef, hr⟩ | ⟨hor, hr⟩ <;> subst hr
              · -- right folded to true: the node is the left operand (a kept
                -- guard, then guarding nothing, folds to `true` — plan 5)
                have hrvt := asLit_some hrt ; subst hrvt
                have hx₂ : evaluate x₂ env.request env.entities = .ok (.prim (.bool true)) := by
                  have h2 := IHr.right
                  simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
                  exact toOption_some_inv h2.symm
                obtain ⟨hltt', hlok'⟩ := unguard_true hltt hlok
                constructor
                · intro u hu
                  rw [hand, hx₂] at hu
                  simp only [result_as_bool_ok, Except.map, outcomeOf, Option.some.injEq] at hu
                  subst hu
                  exact hltt'
                · rw [hand, hx₂, hlok']
                  simp [result_as_bool_ok, Except.map, Except.toOption]
              · -- right folded to false on an error-free left: the node is false
                have hrvf := asLit_some hrf ; subst hrvf
                have hx₂ : evaluate x₂ env.request env.entities = .ok (.prim (.bool false)) := by
                  have h2 := IHr.right
                  simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
                  exact toOption_some_inv h2.symm
                constructor
                · intro u hu
                  rw [hand, hx₂] at hu
                  simp only [result_as_bool_ok, Except.map, outcomeOf, Option.some.injEq] at hu
                  subst hu ; rfl
                · rw [hand, hx₂]
                  simp [result_as_bool_ok, Except.map, evaluate, Except.toOption]
              · -- kept as an And node
                constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [seexpr_outcomes_and]
                  cases heval₂ : evaluate x₂ env.request env.entities with
                  | error e =>
                    rw [heval₂] at hu
                    simp only [result_as_bool_error, Except.map, outcomeOf,
                      Option.some.injEq] at hu
                    subst hu
                    exact outcomes_and_mem_tt hltt (IHr.left .err (by rw [heval₂] ; rfl))
                  | ok v =>
                    obtain ⟨b, hb⟩ := eval_ok_bool hwI heq hwε₂ hwe₂ hokr htyr heval₂
                    subst hb
                    rw [heval₂] at hu
                    simp only [result_as_bool_ok, Except.map] at hu
                    have hm := IHr.left (if b then .tt else .ff)
                      (by cases b <;> rw [heval₂] <;> rfl)
                    cases b <;> simp only [outcomeOf, Option.some.injEq] at hu <;> subst hu <;>
                      exact outcomes_and_mem_tt hltt (by simpa using hm)
                · rw [hand]
                  simp only [seexpr_toExpr_and]
                  rw [evaluate_and_true (x₂ := rv.toExpr) hlok]
                  exact toOption_as_bool IHr.right
    | or xn tn l ro =>
      cases hwb with
      | @or x₁ x₂ t' l' ro' hwbl hwbr hok =>
      simp only [SENode.term] at hty
      obtain ⟨t₁, hok₁, hmatch⟩ := compile_or_ok_implies hok
      obtain ⟨hokl, _⟩ := wellBuilt_compile hwbl
      have ht₁ : t₁ = l.term := by
        have hh := hokl.symm.trans hok₁ ; injection hh with h' ; exact h'.symm
      subst ht₁
      obtain ⟨hwε₁, hwε₂⟩ := wf_εnv_for_or_implies hwε
      obtain ⟨hwe₁, hwe₂⟩ := wf_env_for_or_implies hwe
      have htyl : l.term.typeOf = .option .bool := by
        split at hmatch
        · rename_i heqf ; rw [heqf] ; simp [typeOf_term_some, typeOf_bool]
        · exact hmatch.left
      have hbool₁ : ∀ v, evaluate x₁ env.request env.entities = .ok v →
          ∃ b, v = .prim (.bool b) :=
        λ v hv => eval_ok_bool hwI heq hwε₁ hwe₁ hokl htyl hv
      obtain ⟨lv, hlv, hcase⟩ := evalNode_or_id_spec h
      have hszl : sizeOf l ≤ N := by simp at hle ; omega
      have IHl := ihN l x₁ trail lv hszl hwbl htyl hwε₁ hwe₁ hlv hsat
      rcases hcase with ⟨hone, hr⟩ | ⟨hone, hcase⟩
      · -- left operand necessarily errors: collapse to it
        subst hr
        have herr : ∀ v, evaluate x₁ env.request env.entities ≠ .ok v := by
          intro v hv
          obtain ⟨b, hb⟩ := hbool₁ v hv ; subst hb
          have hm := IHl.left (if b then .tt else .ff) (by cases b <;> rw [hv] <;> rfl)
          simp only [Outcomes.isOnlyError, decide_eq_true_eq] at hone
          rw [hone] at hm
          cases b <;> simp [Outcomes.mem] at hm
        cases heval : evaluate x₁ env.request env.entities with
        | ok v => exact absurd heval (herr v)
        | error e =>
          have hand := evaluate_or_error (x₂ := x₂) heval
          constructor
          · intro u hu
            rw [hand] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
            exact outcomes_isOnlyError_mem hone
          · rw [hand]
            have h2 := IHl.right ; rw [heval] at h2
            obtain ⟨e', he'⟩ := toOption_none_inv h2
            rw [he'] ; simp [Except.toOption]
      · rcases hcase with ⟨htl, hr⟩ | ⟨hfl, rn, hro, hrn⟩ | ⟨hnl, hng, hr⟩ | ⟨hnl, hng, rn, rv, hro, hrv, hrvcase⟩
        · -- left folded to true: the node is true
          subst hr
          have hlvt := asLit_some htl ; subst hlvt
          have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool true)) := by
            have h2 := IHl.right
            simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
            exact toOption_some_inv h2.symm
          have hand := evaluate_or_true (x₂ := x₂) hx₁
          constructor
          · intro u hu
            rw [hand] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu ; rfl
          · rw [hand] ; simp [evaluate, Except.toOption]
        · -- left folded to false: the node is the right operand
          have hlvf := asLit_some hfl ; subst hlvf
          have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool false)) := by
            have h2 := IHl.right
            simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
            exact toOption_some_inv h2.symm
          have hcs : CompileOrSym tn l.term (SymCC.compile x₂ εnv) := by
            split at hmatch
            · rename_i heqf
              exfalso
              have hrb := compile_bisimulation hwε₁ hwe₁ hwI heq hokl
              rw [hx₁, heqf] at hrb
              simp only [Same.same, interpret_term_some, interpret_term_prim] at hrb
              have := same_ok_bool_term_implies hrb
              simp at this
            · exact hmatch
          obtain ⟨_, t₂, hok₂, hty₂, _⟩ := hcs
          have hwbrn := hwbr rn hro
          obtain ⟨hokr, _⟩ := wellBuilt_compile hwbrn
          have htyr : rn.term.typeOf = .option .bool := by
            have hh := hok₂.symm.trans hokr ; injection hh with h' ; rw [← h'] ; exact hty₂
          have hszr : sizeOf rn ≤ N := by subst hro ; simp at hle ; omega
          have IHr := ihN rn x₂ trail r hszr hwbrn htyr hwε₂ hwe₂ hrn hsat
          have hand := evaluate_or_false (x₂ := x₂) hx₁
          constructor
          · intro u hu
            rw [hand] at hu
            cases heval₂ : evaluate x₂ env.request env.entities with
            | error e =>
              rw [heval₂] at hu
              simp only [result_as_bool_error, Except.map, outcomeOf, Option.some.injEq] at hu
              subst hu
              exact IHr.left .err (by rw [heval₂] ; rfl)
            | ok v =>
              obtain ⟨b, hb⟩ := eval_ok_bool hwI heq hwε₂ hwe₂ hokr htyr heval₂ ; subst hb
              rw [heval₂] at hu
              simp only [result_as_bool_ok, Except.map] at hu
              have hm := IHr.left (if b then .tt else .ff) (by cases b <;> rw [heval₂] <;> rfl)
              cases b <;> simp only [outcomeOf, Option.some.injEq] at hu <;> subst hu <;>
                simpa using hm
          · rw [hand]
            have h2 := IHr.right
            calc (evaluate r.toExpr env.request env.entities).toOption
                = (evaluate x₂ env.request env.entities).toOption := h2
              _ = ((Result.as Bool (evaluate x₂ env.request env.entities)).map
                    (λ b => Value.prim (.bool b))).toOption := ?_
            cases heval₂ : evaluate x₂ env.request env.entities with
            | error e => simp [result_as_bool_error, Except.map, Except.toOption]
            | ok v =>
              obtain ⟨b, hb⟩ := eval_ok_bool hwI heq hwε₂ hwe₂ hokr htyr heval₂ ; subst hb
              simp [result_as_bool_ok, Except.map, Except.toOption]
        · -- gating: the left operand cannot be false, so `l || r ≡ l`
          subst hr
          constructor
          · intro u hu
            cases heval : evaluate x₁ env.request env.entities with
            | error e =>
              rw [evaluate_or_error (x₂ := x₂) heval] at hu
              simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
              exact IHl.left .err (by rw [heval] ; rfl)
            | ok v =>
              obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
              cases b
              case false =>
                have hm := IHl.left .ff (by rw [heval] ; rfl)
                simp only [Outcomes.mem] at hm
                simp [hm] at hng
              case true =>
                rw [evaluate_or_true (x₂ := x₂) heval] at hu
                simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                exact IHl.left .tt (by rw [heval] ; rfl)
          · cases heval : evaluate x₁ env.request env.entities with
            | error e =>
              rw [evaluate_or_error (x₂ := x₂) heval]
              have h2 := IHl.right ; rw [heval] at h2
              obtain ⟨e', he'⟩ := toOption_none_inv h2
              rw [he'] ; simp [Except.toOption]
            | ok v =>
              obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
              cases b
              case false =>
                have hm := IHl.left .ff (by rw [heval] ; rfl)
                simp only [Outcomes.mem] at hm
                simp [hm] at hng
              case true =>
                rw [evaluate_or_true (x₂ := x₂) heval]
                have h2 := IHl.right ; rw [heval] at h2
                rw [h2] ; try simp [Except.toOption]
        · -- the right operand was evaluated under the extended trail
          subst hro
          have hwbrn := hwbr rn rfl
          obtain ⟨hokr, _⟩ := wellBuilt_compile hwbrn
          have hszr : sizeOf rn ≤ N := by simp at hle ; omega
          cases heval : evaluate x₁ env.request env.entities with
          | error e =>
            have hand := evaluate_or_error (x₂ := x₂) heval
            have hlerr := IHl.left .err (by rw [heval] ; rfl)
            have h2l := IHl.right ; rw [heval] at h2l
            obtain ⟨e', he'⟩ := toOption_none_inv h2l
            rcases hrvcase with ⟨hrf, hr⟩ | ⟨hrt, hef, hr⟩ | ⟨hor, hr⟩ <;> subst hr
            · constructor
              · intro u hu
                rw [hand] at hu
                simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                exact hlerr
              · rw [hand, he'] ; simp [Except.toOption]
            · exfalso
              simp only [Outcomes.isErrorFree, Bool.not_eq_true'] at hef
              simp only [Outcomes.mem] at hlerr
              rw [hlerr] at hef ; cases hef
            · constructor
              · intro u hu
                rw [hand] at hu
                simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                simp only [seexpr_outcomes_or]
                exact outcomes_or_mem_err hlerr
              · rw [hand]
                simp only [seexpr_toExpr_or]
                rw [evaluate_or_error (x₂ := rv.toExpr) he']
                simp [Except.toOption]
          | ok v =>
            obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
            cases b
            case true =>
              have hand := evaluate_or_true (x₂ := x₂) heval
              have hltt := IHl.left .tt (by rw [heval] ; rfl)
              have h2l := IHl.right ; rw [heval] at h2l
              have hlok := toOption_some_inv h2l
              rcases hrvcase with ⟨hrf, hr⟩ | ⟨hrt, hef, hr⟩ | ⟨hor, hr⟩ <;> subst hr
              · constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                  exact hltt
                · rw [hand, hlok] ; try simp [Except.toOption]
              · constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [outcomeOf, Option.some.injEq] at hu ; subst hu ; rfl
                · rw [hand] ; simp [evaluate, Except.toOption]
              · constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
                  simp only [seexpr_outcomes_or]
                  exact outcomes_or_mem_tt hltt
                · rw [hand]
                  simp only [seexpr_toExpr_or]
                  rw [evaluate_or_true (x₂ := rv.toExpr) hlok]
                  try simp [Except.toOption]
            case false =>
              -- the extended trail is satisfied; the right IH applies
              have hlff := IHl.left .ff (by rw [heval] ; rfl)
              have hrb := compile_bisimulation hwε₁ hwe₁ hwI heq hokl
              rw [heval] at hrb
              simp only [Same.same] at hrb
              have hti := same_ok_bool_implies hrb
              have htr : (eq l.term (⊙ false)).interpret I = true := by
                simp only [someOf]
                rw [interpret_eq hwI (compile_wf hwε₁ hokl).left
                  (Term.WellFormed.some_wf wf_bool)]
                rw [interpret_term_some, interpret_term_prim, hti]
                exact pe_eq_same
              have hsat' : (base ++ (trail ++ [eq l.term (⊙ false)] ++ l.factTerms false)).satisfiedBy I := by
                simpa only [List.append_assoc] using satisfiedBy_facts hex (satisfiedBy_snoc hsat htr)
              have hcs : CompileOrSym tn l.term (SymCC.compile x₂ εnv) := by
                split at hmatch
                · rename_i heqf
                  exfalso
                  rw [heqf] at hti
                  simp only [interpret_term_some, interpret_term_prim] at hti
                  injection hti with hti' ; injection hti' with hti'' ; cases hti''
                · exact hmatch
              obtain ⟨_, t₂, hok₂, hty₂, _⟩ := hcs
              have htyr : rn.term.typeOf = .option .bool := by
                have hh := hok₂.symm.trans hokr ; injection hh with h' ; rw [← h'] ; exact hty₂
              have IHr := ihN rn x₂ (trail ++ [eq l.term (⊙ false)] ++ l.factTerms false) rv hszr hwbrn htyr
                hwε₂ hwe₂ hrv hsat'
              have hand := evaluate_or_false (x₂ := x₂) heval
              have h2l := IHl.right ; rw [heval] at h2l
              have hlok := toOption_some_inv h2l
              rcases hrvcase with ⟨hrf, hr⟩ | ⟨hrt, hef, hr⟩ | ⟨hor, hr⟩ <;> subst hr
              · -- right folded to false: the node is the left operand
                have hrvf := asLit_some hrf ; subst hrvf
                have hx₂ : evaluate x₂ env.request env.entities = .ok (.prim (.bool false)) := by
                  have h2 := IHr.right
                  simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
                  exact toOption_some_inv h2.symm
                constructor
                · intro u hu
                  rw [hand, hx₂] at hu
                  simp only [result_as_bool_ok, Except.map, outcomeOf, Option.some.injEq] at hu
                  subst hu
                  exact hlff
                · rw [hand, hx₂, hlok]
                  try simp [result_as_bool_ok, Except.map, Except.toOption]
              · -- right folded to true on an error-free left: the node is true
                have hrvt := asLit_some hrt ; subst hrvt
                have hx₂ : evaluate x₂ env.request env.entities = .ok (.prim (.bool true)) := by
                  have h2 := IHr.right
                  simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
                  exact toOption_some_inv h2.symm
                constructor
                · intro u hu
                  rw [hand, hx₂] at hu
                  simp only [result_as_bool_ok, Except.map, outcomeOf, Option.some.injEq] at hu
                  subst hu ; rfl
                · rw [hand, hx₂]
                  simp [result_as_bool_ok, Except.map, evaluate, Except.toOption]
              · -- kept as an Or node
                constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [seexpr_outcomes_or]
                  cases heval₂ : evaluate x₂ env.request env.entities with
                  | error e =>
                    rw [heval₂] at hu
                    simp only [result_as_bool_error, Except.map, outcomeOf,
                      Option.some.injEq] at hu
                    subst hu
                    exact outcomes_or_mem_ff hlff (IHr.left .err (by rw [heval₂] ; rfl))
                  | ok v =>
                    obtain ⟨b, hb⟩ := eval_ok_bool hwI heq hwε₂ hwe₂ hokr htyr heval₂
                    subst hb
                    rw [heval₂] at hu
                    simp only [result_as_bool_ok, Except.map] at hu
                    have hm := IHr.left (if b then .tt else .ff)
                      (by cases b <;> rw [heval₂] <;> rfl)
                    cases b <;> simp only [outcomeOf, Option.some.injEq] at hu <;> subst hu <;>
                      exact outcomes_or_mem_ff hlff (by simpa using hm)
                · rw [hand]
                  simp only [seexpr_toExpr_or]
                  rw [evaluate_or_false (x₂ := rv.toExpr) hlok]
                  exact toOption_as_bool IHr.right
    | ite xn tn c ao bo =>
      cases hwb with
      | @ite x₁ x₂ x₃ t' c' ao' bo' hwbc hwba hwbb hok =>
      simp only [SENode.term] at hty
      obtain ⟨t₁, hok₁, hmatch⟩ := compile_ite_ok_implies hok
      obtain ⟨hokc, _⟩ := wellBuilt_compile hwbc
      have ht₁ : t₁ = c.term := by
        have hh := hokc.symm.trans hok₁ ; injection hh with h' ; exact h'.symm
      subst ht₁
      obtain ⟨hwε₁, hwε₂, hwε₃⟩ := wf_εnv_for_ite_implies hwε
      obtain ⟨hwe₁, hwe₂, hwe₃⟩ := wf_env_for_ite_implies hwe
      have htyc : c.term.typeOf = .option .bool := by
        split at hmatch
        · rename_i heq ; rw [heq] ; simp [typeOf_term_some, typeOf_bool]
        · rename_i heq ; rw [heq] ; simp [typeOf_term_some, typeOf_bool]
        · exact hmatch.left
      have hbool₁ : ∀ v, evaluate x₁ env.request env.entities = .ok v →
          ∃ b, v = .prim (.bool b) :=
        λ v hv => eval_ok_bool hwI heq hwε₁ hwe₁ hokc htyc hv
      have hbranchty : CompileIfSym tn c.term (SymCC.compile x₂ εnv) (SymCC.compile x₃ εnv) →
          (∃ t₂, SymCC.compile x₂ εnv = .ok t₂ ∧ t₂.typeOf = .option .bool) ∧
          (∃ t₃, SymCC.compile x₃ εnv = .ok t₃ ∧ t₃.typeOf = .option .bool) := by
        intro ⟨_, t₂, t₃, hok₂, hok₃, hty23, hteq⟩
        obtain ⟨hwc, _⟩ := compile_wf hwε₁ hokc
        obtain ⟨hw₂, ty₂, hty₂⟩ := compile_wf hwε₂ hok₂
        obtain ⟨hw₃, _, hty₃⟩ := compile_wf hwε₃ hok₃
        obtain ⟨hwg, htyg⟩ := wf_option_get hwc htyc
        have hite := wf_ite hwg hw₂ hw₃ htyg hty23
        rw [hty₂] at hite
        have hif := typeOf_ifSome_option (g := c.term) hite.right
        rw [← hteq, hty] at hif
        injection hif with hif'
        subst hif'
        exact ⟨⟨t₂, hok₂, hty₂⟩, ⟨t₃, hok₃, by rw [← hty23, hty₂]⟩⟩
      obtain ⟨cv, hcv, hcase⟩ := evalNode_ite_id_spec h
      have hszc : sizeOf c ≤ N := by simp at hle ; omega
      have IHc := ihN c x₁ trail cv hszc hwbc htyc hwε₁ hwe₁ hcv hsat
      -- bisimulation of the test, used to rule out the literal shortcuts
      have hrbc := compile_bisimulation hwε₁ hwe₁ hwI heq hokc
      simp only [Same.same] at hrbc
      -- typing of the then-branch child when the test is concretely true
      have htyan : ∀ an, ao = .some an →
          evaluate x₁ env.request env.entities = .ok (.prim (.bool true)) →
          an.term.typeOf = .option .bool := by
        intro an hao hx₁
        obtain ⟨hokan, _⟩ := wellBuilt_compile (hwba an hao)
        split at hmatch
        · have hh := hmatch.trans hokan ; injection hh with h' ; rw [← h'] ; exact hty
        · rename_i heqf
          exfalso
          rw [hx₁, heqf] at hrbc
          simp only [interpret_term_some, interpret_term_prim] at hrbc
          have := same_ok_bool_term_implies hrbc
          simp at this
        · obtain ⟨⟨t₂, hok₂, hty₂⟩, _⟩ := hbranchty hmatch
          have hh := hok₂.symm.trans hokan ; injection hh with h' ; rw [← h'] ; exact hty₂
      -- typing of the else-branch child when the test is concretely false
      have htybn : ∀ bn, bo = .some bn →
          evaluate x₁ env.request env.entities = .ok (.prim (.bool false)) →
          bn.term.typeOf = .option .bool := by
        intro bn hbo hx₁
        obtain ⟨hokbn, _⟩ := wellBuilt_compile (hwbb bn hbo)
        split at hmatch
        · rename_i heqt
          exfalso
          rw [hx₁, heqt] at hrbc
          simp only [interpret_term_some, interpret_term_prim] at hrbc
          have := same_ok_bool_term_implies hrbc
          simp at this
        · have hh := hmatch.trans hokbn ; injection hh with h' ; rw [← h'] ; exact hty
        · obtain ⟨_, ⟨t₃, hok₃, hty₃⟩⟩ := hbranchty hmatch
          have hh := hok₃.symm.trans hokbn ; injection hh with h' ; rw [← h'] ; exact hty₃
      rcases hcase with ⟨hone, hr⟩ | ⟨hone, hcase⟩
      · -- the test necessarily errors: collapse to it
        subst hr
        have herr : ∀ v, evaluate x₁ env.request env.entities ≠ .ok v := by
          intro v hv
          obtain ⟨b, hb⟩ := hbool₁ v hv ; subst hb
          have hm := IHc.left (if b then .tt else .ff) (by cases b <;> rw [hv] <;> rfl)
          simp only [Outcomes.isOnlyError, decide_eq_true_eq] at hone
          rw [hone] at hm
          cases b <;> simp [Outcomes.mem] at hm
        cases heval : evaluate x₁ env.request env.entities with
        | ok v => exact absurd heval (herr v)
        | error e =>
          have hand := evaluate_ite_error (x₂ := x₂) (x₃ := x₃) heval
          constructor
          · intro u hu
            rw [hand] at hu
            simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
            exact outcomes_isOnlyError_mem hone
          · rw [hand]
            have h2 := IHc.right ; rw [heval] at h2
            obtain ⟨e', he'⟩ := toOption_none_inv h2
            rw [he'] ; simp [Except.toOption]
      · rcases hcase with ⟨hct, an, hao, han⟩ | ⟨hcf, bn, hbo, hbn⟩ |
          ⟨hnl, an, bn, av, bv, hao, hbo, hav, hbv, hr⟩
        · -- test folded to true: the node is the then-branch
          have hcvt := asLit_some hct ; subst hcvt
          have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool true)) := by
            have h2 := IHc.right
            simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
            exact toOption_some_inv h2.symm
          have hwban := hwba an hao
          have hszan : sizeOf an ≤ N := by subst hao ; simp at hle ; omega
          have IHa := ihN an x₂ trail r hszan hwban (htyan an hao hx₁) hwε₂ hwe₂ han hsat
          have hand := evaluate_ite_true (x₂ := x₂) (x₃ := x₃) hx₁
          exact ⟨λ u hu => IHa.left u (by rw [hand] at hu ; exact hu),
                 by rw [hand] ; exact IHa.right⟩
        · -- test folded to false: the node is the else-branch
          have hcvf := asLit_some hcf ; subst hcvf
          have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool false)) := by
            have h2 := IHc.right
            simp only [seexpr_toExpr_lit, evaluate, Except.toOption] at h2
            exact toOption_some_inv h2.symm
          have hwbbn := hwbb bn hbo
          have hszbn : sizeOf bn ≤ N := by subst hbo ; simp at hle ; omega
          have IHb := ihN bn x₃ trail r hszbn hwbbn (htybn bn hbo hx₁) hwε₃ hwe₃ hbn hsat
          have hand := evaluate_ite_false (x₂ := x₂) (x₃ := x₃) hx₁
          exact ⟨λ u hu => IHb.left u (by rw [hand] at hu ; exact hu),
                 by rw [hand] ; exact IHb.right⟩
        · -- kept as an If node, branches visited under their trails — or, a
          -- kept guard as the test with a then-branch folded to a literal,
          -- that branch alone (plan 5)
          subst hao hbo
          have hwban := hwba an rfl
          have hwbbn := hwbb bn rfl
          have hszan : sizeOf an ≤ N := by simp at hle ; omega
          have hszbn : sizeOf bn ≤ N := by simp at hle ; omega
          rcases iteResult_cases hr with ⟨avv, hav', _, hcvo, hr⟩ | hr
          · -- the test is concretely true (its outcomes are `{True}`), so the
            -- then-branch was visited under a satisfied trail
            subst hr hav'
            have hx₁ : evaluate x₁ env.request env.entities = .ok (.prim (.bool true)) := by
              cases heval : evaluate x₁ env.request env.entities with
              | error e =>
                have := IHc.left .err (by rw [heval] ; rfl)
                rw [hcvo] at this
                simp [Outcomes.lit, Outcomes.mem] at this
              | ok v =>
                obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
                cases b
                case false =>
                  have := IHc.left .ff (by rw [heval] ; rfl)
                  rw [hcvo] at this
                  simp [Outcomes.lit, Outcomes.mem] at this
                case true => rfl
            rcases hav with ⟨_, rv, hrv, hrveq⟩ | ⟨_, hnone⟩
            · injection hrveq with hrveq ; subst hrveq
              rw [hx₁] at hrbc
              have hti := same_ok_bool_implies hrbc
              have htr : (eq c.term (⊙ true)).interpret I = true := by
                simp only [someOf]
                rw [interpret_eq hwI (compile_wf hwε₁ hokc).left
                  (Term.WellFormed.some_wf wf_bool)]
                rw [interpret_term_some, interpret_term_prim, hti]
                exact pe_eq_same
              have hsat' : (base ++ (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true)).satisfiedBy I := by
                simpa only [List.append_assoc] using satisfiedBy_facts hex (satisfiedBy_snoc hsat htr)
              have IHa := ihN an x₂ (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true) r hszan hwban
                (htyan an rfl hx₁) hwε₂ hwe₂ hrv hsat'
              have hand := evaluate_ite_true (x₂ := x₂) (x₃ := x₃) hx₁
              exact ⟨λ u hu => IHa.left u (by rw [hand] at hu ; exact hu),
                     by rw [hand] ; exact IHa.right⟩
            · cases hnone
          subst hr
          cases heval : evaluate x₁ env.request env.entities with
          | error e =>
            have hand := evaluate_ite_error (x₂ := x₂) (x₃ := x₃) heval
            have hcerr := IHc.left .err (by rw [heval] ; rfl)
            have h2c := IHc.right ; rw [heval] at h2c
            obtain ⟨e', he'⟩ := toOption_none_inv h2c
            constructor
            · intro u hu
              rw [hand] at hu
              simp only [outcomeOf, Option.some.injEq] at hu ; subst hu
              simp only [seexpr_outcomes_ite]
              exact outcomes_ite_mem_err hcerr
            · rw [hand]
              simp only [seexpr_toExpr_ite]
              rw [evaluate_ite_error (x₂ := (av.getD (.unvisited an.expr)).toExpr)
                (x₃ := (bv.getD (.unvisited bn.expr)).toExpr) he']
              simp [Except.toOption]
          | ok v =>
            obtain ⟨b, hb⟩ := hbool₁ v heval ; subst hb
            have h2c := IHc.right ; rw [heval] at h2c
            have hcok := toOption_some_inv h2c
            rw [heval] at hrbc
            have hti := same_ok_bool_implies hrbc
            cases b
            case true =>
              have hctt := IHc.left .tt (by rw [heval] ; rfl)
              rcases hav with ⟨hct, rv, hrv, hav⟩ | ⟨hct, _⟩
              · subst hav
                have htr : (eq c.term (⊙ true)).interpret I = true := by
                  simp only [someOf]
                  rw [interpret_eq hwI (compile_wf hwε₁ hokc).left
                    (Term.WellFormed.some_wf wf_bool)]
                  rw [interpret_term_some, interpret_term_prim, hti]
                  exact pe_eq_same
                have hsat' : (base ++ (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true)).satisfiedBy I := by
                  simpa only [List.append_assoc] using satisfiedBy_facts hex (satisfiedBy_snoc hsat htr)
                have IHa := ihN an x₂ (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true) rv hszan hwban
                  (htyan an rfl heval) hwε₂ hwe₂ hrv hsat'
                have hand := evaluate_ite_true (x₂ := x₂) (x₃ := x₃) heval
                constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [seexpr_outcomes_ite, Option.map]
                  exact outcomes_ite_mem_then hctt rfl (IHa.left u hu)
                · rw [hand]
                  simp only [seexpr_toExpr_ite, Option.getD_some]
                  rw [evaluate_ite_true (x₂ := rv.toExpr)
                    (x₃ := (bv.getD (.unvisited bn.expr)).toExpr) hcok]
                  exact IHa.right
              · exfalso
                simp only [Outcomes.mem] at hctt
                simp [hctt] at hct
            case false =>
              have hcff := IHc.left .ff (by rw [heval] ; rfl)
              rcases hbv with ⟨hcf, rv, hrv, hbv⟩ | ⟨hcf, _⟩
              · subst hbv
                have htr : (eq c.term (⊙ false)).interpret I = true := by
                  simp only [someOf]
                  rw [interpret_eq hwI (compile_wf hwε₁ hokc).left
                    (Term.WellFormed.some_wf wf_bool)]
                  rw [interpret_term_some, interpret_term_prim, hti]
                  exact pe_eq_same
                have hsat' : (base ++ (trail ++ [eq c.term (⊙ false)] ++ c.factTerms false)).satisfiedBy I := by
                  simpa only [List.append_assoc] using satisfiedBy_facts hex (satisfiedBy_snoc hsat htr)
                have IHb := ihN bn x₃ (trail ++ [eq c.term (⊙ false)] ++ c.factTerms false) rv hszbn hwbbn
                  (htybn bn rfl heval) hwε₃ hwe₃ hrv hsat'
                have hand := evaluate_ite_false (x₂ := x₂) (x₃ := x₃) heval
                constructor
                · intro u hu
                  rw [hand] at hu
                  simp only [seexpr_outcomes_ite, Option.map]
                  exact outcomes_ite_mem_else hcff rfl (IHb.left u hu)
                · rw [hand]
                  simp only [seexpr_toExpr_ite, Option.getD_some]
                  rw [evaluate_ite_false (x₂ := (av.getD (.unvisited an.expr)).toExpr)
                    (x₃ := rv.toExpr) hcok]
                  exact IHb.right
              · exfalso
                simp only [Outcomes.mem] at hcff
                simp [hcff] at hcf


/-! ### Top-level soundness with the base asserts as hypothesis -/

/-- Characterization of `evalRoot` at `m := Id`. -/
theorem evalRoot_id_spec {unsat? : Asserts → Bool} {root : SENode} {base : Asserts}
    {r : SEExpr} :
  evalRoot (m := Id) unsat? root base = .ok r →
  root.term.typeOf = .option .bool ∧
  unsat? base = false ∧
  evalNode (m := Id) unsat? base root [] = .ok r
:= by
  intro h
  simp only [evalRoot, pure, bind, ExceptT.bind, ExceptT.bindCont, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  next => cases h
  next hne =>
    change (if unsat? base = true then Except.error EvalError.unsatisfiableAssumptions
      else evalNode (m := Id) unsat? base root []) = Except.ok r at h
    split at h
    next => cases h
    next hus =>
      refine ⟨by simpa using hne, by simpa using hus, h⟩

/--
Soundness of `symEvalWithBase`: for every well-formed interpretation `I` of
`εnv` that satisfies the base asserts, and every concrete environment
`env ∼ εnv.interpret I` well-formed for `x`, (S1) the concrete outcome of `x`
is in the root outcome set and (S2) the folded expression evaluates like `x`
up to the error kind.
-/
theorem symEvalWithBase_sound {unsat? : Asserts → Bool} {εnv : SymEnv} {x : Expr}
    {base : Asserts} {r : SEExpr} :
  UnsatSound unsat? εnv →
  εnv.WellFormedFor x →
  symEvalWithBase (m := Id) unsat? x base εnv = .ok r →
  ∀ (env : Env) (I : Interpretation),
    I.WellFormed εnv.entities →
    ExistsTrue I →
    env ∼ εnv.interpret I →
    env.WellFormedFor x →
    base.satisfiedBy I →
    (∀ u, outcomeOf (evaluate x env.request env.entities) = .some u →
      r.outcomes.mem u = true) ∧
    (evaluate r.toExpr env.request env.entities).toOption
      = (evaluate x env.request env.entities).toOption
:= by
  intro hsound hwε h env I hwI hex heq hwe hsat
  simp only [symEvalWithBase] at h
  split at h
  next e hbt =>
    (try simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk] at h)
    cases h
  next root fp hbt =>
    obtain ⟨hty, _, hnode⟩ := evalRoot_id_spec h
    have hwb := markKept_wellBuilt (ks := keptGuards x εnv) (buildTree_wellBuilt hbt)
    have hsat' : (base ++ []).satisfiedBy I := by rw [List.append_nil] ; exact hsat
    exact evalNode_sound hsound hwI hex heq hwb hty hwε hwe hnode hsat'


/-! ### The proved entry point: assumptions as expressions -/

theorem compileAll_spec {xs : List Expr} {εnv : SymEnv} {prs : List (Expr × CompileResult)} :
  compileAll xs εnv = .ok prs →
  ∀ p ∈ prs, p.1 ∈ xs ∧ Opt.compile p.1 εnv = .ok p.2
:= by
  intro h p hp
  induction xs generalizing prs with
  | nil =>
    simp only [compileAll, Except.ok.injEq] at h
    subst h
    simp at hp
  | cons a rest ih =>
    simp only [compileAll] at h
    cases hc : Opt.compile a εnv <;> rw [hc] at h <;>
      simp only [Except.bind_ok, Except.bind_err] at h
    case error => cases h
    case ok cr =>
      cases hr : compileAll rest εnv <;> rw [hr] at h <;>
        simp only [Except.bind_ok, Except.bind_err] at h
      case error => cases h
      case ok rest' =>
        injection h with h' ; subst h'
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · subst hp ; exact ⟨List.mem_cons_self .., hc⟩
        · obtain ⟨hin, hok⟩ := ih hr hp
          exact ⟨List.mem_cons_of_mem _ hin, hok⟩

theorem symEvaluate_id_spec {unsat? : Asserts → Bool} {x : Expr} {axs : List Expr}
    {εnv : SymEnv} {r : SEExpr} :
  symEvaluate (m := Id) unsat? x axs εnv = .ok r →
  ∃ root fp prs,
    Opt.buildTree x εnv = .ok (root, fp) ∧
    compileAll axs εnv = .ok prs ∧
    evalRoot (m := Id) unsat? (markKept (keptGuards x εnv) root)
      (prs.map (λ (p : Expr × CompileResult) => eq p.2.term (⊙ true))
        ++ (enforce (x :: axs) εnv).elts) = .ok r
:= by
  intro h
  simp only [symEvaluate] at h
  split at h
  next e hbt =>
    (try simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk] at h)
    cases h
  next root fp hbt =>
    split at h
    next e hca =>
      (try simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk] at h)
      cases h
    next prs hca => exact ⟨root, fp, prs, hbt, hca, h⟩

/-- `Opt.compile` success gives `SymCC.compile` success with the same term. -/
private theorem opt_compile_ok_term {x : Expr} {εnv : SymEnv} {cr : CompileResult} :
  Opt.compile x εnv = .ok cr → SymCC.compile x εnv = .ok cr.term
:= by
  intro h
  have hc := Opt.compile.correctness x εnv
  rw [h] at hc
  cases hc' : SymCC.compile x εnv <;> rw [hc'] at hc <;> simp_all

/--
Soundness of `symEvaluate`: for every concrete environment of `εnv` that is
strongly well-formed for the target and the assumptions and on which every
assumption evaluates to `true`, (S1) the concrete outcome of the target is in
the root outcome set and (S2) the folded expression evaluates like the target
up to the error kind.
-/
theorem symEvaluate_sound {unsat? : Asserts → Bool} {εnv : SymEnv} {x : Expr}
    {axs : List Expr} {r : SEExpr} :
  UnsatSound unsat? εnv →
  εnv.StronglyWellFormedForAll (x :: axs) →
  symEvaluate (m := Id) unsat? x axs εnv = .ok r →
  ∀ (env : Env) (I : Interpretation),
    I.WellFormed εnv.entities →
    ExistsTrue I →
    env ∼ εnv.interpret I →
    env.StronglyWellFormedForAll (x :: axs) →
    (∀ a ∈ axs, evaluate a env.request env.entities = .ok (.prim (.bool true))) →
    (∀ u, outcomeOf (evaluate x env.request env.entities) = .some u →
      r.outcomes.mem u = true) ∧
    (evaluate r.toExpr env.request env.entities).toOption
      = (evaluate x env.request env.entities).toOption
:= by
  intro hsound hsε h env I hwI hex heq hse hax
  obtain ⟨root, fp, prs, hbt, hca, hroot⟩ := symEvaluate_id_spec h
  obtain ⟨hty, _, hnode⟩ := evalRoot_id_spec hroot
  have hwb := markKept_wellBuilt (ks := keptGuards x εnv) (buildTree_wellBuilt hbt)
  have hwεall := swf_εnv_all_implies_wf_all hsε
  have hweall := swf_env_all_implies_wf_all hse
  have hwε : εnv.WellFormedFor x := hwεall x (List.mem_cons_self ..)
  have hwe : env.WellFormedFor x := hweall x (List.mem_cons_self ..)
  have hbase : Asserts.satisfiedBy I (prs.map (λ (p : Expr × CompileResult) => eq p.2.term (⊙ true))
      ++ (enforce (x :: axs) εnv).elts) := by
    rw [asserts_satisfiedBy_true]
    intro t ht
    simp only [List.mem_append, List.mem_map] at ht
    rcases ht with ⟨p, hp, hpt⟩ | ht
    · subst hpt
      obtain ⟨hin, hok⟩ := compileAll_spec hca p hp
      have hin' : p.1 ∈ x :: axs := List.mem_cons_of_mem _ hin
      have hokc := opt_compile_ok_term hok
      have hrb := compile_bisimulation (hwεall p.1 hin') (hweall p.1 hin') hwI heq hokc
      rw [hax p.1 hin] at hrb
      simp only [Same.same] at hrb
      have hti := same_ok_bool_implies hrb
      simp only [someOf]
      rw [interpret_eq hwI (compile_wf (hwεall p.1 hin') hokc).left
        (Term.WellFormed.some_wf wf_bool)]
      rw [interpret_term_some, interpret_term_prim, hti]
      exact pe_eq_same
    · have henf := enforce_satisfiedBy_swf heq hwI hsε hse rfl
      rw [asserts_satisfiedBy_true] at henf
      exact henf t ht
  have hsat' : Asserts.satisfiedBy I ((prs.map (λ (p : Expr × CompileResult) => eq p.2.term (⊙ true))
      ++ (enforce (x :: axs) εnv).elts) ++ []) := by
    rw [List.append_nil] ; exact hbase
  exact evalNode_sound hsound hwI hex heq hwb hty hwε hwe hnode hsat'

/-! ### The equivalence self-check -/

theorem checkEquivalent_id_spec {unsat? : Asserts → Bool} {base : Asserts} {t : Term}
    {r : SEExpr} {εnv : SymEnv} :
  checkEquivalent (m := Id) unsat? base t r εnv = .ok true →
  ∃ cr, Opt.compile r.toExpr εnv = .ok cr ∧
    unsat? (base ++ [not (eq t cr.term)]) = true
:= by
  intro h
  simp only [Opt.checkEquivalent] at h
  split at h
  next e hc =>
    (try simp only [throw, throwThe, MonadExceptOf.throw, ExceptT.mk] at h)
    cases h
  next cr hc =>
    change (Except.ok (unsat? (base ++ [not (eq t cr.term)])) : Except EvalError Bool)
      = Except.ok true at h
    injection h with h'
    exact ⟨cr, hc, h'⟩

private theorem same_results_toOption {r₁ r₂ : Spec.Result Value} {t : Term} :
  SameResults r₁ t → SameResults r₂ t → r₁.toOption = r₂.toOption
:= by
  intro h₁ h₂
  cases t <;> cases r₁ <;> cases r₂ <;> simp only [SameResults] at h₁ h₂ <;>
    simp only [Except.toOption]
  rename_i t' v₁ v₂
  simp only [SameValues] at h₁ h₂
  rw [h₁] at h₂
  injection h₂ with h₂
  rw [h₂]

/--
Soundness of `checkEquivalent`: a `true` verdict means the two expressions
evaluate the same way, up to the error kind, on every environment of `εnv`
satisfying the base asserts.
-/
theorem checkEquivalent_sound {unsat? : Asserts → Bool} {εnv : SymEnv} {base : Asserts}
    {x : Expr} {t tr : Term} {r : SEExpr} :
  UnsatSound unsat? εnv →
  εnv.WellFormedFor x →
  εnv.WellFormedFor r.toExpr →
  SymCC.compile x εnv = .ok t →
  SymCC.compile r.toExpr εnv = .ok tr →
  t.typeOf = tr.typeOf →
  checkEquivalent (m := Id) unsat? base t r εnv = .ok true →
  ∀ (env : Env) (I : Interpretation),
    I.WellFormed εnv.entities →
    env ∼ εnv.interpret I →
    env.WellFormedFor x →
    env.WellFormedFor r.toExpr →
    base.satisfiedBy I →
    (evaluate r.toExpr env.request env.entities).toOption
      = (evaluate x env.request env.entities).toOption
:= by
  intro hsound hwε hwεr hok hokr htyeq h env I hwI heq hwe hwer hsat
  obtain ⟨cr, hcr, hus⟩ := checkEquivalent_id_spec h
  have hcrt : cr.term = tr := by
    have hh := (opt_compile_ok_term hcr).symm.trans hokr
    injection hh with hh'
    try exact hh'
  rw [hcrt] at hus
  have hwt := (compile_wf hwε hok).left
  have hwtr := (compile_wf hwεr hokr).left
  have hweq := (wf_eq hwt hwtr htyeq).left
  -- the negated equality is falsified at `I`
  have hne : (not (eq t tr)).interpret I ≠ true := by
    obtain ⟨a, ha, hne⟩ := (asserts_unsatisfiable_def.mp (hsound _ hus)) I hwI
    rw [asserts_satisfiedBy_true] at hsat
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact absurd (hsat a ha) hne
    · exact ha ▸ hne
  rw [interpret_not hwI hweq, interpret_eq hwI hwt hwtr] at hne
  have hl₁ := interpret_term_wfl hwI hwt
  have hl₂ := interpret_term_wfl hwI hwtr
  have hpe := (pe_eq_lit hl₁.left.right hl₂.left.right).right
  rw [hpe] at hne
  have hbeq : (t.interpret I == tr.interpret I) = true := by
    cases hb : (t.interpret I == tr.interpret I)
    · rw [hb] at hne ; simp [pe_not_false] at hne
    · rfl
  have hteq : t.interpret I = tr.interpret I := eq_of_beq hbeq
  have hrb := compile_bisimulation hwε hwe hwI heq hok
  have hrbr := compile_bisimulation hwεr hwer hwI heq hokr
  simp only [Same.same] at hrb hrbr
  rw [← hteq] at hrbr
  exact same_results_toOption hrbr hrb

end Cedar.Thm
