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

import Cedar.SymCCOpt.SymEval

/-!
Membership lemmas for the symbolic evaluator's outcome sets
(`Cedar.SymCC.Opt.Outcomes`): how membership propagates through the
`negated`/`and`/`or`/`ite` combination rules. These carry the (S1) direction
of the soundness induction in `Cedar.Thm.SymCC.Evaluator.Soundness`.
-/

namespace Cedar.Thm

open Cedar Spec SymCC
open Cedar.SymCC.Opt

theorem outcomes_mem_all (o : EvalOutcome) :
  Outcomes.all.mem o = true
:= by cases o <;> rfl

theorem outcomes_mem_single (o : EvalOutcome) :
  (Outcomes.single o).mem o = true
:= by cases o <;> rfl

theorem outcomes_single_mem {o u : EvalOutcome} :
  (Outcomes.single o).mem u = true → u = o
:= by cases o <;> cases u <;> simp [Outcomes.single, Outcomes.mem]

theorem outcomes_lit_mem {b : Bool} {o : EvalOutcome} :
  (Outcomes.lit b).mem o = true ↔ (b = true ∧ o = .tt) ∨ (b = false ∧ o = .ff)
:= by cases b <;> cases o <;> simp [Outcomes.lit, Outcomes.mem]

theorem outcomes_negated_mem {l : Outcomes} {o : EvalOutcome} :
  l.mem o = true → l.negated.mem o.negated = true
:= by cases o <;> simp [Outcomes.mem, Outcomes.negated, EvalOutcome.negated]

theorem outcomes_and_mem_ff {l r : Outcomes} :
  l.mem .ff = true → (l.and r).mem .ff = true
:= by simp [Outcomes.mem, Outcomes.and] ; intro h ; simp [h]

theorem outcomes_and_mem_err {l r : Outcomes} :
  l.mem .err = true → (l.and r).mem .err = true
:= by simp [Outcomes.mem, Outcomes.and] ; intro h ; simp [h]

theorem outcomes_and_mem_tt {l r : Outcomes} {o : EvalOutcome} :
  l.mem .tt = true → r.mem o = true → (l.and r).mem o = true
:= by
  cases o <;> simp [Outcomes.mem, Outcomes.and] <;> intro h₁ h₂ <;> simp [h₁, h₂]

theorem outcomes_or_mem_tt {l r : Outcomes} :
  l.mem .tt = true → (l.or r).mem .tt = true
:= by simp [Outcomes.mem, Outcomes.or] ; intro h ; simp [h]

theorem outcomes_or_mem_err {l r : Outcomes} :
  l.mem .err = true → (l.or r).mem .err = true
:= by simp [Outcomes.mem, Outcomes.or] ; intro h ; simp [h]

theorem outcomes_or_mem_ff {l r : Outcomes} {o : EvalOutcome} :
  l.mem .ff = true → r.mem o = true → (l.or r).mem o = true
:= by
  cases o <;> simp [Outcomes.mem, Outcomes.or] <;> intro h₁ h₂ <;> simp [h₁, h₂]

private theorem outcomes_ite_fallback {r : Outcomes} {o : EvalOutcome} :
  r.mem o = true → (if r = Outcomes.empty then Outcomes.all else r).mem o = true
:= by
  intro h
  split
  · exact outcomes_mem_all o
  · exact h

theorem outcomes_ite_mem_err {c : Outcomes} {a b : Option Outcomes} :
  c.mem .err = true → (c.ite a b).mem .err = true
:= by
  intro h
  simp only [Outcomes.mem] at h
  simp only [Outcomes.ite]
  apply outcomes_ite_fallback
  simp only [Outcomes.mem]
  simp [h]

theorem outcomes_ite_mem_then {c oa : Outcomes} {a b : Option Outcomes} {o : EvalOutcome} :
  c.mem .tt = true → a = some oa → oa.mem o = true → (c.ite a b).mem o = true
:= by
  intro h₁ h₂ h₃
  subst h₂
  simp only [Outcomes.mem] at h₁
  simp only [Outcomes.ite]
  apply outcomes_ite_fallback
  cases o <;> simp only [Outcomes.mem] at h₃ ⊢ <;> simp [h₁, h₃]

theorem outcomes_ite_mem_else {c ob : Outcomes} {a b : Option Outcomes} {o : EvalOutcome} :
  c.mem .ff = true → b = some ob → ob.mem o = true → (c.ite a b).mem o = true
:= by
  intro h₁ h₂ h₃
  subst h₂
  simp only [Outcomes.mem] at h₁
  simp only [Outcomes.ite]
  apply outcomes_ite_fallback
  cases o <;> simp only [Outcomes.mem] at h₃ ⊢ <;> simp [h₁, h₃]

theorem outcomes_isOnlyError_mem {l : Outcomes} :
  l.isOnlyError = true → l.mem .err = true
:= by
  simp [Outcomes.isOnlyError, Outcomes.mem]
  intro h ; simp [h]

theorem outcomes_lit_true_mem {l : Outcomes} {o : EvalOutcome} :
  l.mem o = true → l = Outcomes.lit true → o = .tt
:= by
  intro h heq ; subst heq
  cases o <;> simp_all [Outcomes.lit, Outcomes.mem]

end Cedar.Thm
