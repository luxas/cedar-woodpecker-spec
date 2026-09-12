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

import Cedar.Thm.DNF.HoistSpec
import Cedar.Thm.DNF.Pruning

/-!
The main Step 2 theorems: `evaluate_splitAtoms` — splitting the atoms of
*any* expression preserves evaluation *exactly* (the same value, of any type,
or the same error), on every request and entity store, with no hypotheses —
plus the cleanliness postcondition (`splitAtoms_clean`: no atom of the output
contains any `&&`/`||`/`!`/`if` node outside an `iferror` call; the guards
`g == g` are clean because a guard is a child searched without finding an
offender) and the pipeline corollary `evaluate_dnf_splitAtoms` composing with
the Step 1 DNF theorems.
-/

namespace Cedar.DNF

open Cedar.Spec

/-- The substituted copies keep the expression's (non-offending) root. -/
theorem hoist_not_offender {e cond t f : Expr} {gs : List Expr}
  (hno : isOffender e = false) (h : hoist e = some (gs, cond, t, f)) :
  isOffender t = false ∧ isOffender f = false
:= by
  match e with
  | .lit _ => simp [hoist] at h
  | .var _ => simp [hoist] at h
  | .and _ _ => simp [isOffender] at hno
  | .or _ _ => simp [isOffender] at hno
  | .ite _ _ _ => simp [isOffender] at hno
  | .unaryApp op x =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      -- `op` cannot be `.not` (`hno`), so the rebuilt nodes are not offenders
      cases op <;> simp_all [isOffender]
    next => simp at h
  | .binaryApp op x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      simp [isOffender]
    next =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        simp [isOffender]
      next => simp at h
  | .getAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      simp [isOffender]
    next => simp at h
  | .hasAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      simp [isOffender]
    next => simp at h
  | .set xs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      simp [isOffender]
    next => simp at h
  | .record axs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      simp [isOffender]
    next => simp at h
  | .call xfn xs =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next =>
      split at h
      next gs' cond' ts fs heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        simp [isOffender]
      next => simp at h

/-! ### Soundness -/

mutual

theorem splitStructure_sound (ctx : List Expr) (e : Expr) (req : Request) (es : Entities)
  (hctx : Transparent ctx req es) :
  evaluate (splitStructure ctx e) req es = evaluate e req es
:= by
  match e with
  | .lit (.bool b) =>
    simp only [splitStructure, boolLit]
  | .and x₁ x₂ =>
    have hs : splitStructure ctx (.and x₁ x₂) =
        .and (splitStructure ctx x₁) (splitStructure (ctx ++ learnTrue x₁) x₂) := by
      simp only [splitStructure]
    rw [hs]
    have h₁ := splitStructure_sound ctx x₁ req es hctx
    cases hv : evaluate x₁ req es with
    | error e => simp [evaluate, h₁, hv, Result.as]
    | ok v =>
      match v with
      | .prim (.bool true) =>
        have h₂ := splitStructure_sound (ctx ++ learnTrue x₁) x₂ req es
          (transparent_append hctx (learnTrue_transparent hv))
        simp [evaluate, h₁, hv, h₂, Result.as, Coe.coe, Value.asBool]
      | .prim (.bool false) => simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
  | .or x₁ x₂ =>
    have hs : splitStructure ctx (.or x₁ x₂) =
        .or (splitStructure ctx x₁) (splitStructure (ctx ++ learnFalse x₁) x₂) := by
      simp only [splitStructure]
    rw [hs]
    have h₁ := splitStructure_sound ctx x₁ req es hctx
    cases hv : evaluate x₁ req es with
    | error e => simp [evaluate, h₁, hv, Result.as]
    | ok v =>
      match v with
      | .prim (.bool false) =>
        have h₂ := splitStructure_sound (ctx ++ learnFalse x₁) x₂ req es
          (transparent_append hctx (learnFalse_transparent hv))
        simp [evaluate, h₁, hv, h₂, Result.as, Coe.coe, Value.asBool]
      | .prim (.bool true) => simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
  | .unaryApp .not x =>
    have hs : splitStructure ctx (.unaryApp .not x) =
        .unaryApp .not (splitStructure ctx x) := by
      simp only [splitStructure]
    rw [hs]
    simp only [evaluate, splitStructure_sound ctx x req es hctx]
  | .ite x₁ x₂ x₃ =>
    have hs : splitStructure ctx (.ite x₁ x₂ x₃) =
        .ite (splitStructure ctx x₁) (splitStructure (ctx ++ learnTrue x₁) x₂)
          (splitStructure (ctx ++ learnFalse x₁) x₃) := by
      simp only [splitStructure]
    rw [hs]
    have h₁ := splitStructure_sound ctx x₁ req es hctx
    cases hv : evaluate x₁ req es with
    | error e => simp [evaluate, h₁, hv, Result.as]
    | ok v =>
      match v with
      | .prim (.bool true) =>
        have h₂ := splitStructure_sound (ctx ++ learnTrue x₁) x₂ req es
          (transparent_append hctx (learnTrue_transparent hv))
        simp [evaluate, h₁, hv, h₂, Result.as, Coe.coe, Value.asBool]
      | .prim (.bool false) =>
        have h₃ := splitStructure_sound (ctx ++ learnFalse x₁) x₃ req es
          (transparent_append hctx (learnFalse_transparent hv))
        simp [evaluate, h₁, hv, h₃, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
  | .lit (.int i) => rw [show splitStructure ctx (.lit (.int i)) = splitAtom ctx (.lit (.int i)) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .lit (.string s) => rw [show splitStructure ctx (.lit (.string s)) = splitAtom ctx (.lit (.string s)) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .lit (.entityUID u) => rw [show splitStructure ctx (.lit (.entityUID u)) = splitAtom ctx (.lit (.entityUID u)) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .var v => rw [show splitStructure ctx (.var v) = splitAtom ctx (.var v) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .unaryApp .neg x => rw [show splitStructure ctx (.unaryApp .neg x) = splitAtom ctx (.unaryApp .neg x) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .unaryApp .isEmpty x => rw [show splitStructure ctx (.unaryApp .isEmpty x) = splitAtom ctx (.unaryApp .isEmpty x) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .unaryApp (.like p) x => rw [show splitStructure ctx (.unaryApp (.like p) x) = splitAtom ctx (.unaryApp (.like p) x) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .unaryApp (.is ty) x => rw [show splitStructure ctx (.unaryApp (.is ty) x) = splitAtom ctx (.unaryApp (.is ty) x) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .binaryApp op x₁ x₂ => rw [show splitStructure ctx (.binaryApp op x₁ x₂) = splitAtom ctx (.binaryApp op x₁ x₂) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .getAttr x a => rw [show splitStructure ctx (.getAttr x a) = splitAtom ctx (.getAttr x a) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .hasAttr x a => rw [show splitStructure ctx (.hasAttr x a) = splitAtom ctx (.hasAttr x a) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .set xs => rw [show splitStructure ctx (.set xs) = splitAtom ctx (.set xs) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .record axs => rw [show splitStructure ctx (.record axs) = splitAtom ctx (.record axs) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
  | .call xfn xs => rw [show splitStructure ctx (.call xfn xs) = splitAtom ctx (.call xfn xs) from by simp only [splitStructure]]; exact splitAtom_sound ctx _ rfl req es hctx
termination_by (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; simp +arith; done)

theorem splitAtom_sound (ctx : List Expr) (e : Expr) (hno : isOffender e = false)
  (req : Request) (es : Entities) (hctx : Transparent ctx req es) :
  evaluate (splitAtom ctx e) req es = evaluate e req es
:= by
  rw [splitAtom.eq_1]
  split
  next hh =>
    exact foldEq_sound e req es
  next gs cond t f hh =>
    obtain ⟨hnt, hnf⟩ := hoist_not_offender hno hh
    have hc_size := (hoist_size hh).1
    have ht_size := (hoist_size hh).2.1
    have hf_size := (hoist_size hh).2.2
    -- the fresh guards reproduce the left siblings' errors (the context's
    -- are transparent); where they all evaluate, the three parts are split
    -- exactly under the extended context, and the hoist specification
    -- closes the gap
    rw [evaluate_guarded, underGuards_newGuards gs hctx, hoist_spec hno hh req es]
    rcases underGuards_cases gs req es with hid | ⟨err, herr⟩
    · have hctx' : Transparent (ctx ++ newGuards ctx gs) req es := by
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hctx g hg
        · exact ok_of_underGuards_id hid g (newGuards_subset hg)
      rw [hid, hid, evaluate_ite, splitStructure_sound _ cond req es hctx']
      -- the copies run only where the hoisted condition evaluated, so its
      -- strict subterms are transparent there
      cases hc : evaluate cond req es with
      | error err => rw [iteRes_error, iteRes_error]
      | ok v =>
        have hcopies : Transparent (ctx ++ newGuards ctx gs ++ evaluated cond []) req es :=
          transparent_append hctx' (evaluated_transparent (transparent_nil req es) hc)
        rw [splitAtom_sound _ t hnt req es hcopies, splitAtom_sound _ f hnf req es hcopies]
    · rw [herr, herr]
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; omega)

end

/-! ### Cleanliness -/

mutual

theorem hoistStep_none_offFree {c : Expr} (h : hoistStep c = none) :
  offFree c = true
:= by
  match c with
  | .ite _ _ _ => simp [hoistStep] at h
  | .and _ _ => simp [hoistStep] at h
  | .or _ _ => simp [hoistStep] at h
  | .unaryApp .not _ => simp [hoistStep] at h
  | .lit p => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .var v => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp .neg x => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp .isEmpty x => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp (.like _) x => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp (.is _) x => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .binaryApp _ _ _ => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .getAttr _ _ => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .hasAttr _ _ => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .set _ => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .record _ => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
  | .call _ _ => exact hoist_none_offFree rfl (by simpa [hoistStep] using h)
termination_by (sizeOf c, 1)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; omega)

theorem hoist_none_offFree {e : Expr} (hno : isOffender e = false)
  (h : hoist e = none) :
  offFree e = true
:= by
  match e with
  | .lit _ => simp [offFree]
  | .var _ => simp [offFree]
  | .and _ _ => simp [isOffender] at hno
  | .or _ _ => simp [isOffender] at hno
  | .ite _ _ _ => simp [isOffender] at hno
  | .unaryApp op x =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next heq =>
      simp only [offFree, Bool.and_eq_true]
      refine ⟨?_, hoistStep_none_offFree heq⟩
      cases op <;> simp_all [isOffender]
  | .binaryApp op x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next heq₁ =>
      split at h
      next => simp at h
      next heq₂ =>
        simp only [offFree, Bool.and_eq_true]
        exact ⟨hoistStep_none_offFree heq₁, hoistStep_none_offFree heq₂⟩
  | .getAttr x a =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next heq =>
      simp only [offFree]
      exact hoistStep_none_offFree heq
  | .hasAttr x a =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next heq =>
      simp only [offFree]
      exact hoistStep_none_offFree heq
  | .set xs =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next heq =>
      simp only [offFree, List.all_eq_true]
      intro px _
      obtain ⟨x, hx⟩ := px
      exact hoistList_none_offFree heq x hx
  | .record axs =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next heq =>
      simp only [offFree, List.all_eq_true]
      intro px _
      obtain ⟨⟨a, x⟩, hx⟩ := px
      exact hoistRecord_none_offFree heq (a, x) hx
  | .call xfn xs =>
    simp only [hoist] at h
    split at h
    next hif => simp [offFree, hif]
    next hne =>
      split at h
      next => simp at h
      next heq =>
        simp only [offFree, hne, decide_false, Bool.false_or, List.all_eq_true]
        intro px _
        obtain ⟨x, hx⟩ := px
        exact hoistList_none_offFree heq x hx
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith; done)

theorem hoistList_none_offFree {xs : List Expr} (h : hoistList xs = none) :
  ∀ x ∈ xs, offFree x = true
:= by
  match xs with
  | [] => intro x hx; cases hx
  | x :: rest =>
    simp only [hoistList] at h
    split at h
    next => simp at h
    next heq₁ =>
      split at h
      next => simp at h
      next heq₂ =>
        intro y hy
        cases List.mem_cons.mp hy with
        | inl he =>
          rw [he]
          exact hoistStep_none_offFree heq₁
        | inr hr => exact hoistList_none_offFree heq₂ y hr
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith; done)

theorem hoistRecord_none_offFree {axs : List (Attr × Expr)}
  (h : hoistRecord axs = none) :
  ∀ ax ∈ axs, offFree ax.2 = true
:= by
  match axs with
  | [] => intro ax hax; cases hax
  | (a, x) :: rest =>
    simp only [hoistRecord] at h
    split at h
    next => simp at h
    next heq₁ =>
      split at h
      next => simp at h
      next heq₂ =>
        intro ax hax
        cases List.mem_cons.mp hax with
        | inl he =>
          rw [he]
          exact hoistStep_none_offFree heq₁
        | inr hr => exact hoistRecord_none_offFree heq₂ ax hr
termination_by (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith; done)

end

theorem foldEq_offFree {e : Expr} (h : offFree e = true) :
  offFree (foldEq e) = true
:= by
  match e with
  | .lit p => simpa [foldEq] using h
  | .var v => simpa [foldEq] using h
  | .and _ _ => simp [offFree] at h
  | .or _ _ => simp [offFree] at h
  | .ite _ _ _ => simp [offFree] at h
  | .unaryApp op x =>
    simp only [offFree, Bool.and_eq_true] at h
    obtain ⟨hop, hx⟩ := h
    have hf := foldEq_offFree hx
    simp only [foldEq, offFree, Bool.and_eq_true]
    exact ⟨hop, hf⟩
  | .binaryApp op x₁ x₂ =>
    simp only [offFree, Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    have f₁ := foldEq_offFree h₁
    have f₂ := foldEq_offFree h₂
    have hunf : foldEq (.binaryApp op x₁ x₂) =
        (match op, foldEq x₁, foldEq x₂ with
         | .eq, .lit p₁, .lit p₂ => boolLit (p₁ == p₂)
         | op, y₁, y₂ => .binaryApp op y₁ y₂) := by
      rw [foldEq.eq_def]
      rfl
    rw [hunf]
    split
    · simp [boolLit, offFree]
    · simp only [offFree, Bool.and_eq_true]
      exact ⟨f₁, f₂⟩
  | .getAttr x a =>
    simp only [offFree] at h
    have hf := foldEq_offFree h
    simp only [foldEq, offFree]
    exact hf
  | .hasAttr x a =>
    simp only [offFree] at h
    have hf := foldEq_offFree h
    simp only [foldEq, offFree]
    exact hf
  | .set xs =>
    simp only [offFree, List.all_eq_true] at h
    simp only [foldEq, List.map₁_eq_map, offFree, List.all_eq_true]
    intro px _
    obtain ⟨y, hy⟩ := px
    obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
    subst hxy
    exact foldEq_offFree (h ⟨x, hx⟩ (List.mem_attach _ _))
  | .record axs =>
    simp only [offFree, List.all_eq_true] at h
    simp only [foldEq, List.map₂_eq_map_snd, offFree, List.all_eq_true]
    intro px _
    obtain ⟨⟨a, y⟩, hy⟩ := px
    obtain ⟨⟨a', x⟩, hx, hxy⟩ := List.mem_map.mp hy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨ha, hy'⟩ := hxy
    subst ha hy'
    exact foldEq_offFree (h ⟨(a', x), hx⟩ (List.mem_attach _ _))
  | .call xfn xs =>
    by_cases hif : xfn = .ifError
    · subst hif
      simp [foldEq, offFree]
    · simp only [offFree, hif, decide_false, Bool.false_or, List.all_eq_true] at h
      simp only [foldEq, List.map₁_eq_map, offFree, hif, decide_false, Bool.false_or,
        List.all_eq_true]
      intro px _
      obtain ⟨y, hy⟩ := px
      obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hy
      subst hxy
      exact foldEq_offFree (h ⟨x, hx⟩ (List.mem_attach _ _))
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (have := List.sizeOf_lt_of_mem hx; simp +arith; omega)
    | (have := List.sizeOf_lt_of_mem hx
       simp +arith at this
       omega))

theorem cleanAtoms_of_offFree {e : Expr} (h : offFree e = true) :
  cleanAtoms e = true
:= by
  match e with
  | .and _ _ => simp [offFree] at h
  | .or _ _ => simp [offFree] at h
  | .ite _ _ _ => simp [offFree] at h
  | .lit (.bool b) => simp [cleanAtoms]
  | .unaryApp op x =>
    cases op
    case not => simp [offFree] at h
    all_goals simpa [cleanAtoms] using h
  | .lit (.int _) => simpa [cleanAtoms] using h
  | .lit (.string _) => simpa [cleanAtoms] using h
  | .lit (.entityUID _) => simpa [cleanAtoms] using h
  | .var _ => simpa [cleanAtoms] using h
  | .binaryApp _ _ _ => simpa [cleanAtoms] using h
  | .getAttr _ _ => simpa [cleanAtoms] using h
  | .hasAttr _ _ => simpa [cleanAtoms] using h
  | .set _ => simpa [cleanAtoms] using h
  | .record _ => simpa [cleanAtoms] using h
  | .call _ _ => simpa [cleanAtoms] using h

/-! The guards a sibling contributes are offender-free when it is: its
elements, or the sibling itself. -/

mutual

theorem mem_addGuards_offFree {g x : Expr} {gs : List Expr} (hx : offFree x = true)
  (h : g ∈ addGuards x gs) : g ∈ gs ∨ offFree g = true := by
  match x with
  | .lit _ => exact .inl (by simpa [addGuards] using h)
  | .var _ => exact .inl (by simpa [addGuards] using h)
  | .set xs =>
    simp only [offFree, List.all_eq_true] at hx
    exact mem_addGuardsList_offFree (fun y hy => hx ⟨y, hy⟩ (List.mem_attach _ _))
      (by simpa [addGuards] using h)
  | .record axs =>
    simp only [offFree, List.all_eq_true] at hx
    exact mem_addGuardsRecord_offFree (fun ay hy => hx ⟨ay, hy⟩ (List.mem_attach _ _))
      (by simpa [addGuards] using h)
  | .binaryApp op a b =>
    cases op with
    | eq =>
      simp only [addGuards] at h
      simp only [offFree, Bool.and_eq_true] at hx
      rcases mem_addGuards_offFree hx.1 h with h | h
      · exact mem_addGuards_offFree hx.2 h
      · exact .inr h
    | _ =>
      simp only [addGuards] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact .inr hx
      · exact .inl h
  | .and _ _ | .or _ _ | .ite _ _ _ | .unaryApp _ _ | .getAttr _ _
  | .hasAttr _ _ | .call _ _ =>
    simp only [addGuards] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact .inr hx
    · exact .inl h
termination_by sizeOf x

theorem mem_addGuardsList_offFree {g : Expr} {xs gs : List Expr}
  (hx : ∀ x ∈ xs, offFree x = true) (h : g ∈ addGuardsList xs gs) :
  g ∈ gs ∨ offFree g = true := by
  match xs with
  | [] => exact .inl (by simpa [addGuardsList] using h)
  | x :: rest =>
    simp only [addGuardsList] at h
    rcases mem_addGuards_offFree (hx x List.mem_cons_self) h with h | h
    · exact mem_addGuardsList_offFree (fun y hy => hx y (List.mem_cons_of_mem x hy)) h
    · exact .inr h
termination_by sizeOf xs

theorem mem_addGuardsRecord_offFree {g : Expr} {axs : List (Attr × Expr)} {gs : List Expr}
  (hx : ∀ ax ∈ axs, offFree ax.2 = true) (h : g ∈ addGuardsRecord axs gs) :
  g ∈ gs ∨ offFree g = true := by
  match axs with
  | [] => exact .inl (by simpa [addGuardsRecord] using h)
  | (a, x) :: rest =>
    simp only [addGuardsRecord] at h
    rcases mem_addGuards_offFree (hx (a, x) List.mem_cons_self) h with h | h
    · exact mem_addGuardsRecord_offFree (fun ay hy => hx ay (List.mem_cons_of_mem (a, x) hy)) h
    · exact .inr h
termination_by sizeOf axs

end

/-- A guard is a child searched without finding an offender (`hoistStep`
returned `none`), folded and decomposed — hence offender-free. -/
theorem mem_addGuard {g x : Expr} {gs : List Expr} (hx : offFree x = true)
  (h : g ∈ addGuard x gs) : g ∈ gs ∨ offFree g = true :=
  mem_addGuards_offFree (foldEq_offFree hx) h

mutual

theorem hoistStep_guards_offFree {c cond t f : Expr} {gs : List Expr}
  (h : hoistStep c = some (gs, cond, t, f)) :
  ∀ g ∈ gs, offFree g = true
:= by
  match c with
  | .ite _ _ _ | .and _ _ | .or _ _ | .unaryApp .not _ =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hg, -, -, -⟩ := h
    subst hg
    simp
  | .lit p => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .var v => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp .neg x => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp .isEmpty x => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp (.like _) x => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .unaryApp (.is _) x => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .binaryApp _ _ _ => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .getAttr _ _ => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .hasAttr _ _ => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .set _ => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .record _ => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
  | .call _ _ => exact hoist_guards_offFree rfl (by simpa [hoistStep] using h)
termination_by (sizeOf c, 1)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; omega)

theorem hoist_guards_offFree {e cond t f : Expr} {gs : List Expr} (hno : isOffender e = false)
  (h : hoist e = some (gs, cond, t, f)) :
  ∀ g ∈ gs, offFree g = true
:= by
  match e with
  | .lit _ => simp [hoist] at h
  | .var _ => simp [hoist] at h
  | .and _ _ => simp [isOffender] at hno
  | .or _ _ => simp [isOffender] at hno
  | .ite _ _ _ => simp [isOffender] at hno
  | .unaryApp op x =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistStep_guards_offFree heq
    next => simp at h
  | .binaryApp op x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistStep_guards_offFree heq
    next heq₁ =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        intro g hg
        rcases mem_addGuard (hoistStep_none_offFree heq₁) hg with hg | hoff
        · exact hoistStep_guards_offFree heq g hg
        · exact hoff
      next => simp at h
  | .getAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistStep_guards_offFree heq
    next => simp at h
  | .hasAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistStep_guards_offFree heq
    next => simp at h
  | .set xs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistList_guards_offFree heq
    next => simp at h
  | .record axs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistRecord_guards_offFree heq
    next => simp at h
  | .call xfn xs =>
    simp only [hoist] at h
    split at h
    next => simp at h
    next =>
      split at h
      next gs' cond' ts fs heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        exact hoistList_guards_offFree heq
      next => simp at h
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem hoistList_guards_offFree {xs : List Expr} {cond : Expr} {ts fs gs : List Expr}
  (h : hoistList xs = some (gs, cond, ts, fs)) :
  ∀ g ∈ gs, offFree g = true
:= by
  match xs with
  | [] => simp [hoistList] at h
  | x :: rest =>
    simp only [hoistList] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistStep_guards_offFree heq
    next heq₁ =>
      split at h
      next gs' cond' ts' fs' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        intro g hg
        rcases mem_addGuard (hoistStep_none_offFree heq₁) hg with hg | hoff
        · exact hoistList_guards_offFree heq g hg
        · exact hoff
      next => simp at h
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem hoistRecord_guards_offFree {axs : List (Attr × Expr)} {cond : Expr} {gs : List Expr}
  {ts fs : List (Attr × Expr)}
  (h : hoistRecord axs = some (gs, cond, ts, fs)) :
  ∀ g ∈ gs, offFree g = true
:= by
  match axs with
  | [] => simp [hoistRecord] at h
  | (a, x) :: rest =>
    simp only [hoistRecord] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      exact hoistStep_guards_offFree heq
    next heq₁ =>
      split at h
      next gs' cond' ts' fs' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        intro g hg
        rcases mem_addGuard (hoistStep_none_offFree heq₁) hg with hg | hoff
        · exact hoistRecord_guards_offFree heq g hg
        · exact hoff
      next => simp at h
termination_by (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

end

/-- The guard chain over offender-free guards is clean. -/
theorem cleanAtoms_andChain_selfEq {gs : List Expr} (h : ∀ g ∈ gs, offFree g = true) :
  cleanAtoms (andChain (gs.map selfEq)) = true
:= by
  match gs with
  | [] => simp [andChain, boolLit, cleanAtoms]
  | [g] =>
    simp only [List.map_cons, List.map_nil, andChain, selfEq, cleanAtoms, offFree,
      Bool.and_eq_true]
    exact ⟨h g (by simp), h g (by simp)⟩
  | g :: g' :: rest =>
    have ih := cleanAtoms_andChain_selfEq (gs := g' :: rest)
      (fun x hx => h x (List.mem_cons_of_mem g hx))
    simp only [List.map_cons] at ih ⊢
    simp only [andChain, cleanAtoms, Bool.and_eq_true]
    refine ⟨?_, ih⟩
    simp only [selfEq, cleanAtoms, offFree, Bool.and_eq_true]
    exact ⟨h g (by simp), h g (by simp)⟩

/-- Guarding a clean expression by offender-free guards keeps it clean. -/
theorem cleanAtoms_guarded {gs : List Expr} {e : Expr} (hg : ∀ g ∈ gs, offFree g = true)
  (he : cleanAtoms e = true) :
  cleanAtoms (guarded gs e) = true
:= by
  match gs with
  | [] => simpa [guarded] using he
  | g :: rest =>
    simp only [guarded, cleanAtoms, Bool.and_eq_true]
    exact ⟨⟨cleanAtoms_andChain_selfEq hg, he⟩, by simp [boolLit, cleanAtoms]⟩

mutual

theorem splitStructure_clean (ctx : List Expr) (e : Expr) :
  cleanAtoms (splitStructure ctx e) = true
:= by
  match e with
  | .lit (.bool b) =>
    rw [show splitStructure ctx (.lit (.bool b)) = boolLit b from by simp only [splitStructure]]
    simp [boolLit, cleanAtoms]
  | .and x₁ x₂ =>
    rw [show splitStructure ctx (.and x₁ x₂) =
      .and (splitStructure ctx x₁) (splitStructure (ctx ++ learnTrue x₁) x₂) from by
      simp only [splitStructure]]
    simp only [cleanAtoms, Bool.and_eq_true]
    exact ⟨splitStructure_clean ctx x₁, splitStructure_clean _ x₂⟩
  | .or x₁ x₂ =>
    rw [show splitStructure ctx (.or x₁ x₂) =
      .or (splitStructure ctx x₁) (splitStructure (ctx ++ learnFalse x₁) x₂) from by
      simp only [splitStructure]]
    simp only [cleanAtoms, Bool.and_eq_true]
    exact ⟨splitStructure_clean ctx x₁, splitStructure_clean _ x₂⟩
  | .unaryApp .not x =>
    rw [show splitStructure ctx (.unaryApp .not x) =
      .unaryApp .not (splitStructure ctx x) from by simp only [splitStructure]]
    rw [show cleanAtoms (.unaryApp .not (splitStructure ctx x)) =
      cleanAtoms (splitStructure ctx x) from by simp only [cleanAtoms]]
    exact splitStructure_clean ctx x
  | .ite x₁ x₂ x₃ =>
    rw [show splitStructure ctx (.ite x₁ x₂ x₃) =
      .ite (splitStructure ctx x₁) (splitStructure (ctx ++ learnTrue x₁) x₂)
        (splitStructure (ctx ++ learnFalse x₁) x₃) from by simp only [splitStructure]]
    simp only [cleanAtoms, Bool.and_eq_true]
    exact ⟨⟨splitStructure_clean ctx x₁, splitStructure_clean _ x₂⟩, splitStructure_clean _ x₃⟩
  | .lit (.int i) => rw [show splitStructure ctx (.lit (.int i)) = splitAtom ctx (.lit (.int i)) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .lit (.string s) => rw [show splitStructure ctx (.lit (.string s)) = splitAtom ctx (.lit (.string s)) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .lit (.entityUID u) => rw [show splitStructure ctx (.lit (.entityUID u)) = splitAtom ctx (.lit (.entityUID u)) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .var v => rw [show splitStructure ctx (.var v) = splitAtom ctx (.var v) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .unaryApp .neg x => rw [show splitStructure ctx (.unaryApp .neg x) = splitAtom ctx (.unaryApp .neg x) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .unaryApp .isEmpty x => rw [show splitStructure ctx (.unaryApp .isEmpty x) = splitAtom ctx (.unaryApp .isEmpty x) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .unaryApp (.like p) x => rw [show splitStructure ctx (.unaryApp (.like p) x) = splitAtom ctx (.unaryApp (.like p) x) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .unaryApp (.is ty) x => rw [show splitStructure ctx (.unaryApp (.is ty) x) = splitAtom ctx (.unaryApp (.is ty) x) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .binaryApp op x₁ x₂ => rw [show splitStructure ctx (.binaryApp op x₁ x₂) = splitAtom ctx (.binaryApp op x₁ x₂) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .getAttr x a => rw [show splitStructure ctx (.getAttr x a) = splitAtom ctx (.getAttr x a) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .hasAttr x a => rw [show splitStructure ctx (.hasAttr x a) = splitAtom ctx (.hasAttr x a) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .set xs => rw [show splitStructure ctx (.set xs) = splitAtom ctx (.set xs) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .record axs => rw [show splitStructure ctx (.record axs) = splitAtom ctx (.record axs) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
  | .call xfn xs => rw [show splitStructure ctx (.call xfn xs) = splitAtom ctx (.call xfn xs) from by simp only [splitStructure]]; exact splitAtom_clean ctx _ rfl
termination_by (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; simp +arith; done)

theorem splitAtom_clean (ctx : List Expr) (e : Expr) (hno : isOffender e = false) :
  cleanAtoms (splitAtom ctx e) = true
:= by
  rw [splitAtom.eq_1]
  split
  next hh =>
    exact cleanAtoms_of_offFree (foldEq_offFree (hoist_none_offFree hno hh))
  next gs cond t f hh =>
    obtain ⟨hnt, hnf⟩ := hoist_not_offender hno hh
    have hc_size := (hoist_size hh).1
    have ht_size := (hoist_size hh).2.1
    have hf_size := (hoist_size hh).2.2
    apply cleanAtoms_guarded (fun g hg => hoist_guards_offFree hno hh g (newGuards_subset hg))
    simp only [cleanAtoms, Bool.and_eq_true]
    exact ⟨⟨splitStructure_clean _ cond, splitAtom_clean _ t hnt⟩, splitAtom_clean _ f hnf⟩
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; omega)

end

/-- **Cleanliness**: after splitting, no atom contains any `&&`/`||`/`!`/`if`
node outside an opaque `iferror` call. -/
theorem splitAtoms_clean (e : Expr) : cleanAtoms (splitAtoms e) = true
:= splitStructure_clean [] e

/-- **Equivalence**: splitting the atoms preserves evaluation exactly — the
same value (of any type) or the same error — for every expression, request
and entity store, with no hypotheses. -/
theorem evaluate_splitAtoms (e : Expr) (req : Request) (es : Entities) :
  evaluate (splitAtoms e) req es = evaluate e req es
:= splitStructure_sound [] e req es (fun _ hg => absurd hg (List.not_mem_nil))

/-- **The pipeline**: the DNF of the split expression evaluates like the
original — same boolean value or both err — under the Step 1 hypotheses for
the *split* expression. -/
theorem evaluate_dnf_splitAtoms {e : Expr} {canError : Expr → Bool}
  {req : Request} {es : Entities}
  (hbool : ∀ a ∈ atoms (splitAtoms e), ∀ v, evaluate a req es = .ok v →
    ∃ b, v = .prim (.bool b))
  (herr : ∀ a ∈ atoms (splitAtoms e), canError a = false →
    ∀ err, evaluate a req es ≠ .error err) :
  (∃ b, evaluate (dnf (splitAtoms e) canError) req es = .ok (.prim (.bool b)) ∧
        evaluate e req es = .ok (.prim (.bool b))) ∨
  ((∃ err, evaluate (dnf (splitAtoms e) canError) req es = .error err) ∧
   (∃ err, evaluate e req es = .error err))
:= by
  rw [← evaluate_splitAtoms e req es]
  exact evaluate_dnf hbool herr

end Cedar.DNF
