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

import Cedar.Thm.DNF.ElimRules

/-!
The evaluation order of a term, as `Cedar.DNF.evalList` lists it: guards that
are a prefix of that order are redundant in front of the term
(`underGuards_evalList_prefix`), which is what lets the elimination drop them
(`dropRepeated`, `underGuards_dropRepeated`).
-/

namespace Cedar.DNF

open Cedar.Spec

/-! ### List prefixes -/

theorem prefix_append_cases {α} {P A B : List α} (h : P <+: A ++ B) :
  P <+: A ∨ ∃ P', P = A ++ P' ∧ P' <+: B := by
  obtain ⟨t, ht⟩ := h
  rcases List.append_eq_append_iff.mp ht with ⟨a', hA, _⟩ | ⟨c', hP, hB⟩
  · exact .inl ⟨a', hA.symm⟩
  · exact .inr ⟨c', hP, ⟨t, hB.symm⟩⟩

theorem prefix_singleton_cases {α} {P : List α} {x : α} (h : P <+: [x]) :
  P = [] ∨ P = [x] := by
  obtain ⟨t, ht⟩ := h
  cases P with
  | nil => exact .inl rfl
  | cons p ps =>
    simp only [List.cons_append, List.cons.injEq] at ht
    obtain ⟨rfl, hps⟩ := ht
    rcases List.append_eq_nil_iff.mp hps with ⟨rfl, _⟩
    exact .inr rfl

/-! ### Guards that err exactly as a child does commute with the node -/

theorem underGuards_of_child {α : Type} {P : List Expr} {req : Request} {es : Entities}
  {c : Result Value} {n : Result α}
  (hc : underGuards P req es c = c) (hprop : ∀ err, c = .error err → n = .error err) :
  underGuards P req es n = n := by
  rcases underGuards_cases P req es with hid | ⟨err, herr⟩
  · exact hid n
  · rw [herr] at hc ⊢
    exact (hprop err hc.symm).symm

theorem bindAttr_pure {α} (a : Attr) (v : α) :
  bindAttr a (pure v : Result α) = pure (a, v) := rfl

theorem transparent_append_left {gs₁ gs₂ : List Expr} {req : Request} {es : Entities}
  (h : Transparent (gs₁ ++ gs₂) req es) : Transparent gs₁ req es :=
  fun g hg => h g (List.mem_append_left _ hg)

theorem transparent_append_right {gs₁ gs₂ : List Expr} {req : Request} {es : Entities}
  (h : Transparent (gs₁ ++ gs₂) req es) : Transparent gs₂ req es :=
  fun g hg => h g (List.mem_append_right _ hg)

/-! ### A complete, transparent list means the term evaluates -/

mutual

theorem transparent_evalList_ok (e : Expr) (req : Request) (es : Entities)
  (hc : (evalList e).2 = true) (ht : Transparent (evalList e).1 req es) :
  ∃ v, evaluate e req es = .ok v := by
  match e with
  | .lit p => exact ⟨.prim p, by simp [evaluate]⟩
  | .var .principal => exact ⟨req.principal, by simp [evaluate]⟩
  | .var .action => exact ⟨req.action, by simp [evaluate]⟩
  | .var .resource => exact ⟨req.resource, by simp [evaluate]⟩
  | .var .context => exact ⟨req.context, by simp [evaluate]⟩
  | .ite _ _ _ => simp [evalList] at hc
  | .and _ _ => simp [evalList] at hc
  | .or _ _ => simp [evalList] at hc
  | .binaryApp op a b =>
    cases op
    case eq =>
      simp only [evalList] at hc ht
      by_cases ha : (evalList a).2 = true
      · rw [if_pos ha] at hc ht
        simp only at hc ht
        obtain ⟨va, hva⟩ := transparent_evalList_ok a req es ha (transparent_append_left ht)
        obtain ⟨vb, hvb⟩ := transparent_evalList_ok b req es hc (transparent_append_right ht)
        exact ⟨.prim (.bool (va == vb)), by simp [evaluate, hva, hvb, Bind.bind, Except.bind, apply₂]⟩
      · rw [if_neg ha] at hc
        simp at hc
    all_goals exact ht _ (by simp [evalList])
  | .set xs =>
    simp only [evalList] at hc ht
    obtain ⟨vs, hvs⟩ := transparent_evalListList_ok xs req es hc ht
    exact ⟨_, evaluate_set_of_mapM hvs⟩
  | .record axs =>
    simp only [evalList] at hc ht
    obtain ⟨avs, havs⟩ := transparent_evalListRecord_ok axs req es hc ht
    exact ⟨.record (Data.Map.make avs), by
      simp [evaluate,
        List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)),
        havs, Bind.bind, Except.bind]⟩
  | .unaryApp _ _ | .getAttr _ _ | .hasAttr _ _ | .call _ _ =>
    exact ht _ (by simp [evalList])
termination_by sizeOf e

theorem transparent_evalListList_ok (xs : List Expr) (req : Request) (es : Entities)
  (hc : (evalListList xs).2 = true) (ht : Transparent (evalListList xs).1 req es) :
  ∃ vs, xs.mapM (fun x => evaluate x req es) = .ok vs := by
  match xs with
  | [] => exact ⟨[], rfl⟩
  | x :: rest =>
    simp only [evalListList] at hc ht
    by_cases hx : (evalList x).2 = true
    · rw [if_pos hx] at hc ht
      simp only at hc ht
      obtain ⟨v, hv⟩ := transparent_evalList_ok x req es hx (transparent_append_left ht)
      obtain ⟨vs, hvs⟩ := transparent_evalListList_ok rest req es hc (transparent_append_right ht)
      exact ⟨v :: vs, by simp [List.mapM_cons, hv, hvs, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
    · rw [if_neg hx] at hc
      simp at hc
termination_by sizeOf xs

theorem transparent_evalListRecord_ok (axs : List (Attr × Expr)) (req : Request) (es : Entities)
  (hc : (evalListRecord axs).2 = true) (ht : Transparent (evalListRecord axs).1 req es) :
  ∃ avs, axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs := by
  match axs with
  | [] => exact ⟨[], rfl⟩
  | (a, x) :: rest =>
    simp only [evalListRecord] at hc ht
    by_cases hx : (evalList x).2 = true
    · rw [if_pos hx] at hc ht
      simp only at hc ht
      obtain ⟨v, hv⟩ := transparent_evalList_ok x req es hx (transparent_append_left ht)
      obtain ⟨avs, havs⟩ :=
        transparent_evalListRecord_ok rest req es hc (transparent_append_right ht)
      exact ⟨(a, v) :: avs, by
        simp [List.mapM_cons, hv, havs, bindAttr_ok, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩
    · rw [if_neg hx] at hc
      simp at hc
termination_by sizeOf axs

end

/-! ### A prefix of the evaluation order is redundant in front of the term -/

mutual

theorem underGuards_evalList_prefix (t : Expr) (P : List Expr) (req : Request) (es : Entities)
  (hP : P <+: (evalList t).1) :
  underGuards P req es (evaluate t req es) = evaluate t req es := by
  match t with
  | .lit _ =>
    simp only [evalList] at hP
    rw [List.prefix_nil.mp hP]
    rfl
  | .var _ =>
    simp only [evalList] at hP
    rw [List.prefix_nil.mp hP]
    rfl
  | .ite c _ _ =>
    simp only [evalList] at hP
    exact underGuards_of_child (underGuards_evalList_prefix c P req es hP)
      (fun err hc => by simp [evaluate, hc, Result.as])
  | .and l _ =>
    simp only [evalList] at hP
    exact underGuards_of_child (underGuards_evalList_prefix l P req es hP)
      (fun err hl => by simp [evaluate, hl, Result.as])
  | .or l _ =>
    simp only [evalList] at hP
    exact underGuards_of_child (underGuards_evalList_prefix l P req es hP)
      (fun err hl => by simp [evaluate, hl, Result.as])
  | .binaryApp op a b =>
    cases op
    case eq =>
      simp only [evalList] at hP
      by_cases ha : (evalList a).2 = true
      · rw [if_pos ha] at hP
        simp only at hP
        rcases prefix_append_cases hP with hPa | ⟨P', rfl, hP'⟩
        · exact underGuards_of_child (underGuards_evalList_prefix a P req es hPa)
            (fun err hc => by simp [evaluate, hc, Bind.bind, Except.bind])
        · rw [underGuards_append]
          rcases underGuards_cases (evalList a).1 req es with hid | ⟨err, herr⟩
          · obtain ⟨va, hva⟩ := transparent_evalList_ok a req es ha (ok_of_underGuards_id hid)
            rw [hid]
            have hva' : evaluate a req es = pure va := hva
            simp only [evaluate, hva', pure_bind]
            rw [← underGuards_bind, underGuards_evalList_prefix b P' req es hP']
          · have h₁ := underGuards_evalList_prefix a (evalList a).1 req es (List.prefix_refl _)
            rw [herr] at h₁ ⊢
            simp [evaluate, ← h₁, Bind.bind, Except.bind]
      · rw [if_neg ha] at hP
        simp only at hP
        exact underGuards_of_child (underGuards_evalList_prefix a P req es hP)
          (fun err hc => by simp [evaluate, hc, Bind.bind, Except.bind])
    all_goals
      simp only [evalList] at hP
      rcases prefix_singleton_cases hP with rfl | rfl
      · rfl
      · exact underGuards_self _ _ _
  | .set xs =>
    simp only [evalList] at hP
    have h := underGuards_evalListList_prefix xs P req es hP
    simp only [evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es)]
    rw [← underGuards_bind, h]
  | .record axs =>
    simp only [evalList] at hP
    have h := underGuards_evalListRecord_prefix axs P req es hP
    simp only [evaluate,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es))]
    rw [← underGuards_bind, h]
  | .unaryApp _ _ | .getAttr _ _ | .hasAttr _ _ | .call _ _ =>
    simp only [evalList] at hP
    rcases prefix_singleton_cases hP with rfl | rfl
    · rfl
    · exact underGuards_self _ _ _
termination_by sizeOf t

theorem underGuards_evalListList_prefix (xs : List Expr) (P : List Expr) (req : Request)
  (es : Entities) (hP : P <+: (evalListList xs).1) :
  underGuards P req es (xs.mapM (fun x => evaluate x req es)) =
    xs.mapM (fun x => evaluate x req es) := by
  match xs with
  | [] =>
    simp only [evalListList] at hP
    rw [List.prefix_nil.mp hP]
    rfl
  | x :: rest =>
    simp only [evalListList] at hP
    by_cases hx : (evalList x).2 = true
    · rw [if_pos hx] at hP
      simp only at hP
      rcases prefix_append_cases hP with hPx | ⟨P', rfl, hP'⟩
      · exact underGuards_of_child (underGuards_evalList_prefix x P req es hPx)
          (fun err hc => by simp [List.mapM_cons, hc, Bind.bind, Except.bind])
      · rw [underGuards_append]
        rcases underGuards_cases (evalList x).1 req es with hid | ⟨err, herr⟩
        · obtain ⟨v, hv⟩ := transparent_evalList_ok x req es hx (ok_of_underGuards_id hid)
          rw [hid]
          have hv' : evaluate x req es = pure v := hv
          simp only [List.mapM_cons, hv', pure_bind]
          rw [← underGuards_bind, underGuards_evalListList_prefix rest P' req es hP']
        · have h₁ := underGuards_evalList_prefix x (evalList x).1 req es (List.prefix_refl _)
          rw [herr] at h₁ ⊢
          simp [List.mapM_cons, ← h₁, Bind.bind, Except.bind]
    · rw [if_neg hx] at hP
      simp only at hP
      exact underGuards_of_child (underGuards_evalList_prefix x P req es hP)
        (fun err hc => by simp [List.mapM_cons, hc, Bind.bind, Except.bind])
termination_by sizeOf xs

theorem underGuards_evalListRecord_prefix (axs : List (Attr × Expr)) (P : List Expr)
  (req : Request) (es : Entities) (hP : P <+: (evalListRecord axs).1) :
  underGuards P req es (axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es))) =
    axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) := by
  match axs with
  | [] =>
    simp only [evalListRecord] at hP
    rw [List.prefix_nil.mp hP]
    rfl
  | (a, x) :: rest =>
    simp only [evalListRecord] at hP
    by_cases hx : (evalList x).2 = true
    · rw [if_pos hx] at hP
      simp only at hP
      rcases prefix_append_cases hP with hPx | ⟨P', rfl, hP'⟩
      · exact underGuards_of_child (underGuards_evalList_prefix x P req es hPx)
          (fun err hc => by simp [List.mapM_cons, hc, bindAttr_error, Bind.bind, Except.bind])
      · rw [underGuards_append]
        rcases underGuards_cases (evalList x).1 req es with hid | ⟨err, herr⟩
        · obtain ⟨v, hv⟩ := transparent_evalList_ok x req es hx (ok_of_underGuards_id hid)
          rw [hid]
          have hv' : evaluate x req es = pure v := hv
          simp only [List.mapM_cons, hv', bindAttr_pure, pure_bind]
          rw [← underGuards_bind, underGuards_evalListRecord_prefix rest P' req es hP']
        · have h₁ := underGuards_evalList_prefix x (evalList x).1 req es (List.prefix_refl _)
          rw [herr] at h₁ ⊢
          simp [List.mapM_cons, ← h₁, bindAttr_error, Bind.bind, Except.bind]
    · rw [if_neg hx] at hP
      simp only at hP
      exact underGuards_of_child (underGuards_evalList_prefix x P req es hP)
        (fun err hc => by simp [List.mapM_cons, hc, bindAttr_error, Bind.bind, Except.bind])
termination_by sizeOf axs

end

/-! ### Dropping the guards the term evaluates first -/

/-- The dropped guards were a prefix of the term's own evaluation order, so the
term under them evaluates as on its own. -/
theorem underGuards_dropRepeated (gs : List Expr) (t : Expr) (req : Request) (es : Entities) :
  underGuards (dropRepeated gs t) req es (evaluate t req es) =
    underGuards gs req es (evaluate t req es) := by
  simp only [dropRepeated]
  split
  next keep hfind =>
    have hp : (gs.drop keep).isPrefixOf (evalList t).1 = true := by
      have := List.find?_some hfind
      simpa using this
    have hpre : gs.drop keep <+: (evalList t).1 := List.isPrefixOf_iff_prefix.mp hp
    have hsplit : underGuards gs req es (evaluate t req es) =
        underGuards (gs.take keep ++ gs.drop keep) req es (evaluate t req es) := by
      rw [List.take_append_drop]
    rw [hsplit, underGuards_append, underGuards_evalList_prefix t _ req es hpre]
  next => rfl

end Cedar.DNF
