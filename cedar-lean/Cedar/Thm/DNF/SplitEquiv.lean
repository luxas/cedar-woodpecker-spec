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

import Cedar.DNF.Split
import Cedar.Thm.DNF.Equivalence
import Cedar.Thm.Data

/-!
The exact algebra of the splitter theorems. Splitting preserves evaluation on
the nose — the same value or the same error — so the theorems are equalities
of `Result Value`s; this file has what they are phrased over:

* `iteRes` — the evaluation of an `if` over already-evaluated parts, and how
  a bind pushes into its branches;
* `underGuards` — "`r`, once every guard has evaluated; otherwise the first
  guard's error", the meaning of the guards `g == g` that `guarded` places
  in front of a hoisted `if`, with `evaluate_guarded`;
* `foldEq_sound` — folding `lit == lit` preserves evaluation on the nose,
  because `apply₂ .eq` is total value equality (which is also why `g == g`
  is `true` whenever `g` evaluates: `evaluate_selfEq`).
-/

namespace Cedar.DNF

open Cedar.Spec

/-- A result that can only be a boolean or an error. -/
def Boolish (r : Result Value) : Prop :=
  ∀ v, r = .ok v → ∃ b, v = .prim (.bool b)

theorem bindAttr_ok {α} (a : Attr) (v : α) :
  bindAttr a (Except.ok v : Result α) = .ok (a, v) := rfl

theorem bindAttr_error {α} (a : Attr) (err : Error) :
  bindAttr a (Except.error err : Result α) = .error err := rfl

/-! ### `ite` evaluation -/

/-- The evaluation of an `if` over its already-evaluated test and branches:
the branch selected by the test's boolean, the test's error, or a type error
for a non-boolean test. -/
def iteRes {α} (rc : Result Value) (r₁ r₂ : Result α) : Result α := do
  let b ← rc.as Bool
  if b then r₁ else r₂

theorem evaluate_ite (c t e : Expr) (req : Request) (es : Entities) :
  evaluate (.ite c t e) req es = iteRes (evaluate c req es) (evaluate t req es) (evaluate e req es)
:= by
  simp only [evaluate, iteRes]

theorem iteRes_ok_true {α} (r₁ r₂ : Result α) :
  iteRes (.ok (.prim (.bool true))) r₁ r₂ = r₁ := by
  simp [iteRes, Result.as, Coe.coe, Value.asBool]

theorem iteRes_error {α} (err : Error) (r₁ r₂ : Result α) :
  iteRes (.error err) r₁ r₂ = .error err := by
  simp [iteRes, Result.as, Bind.bind, Except.bind]

/-- A bind pushes into both branches. -/
theorem iteRes_bind {α β} (rc : Result Value) (r₁ r₂ : Result α) (k : α → Result β) :
  iteRes rc r₁ r₂ >>= k = iteRes rc (r₁ >>= k) (r₂ >>= k) := by
  simp only [iteRes]
  cases h : Result.as Bool rc with
  | error err => simp [Bind.bind, Except.bind]
  | ok b => cases b <;> simp [Bind.bind, Except.bind]

/-! ### Guards -/

/-- `r` once every guard evaluates, otherwise the first guard's error: what
the guards of a hoisted node contribute to its evaluation. -/
def underGuards {α} (gs : List Expr) (req : Request) (es : Entities) (r : Result α) : Result α :=
  match gs with
  | [] => r
  | g :: rest =>
    match evaluate g req es with
    | .ok _ => underGuards rest req es r
    | .error err => .error err

theorem underGuards_nil {α} (req : Request) (es : Entities) (r : Result α) :
  underGuards [] req es r = r := rfl

theorem underGuards_cons {α} (g : Expr) (gs : List Expr) (req : Request) (es : Entities)
  (r : Result α) :
  underGuards (g :: gs) req es r =
    match evaluate g req es with
    | .ok _ => underGuards gs req es r
    | .error err => .error err := rfl

/-- The guards are the identity or a constant error, whatever they guard. -/
theorem underGuards_cases (gs : List Expr) (req : Request) (es : Entities) :
  (∀ {α : Type} (r : Result α), underGuards gs req es r = r) ∨
  (∃ err, ∀ {α : Type} (r : Result α), underGuards gs req es r = .error err) := by
  induction gs with
  | nil => exact .inl (fun _ => rfl)
  | cons g rest ih =>
    cases hg : evaluate g req es with
    | error err => exact .inr ⟨err, fun r => by simp [underGuards, hg]⟩
    | ok v =>
      rcases ih with ih | ⟨err, ih⟩
      · exact .inl (fun r => by simp [underGuards, hg, ih])
      · exact .inr ⟨err, fun r => by simp [underGuards, hg, ih]⟩

/-- A bind pushes under the guards. -/
theorem underGuards_bind {α β} (gs : List Expr) (req : Request) (es : Entities)
  (r : Result α) (k : α → Result β) :
  underGuards gs req es r >>= k = underGuards gs req es (r >>= k) := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    simp only [underGuards]
    split
    · exact ih
    · simp [Bind.bind, Except.bind]

/-! ### Contexts: guards already established -/

/-- A transparent context: guards that all evaluate without error. -/
def Transparent (ctx : List Expr) (req : Request) (es : Entities) : Prop :=
  ∀ g ∈ ctx, ∃ v, evaluate g req es = .ok v

theorem transparent_append {ctx₁ ctx₂ : List Expr} {req : Request} {es : Entities}
  (h₁ : Transparent ctx₁ req es) (h₂ : Transparent ctx₂ req es) :
  Transparent (ctx₁ ++ ctx₂) req es := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact h₁ g hg
  · exact h₂ g hg

/-- Every guard of `newGuards ctx gs` is one of `gs`. -/
theorem newGuards_subset {ctx gs : List Expr} {g : Expr} (h : g ∈ newGuards ctx gs) : g ∈ gs := by
  induction gs generalizing ctx with
  | nil => simp [newGuards] at h
  | cons x rest ih =>
    simp only [newGuards] at h
    split at h
    · exact List.mem_cons_of_mem x (ih h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (ih h)

/-- Guards that all evaluate are transparent. -/
theorem underGuards_eq_of_ok {α} {gs : List Expr} {req : Request} {es : Entities}
  (h : Transparent gs req es) (r : Result α) :
  underGuards gs req es r = r := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    obtain ⟨v, hv⟩ := h g List.mem_cons_self
    simp only [underGuards, hv]
    exact ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))

theorem underGuards_append {α} (gs₁ gs₂ : List Expr) (req : Request) (es : Entities)
  (r : Result α) :
  underGuards (gs₁ ++ gs₂) req es r = underGuards gs₁ req es (underGuards gs₂ req es r) := by
  induction gs₁ with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.cons_append, underGuards]
    split <;> simp [ih]

/-- A term as its own guard changes nothing. -/
theorem underGuards_self (x : Expr) (req : Request) (es : Entities) :
  underGuards [x] req es (evaluate x req es) = evaluate x req es := by
  simp only [underGuards]
  split <;> simp_all

/-- Transparent guards all evaluate. -/
theorem ok_of_underGuards_id {gs : List Expr} {req : Request} {es : Entities}
  (h : ∀ {α : Type} (r : Result α), underGuards gs req es r = r) :
  ∀ g ∈ gs, ∃ v, evaluate g req es = .ok v := by
  induction gs with
  | nil => intro g hg; cases hg
  | cons g rest ih =>
    have hg : ∃ v, evaluate g req es = .ok v := by
      cases hg : evaluate g req es with
      | ok v => exact ⟨v, rfl⟩
      | error err =>
        have := h (Except.ok () : Result Unit)
        simp [underGuards, hg] at this
    obtain ⟨v, hv⟩ := hg
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact ⟨v, hv⟩
    · exact ih (fun r => by have := h r; simpa [underGuards, hv] using this) g' hg'

/-- Guards of a later sibling move out past an earlier child's bind, once
that child is known to evaluate whenever its own guards do. -/
theorem underGuards_bind_swap {α β : Type} {gs₁ gs₂ : List Expr} {req : Request} {es : Entities}
  {r : Result α} (hr : Transparent gs₁ req es → ∃ v, r = .ok v) (k : α → Result β) :
  underGuards gs₁ req es (r >>= fun v => underGuards gs₂ req es (k v)) =
    underGuards gs₁ req es (underGuards gs₂ req es (r >>= k)) := by
  rcases underGuards_cases gs₁ req es with hid | ⟨err, herr⟩
  · obtain ⟨v, hv⟩ := hr (ok_of_underGuards_id hid)
    rw [hid, hid, hv]
    simp [Bind.bind, Except.bind]
  · rw [herr, herr]

/-- Dropping the guards a transparent context already establishes (and the
repetitions) does not change the meaning of the guards. -/
theorem underGuards_newGuards {α} {ctx : List Expr} (gs : List Expr) {req : Request} {es : Entities}
  (hctx : ∀ g ∈ ctx, ∃ v, evaluate g req es = .ok v) (r : Result α) :
  underGuards (newGuards ctx gs) req es r = underGuards gs req es r := by
  induction gs generalizing ctx with
  | nil => rfl
  | cons g rest ih =>
    simp only [newGuards]
    split
    next hmem =>
      obtain ⟨v, hv⟩ := hctx g hmem
      rw [ih hctx, underGuards_cons, hv]
    next =>
      rw [underGuards_cons, underGuards_cons]
      cases hg : evaluate g req es with
      | error err => rfl
      | ok v =>
        exact ih (fun g' hg' => by
          rcases List.mem_cons.mp hg' with rfl | hg'
          · exact ⟨v, hg⟩
          · exact hctx g' hg')

/-- `g == g` is `true` whenever `g` evaluates (`apply₂ .eq` is total,
reflexive value equality) and `g`'s own error otherwise. -/
theorem evaluate_selfEq (g : Expr) (req : Request) (es : Entities) :
  evaluate (selfEq g) req es =
    match evaluate g req es with
    | .ok _ => .ok (.prim (.bool true))
    | .error err => .error err := by
  simp only [selfEq, evaluate]
  cases evaluate g req es with
  | error err => simp [Bind.bind, Except.bind]
  | ok v => simp [Bind.bind, Except.bind, apply₂]

/-- The guard chain is `true` once every guard evaluates, otherwise the first
guard's error. -/
theorem evaluate_andChain_selfEq (gs : List Expr) (req : Request) (es : Entities) :
  evaluate (andChain (gs.map selfEq)) req es =
    underGuards gs req es (.ok (.prim (.bool true))) := by
  match gs with
  | [] => simp [andChain, boolLit, evaluate, underGuards]
  | [g] =>
    simp only [List.map_cons, List.map_nil, andChain, evaluate_selfEq, underGuards]
  | g :: g' :: rest =>
    have ih := evaluate_andChain_selfEq (g' :: rest) req es
    rw [underGuards_cons]
    simp only [List.map_cons, andChain, evaluate, evaluate_selfEq]
    cases evaluate g req es with
    | error err => simp [Result.as, Bind.bind, Except.bind]
    | ok v =>
      simp only [List.map_cons] at ih
      simp only [Result.as, Coe.coe, Value.asBool, Bind.bind, Except.bind, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      rcases underGuards_cases (g' :: rest) req es with h | ⟨err, h⟩
      · simp [h, Pure.pure, Except.pure]
      · simp [h]

/-- The guarded expression evaluates like the expression once every guard
evaluates, and to the first guard's error otherwise. -/
theorem evaluate_guarded (gs : List Expr) (e : Expr) (req : Request) (es : Entities) :
  evaluate (guarded gs e) req es = underGuards gs req es (evaluate e req es) := by
  match gs with
  | [] => rfl
  | g :: rest =>
    simp only [guarded, evaluate_ite, evaluate_andChain_selfEq]
    rcases underGuards_cases (g :: rest) req es with h | ⟨err, h⟩
    · rw [h, h, iteRes_ok_true]
    · rw [h, h, iteRes_error]

/-! ### The literal-equality fold is exact -/

theorem value_prim_beq (p₁ p₂ : Prim) :
  (Value.prim p₁ == Value.prim p₂) = (p₁ == p₂) := by
  cases h : p₁ == p₂
  · simp only [beq_eq_false_iff_ne] at h
    simp [beq_eq_false_iff_ne, h]
  · simp only [beq_iff_eq] at h
    simp [h]

mutual

theorem foldEq_sound (e : Expr) (req : Request) (es : Entities) :
  evaluate (foldEq e) req es = evaluate e req es := by
  match e with
  | .lit p => simp only [foldEq]
  | .var v => simp only [foldEq]
  | .ite x₁ x₂ x₃ =>
    have ih₁ := foldEq_sound x₁ req es
    have ih₂ := foldEq_sound x₂ req es
    have ih₃ := foldEq_sound x₃ req es
    simp only [foldEq, evaluate, ih₁, ih₂, ih₃]
  | .and x₁ x₂ =>
    have ih₁ := foldEq_sound x₁ req es
    have ih₂ := foldEq_sound x₂ req es
    simp only [foldEq, evaluate, ih₁, ih₂]
  | .or x₁ x₂ =>
    have ih₁ := foldEq_sound x₁ req es
    have ih₂ := foldEq_sound x₂ req es
    simp only [foldEq, evaluate, ih₁, ih₂]
  | .unaryApp op x =>
    have ih := foldEq_sound x req es
    simp only [foldEq, evaluate, ih]
  | .binaryApp op x₁ x₂ =>
    have ih₁ := foldEq_sound x₁ req es
    have ih₂ := foldEq_sound x₂ req es
    have hunf : foldEq (.binaryApp op x₁ x₂) =
        (match op, foldEq x₁, foldEq x₂ with
         | .eq, .lit p₁, .lit p₂ => boolLit (p₁ == p₂)
         | op, y₁, y₂ => .binaryApp op y₁ y₂) := by
      rw [foldEq.eq_def]
      rfl
    rw [hunf]
    split
    next p₁ p₂ h₁ h₂ =>
      have e₁ : evaluate x₁ req es = .ok (.prim p₁) := by
        rw [← ih₁, h₁]
        simp [evaluate]
      have e₂ : evaluate x₂ req es = .ok (.prim p₂) := by
        rw [← ih₂, h₂]
        simp [evaluate]
      simp [evaluate, e₁, e₂, apply₂, boolLit, value_prim_beq]
    next =>
      simp only [evaluate, ih₁, ih₂]
  | .getAttr x a =>
    have ih := foldEq_sound x req es
    simp only [foldEq, evaluate, ih]
  | .hasAttr x a =>
    have ih := foldEq_sound x req es
    simp only [foldEq, evaluate, ih]
  | .set xs =>
    have ih := foldEq_sound_list xs req es
    simp only [foldEq, evaluate, List.map₁_eq_map,
      List.mapM₁_eq_mapM (fun x => evaluate x req es), List.mapM_map,
      Function.comp_def, ih]
  | .record axs =>
    have ih := foldEq_sound_record axs req es
    simp only [foldEq, evaluate, List.map₂_eq_map_snd,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)),
      List.mapM_map, Function.comp_def, ih]
  | .call xfn xs =>
    by_cases hif : xfn = .ifError ∧ ∃ x₁ x₂, xs = [x₁, x₂]
    · -- `iferror`: lazy, but folding each argument is exact
      obtain ⟨hxfn, x₁, x₂, hxs⟩ := hif
      subst hxfn hxs
      have ih₁ := foldEq_sound x₁ req es
      have ih₂ := foldEq_sound x₂ req es
      simp only [foldEq, List.map₁_eq_map, List.map_cons, List.map_nil, evaluate, ih₁, ih₂]
    · have ih := foldEq_sound_list xs req es
      have hshape : ∀ y₁ y₂, xs.map foldEq = [y₁, y₂] → ∃ a b, xs = [a, b] := by
        intro y₁ y₂ h
        match xs, h with
        | [a, b], _ => exact ⟨a, b, rfl⟩
        | [], h => simp at h
        | [_], h => simp at h
        | _ :: _ :: _ :: _, h => simp at h
      simp only [foldEq, List.map₁_eq_map]
      rw [evaluate.eq_16 _ _ _ _ (fun y₁ y₂ h₁ h₂ => by
            obtain ⟨a, b, hab⟩ := hshape y₁ y₂ h₂
            exact hif ⟨h₁, a, b, hab⟩),
          evaluate.eq_16 _ _ _ _ (fun y₁ y₂ h₁ h₂ => hif ⟨h₁, y₁, y₂, h₂⟩)]
      simp only [List.mapM₁_eq_mapM (fun x => evaluate x req es), List.mapM_map,
        Function.comp_def, ih]
termination_by (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; simp +arith; done)
    | (apply Prod.Lex.left; subst_vars; simp +arith; done)

theorem foldEq_sound_list (xs : List Expr) (req : Request) (es : Entities) :
  xs.mapM (fun x => evaluate (foldEq x) req es) =
    xs.mapM (fun x => evaluate x req es) := by
  match xs with
  | [] => rfl
  | x :: rest =>
    have hx := foldEq_sound x req es
    have hrest := foldEq_sound_list rest req es
    simp only [List.mapM_cons, hx, hrest]
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem foldEq_sound_record (axs : List (Attr × Expr)) (req : Request) (es : Entities) :
  axs.mapM (fun ax => bindAttr ax.1 (evaluate (foldEq ax.2) req es)) =
    axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) := by
  match axs with
  | [] => rfl
  | (a, x) :: rest =>
    have hx := foldEq_sound x req es
    have hrest := foldEq_sound_record rest req es
    simp only [List.mapM_cons, hx, hrest]
termination_by (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

end

/-! ### Decomposed guards -/

mutual

/-- A set or record literal errs exactly when an element does, so its
elements' guards mean what the literal's guard would. -/
theorem underGuards_addGuards {α} (x : Expr) (gs : List Expr) (req : Request) (es : Entities)
  (r : Result α) :
  underGuards (addGuards x gs) req es r =
    match evaluate x req es with
    | .ok _ => underGuards gs req es r
    | .error err => .error err := by
  match x with
  | .lit p => simp [addGuards, evaluate]
  | .var v => cases v <;> simp [addGuards, evaluate]
  | .set xs =>
    have ih := underGuards_addGuardsList xs gs req es r
    simp only [addGuards, evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es)]
    rw [ih]
    cases xs.mapM (fun x => evaluate x req es) <;> simp [Bind.bind, Except.bind]
  | .record axs =>
    have ih := underGuards_addGuardsRecord axs gs req es r
    simp only [addGuards, evaluate,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es))]
    rw [ih]
    cases axs.mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)) <;>
      simp [Bind.bind, Except.bind]
  | .binaryApp op a b =>
    cases op with
    | eq =>
      simp only [addGuards]
      have iha := underGuards_addGuards a (addGuards b gs) req es r
      have ihb := underGuards_addGuards b gs req es r
      simp only [evaluate]
      rw [iha]
      cases evaluate a req es with
      | error err => simp [Bind.bind, Except.bind]
      | ok va =>
        rw [ihb]
        cases evaluate b req es with
        | error err => simp [Bind.bind, Except.bind]
        | ok vb => simp [Bind.bind, Except.bind, apply₂]
    | _ => simp only [addGuards, underGuards]
  | .and _ _ | .or _ _ | .ite _ _ _ | .unaryApp _ _ | .getAttr _ _
  | .hasAttr _ _ | .call _ _ => simp only [addGuards, underGuards]
termination_by sizeOf x

theorem underGuards_addGuardsList {α} (xs : List Expr) (gs : List Expr) (req : Request)
  (es : Entities) (r : Result α) :
  underGuards (addGuardsList xs gs) req es r =
    match xs.mapM (fun x => evaluate x req es) with
    | .ok _ => underGuards gs req es r
    | .error err => .error err := by
  match xs with
  | [] => simp [addGuardsList, Pure.pure, Except.pure]
  | x :: rest =>
    have ihx := underGuards_addGuards x (addGuardsList rest gs) req es r
    have ihr := underGuards_addGuardsList rest gs req es r
    simp only [addGuardsList, List.mapM_cons]
    rw [ihx]
    cases evaluate x req es with
    | error err => simp [Bind.bind, Except.bind]
    | ok v =>
      rw [ihr]
      cases rest.mapM (fun x => evaluate x req es) <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
termination_by sizeOf xs

theorem underGuards_addGuardsRecord {α} (axs : List (Attr × Expr)) (gs : List Expr)
  (req : Request) (es : Entities) (r : Result α) :
  underGuards (addGuardsRecord axs gs) req es r =
    match axs.mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)) with
    | .ok _ => underGuards gs req es r
    | .error err => .error err := by
  match axs with
  | [] => simp [addGuardsRecord, Pure.pure, Except.pure]
  | (a, x) :: rest =>
    have ihx := underGuards_addGuards x (addGuardsRecord rest gs) req es r
    have ihr := underGuards_addGuardsRecord rest gs req es r
    simp only [addGuardsRecord, List.mapM_cons]
    rw [ihx]
    cases evaluate x req es with
    | error err => simp [bindAttr_error, Bind.bind, Except.bind]
    | ok v =>
      rw [ihr]
      simp only [bindAttr_ok]
      cases rest.mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)) <;>
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
termination_by sizeOf axs

end

/-- A folded, decomposed guard means what the sibling did (`foldEq_sound`). -/
theorem underGuards_addGuard {α} (x : Expr) (gs : List Expr) (req : Request) (es : Entities)
  (r : Result α) :
  underGuards (addGuard x gs) req es r =
    match evaluate x req es with
    | .ok _ => underGuards gs req es r
    | .error err => .error err := by
  simp only [addGuard, underGuards_addGuards, foldEq_sound]

/-! ### Learned guards -/

theorem and_ok_true {l r : Expr} {req : Request} {es : Entities}
  (h : evaluate (.and l r) req es = .ok (.prim (.bool true))) :
  evaluate l req es = .ok (.prim (.bool true)) ∧ evaluate r req es = .ok (.prim (.bool true))
:= by
  cases hl : evaluate l req es with
  | error e => simp [evaluate, hl, Result.as] at h
  | ok w =>
    match w with
    | .prim (.bool false) => simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h
    | .prim (.bool true) =>
      cases hr : evaluate r req es with
      | error e => simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
      | ok u =>
        match u with
        | .prim (.bool true) => exact ⟨rfl, rfl⟩
        | .prim (.bool false) => simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h

/-- A true expression makes every conjunct of its `&&`-spine true. -/
theorem conjuncts_true {c : Expr} {req : Request} {es : Entities}
  (h : evaluate c req es = .ok (.prim (.bool true))) :
  ∀ d ∈ conjuncts c, evaluate d req es = .ok (.prim (.bool true)) := by
  match c with
  | .and x₁ x₂ =>
    obtain ⟨h₁, h₂⟩ := and_ok_true h
    intro d hd
    simp only [conjuncts, List.mem_append] at hd
    rcases hd with hd | hd
    · exact conjuncts_true h₁ d hd
    · exact conjuncts_true h₂ d hd
  | .lit (.bool true) => simp [conjuncts]
  | .lit (.bool false) | .lit (.int _) | .lit (.string _) | .lit (.entityUID _) | .var _
  | .or _ _ | .ite _ _ _ | .unaryApp _ _ | .binaryApp _ _ _ | .getAttr _ _ | .hasAttr _ _
  | .set _ | .record _ | .call _ _ =>
    intro d hd
    simp only [conjuncts, List.mem_singleton] at hd
    subst hd
    exact h

theorem transparent_nil (req : Request) (es : Entities) : Transparent [] req es :=
  fun _ hg => absurd hg List.not_mem_nil

theorem transparent_cons {e : Expr} {gs : List Expr} {req : Request} {es : Entities}
  (he : ∃ v, evaluate e req es = .ok v) (hgs : Transparent gs req es) :
  Transparent (e :: gs) req es := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact he
  · exact hgs g hg

theorem or_ok_false {l r : Expr} {req : Request} {es : Entities}
  (h : evaluate (.or l r) req es = .ok (.prim (.bool false))) :
  evaluate l req es = .ok (.prim (.bool false)) ∧ evaluate r req es = .ok (.prim (.bool false))
:= by
  cases hl : evaluate l req es with
  | error e => simp [evaluate, hl, Result.as] at h
  | ok w =>
    match w with
    | .prim (.bool true) => simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h
    | .prim (.bool false) =>
      cases hr : evaluate r req es with
      | error e => simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
      | ok u =>
        match u with
        | .prim (.bool false) => exact ⟨rfl, rfl⟩
        | .prim (.bool true) => simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
        | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
        | .set _ | .record _ | .ext _ =>
          simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool] at h
    | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
    | .set _ | .record _ | .ext _ =>
      simp [evaluate, hl, Result.as, Coe.coe, Value.asBool] at h

/-- A false expression makes every disjunct of its `||`-spine false. -/
theorem disjuncts_false {c : Expr} {req : Request} {es : Entities}
  (h : evaluate c req es = .ok (.prim (.bool false))) :
  ∀ d ∈ disjuncts c, evaluate d req es = .ok (.prim (.bool false)) := by
  match c with
  | .or x₁ x₂ =>
    obtain ⟨h₁, h₂⟩ := or_ok_false h
    intro d hd
    simp only [disjuncts, List.mem_append] at hd
    rcases hd with hd | hd
    · exact disjuncts_false h₁ d hd
    · exact disjuncts_false h₂ d hd
  | .lit (.bool false) => simp [disjuncts]
  | .lit (.bool true) | .lit (.int _) | .lit (.string _) | .lit (.entityUID _) | .var _
  | .and _ _ | .ite _ _ _ | .unaryApp _ _ | .binaryApp _ _ _ | .getAttr _ _ | .hasAttr _ _
  | .set _ | .record _ | .call _ _ =>
    intro d hd
    simp only [disjuncts, List.mem_singleton] at hd
    subst hd
    exact h

/-! An expression that evaluates has all of its strict subterms evaluate:
the evaluated closure is transparent. -/

mutual

theorem evaluated_transparent {e : Expr} {v : Value} {gs : List Expr} {req : Request}
  {es : Entities} (hgs : Transparent gs req es) (h : evaluate e req es = .ok v) :
  Transparent (evaluated e gs) req es := by
  match e with
  | .lit _ => simpa [evaluated] using hgs
  | .var _ => simpa [evaluated] using hgs
  | .ite c t f =>
    simp only [evaluated]
    refine transparent_cons ⟨v, h⟩ ?_
    simp only [evaluate] at h
    cases hc : evaluate c req es with
    | error err => simp [hc, Result.as] at h
    | ok w => exact evaluated_transparent hgs hc
  | .and l r =>
    simp only [evaluated]
    refine transparent_cons ⟨v, h⟩ ?_
    simp only [evaluate] at h
    cases hl : evaluate l req es with
    | error err => simp [hl, Result.as] at h
    | ok w => exact evaluated_transparent hgs hl
  | .or l r =>
    simp only [evaluated]
    refine transparent_cons ⟨v, h⟩ ?_
    simp only [evaluate] at h
    cases hl : evaluate l req es with
    | error err => simp [hl, Result.as] at h
    | ok w => exact evaluated_transparent hgs hl
  | .unaryApp op x =>
    simp only [evaluated]
    refine transparent_cons ⟨v, h⟩ ?_
    simp only [evaluate] at h
    cases hx : evaluate x req es with
    | error err => simp [hx, Bind.bind, Except.bind] at h
    | ok w => exact evaluated_transparent hgs hx
  | .binaryApp op a b =>
    have h₀ := h
    simp only [evaluate] at h
    cases ha : evaluate a req es with
    | error err => simp [ha, Bind.bind, Except.bind] at h
    | ok wa =>
      cases hb : evaluate b req es with
      | error err => simp [ha, hb, Bind.bind, Except.bind] at h
      | ok wb =>
        have hin := evaluated_transparent (evaluated_transparent hgs hb) ha
        cases op
        case eq => simpa [evaluated] using hin
        all_goals
          simp only [evaluated]
          exact transparent_cons ⟨v, h₀⟩ hin
  | .getAttr x _ =>
    simp only [evaluated]
    refine transparent_cons ⟨v, h⟩ ?_
    simp only [evaluate] at h
    cases hx : evaluate x req es with
    | error err => simp [hx, Bind.bind, Except.bind] at h
    | ok w => exact evaluated_transparent hgs hx
  | .hasAttr x _ =>
    simp only [evaluated]
    refine transparent_cons ⟨v, h⟩ ?_
    simp only [evaluate] at h
    cases hx : evaluate x req es with
    | error err => simp [hx, Bind.bind, Except.bind] at h
    | ok w => exact evaluated_transparent hgs hx
  | .set xs =>
    simp only [evaluated]
    simp only [evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es)] at h
    cases hm : xs.mapM (fun x => evaluate x req es) with
    | error err => simp [hm, Bind.bind, Except.bind] at h
    | ok vs =>
      exact evaluatedList_transparent hgs (fun x hx => by
        obtain ⟨w, _, hw⟩ := List.forall₂_implies_all_left (List.mapM_ok_iff_forall₂.mp hm) x hx
        exact ⟨w, hw⟩)
  | .record axs =>
    simp only [evaluated]
    simp only [evaluate,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es))] at h
    cases hm : axs.mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)) with
    | error err => simp [hm, Bind.bind, Except.bind] at h
    | ok avs =>
      exact evaluatedRecord_transparent hgs (fun ax hax => by
        obtain ⟨av, _, hav⟩ := List.forall₂_implies_all_left (List.mapM_ok_iff_forall₂.mp hm) ax hax
        cases hv : evaluate ax.2 req es with
        | error err => simp [bindAttr, hv, Bind.bind, Except.bind] at hav
        | ok w => exact ⟨w, rfl⟩)
  | .call xfn xs =>
    simp only [evaluated]
    split
    next => exact transparent_cons ⟨v, h⟩ hgs
    next hne =>
      refine transparent_cons ⟨v, h⟩ ?_
      rw [evaluate_call_ne xs req es hne] at h
      simp only [List.mapM₁_eq_mapM (fun x => evaluate x req es)] at h
      cases hm : xs.mapM (fun x => evaluate x req es) with
      | error err => simp [hm, Bind.bind, Except.bind] at h
      | ok vs =>
        exact evaluatedList_transparent hgs (fun x hx => by
          obtain ⟨w, _, hw⟩ := List.forall₂_implies_all_left (List.mapM_ok_iff_forall₂.mp hm) x hx
          exact ⟨w, hw⟩)
termination_by sizeOf e

theorem evaluatedList_transparent {xs gs : List Expr} {req : Request} {es : Entities}
  (hgs : Transparent gs req es) (h : ∀ x ∈ xs, ∃ v, evaluate x req es = .ok v) :
  Transparent (evaluatedList xs gs) req es := by
  match xs with
  | [] => simpa [evaluatedList] using hgs
  | x :: rest =>
    simp only [evaluatedList]
    obtain ⟨v, hv⟩ := h x List.mem_cons_self
    exact evaluated_transparent
      (evaluatedList_transparent hgs (fun y hy => h y (List.mem_cons_of_mem x hy))) hv
termination_by sizeOf xs

theorem evaluatedRecord_transparent {axs : List (Attr × Expr)} {gs : List Expr} {req : Request}
  {es : Entities} (hgs : Transparent gs req es)
  (h : ∀ ax ∈ axs, ∃ v, evaluate ax.2 req es = .ok v) :
  Transparent (evaluatedRecord axs gs) req es := by
  match axs with
  | [] => simpa [evaluatedRecord] using hgs
  | (a, x) :: rest =>
    simp only [evaluatedRecord]
    obtain ⟨v, hv⟩ := h (a, x) List.mem_cons_self
    exact evaluated_transparent
      (evaluatedRecord_transparent hgs (fun y hy => h y (List.mem_cons_of_mem (a, x) hy))) hv
termination_by sizeOf axs

end

theorem foldr_evaluated_transparent {ds : List Expr} {req : Request} {es : Entities}
  (h : ∀ d ∈ ds, ∃ v, evaluate d req es = .ok v) :
  Transparent (ds.foldr evaluated []) req es := by
  induction ds with
  | nil => exact transparent_nil req es
  | cons d rest ih =>
    obtain ⟨v, hv⟩ := h d List.mem_cons_self
    exact evaluated_transparent (ih (fun y hy => h y (List.mem_cons_of_mem d hy))) hv

/-- A true condition establishes what `learnTrue` says it does. -/
theorem learnTrue_transparent {c : Expr} {req : Request} {es : Entities}
  (h : evaluate c req es = .ok (.prim (.bool true))) :
  Transparent (learnTrue c) req es :=
  foldr_evaluated_transparent (fun d hd => ⟨_, conjuncts_true h d hd⟩)

/-- A false condition establishes what `learnFalse` says it does. -/
theorem learnFalse_transparent {c : Expr} {req : Request} {es : Entities}
  (h : evaluate c req es = .ok (.prim (.bool false))) :
  Transparent (learnFalse c) req es :=
  foldr_evaluated_transparent (fun d hd => ⟨_, disjuncts_false h d hd⟩)

end Cedar.DNF
