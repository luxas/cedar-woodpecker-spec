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
import Cedar.Thm.DNF.EvalOrder

/-!
The main Phase 4 Step 1 theorem: `evaluate_eliminate` — eliminating the
record and set literals of an expression preserves evaluation exactly, on
every request and entity store on which the expression is *typed*
(`Typed`: the operands of `containsAll`/`containsAny` are set-typed, those of
`in` entity-typed, and the values meeting in an equality — at `==`, and
through the element equalities the chains produce at `contains`/
`containsAll`/`containsAny` — are `EqTyped`: two sets well formed and
element-wise so, two records field-wise, a set never against a non-set;
wherever they evaluate) — and `evaluate_normalize` for
the pipeline, with the hypothesis on the split input. `Typed` is what the
validator's soundness gives every *reachable* node of a validated expression
on a schema-conformant input; it is stronger than validation on dead code
(`false && r`, the untaken branch of `if true …`), which the strict typechecker
never looks at while `Typed` constrains every node. The bridge from `typeOf`
to `Typed (splitAtoms e)` is not proved here.

The invariant of the bottom-up pass (`elim_spec`): when a subterm `e` is
rewritten to `t` under guards `gs`, `evaluate e = underGuards gs (evaluate t)`,
and `t` evaluates whenever the guards do. The second half is what lets a
later sibling's guards move out past an earlier child's bind
(`underGuards_bind_swap`); a leaf region has it by construction
(`underGuards_addGuard`), a rewritten node by the rule lemmas and typing, an
unrewritten node above a rewritten one by its own guard.
-/

namespace Cedar.DNF

open Cedar.Spec Cedar.Data

/-! ### Typing -/

/-- `x` evaluates to a set, or errs. -/
def SetTyped (x : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ v, evaluate x req es = .ok v → ∃ S, v = .set S

/-- `x` evaluates to an entity, or errs. -/
def EntityTyped (x : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ v, evaluate x req es = .ok v → ∃ u, v = .prim (.entityUID u)

/-- The values that meet in `x₁ == x₂` are `EqTyped` (the set rules' value-
level typing), wherever both evaluate. -/
def EqTypedAt (x₁ x₂ : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ v₁ v₂, evaluate x₁ req es = .ok v₁ → evaluate x₂ req es = .ok v₂ → EqTyped v₁ v₂

/-- Every element of `x₁`'s set value is `EqTyped` with `x₂`'s value (the
element equalities `x₁.contains(x₂)` may become). -/
def ElemTyped (x₁ x₂ : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ S v, evaluate x₁ req es = .ok (.set S) → evaluate x₂ req es = .ok v → ∀ a ∈ S, EqTyped a v

/-- The elements of two set values are pairwise `EqTyped` (the element
equalities `containsAll`/`containsAny` chains may become). -/
def SetsTyped (x₁ x₂ : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ S T, evaluate x₁ req es = .ok (.set S) → evaluate x₂ req es = .ok (.set T) →
    ∀ a ∈ S, ∀ b ∈ T, EqTyped a b

/-- `x` evaluates to an entity or to a set of entities, or errs (the right
operand of `in`). -/
def EntitySetTyped (x : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ v, evaluate x req es = .ok v →
    (∃ u, v = .prim (.entityUID u)) ∨ (∃ S, v = .set S ∧ ∀ w ∈ S, ∃ u, w = .prim (.entityUID u))

mutual

/-- The typing facts the elimination rules rest on, at every node. -/
def Typed (req : Request) (es : Entities) : Expr → Prop
  | .lit _ => True
  | .var _ => True
  | .ite x₁ x₂ x₃ => Typed req es x₁ ∧ Typed req es x₂ ∧ Typed req es x₃
  | .and x₁ x₂ => Typed req es x₁ ∧ Typed req es x₂
  | .or x₁ x₂ => Typed req es x₁ ∧ Typed req es x₂
  | .unaryApp _ x => Typed req es x
  | .binaryApp .eq x₁ x₂ => EqTypedAt x₁ x₂ req es ∧ Typed req es x₁ ∧ Typed req es x₂
  | .binaryApp .contains x₁ x₂ => ElemTyped x₁ x₂ req es ∧ Typed req es x₁ ∧ Typed req es x₂
  | .binaryApp .containsAll x₁ x₂ =>
    SetTyped x₁ req es ∧ SetsTyped x₁ x₂ req es ∧ Typed req es x₁ ∧ Typed req es x₂
  | .binaryApp .containsAny x₁ x₂ =>
    SetTyped x₁ req es ∧ SetTyped x₂ req es ∧ SetsTyped x₁ x₂ req es ∧
      Typed req es x₁ ∧ Typed req es x₂
  | .binaryApp .mem x₁ x₂ =>
    EntityTyped x₁ req es ∧ EntitySetTyped x₂ req es ∧ Typed req es x₁ ∧ Typed req es x₂
  | .binaryApp _ x₁ x₂ => Typed req es x₁ ∧ Typed req es x₂
  | .getAttr x _ => Typed req es x
  | .hasAttr x _ => Typed req es x
  | .set xs => TypedList req es xs
  | .record axs => TypedRecord req es axs
  | .call _ xs => TypedList req es xs
termination_by e => sizeOf e

def TypedList (req : Request) (es : Entities) : List Expr → Prop
  | [] => True
  | x :: xs => Typed req es x ∧ TypedList req es xs
termination_by xs => sizeOf xs

def TypedRecord (req : Request) (es : Entities) : List (Attr × Expr) → Prop
  | [] => True
  | (_, x) :: axs => Typed req es x ∧ TypedRecord req es axs
termination_by axs => sizeOf axs

end

/-- Every binary node's operands are typed. -/
theorem Typed.binary {op : BinaryOp} {x₁ x₂ : Expr} {req : Request} {es : Entities}
  (h : Typed req es (.binaryApp op x₁ x₂)) : Typed req es x₁ ∧ Typed req es x₂ := by
  cases op <;> (rw [Typed.eq_def] at h; try simp only at h) <;>
    first | exact h | exact h.2 | exact h.2.2 | exact h.2.2.2

/-! ### What a child contributes -/

/-- The specification of a child's contribution `(gs, t)`: the child
evaluates like `t` under the guards, and `t` evaluates whenever the guards
do. -/
def ChildSpec (x : Expr) (gs : List Expr) (t : Expr) (req : Request) (es : Entities) : Prop :=
  evaluate x req es = underGuards gs req es (evaluate t req es) ∧
  (Transparent gs req es → ∃ v, evaluate t req es = .ok v)

/-- A leaf region: its decomposed guard, and itself. -/
theorem childSpec_leaf (x : Expr) (req : Request) (es : Entities) :
  ChildSpec x (addGuard x []) x req es := by
  constructor
  · rw [underGuards_addGuard]
    cases evaluate x req es <;> simp [underGuards]
  · intro ht
    have := underGuards_eq_of_ok ht (Except.ok () : Result Unit)
    rw [underGuards_addGuard] at this
    cases hx : evaluate x req es with
    | error e => simp [hx] at this
    | ok v => exact ⟨v, rfl⟩

/-- `childOf` meets the specification whenever the rewrite does. -/
theorem childOf_spec {x : Expr} {r : Option (List Expr × Expr)} {req : Request} {es : Entities}
  (h : ∀ gs t, r = some (gs, t) → ChildSpec x gs t req es) :
  ChildSpec x (childOf x r).2.1 (childOf x r).2.2 req es := by
  cases r with
  | none => exact childSpec_leaf x req es
  | some p => exact h p.1 p.2 (by simp)

/-! ### Finishing a node -/

/-- What `finish` produces meets the specification, given the sequencing of
the children (`hseq`), the rule (`hrule`) and the never-erring nodes
(`hnever`). -/
theorem finish_spec {e rebuilt : Expr} {changed : Bool} {gs : List Expr} {req : Request}
  {es : Entities}
  (hseq : evaluate e req es = underGuards gs req es (evaluate rebuilt req es))
  (hrule : ∀ r, rewrite rebuilt = some r → Transparent gs req es →
    evaluate r req es = evaluate rebuilt req es ∧ ∃ v, evaluate r req es = .ok v)
  (hnever : neverErrsItself rebuilt = true → Transparent gs req es →
    ∃ v, evaluate rebuilt req es = .ok v) :
  ∀ gs' t, finish rebuilt changed gs = some (gs', t) → ChildSpec e gs' t req es := by
  intro gs' t hfin
  simp only [finish] at hfin
  split at hfin
  next r hr =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hfin
    obtain ⟨rfl, rfl⟩ := hfin
    constructor
    · rw [hseq]
      rcases underGuards_cases gs req es with hid | ⟨err, herr⟩
      · rw [hid, hid, (hrule r hr (ok_of_underGuards_id hid)).1]
      · rw [herr, herr]
    · intro ht
      exact (hrule r hr ht).2
  next =>
    split at hfin
    next hchanged =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hfin
      obtain ⟨rfl, rfl⟩ := hfin
      split
      next hne =>
        exact ⟨hseq, hnever hne⟩
      next =>
        constructor
        · rw [hseq, underGuards_append, underGuards_self]
        · intro ht
          exact ht rebuilt (by simp)
    next => cases hfin

/-! ### Sequencing the children of a strict node -/

theorem seq_unary {op : UnaryOp} {x t : Expr} {gs : List Expr} {req : Request} {es : Entities}
  (h : ChildSpec x gs t req es) :
  evaluate (.unaryApp op x) req es = underGuards gs req es (evaluate (.unaryApp op t) req es) := by
  simp only [evaluate, h.1, underGuards_bind]

theorem seq_getAttr {x t : Expr} {a : Attr} {gs : List Expr} {req : Request} {es : Entities}
  (h : ChildSpec x gs t req es) :
  evaluate (.getAttr x a) req es = underGuards gs req es (evaluate (.getAttr t a) req es) := by
  simp only [evaluate, h.1, underGuards_bind]

theorem seq_hasAttr {x t : Expr} {a : Attr} {gs : List Expr} {req : Request} {es : Entities}
  (h : ChildSpec x gs t req es) :
  evaluate (.hasAttr x a) req es = underGuards gs req es (evaluate (.hasAttr t a) req es) := by
  simp only [evaluate, h.1, underGuards_bind]

theorem seq_binary {op : BinaryOp} {x₁ x₂ t₁ t₂ : Expr} {gs₁ gs₂ : List Expr} {req : Request}
  {es : Entities} (h₁ : ChildSpec x₁ gs₁ t₁ req es) (h₂ : ChildSpec x₂ gs₂ t₂ req es) :
  evaluate (.binaryApp op x₁ x₂) req es =
    underGuards (gs₁ ++ gs₂) req es (evaluate (.binaryApp op t₁ t₂) req es) := by
  simp only [evaluate, h₁.1, h₂.1, underGuards_bind, underGuards_append]
  exact underGuards_bind_swap h₁.2 _

/-- The list specification: the list's `mapM` under the concatenated guards. -/
def ListSpec (xs : List Expr) (gs : List Expr) (ts : List Expr) (req : Request) (es : Entities) :
  Prop :=
  xs.mapM (fun x => evaluate x req es) = underGuards gs req es (ts.mapM (fun x => evaluate x req es)) ∧
  (Transparent gs req es → ∃ vs, ts.mapM (fun x => evaluate x req es) = .ok vs)

theorem listSpec_nil (req : Request) (es : Entities) : ListSpec [] [] [] req es :=
  ⟨rfl, fun _ => ⟨[], rfl⟩⟩

theorem listSpec_cons {x t : Expr} {xs ts gs gs' : List Expr} {req : Request} {es : Entities}
  (h : ChildSpec x gs t req es) (hs : ListSpec xs gs' ts req es) :
  ListSpec (x :: xs) (gs ++ gs') (t :: ts) req es := by
  constructor
  · simp only [List.mapM_cons, h.1, hs.1, underGuards_bind, underGuards_append]
    exact underGuards_bind_swap h.2 _
  · intro ht
    have ht₁ : Transparent gs req es := fun g hg => ht g (List.mem_append_left _ hg)
    have ht₂ : Transparent gs' req es := fun g hg => ht g (List.mem_append_right _ hg)
    obtain ⟨v, hv⟩ := h.2 ht₁
    obtain ⟨vs, hvs⟩ := hs.2 ht₂
    exact ⟨v :: vs, by simp [List.mapM_cons, hv, hvs, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

/-- The record-field list specification. -/
def RecordSpec (axs : List (Attr × Expr)) (gs : List Expr) (ts : List (Attr × Expr))
  (req : Request) (es : Entities) : Prop :=
  axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) =
    underGuards gs req es (ts.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es))) ∧
  (Transparent gs req es → ∃ avs, ts.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs)

theorem recordSpec_nil (req : Request) (es : Entities) : RecordSpec [] [] [] req es :=
  ⟨rfl, fun _ => ⟨[], rfl⟩⟩

theorem recordSpec_cons {a : Attr} {x t : Expr} {axs ts : List (Attr × Expr)} {gs gs' : List Expr}
  {req : Request} {es : Entities}
  (h : ChildSpec x gs t req es) (hs : RecordSpec axs gs' ts req es) :
  RecordSpec ((a, x) :: axs) (gs ++ gs') ((a, t) :: ts) req es := by
  constructor
  · have hs1 := hs.1
    simp only [List.mapM_cons]
    rw [show bindAttr a (evaluate x req es) = evaluate x req es >>= fun v => pure (a, v) from rfl,
      show bindAttr a (evaluate t req es) = evaluate t req es >>= fun v => pure (a, v) from rfl,
      h.1, hs1]
    simp only [bind_assoc, pure_bind, underGuards_bind, underGuards_append]
    exact underGuards_bind_swap h.2 _
  · intro ht
    have ht₁ : Transparent gs req es := fun g hg => ht g (List.mem_append_left _ hg)
    have ht₂ : Transparent gs' req es := fun g hg => ht g (List.mem_append_right _ hg)
    obtain ⟨v, hv⟩ := h.2 ht₁
    obtain ⟨avs, havs⟩ := hs.2 ht₂
    exact ⟨(a, v) :: avs, by
      simp [List.mapM_cons, hv, bindAttr_ok, havs, Bind.bind, Except.bind, Pure.pure, Except.pure]⟩

theorem seq_set {xs ts gs : List Expr} {req : Request} {es : Entities}
  (h : ListSpec xs gs ts req es) :
  evaluate (.set xs) req es = underGuards gs req es (evaluate (.set ts) req es) := by
  simp only [evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es), h.1, underGuards_bind]

theorem seq_record {axs ts : List (Attr × Expr)} {gs : List Expr} {req : Request} {es : Entities}
  (h : RecordSpec axs gs ts req es) :
  evaluate (.record axs) req es = underGuards gs req es (evaluate (.record ts) req es) := by
  simp only [evaluate,
    List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)), h.1,
    underGuards_bind]

theorem seq_call {xfn : ExtFun} (hne : xfn ≠ .ifError) {xs ts gs : List Expr} {req : Request}
  {es : Entities} (h : ListSpec xs gs ts req es) :
  evaluate (.call xfn xs) req es = underGuards gs req es (evaluate (.call xfn ts) req es) := by
  rw [evaluate_call_ne xs req es hne, evaluate_call_ne ts req es hne]
  simp only [List.mapM₁_eq_mapM (fun x => evaluate x req es), h.1, underGuards_bind]


/-! ### The rules at a rebuilt node -/

/-- No rule fires at a set, record or call node. -/
theorem rewrite_set (ts : List Expr) : rewrite (.set ts) = none := by simp [rewrite]
theorem rewrite_record (ts : List (Attr × Expr)) : rewrite (.record ts) = none := by simp [rewrite]
theorem rewrite_call (xfn : ExtFun) (ts : List Expr) : rewrite (.call xfn ts) = none := by
  simp [rewrite]

/-- Under transparent guards a child's term evaluates like the child. -/
theorem childSpec_eval {x t : Expr} {gs : List Expr} {req : Request} {es : Entities}
  (h : ChildSpec x gs t req es) (ht : Transparent gs req es) :
  ∃ v, evaluate t req es = .ok v ∧ evaluate x req es = .ok v := by
  obtain ⟨v, hv⟩ := h.2 ht
  exact ⟨v, hv, by rw [h.1, underGuards_eq_of_ok ht, hv]⟩

/-! ### The invariant of the pass -/

/-- A rule fires only at the node kinds it is for: the contradictory arms
of `rewrite`'s match. -/
macro "close_rule_arms" : tactic => `(tactic| all_goals try (simp_all; done))

mutual

theorem elim_spec (e : Expr) (req : Request) (es : Entities) (hty : Typed req es e) :
  ∀ gs t, elim e = some (gs, t) → ChildSpec e gs t req es := by
  match e with
  | .lit _ => intro gs t h; simp [elim] at h
  | .var _ => intro gs t h; simp [elim] at h
  | .and _ _ => intro gs t h; simp [elim] at h
  | .or _ _ => intro gs t h; simp [elim] at h
  | .ite _ _ _ => intro gs t h; simp [elim] at h
  | .unaryApp op x =>
    have hx := childOf_spec (r := elim x) (elim_spec x req es (by simpa [Typed] using hty))
    cases op with
    | not => intro gs t h; simp [elim] at h
    | isEmpty =>
      intro gs t h
      simp only [elim] at h
      generalize hc : childOf x (elim x) = c at hx h
      obtain ⟨c₁, gs₀, t₀⟩ := c
      refine finish_spec (seq_unary hx) ?_ ?_ gs t h
      · intro r hr htr
        rw [rewrite.eq_def] at hr
        split at hr
        case h_3 ls heq =>
          simp only [Expr.unaryApp.injEq] at heq
          obtain ⟨_, rfl⟩ := heq
          simp only [Option.some.injEq] at hr
          subst hr
          obtain ⟨v, hv, _⟩ := childSpec_eval hx htr
          obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv
          exact ⟨isEmpty_lit_sound hvs, .prim (.bool ls.isEmpty), by simp [evaluate, boolLit]⟩
        close_rule_arms
      · intro hne; simp [neverErrsItself] at hne
    | _ =>
      intro gs t h
      simp only [elim] at h
      generalize hc : childOf x (elim x) = c at hx h
      obtain ⟨c₁, gs₀, t₀⟩ := c
      refine finish_spec (seq_unary hx) ?_ ?_ gs t h
      · intro r hr htr
        rw [rewrite.eq_def] at hr
        split at hr
        close_rule_arms
      · intro hne; simp [neverErrsItself] at hne
  | .binaryApp op x₁ x₂ =>
    have hty' := hty.binary
    have h₁ := childOf_spec (r := elim x₁) (elim_spec x₁ req es hty'.1)
    have h₂ := childOf_spec (r := elim x₂) (elim_spec x₂ req es hty'.2)
    intro gs t h
    simp only [elim] at h
    generalize hc₁ : childOf x₁ (elim x₁) = c₁ at h₁ h
    generalize hc₂ : childOf x₂ (elim x₂) = c₂ at h₂ h
    obtain ⟨b₁, gs₁, t₁⟩ := c₁
    obtain ⟨b₂, gs₂, t₂⟩ := c₂
    refine finish_spec (seq_binary h₁ h₂) ?_ ?_ gs t h
    · intro r hr htr
      have htr₁ := transparent_append_left htr
      have htr₂ := transparent_append_right htr
      obtain ⟨v₁, hv₁, hx₁⟩ := childSpec_eval h₁ htr₁
      obtain ⟨v₂, hv₂, hx₂⟩ := childSpec_eval h₂ htr₂
      rw [rewrite.eq_def] at hr
      split at hr
      -- record equality
      case h_4 axs bys heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        split at hr
        next hcond =>
          simp only [Option.some.injEq] at hr
          subst hr
          have hchain : andChain (eqFields axs bys) = elimEq (.record axs) (.record bys) := by
            rw [elimEq.eq_def]
            simp only [if_pos hcond]
          have hety : EqTypedAt x₁ x₂ req es := by simp only [Typed] at hty; exact hty.1
          rw [hchain, elimEq_sound hv₁ hv₂ (hety v₁ v₂ hx₁ hx₂)]
          exact ⟨by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind], _, rfl⟩
        next => cases hr
      -- set equality, the literal on the left / on the right
      case h_5 ls x heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have hety : EqTypedAt x₁ x₂ req es := by simp only [Typed] at hty; exact hty.1
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₁
        rw [elimSetEq_sound hv₁ hv₂ (hety _ _ hx₁ hx₂) (.inl ⟨_, rfl⟩)]
        exact ⟨by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind], _, rfl⟩
      case h_6 x ls heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have hety : EqTypedAt x₁ x₂ req es := by simp only [Typed] at hty; exact hty.1
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₂
        rw [elimSetEq_sound hv₁ hv₂ (hety _ _ hx₁ hx₂) (.inr ⟨_, rfl⟩)]
        exact ⟨by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind], _, rfl⟩
      -- `contains` on a set literal
      case h_7 ls x heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have helem : ElemTyped x₁ x₂ req es := by simp only [Typed] at hty; exact hty.1
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₁
        rw [contains_lit_sound hvs hv₂
          (fun vl hvl => helem _ _ hx₁ hx₂ vl ((Set.mem_make _ _).mpr hvl))]
        exact ⟨by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind], _, rfl⟩
      -- `containsAll`
      case h_8 s ls heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have hset : SetTyped x₁ req es := by simp only [Typed] at hty; exact hty.1
        have hsets : SetsTyped x₁ x₂ req es := by simp only [Typed] at hty; exact hty.2.1
        obtain ⟨S, rfl⟩ := hset v₁ hx₁
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₂
        have hpairs : ∀ a ∈ S, ∀ vl ∈ vs, EqTyped a vl :=
          fun a ha vl hvl => hsets _ _ hx₁ hx₂ a ha vl ((Set.mem_make _ _).mpr hvl)
        refine ⟨containsAll_lit_sound hv₁ hvs hpairs, ?_⟩
        rw [containsAll_lit_sound hv₁ hvs hpairs]
        exact ⟨.prim (.bool ((Set.make vs).subset S)),
          by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind]⟩
      -- `containsAny`, literal on the right
      case h_9 s ls heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have hset : SetTyped x₁ req es := by simp only [Typed] at hty; exact hty.1
        have hsets : SetsTyped x₁ x₂ req es := by simp only [Typed] at hty; exact hty.2.2.1
        obtain ⟨S, rfl⟩ := hset v₁ hx₁
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₂
        have hpairs : ∀ a ∈ S, ∀ vl ∈ vs, EqTyped a vl :=
          fun a ha vl hvl => hsets _ _ hx₁ hx₂ a ha vl ((Set.mem_make _ _).mpr hvl)
        refine ⟨containsAny_lit_sound hv₁ hvs hpairs, ?_⟩
        rw [containsAny_lit_sound hv₁ hvs hpairs]
        exact ⟨.prim (.bool (S.intersects (Set.make vs))),
          by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind]⟩
      -- `containsAny`, literal on the left
      case h_10 ls s heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have hset : SetTyped x₂ req es := by simp only [Typed] at hty; exact hty.2.1
        have hsets : SetsTyped x₁ x₂ req es := by simp only [Typed] at hty; exact hty.2.2.1
        obtain ⟨S, rfl⟩ := hset v₂ hx₂
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₁
        have hpairs : ∀ a ∈ S, ∀ vl ∈ vs, EqTyped a vl :=
          fun a ha vl hvl => (hsets _ _ hx₁ hx₂ vl ((Set.mem_make _ _).mpr hvl) a ha).symm
        refine ⟨containsAny_lit_sound' hv₂ hvs hpairs, ?_⟩
        rw [containsAny_lit_sound' hv₂ hvs hpairs]
        exact ⟨.prim (.bool ((Set.make vs).intersects S)),
          by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind]⟩
      -- `in` over a set literal
      case h_11 e xs heq =>
        simp only [Expr.binaryApp.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        have htym : EntityTyped x₁ req es ∧ EntitySetTyped x₂ req es := by
          simp only [Typed] at hty; exact ⟨hty.1, hty.2.1⟩
        obtain ⟨uid, rfl⟩ := htym.1 v₁ hx₁
        obtain ⟨vs, hvs, rfl⟩ := evaluate_set_ok hv₂
        have hent : ∀ v ∈ vs, ∃ u, v = .prim (.entityUID u) := by
          rcases htym.2 _ hx₂ with ⟨u, hu⟩ | ⟨S, hS, hall⟩
          · cases hu
          · simp only [Value.set.injEq] at hS
            subst hS
            intro v hv
            exact hall v ((Set.mem_make _ _).mpr hv)
        refine ⟨mem_lit_sound hv₁ hvs hent, ?_⟩
        rw [mem_lit_sound hv₁ hvs hent]
        obtain ⟨us, hus, _⟩ := mapOrErr_entities hent
        exact ⟨.prim (.bool (us.any (inₑ uid · es))),
          by simp [evaluate, hv₁, hv₂, apply₂, inₛ, hus, Bind.bind, Except.bind]⟩
      close_rule_arms
    · intro hne htr
      have htr₁ := transparent_append_left htr
      have htr₂ := transparent_append_right htr
      obtain ⟨v₁, hv₁, _⟩ := childSpec_eval h₁ htr₁
      obtain ⟨v₂, hv₂, _⟩ := childSpec_eval h₂ htr₂
      cases op <;> (try (rw [neverErrsItself.eq_def] at hne; simp at hne))
      exact ⟨.prim (.bool (v₁ == v₂)), by simp [evaluate, hv₁, hv₂, apply₂, Bind.bind, Except.bind]⟩
  | .getAttr x a =>
    have hx := childOf_spec (r := elim x) (elim_spec x req es (by simpa [Typed] using hty))
    intro gs t h
    simp only [elim] at h
    generalize hc : childOf x (elim x) = c at hx h
    obtain ⟨c₁, gs₀, t₀⟩ := c
    refine finish_spec (seq_getAttr hx) ?_ ?_ gs t h
    · intro r hr htr
      rw [rewrite.eq_def] at hr
      split at hr
      case h_1 axs a' heq =>
        simp only [Expr.getAttr.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨v, hv, _⟩ := childSpec_eval hx htr
        obtain ⟨avs, hav, rfl⟩ := evaluate_record_ok hv
        refine ⟨getAttr_lit_sound hav hr, ?_⟩
        simp only [recordGet] at hr
        obtain ⟨ax, hax, rfl⟩ := Option.map_eq_some_iff.mp hr
        obtain ⟨av, _, hrel⟩ := List.forall₂_implies_all_left (mapM_bindAttr_forall₂ hav) ax
          (List.mem_of_find?_eq_some hax)
        exact ⟨_, hrel.2⟩
      close_rule_arms
    · intro hne; simp [neverErrsItself] at hne
  | .hasAttr x a =>
    have hx := childOf_spec (r := elim x) (elim_spec x req es (by simpa [Typed] using hty))
    intro gs t h
    simp only [elim] at h
    generalize hc : childOf x (elim x) = c at hx h
    obtain ⟨c₁, gs₀, t₀⟩ := c
    refine finish_spec (seq_hasAttr hx) ?_ ?_ gs t h
    · intro r hr htr
      rw [rewrite.eq_def] at hr
      split at hr
      case h_2 axs a' heq =>
        simp only [Expr.hasAttr.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simp only [Option.some.injEq] at hr
        subst hr
        obtain ⟨v, hv, _⟩ := childSpec_eval hx htr
        obtain ⟨avs, hav, rfl⟩ := evaluate_record_ok hv
        exact ⟨hasAttr_lit_sound hav, .prim (.bool (recordHas axs a)), by simp [evaluate, boolLit]⟩
      close_rule_arms
    · intro hne; simp [neverErrsItself] at hne
  | .set xs =>
    have hs := elimList_spec xs req es (by simpa [Typed] using hty)
    intro gs t h
    simp only [elim] at h
    refine finish_spec (seq_set hs) ?_ ?_ gs t h
    · intro r hr; rw [rewrite_set] at hr; cases hr
    · intro _ htr
      obtain ⟨vs, hvs⟩ := hs.2 htr
      exact ⟨_, evaluate_set_of_mapM hvs⟩
  | .record axs =>
    have hs := elimRecord_spec axs req es (by simpa [Typed] using hty)
    intro gs t h
    simp only [elim] at h
    refine finish_spec (seq_record hs) ?_ ?_ gs t h
    · intro r hr; rw [rewrite_record] at hr; cases hr
    · intro _ htr
      obtain ⟨avs, havs⟩ := hs.2 htr
      exact ⟨.record (Map.make avs), by simp [evaluate,
        List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)), havs,
        Bind.bind, Except.bind]⟩
  | .call xfn xs =>
    have hs := elimList_spec xs req es (by simpa [Typed] using hty)
    intro gs t h
    simp only [elim] at h
    split at h
    next => cases h
    next hne =>
      refine finish_spec (seq_call hne hs) ?_ ?_ gs t h
      · intro r hr; rw [rewrite_call] at hr; cases hr
      · intro hne'; simp [neverErrsItself] at hne'
termination_by sizeOf e

theorem elimList_spec (xs : List Expr) (req : Request) (es : Entities)
  (hty : TypedList req es xs) :
  ListSpec xs (elimList xs).2.1 (elimList xs).2.2 req es := by
  match xs with
  | [] => simp only [elimList]; exact listSpec_nil req es
  | x :: rest =>
    simp only [TypedList] at hty
    have hx := childOf_spec (r := elim x) (elim_spec x req es hty.1)
    have hrest := elimList_spec rest req es hty.2
    simp only [elimList]
    exact listSpec_cons hx hrest
termination_by sizeOf xs

theorem elimRecord_spec (axs : List (Attr × Expr)) (req : Request) (es : Entities)
  (hty : TypedRecord req es axs) :
  RecordSpec axs (elimRecord axs).2.1 (elimRecord axs).2.2 req es := by
  match axs with
  | [] => simp only [elimRecord]; exact recordSpec_nil req es
  | (a, x) :: rest =>
    simp only [TypedRecord] at hty
    have hx := childOf_spec (r := elim x) (elim_spec x req es hty.1)
    have hrest := elimRecord_spec rest req es hty.2
    simp only [elimRecord]
    exact recordSpec_cons hx hrest
termination_by sizeOf axs

end

/-! ### The theorems -/

/-- Eliminating in one atom is exact: the guarded rewrite evaluates like the
atom. -/
theorem elimAtom_sound (ctx : List Expr) (e : Expr) (req : Request) (es : Entities)
  (hty : Typed req es e) (hctx : Transparent ctx req es) :
  evaluate (elimAtom ctx e) req es = evaluate e req es := by
  simp only [elimAtom]
  cases h : elim e with
  | none => rfl
  | some p =>
    have hs := elim_spec e req es hty p.1 p.2 (by rw [h])
    rw [evaluate_guarded, underGuards_dropRepeated, underGuards_newGuards _ hctx, hs.1]

theorem elimStructure_sound (ctx : List Expr) (e : Expr) (req : Request) (es : Entities)
  (hty : Typed req es e) (hctx : Transparent ctx req es) :
  evaluate (elimStructure ctx e) req es = evaluate e req es := by
  match e with
  | .lit (.bool b) => simp only [elimStructure, boolLit]
  | .and x₁ x₂ =>
    simp only [Typed] at hty
    simp only [elimStructure]
    have h₁ := elimStructure_sound ctx x₁ req es hty.1 hctx
    cases hv : evaluate x₁ req es with
    | error e => simp [evaluate, h₁, hv, Result.as]
    | ok v =>
      match v with
      | .prim (.bool true) =>
        have h₂ := elimStructure_sound (ctx ++ learnTrue x₁) x₂ req es hty.2
          (transparent_append hctx (learnTrue_transparent hv))
        simp [evaluate, h₁, hv, h₂, Result.as, Coe.coe, Value.asBool]
      | .prim (.bool false) => simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
  | .or x₁ x₂ =>
    simp only [Typed] at hty
    simp only [elimStructure]
    have h₁ := elimStructure_sound ctx x₁ req es hty.1 hctx
    cases hv : evaluate x₁ req es with
    | error e => simp [evaluate, h₁, hv, Result.as]
    | ok v =>
      match v with
      | .prim (.bool false) =>
        have h₂ := elimStructure_sound (ctx ++ learnFalse x₁) x₂ req es hty.2
          (transparent_append hctx (learnFalse_transparent hv))
        simp [evaluate, h₁, hv, h₂, Result.as, Coe.coe, Value.asBool]
      | .prim (.bool true) => simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
  | .unaryApp .not x =>
    simp only [Typed] at hty
    simp only [elimStructure, evaluate, elimStructure_sound ctx x req es hty hctx]
  | .ite x₁ x₂ x₃ =>
    simp only [Typed] at hty
    simp only [elimStructure]
    have h₁ := elimStructure_sound ctx x₁ req es hty.1 hctx
    cases hv : evaluate x₁ req es with
    | error e => simp [evaluate, h₁, hv, Result.as]
    | ok v =>
      match v with
      | .prim (.bool true) =>
        have h₂ := elimStructure_sound (ctx ++ learnTrue x₁) x₂ req es hty.2.1
          (transparent_append hctx (learnTrue_transparent hv))
        simp [evaluate, h₁, hv, h₂, Result.as, Coe.coe, Value.asBool]
      | .prim (.bool false) =>
        have h₃ := elimStructure_sound (ctx ++ learnFalse x₁) x₃ req es hty.2.2
          (transparent_append hctx (learnFalse_transparent hv))
        simp [evaluate, h₁, hv, h₃, Result.as, Coe.coe, Value.asBool]
      | .prim (.int _) | .prim (.string _) | .prim (.entityUID _)
      | .set _ | .record _ | .ext _ =>
        simp [evaluate, h₁, hv, Result.as, Coe.coe, Value.asBool]
  | .lit (.int i) => rw [show elimStructure ctx (.lit (.int i)) = elimAtom ctx (.lit (.int i)) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .lit (.string s) => rw [show elimStructure ctx (.lit (.string s)) = elimAtom ctx (.lit (.string s)) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .lit (.entityUID u) => rw [show elimStructure ctx (.lit (.entityUID u)) = elimAtom ctx (.lit (.entityUID u)) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .var v => rw [show elimStructure ctx (.var v) = elimAtom ctx (.var v) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .unaryApp .neg x => rw [show elimStructure ctx (.unaryApp .neg x) = elimAtom ctx (.unaryApp .neg x) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .unaryApp .isEmpty x => rw [show elimStructure ctx (.unaryApp .isEmpty x) = elimAtom ctx (.unaryApp .isEmpty x) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .unaryApp (.like p) x => rw [show elimStructure ctx (.unaryApp (.like p) x) = elimAtom ctx (.unaryApp (.like p) x) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .unaryApp (.is ty) x => rw [show elimStructure ctx (.unaryApp (.is ty) x) = elimAtom ctx (.unaryApp (.is ty) x) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .binaryApp op x₁ x₂ => rw [show elimStructure ctx (.binaryApp op x₁ x₂) = elimAtom ctx (.binaryApp op x₁ x₂) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .getAttr x a => rw [show elimStructure ctx (.getAttr x a) = elimAtom ctx (.getAttr x a) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .hasAttr x a => rw [show elimStructure ctx (.hasAttr x a) = elimAtom ctx (.hasAttr x a) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .set xs => rw [show elimStructure ctx (.set xs) = elimAtom ctx (.set xs) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .record axs => rw [show elimStructure ctx (.record axs) = elimAtom ctx (.record axs) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx
  | .call xfn xs => rw [show elimStructure ctx (.call xfn xs) = elimAtom ctx (.call xfn xs) from by simp only [elimStructure]]; exact elimAtom_sound ctx _ req es hty hctx

/-- **Exactness of the elimination**: on every request and entity store on
which `e` is typed, `eliminate e` evaluates exactly like `e`. -/
theorem evaluate_eliminate (e : Expr) (req : Request) (es : Entities) (hty : Typed req es e) :
  evaluate (eliminate e) req es = evaluate e req es :=
  elimStructure_sound [] e req es hty (transparent_nil req es)

/-- **The pipeline**: `normalize` evaluates exactly like its input on every
request and entity store on which the split input is typed. -/
theorem evaluate_normalize (e : Expr) (req : Request) (es : Entities)
  (hty : Typed req es (splitAtoms e)) :
  evaluate (normalize e) req es = evaluate e req es := by
  simp only [normalize]
  rw [evaluate_splitAtoms, evaluate_eliminate _ req es hty, evaluate_splitAtoms]

end Cedar.DNF
