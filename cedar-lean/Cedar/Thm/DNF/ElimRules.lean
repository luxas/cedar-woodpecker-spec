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

import Cedar.Thm.DNF.ElimChains
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set

/-!
The elimination rules, one lemma each: over children that evaluate (and,
for `in`, entity-typed set elements), the rule's result evaluates to the
node's value. Record equality first — `elimEq`/`eqFields` are what the other
rules' equalities go through.
-/

namespace Cedar.DNF

open Cedar.Spec Cedar.Data

/-! ### Evaluated field lists -/

/-- A record literal's fields evaluate to the entries of its value. -/
theorem evaluate_record_ok {axs : List (Attr × Expr)} {req : Request} {es : Entities} {v : Value}
  (h : evaluate (.record axs) req es = .ok v) :
  ∃ avs, axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs ∧
    v = .record (Map.make avs) := by
  simp only [evaluate,
    List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es))] at h
  cases hm : axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok avs =>
    simp [hm, Bind.bind, Except.bind] at h
    exact ⟨avs, rfl, h.symm⟩

/-- A field list whose head evaluates: the value list splits the same way. -/
theorem mapM_bindAttr_cons {a : Attr} {x : Expr} {rest : List (Attr × Expr)}
  {avs : List (Attr × Value)} {req : Request} {es : Entities}
  (h : ((a, x) :: rest).mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs) :
  ∃ v avs', evaluate x req es = .ok v ∧
    rest.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs' ∧
    avs = (a, v) :: avs' := by
  simp only [List.mapM_cons] at h
  cases hv : evaluate x req es with
  | error e =>
    rw [hv, bindAttr_error, Except.bind_err] at h
    cases h
  | ok v =>
    rw [hv, bindAttr_ok, Except.bind_ok] at h
    cases hr : rest.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) with
    | error e =>
      rw [hr, Except.bind_err] at h
      cases h
    | ok avs' =>
      rw [hr, Except.bind_ok] at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      exact ⟨v, avs', rfl, rfl, h.symm⟩

/-- The entries of an evaluated field list: same keys, evaluated values. -/
theorem mapM_bindAttr_forall₂ {axs : List (Attr × Expr)} {avs : List (Attr × Value)}
  {req : Request} {es : Entities}
  (h : axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs) :
  List.Forall₂ (fun (ax : Attr × Expr) (av : Attr × Value) =>
    ax.1 = av.1 ∧ evaluate ax.2 req es = .ok av.2) axs avs := by
  induction axs generalizing avs with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .nil
  | cons ax rest ih =>
    obtain ⟨v, avs', hv, hr, rfl⟩ := mapM_bindAttr_cons (a := ax.1) (x := ax.2) h
    exact .cons ⟨rfl, hv⟩ (ih hr)

theorem forall₂_keys {axs : List (Attr × Expr)} {avs : List (Attr × Value)} {req : Request}
  {es : Entities}
  (h : List.Forall₂ (fun (ax : Attr × Expr) (av : Attr × Value) =>
    ax.1 = av.1 ∧ evaluate ax.2 req es = .ok av.2) axs avs) :
  axs.map Prod.fst = avs.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [hx.1, ih]

/-! ### Maps with the same keys are equal exactly when their values are -/

/-- With equal, duplicate-free key lists, two `Map.make`s are equal exactly
when their value lists are. -/
theorem make_eq_iff_values {avs bws : List (Attr × Value)}
  (hk : avs.map Prod.fst = bws.map Prod.fst) (hn : (avs.map Prod.fst).Nodup) :
  Map.make avs = Map.make bws ↔ avs.map Prod.snd = bws.map Prod.snd := by
  constructor
  · intro heq
    have hfind : ∀ k, (avs.find? (fun x => x.fst == k)).map Prod.snd =
        (bws.find? (fun x => x.fst == k)).map Prod.snd := by
      intro k
      have := congrArg (fun m => Map.find? m k) heq
      simpa only [Map.make_find?_eq_list_find?] using this
    clear heq
    induction avs generalizing bws with
    | nil => cases bws <;> simp_all
    | cons av avs ih =>
      cases bws with
      | nil => simp at hk
      | cons bw bws =>
        simp only [List.map_cons, List.cons.injEq] at hk
        obtain ⟨hk₁, hk₂⟩ := hk
        simp only [List.map_cons, List.nodup_cons] at hn
        obtain ⟨hnot, hn'⟩ := hn
        have hhead := hfind av.1
        rw [List.find?_cons_of_pos (by simp),
          List.find?_cons_of_pos (by show (bw.fst == av.fst) = true; rw [← hk₁]; simp)] at hhead
        simp only [Option.map_some, Option.some.injEq] at hhead
        simp only [List.map_cons, hhead, List.cons.injEq, true_and]
        apply ih hk₂ hn'
        intro k
        by_cases hkk : k = av.1
        · subst hkk
          have h₁ : avs.find? (fun x => x.fst == av.1) = none := by
            apply List.find?_eq_none.mpr
            intro x hx heq
            have := List.mem_map_of_mem (f := Prod.fst) hx
            exact hnot (beq_iff_eq.mp heq ▸ this)
          have h₂ : bws.find? (fun x => x.fst == av.1) = none := by
            apply List.find?_eq_none.mpr
            intro x hx heq
            have := List.mem_map_of_mem (f := Prod.fst) hx
            rw [← hk₂] at this
            exact hnot (beq_iff_eq.mp heq ▸ this)
          simp [h₁, h₂]
        · have := hfind k
          rw [List.find?_cons_of_neg (by show ¬(av.fst == k) = true; simpa using Ne.symm hkk),
            List.find?_cons_of_neg (by
              show ¬(bw.fst == k) = true
              rw [← hk₁]
              simpa using Ne.symm hkk)] at this
          exact this
  · intro hv
    have : avs = bws := by
      induction avs generalizing bws with
      | nil => cases bws <;> simp_all
      | cons av avs ih =>
        cases bws with
        | nil => simp at hk
        | cons bw bws =>
          simp only [List.map_cons, List.cons.injEq] at hk hv
          simp only [List.map_cons, List.nodup_cons] at hn
          rw [ih hk.2 hn.2 hv.2]
          congr 1
          exact Prod.ext hk.1 hv.1
    rw [this]

/-! ### Evaluated element lists and set literals -/

/-- A set literal's elements evaluate to the elements of its value. -/
theorem evaluate_set_ok {ls : List Expr} {req : Request} {es : Entities} {v : Value}
  (h : evaluate (.set ls) req es = .ok v) :
  ∃ vs, ls.mapM (fun x => evaluate x req es) = .ok vs ∧ v = .set (Set.make vs) := by
  simp only [evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es)] at h
  cases hm : ls.mapM (fun x => evaluate x req es) with
  | error e => simp [hm, Bind.bind, Except.bind] at h
  | ok vs =>
    simp [hm, Bind.bind, Except.bind] at h
    exact ⟨vs, rfl, h.symm⟩

theorem evaluate_set_of_mapM {ls : List Expr} {vs : List Value} {req : Request} {es : Entities}
  (h : ls.mapM (fun x => evaluate x req es) = .ok vs) :
  evaluate (.set ls) req es = .ok (.set (Set.make vs)) := by
  simp [evaluate, List.mapM₁_eq_mapM (fun x => evaluate x req es), h, Bind.bind, Except.bind]

/-- `any` over two lists related elementwise. -/
theorem any_forall₂ {α β} {p : α → β → Prop} {f : α → Bool} {g : β → Bool} {xs : List α}
  {ys : List β} (h : List.Forall₂ p xs ys) (hfg : ∀ x y, p x y → f x = g y) :
  xs.any f = ys.any g := by
  induction h with
  | nil => rfl
  | cons hxy _ ih => simp [hfg _ _ hxy, ih]

/-- Membership in a set literal's value, as `any` over the element values. -/
theorem contains_make_eq_any (vs : List Value) (v : Value) :
  (Set.make vs).contains v = vs.any (fun w => w == v) := by
  rw [Bool.eq_iff_iff, Set.contains_prop_bool_equiv, Set.mem_make, List.any_eq_true]
  constructor
  · intro h
    exact ⟨v, h, by simp⟩
  · rintro ⟨w, hw, hwv⟩
    rw [beq_iff_eq] at hwv
    subst hwv
    exact hw

/-! ### Record equality -/

theorem value_record_beq (m₁ m₂ : Map Attr Value) :
  (Value.record m₁ == Value.record m₂) = (m₁ == m₂) := by
  cases h : m₁ == m₂
  · simp only [beq_eq_false_iff_ne] at h
    simp [beq_eq_false_iff_ne, h]
  · simp only [beq_iff_eq] at h
    simp [h]

theorem evaluate_and_bools {l r : Expr} {b₁ b₂ : Bool} {req : Request} {es : Entities}
  (hl : evaluate l req es = .ok (.prim (.bool b₁))) (hr : evaluate r req es = .ok (.prim (.bool b₂))) :
  evaluate (.and l r) req es = .ok (.prim (.bool (b₁ && b₂))) := by
  cases b₁ <;> simp [evaluate, hl, hr, Result.as, Coe.coe, Value.asBool, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- `andChain` of a non-empty list, one step. -/
theorem andChain_cons (d : Expr) (rest : List Expr) :
  andChain (d :: rest) = if rest = [] then d else .and d (andChain rest) := by
  cases rest <;> simp [andChain]

/-! ### The value-level typing of an equality -/

/-- What the values meeting in an equality must satisfy for the set rules
to be exact: two sets are well formed and element-wise `EqTyped`, two
records field-wise, and a set never meets a non-set. -/
inductive EqTyped : Value → Value → Prop
  | sets {S T : Set Value} (hS : S.WellFormed) (hT : T.WellFormed)
      (h : ∀ s ∈ S, ∀ t ∈ T, EqTyped s t) : EqTyped (.set S) (.set T)
  | records {m₁ m₂ : Map Attr Value}
      (h : ∀ k v₁ v₂, m₁.find? k = some v₁ → m₂.find? k = some v₂ → EqTyped v₁ v₂) :
      EqTyped (.record m₁) (.record m₂)
  | other {v₁ v₂ : Value} (h₁ : ∀ S, v₁ ≠ .set S) (h₂ : ∀ S, v₂ ≠ .set S)
      (hr : ¬ ∃ m₁ m₂, v₁ = .record m₁ ∧ v₂ = .record m₂) : EqTyped v₁ v₂

theorem EqTyped.symm {v₁ v₂ : Value} (h : EqTyped v₁ v₂) : EqTyped v₂ v₁ := by
  induction h with
  | sets hS hT _ ih => exact .sets hT hS (fun t ht s hs => ih s hs t ht)
  | records _ ih => exact .records (fun k v₂ v₁ h₂ h₁ => ih k v₁ v₂ h₁ h₂)
  | other h₁ h₂ hr => exact .other h₂ h₁ (fun ⟨m₂, m₁, e₂, e₁⟩ => hr ⟨m₁, m₂, e₁, e₂⟩)

/-- A set value meets a set value. -/
theorem EqTyped.set_left {S : Set Value} {v : Value} (h : EqTyped (.set S) v) :
  ∃ T, v = .set T ∧ S.WellFormed ∧ T.WellFormed ∧ ∀ s ∈ S, ∀ t ∈ T, EqTyped s t := by
  cases h with
  | sets hS hT h => exact ⟨_, rfl, hS, hT, h⟩
  | other h₁ => exact absurd rfl (h₁ S)

theorem EqTyped.record_both {m₁ m₂ : Map Attr Value} (h : EqTyped (.record m₁) (.record m₂)) :
  ∀ k v₁ v₂, m₁.find? k = some v₁ → m₂.find? k = some v₂ → EqTyped v₁ v₂ := by
  cases h with
  | records h => exact h
  | other _ _ hr => exact absurd ⟨m₁, m₂, rfl, rfl⟩ hr

/-- Field by field, for two evaluated field lists with the same
duplicate-free keys. -/
theorem eqTyped_record_forall₂ {avs bws : List (Attr × Value)}
  (hk : avs.map Prod.fst = bws.map Prod.fst) (hn : (avs.map Prod.fst).Nodup)
  (h : ∀ k v₁ v₂, (Map.make avs).find? k = some v₁ → (Map.make bws).find? k = some v₂ →
    EqTyped v₁ v₂) :
  List.Forall₂ (fun (av bw : Attr × Value) => EqTyped av.2 bw.2) avs bws := by
  match avs, bws with
  | [], [] => exact .nil
  | [], _ :: _ => simp at hk
  | _ :: _, [] => simp at hk
  | (a, v) :: avs', (b, w) :: bws' =>
    simp only [List.map_cons, List.cons.injEq] at hk
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨rfl, hk'⟩ := hk
    refine .cons ?_ (eqTyped_record_forall₂ hk' hn.2 ?_)
    · exact h a v w (by simp [Map.make_find?_eq_list_find?, List.find?_cons])
        (by simp [Map.make_find?_eq_list_find?, List.find?_cons])
    · intro k v₁ v₂ h₁ h₂
      rw [Map.make_find?_eq_list_find?] at h₁ h₂
      have hka : (a == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro hka
        subst hka
        cases hf : avs'.find? (fun x => x.fst == a) with
        | none => simp [hf] at h₁
        | some p =>
          have hp := List.find?_some hf
          have hmem := List.mem_of_find?_eq_some hf
          simp only [beq_iff_eq] at hp
          exact hn.1 (List.mem_map.mpr ⟨p, hmem, hp⟩)
      apply h k v₁ v₂ <;> rw [Map.make_find?_eq_list_find?] <;>
        simp only [List.find?_cons, hka] <;> assumption

/-! ### Set equality: well-formed sets are equal exactly when each contains the other -/

theorem value_set_beq (S T : Set Value) : (Value.set S == Value.set T) = (S == T) := by
  cases h : S == T
  · simp only [beq_eq_false_iff_ne] at h
    simp [beq_eq_false_iff_ne, h]
  · simp only [beq_iff_eq] at h
    simp [h]

theorem subset_both_beq {S T : Set Value} (hS : S.WellFormed) (hT : T.WellFormed) :
  ((T.subset S) && (S.subset T)) = (S == T) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq]
  have hiff : (S ⊆ T ∧ T ⊆ S) ↔ S = T := Set.subset_iff_eq hS hT
  constructor
  · rintro ⟨h₁, h₂⟩
    exact hiff.mp ⟨h₂, h₁⟩
  · intro h
    exact ⟨(hiff.mpr h).2, (hiff.mpr h).1⟩

/-- `any` over two lists related elementwise, with membership. -/
theorem any_forall₂_mem {α β} {p : α → β → Prop} {f : α → Bool} {g : β → Bool} {xs : List α}
  {ys : List β} (h : List.Forall₂ p xs ys) (hfg : ∀ x ∈ xs, ∀ y ∈ ys, p x y → f x = g y) :
  xs.any f = ys.any g := by
  induction h with
  | nil => rfl
  | cons hxy _ ih =>
    simp only [List.any_cons]
    rw [hfg _ List.mem_cons_self _ List.mem_cons_self hxy,
      ih (fun x hx y hy hp => hfg x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hp)]

/-! ### The equality, `contains` and `containsAll` rules, together -/

mutual

/-- `elimEq` evaluates to the equality of its operands' values. -/
theorem elimEq_sound {a b : Expr} {va vb : Value} {req : Request} {es : Entities}
  (ha : evaluate a req es = .ok va) (hb : evaluate b req es = .ok vb) (hty : EqTyped va vb) :
  evaluate (elimEq a b) req es = .ok (.prim (.bool (va == vb))) := by
  rw [elimEq.eq_def]
  split
  next axs bys =>
    obtain ⟨avs, hav, rfl⟩ := evaluate_record_ok ha
    obtain ⟨bws, hbw, rfl⟩ := evaluate_record_ok hb
    split
    next hcond =>
      have hka := forall₂_keys (mapM_bindAttr_forall₂ hav)
      have hkb := forall₂_keys (mapM_bindAttr_forall₂ hbw)
      have hfields := eqTyped_record_forall₂ (hka ▸ hkb ▸ hcond.1) (hka ▸ hcond.2) hty.record_both
      rw [eqFields_sound hcond.1 hcond.2 hav hbw hfields, value_record_beq]
    next => simp [evaluate, ha, hb, apply₂, Bind.bind, Except.bind]
  next ls b =>
    obtain ⟨_, _, rfl⟩ := evaluate_set_ok ha
    exact elimSetEq_sound ha hb hty (.inl ⟨_, rfl⟩)
  next a ls =>
    obtain ⟨_, _, rfl⟩ := evaluate_set_ok hb
    exact elimSetEq_sound ha hb hty (.inr ⟨_, rfl⟩)
  next => simp [evaluate, ha, hb, apply₂, Bind.bind, Except.bind]
termination_by (sizeOf a + sizeOf b, 3)
decreasing_by all_goals elim_decreasing

theorem eqFields_sound {axs bys : List (Attr × Expr)} {avs bws : List (Attr × Value)}
  {req : Request} {es : Entities}
  (hkeys : axs.map Prod.fst = bys.map Prod.fst) (hnodup : (axs.map Prod.fst).Nodup)
  (ha : axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs)
  (hb : bys.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok bws)
  (hty : List.Forall₂ (fun (av bw : Attr × Value) => EqTyped av.2 bw.2) avs bws) :
  evaluate (andChain (eqFields axs bys)) req es =
    .ok (.prim (.bool (Map.make avs == Map.make bws))) := by
  match axs, bys with
  | [], [] =>
    simp [List.mapM_nil, Pure.pure, Except.pure] at ha hb
    subst ha hb
    simp [eqFields, andChain, boolLit, evaluate]
  | [], _ :: _ => simp at hkeys
  | _ :: _, [] => simp at hkeys
  | (a, x) :: axs', (b, y) :: bys' =>
    obtain ⟨vx, avs', hvx, ha', rfl⟩ := mapM_bindAttr_cons ha
    obtain ⟨vy, bws', hvy, hb', rfl⟩ := mapM_bindAttr_cons hb
    simp only [List.map_cons, List.cons.injEq] at hkeys
    simp only [List.map_cons, List.nodup_cons] at hnodup
    cases hty with
    | cons hxy hty' =>
    have hx := elimEq_sound hvx hvy hxy
    have hrest := eqFields_sound hkeys.2 hnodup.2 ha' hb' hty'
    -- the value lists decide the maps
    have hka := forall₂_keys (mapM_bindAttr_forall₂ ha')
    have hkb := forall₂_keys (mapM_bindAttr_forall₂ hb')
    have hk' : avs'.map Prod.fst = bws'.map Prod.fst := by rw [← hka, ← hkb, hkeys.2]
    have hn' : (avs'.map Prod.fst).Nodup := hka ▸ hnodup.2
    have hnot : a ∉ avs'.map Prod.fst := hka ▸ hnodup.1
    have hk : ((a, vx) :: avs').map Prod.fst = ((b, vy) :: bws').map Prod.fst := by
      simp [hk', hkeys.1]
    have hn : (((a, vx) :: avs').map Prod.fst).Nodup := by simp [hnot, hn']
    have hmaps : (Map.make ((a, vx) :: avs') == Map.make ((b, vy) :: bws')) =
        ((vx == vy) && (Map.make avs' == Map.make bws')) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, Bool.and_eq_true, make_eq_iff_values hk hn, make_eq_iff_values hk' hn',
        List.map_cons, List.cons.injEq]
    rw [hmaps]
    simp only [eqFields, andChain_cons]
    split
    next hnil =>
      rw [hnil, andChain] at hrest
      simp only [boolLit, evaluate] at hrest
      have : (Map.make avs' == Map.make bws') = true := by
        have := hrest
        simp only [Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at this
        exact this.symm
      rw [this, Bool.and_true, hx]
    next => exact evaluate_and_bools hx hrest
termination_by (sizeOf axs + sizeOf bys, 0)
decreasing_by all_goals elim_decreasing

/-- `elimSetEq` evaluates to the equality of its operands' values, two
well-formed sets. -/
theorem elimSetEq_sound {a b : Expr} {va vb : Value} {req : Request} {es : Entities}
  (ha : evaluate a req es = .ok va) (hb : evaluate b req es = .ok vb) (hty : EqTyped va vb)
  (hset : (∃ S, va = .set S) ∨ (∃ T, vb = .set T)) :
  evaluate (elimSetEq a b) req es = .ok (.prim (.bool (va == vb))) := by
  have hboth : ∃ S T, va = .set S ∧ vb = .set T ∧ S.WellFormed ∧ T.WellFormed ∧
      ∀ s ∈ S, ∀ t ∈ T, EqTyped s t := by
    rcases hset with ⟨S, rfl⟩ | ⟨T, rfl⟩
    · obtain ⟨T, rfl, hS, hT, h⟩ := hty.set_left
      exact ⟨S, T, rfl, rfl, hS, hT, h⟩
    · obtain ⟨S, rfl, hT, hS, h⟩ := hty.symm.set_left
      exact ⟨S, T, rfl, rfl, hS, hT, fun s hs t ht => (h t ht s hs).symm⟩
  obtain ⟨S, T, rfl, rfl, hS, hT, h⟩ := hboth
  have h₁ := elimContainsAll_sound ha hb h
  have h₂ := elimContainsAll_sound hb ha (fun t ht s hs => (h s hs t ht).symm)
  rw [elimSetEq, evaluate_and_bools h₁ h₂, value_set_beq, subset_both_beq hS hT]
termination_by (sizeOf a + sizeOf b, 2)
decreasing_by all_goals elim_decreasing

/-- `elimContainsAll` evaluates like `s.containsAll(t)` on two sets. -/
theorem elimContainsAll_sound {s t : Expr} {S T : Set Value} {req : Request} {es : Entities}
  (hs : evaluate s req es = .ok (.set S)) (ht : evaluate t req es = .ok (.set T))
  (hty : ∀ a ∈ S, ∀ b ∈ T, EqTyped a b) :
  evaluate (elimContainsAll s t) req es = .ok (.prim (.bool (T.subset S))) := by
  rw [elimContainsAll.eq_def]
  split
  next ls =>
    obtain ⟨vs, hvs, hT⟩ := evaluate_set_ok ht
    simp only [Value.set.injEq] at hT
    subst hT
    rw [containsAll_lit_sound hs hvs (fun a ha vl hvl => hty a ha vl ((Set.mem_make _ _).mpr hvl))]
    simp only [evaluate, hs, evaluate_set_of_mapM hvs, apply₂, Bind.bind, Except.bind]
  next => simp only [evaluate, hs, ht, apply₂, Bind.bind, Except.bind]
termination_by (sizeOf s + sizeOf t, 1)
decreasing_by all_goals elim_decreasing

theorem containsAll_lit_sound {s : Expr} {ls : List Expr} {S : Set Value} {vs : List Value}
  {req : Request} {es : Entities}
  (hs : evaluate s req es = .ok (.set S)) (hls : ls.mapM (fun x => evaluate x req es) = .ok vs)
  (hty : ∀ a ∈ S, ∀ vl ∈ vs, EqTyped a vl) :
  evaluate (andChain (ls.map (elimContains s))) req es =
    evaluate (.binaryApp .containsAll s (.set ls)) req es := by
  have hf := List.mapM_ok_iff_forall₂.mp hls
  have hbools : ∀ d ∈ ls.map (elimContains s), ∃ b, evaluate d req es = .ok (.prim (.bool b)) := by
    intro d hd
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    obtain ⟨vl, hvlmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    have hsz := List.sizeOf_lt_of_mem hl
    exact ⟨_, elimContains_ok hs hvl (fun a ha => hty a ha vl hvlmem)⟩
  rw [evaluate_andChain_bools hbools]
  simp only [evaluate, hs, evaluate_set_of_mapM hls, apply₂, Bind.bind, Except.bind]
  congr 3
  rw [List.all_map, Bool.eq_iff_iff, List.all_eq_true]
  show _ ↔ Set.make vs ⊆ S
  rw [Set.subset_def]
  constructor
  · intro h w hw
    rw [Set.mem_make] at hw
    obtain ⟨l, hl, hvl⟩ := List.forall₂_implies_all_right hf w hw
    have := h l hl
    have hsz := List.sizeOf_lt_of_mem hl
    simp only [Function.comp, isTrue, elimContains_ok hs hvl (fun a ha => hty a ha w hw)] at this
    rcases hb : S.contains w with _ | _
    · simp [hb] at this
    · exact Set.contains_prop_bool_equiv.mp hb
  · intro h l hl
    obtain ⟨vl, hvlmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    have hmem : vl ∈ Set.make vs := (Set.mem_make _ _).mpr hvlmem
    have hsz := List.sizeOf_lt_of_mem hl
    simp only [Function.comp, isTrue, elimContains_ok hs hvl (fun a ha => hty a ha vl hvlmem),
      Set.contains_prop_bool_equiv.mpr (h vl hmem)]
    rfl
termination_by (sizeOf s + sizeOf ls, 1)
decreasing_by all_goals elim_decreasing

/-- On a set-typed left operand, `elimContains` evaluates to a boolean. -/
theorem elimContains_ok {s x : Expr} {S : Set Value} {v : Value} {req : Request} {es : Entities}
  (hs : evaluate s req es = .ok (.set S)) (hx : evaluate x req es = .ok v)
  (hty : ∀ a ∈ S, EqTyped a v) :
  evaluate (elimContains s x) req es = .ok (.prim (.bool (S.contains v))) := by
  rw [elimContains.eq_def]
  split
  next ls =>
    obtain ⟨ws, hws, hS⟩ := evaluate_set_ok hs
    simp only [Value.set.injEq] at hS
    subst hS
    exact contains_lit_sound hws hx (fun vl hvl => hty vl ((Set.mem_make _ _).mpr hvl))
  next => simp [evaluate, hs, hx, apply₂, Bind.bind, Except.bind]
termination_by (sizeOf s + sizeOf x, 1)
decreasing_by all_goals elim_decreasing

/-- `[l₁, …].contains(x)` as the disjunction of the element equalities. -/
theorem contains_lit_sound {ls : List Expr} {x : Expr} {vs : List Value} {v : Value}
  {req : Request} {es : Entities}
  (hls : ls.mapM (fun x => evaluate x req es) = .ok vs) (hx : evaluate x req es = .ok v)
  (hty : ∀ vl ∈ vs, EqTyped vl v) :
  evaluate (orChain (ls.map (fun l => elimEq l x))) req es =
    .ok (.prim (.bool ((Set.make vs).contains v))) := by
  have hf := List.mapM_ok_iff_forall₂.mp hls
  have hbools : ∀ d ∈ ls.map (fun l => elimEq l x), ∃ b, evaluate d req es = .ok (.prim (.bool b)) := by
    intro d hd
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    obtain ⟨vl, hvlmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    have hsz := List.sizeOf_lt_of_mem hl
    exact ⟨_, elimEq_sound hvl hx (hty vl hvlmem)⟩
  rw [evaluate_orChain_bools hbools, contains_make_eq_any, List.any_map]
  congr 3
  exact any_forall₂_mem hf (fun l hl vl hvlmem hvl => by
    have hsz := List.sizeOf_lt_of_mem hl
    simp only [Function.comp, isTrue, elimEq_sound hvl hx (hty vl hvlmem)]
    cases vl == v <;> simp)
termination_by (sizeOf ls + sizeOf x, 0)
decreasing_by all_goals elim_decreasing

end

/-! ### `containsAny` with a set literal -/

theorem containsAny_lit_sound {s : Expr} {ls : List Expr} {S : Set Value} {vs : List Value}
  {req : Request} {es : Entities}
  (hs : evaluate s req es = .ok (.set S)) (hls : ls.mapM (fun x => evaluate x req es) = .ok vs)
  (hty : ∀ a ∈ S, ∀ vl ∈ vs, EqTyped a vl) :
  evaluate (orChain (ls.map (elimContains s))) req es =
    evaluate (.binaryApp .containsAny s (.set ls)) req es := by
  have hf := List.mapM_ok_iff_forall₂.mp hls
  have hbools : ∀ d ∈ ls.map (elimContains s), ∃ b, evaluate d req es = .ok (.prim (.bool b)) := by
    intro d hd
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    obtain ⟨vl, hvlmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    have hsz := List.sizeOf_lt_of_mem hl
    exact ⟨_, elimContains_ok hs hvl (fun a ha => hty a ha vl hvlmem)⟩
  rw [evaluate_orChain_bools hbools]
  simp only [evaluate, hs, evaluate_set_of_mapM hls, apply₂, Bind.bind, Except.bind]
  congr 3
  rw [List.any_map, Bool.eq_iff_iff, List.any_eq_true, Set.intersects_iff_exists]
  constructor
  · rintro ⟨l, hl, hl'⟩
    obtain ⟨vl, hvlmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    simp only [Function.comp, isTrue, elimContains_ok hs hvl (fun a ha => hty a ha vl hvlmem)] at hl'
    rcases hb : S.contains vl with _ | _
    · simp [hb] at hl'
    · exact ⟨vl, Set.contains_prop_bool_equiv.mp hb, (Set.mem_make _ _).mpr hvlmem⟩
  · rintro ⟨w, hwS, hw⟩
    rw [Set.mem_make] at hw
    obtain ⟨l, hl, hvl⟩ := List.forall₂_implies_all_right hf w hw
    refine ⟨l, hl, ?_⟩
    simp only [Function.comp, isTrue, elimContains_ok hs hvl (fun a ha => hty a ha w hw),
      Set.contains_prop_bool_equiv.mpr hwS]
    rfl

/-- The symmetric case, `[…].containsAny(s)`. -/
theorem containsAny_lit_sound' {s : Expr} {ls : List Expr} {S : Set Value} {vs : List Value}
  {req : Request} {es : Entities}
  (hs : evaluate s req es = .ok (.set S)) (hls : ls.mapM (fun x => evaluate x req es) = .ok vs)
  (hty : ∀ a ∈ S, ∀ vl ∈ vs, EqTyped a vl) :
  evaluate (orChain (ls.map (elimContains s))) req es =
    evaluate (.binaryApp .containsAny (.set ls) s) req es := by
  rw [containsAny_lit_sound hs hls hty]
  simp only [evaluate, hs, evaluate_set_of_mapM hls, apply₂, Bind.bind, Except.bind]
  congr 3
  rw [Bool.eq_iff_iff, Set.intersects_iff_exists, Set.intersects_iff_exists]
  constructor <;> rintro ⟨a, h₁, h₂⟩ <;> exact ⟨a, h₂, h₁⟩

/-! ### `isEmpty` on a set literal -/

theorem isEmpty_lit_sound {ls : List Expr} {vs : List Value} {req : Request} {es : Entities}
  (hls : ls.mapM (fun x => evaluate x req es) = .ok vs) :
  evaluate (boolLit ls.isEmpty) req es = evaluate (.unaryApp .isEmpty (.set ls)) req es := by
  have hf := List.mapM_ok_iff_forall₂.mp hls
  simp only [evaluate, evaluate_set_of_mapM hls, apply₁, Bind.bind, Except.bind, boolLit]
  congr 3
  rw [Bool.eq_iff_iff, List.isEmpty_iff]
  show ls = [] ↔ (Set.make vs).isEmpty = true
  rw [Set.isEmpty_make]
  cases hf <;> simp

/-! ### `.attr` and `has` on a record literal -/

/-- The first field named `a` of an evaluated field list. -/
theorem find?_forall₂ {axs : List (Attr × Expr)} {avs : List (Attr × Value)} {a : Attr}
  {req : Request} {es : Entities}
  (h : List.Forall₂ (fun (ax : Attr × Expr) (av : Attr × Value) =>
    ax.1 = av.1 ∧ evaluate ax.2 req es = .ok av.2) axs avs) :
  (avs.find? (fun av => av.1 == a)).map Prod.snd =
    (axs.find? (fun ax => ax.1 == a)).bind (fun ax => (evaluate ax.2 req es).toOption) := by
  induction h with
  | nil => rfl
  | @cons x y xs ys hx _ ih =>
    by_cases hk : x.1 = a
    · rw [List.find?_cons_of_pos (a := y) (by simp [← hx.1, hk]),
        List.find?_cons_of_pos (a := x) (by simp [hk])]
      simp [hx.2, Except.toOption]
    · rw [List.find?_cons_of_neg (a := y) (by simpa [← hx.1] using hk),
        List.find?_cons_of_neg (a := x) (by simpa using hk)]
      exact ih

theorem getAttr_lit_sound {axs : List (Attr × Expr)} {avs : List (Attr × Value)} {a : Attr}
  {x : Expr} {req : Request} {es : Entities}
  (hav : axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs)
  (hget : recordGet axs a = some x) :
  evaluate x req es = evaluate (.getAttr (.record axs) a) req es := by
  have hf := mapM_bindAttr_forall₂ hav
  have hfind := find?_forall₂ (a := a) hf
  simp only [recordGet, Option.map_eq_some_iff] at hget
  obtain ⟨ax, hax, rfl⟩ := hget
  rw [hax] at hfind
  obtain ⟨vx, hvx⟩ : ∃ vx, evaluate ax.2 req es = .ok vx := by
    have hmem := List.mem_of_find?_eq_some hax
    obtain ⟨av, _, hav'⟩ := List.forall₂_implies_all_left hf ax hmem
    exact ⟨av.2, hav'.2⟩
  simp only [hvx, Option.bind_some, Except.toOption] at hfind
  have hrec : evaluate (.record axs) req es = .ok (.record (Map.make avs)) := by
    simp [evaluate,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)), hav,
      Bind.bind, Except.bind]
  simp only [evaluate, hrec, Bind.bind, Except.bind, getAttr, attrsOf, Map.findOrErr,
    Map.make_find?_eq_list_find?]
  rw [hfind, hvx]

theorem hasAttr_lit_sound {axs : List (Attr × Expr)} {avs : List (Attr × Value)} {a : Attr}
  {req : Request} {es : Entities}
  (hav : axs.mapM (fun ax => bindAttr ax.1 (evaluate ax.2 req es)) = .ok avs) :
  evaluate (boolLit (recordHas axs a)) req es = evaluate (.hasAttr (.record axs) a) req es := by
  have hf := mapM_bindAttr_forall₂ hav
  have hrec : evaluate (.record axs) req es = .ok (.record (Map.make avs)) := by
    simp [evaluate,
      List.mapM₂_eq_mapM (fun (ax : Attr × Expr) => bindAttr ax.1 (evaluate ax.2 req es)), hav,
      Bind.bind, Except.bind]
  simp only [evaluate, hrec, Bind.bind, Except.bind, hasAttr, attrsOf, boolLit]
  congr 3
  rw [Bool.eq_iff_iff, Map.contains_iff_some_find?, Map.make_find?_eq_list_find?, find?_forall₂ hf]
  simp only [recordHas, List.any_eq_true]
  constructor
  · rintro ⟨ax, hax, hk⟩
    have hsome : (axs.find? (fun ax => ax.1 == a)).isSome := List.find?_isSome.mpr ⟨ax, hax, hk⟩
    obtain ⟨ax', hfind⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨av, _, hrel⟩ := List.forall₂_implies_all_left hf ax' (List.mem_of_find?_eq_some hfind)
    exact ⟨av.2, by rw [hfind, Option.bind_some, hrel.2]; rfl⟩
  · rintro ⟨v, hv⟩
    obtain ⟨ax, hfind, _⟩ := Option.bind_eq_some_iff.mp hv
    exact ⟨ax, List.mem_of_find?_eq_some hfind, List.find?_some (p := fun (ax : Attr × Expr) => ax.fst == a) hfind⟩


/-! ### `in` over a set literal -/

/-- Entity-valued elements map to their ids: the set-level `mapOrErr` succeeds
and its result has exactly the elements' ids. -/
theorem mapOrErr_entities {vs : List Value} (hent : ∀ v ∈ vs, ∃ u, v = .prim (.entityUID u)) :
  ∃ us : Set EntityUID, (Set.make vs).mapOrErr Value.asEntityUID Error.typeError = .ok us ∧
    ∀ u, u ∈ us ↔ Value.prim (.entityUID u) ∈ vs := by
  have hall : ∀ v ∈ (Set.make vs).elts, ∃ u, Value.asEntityUID v = .ok u := by
    intro v hv
    rw [Set.mem_elts_iff_mem_set, Set.mem_make] at hv
    obtain ⟨u, rfl⟩ := hent v hv
    exact ⟨u, rfl⟩
  obtain ⟨us, hus⟩ := List.all_ok_implies_mapM_ok hall
  have hf := List.mapM_ok_iff_forall₂.mp hus
  refine ⟨Set.make us, by simp [Set.mapOrErr, hus], ?_⟩
  intro u
  rw [Set.mem_make]
  constructor
  · intro hu
    obtain ⟨v, hv, hvu⟩ := List.forall₂_implies_all_right hf u hu
    rw [Set.mem_elts_iff_mem_set, Set.mem_make] at hv
    obtain ⟨u', rfl⟩ := hent v hv
    simp only [Value.asEntityUID, Except.ok.injEq] at hvu
    exact hvu ▸ hv
  · intro hv
    have hv' : Value.prim (.entityUID u) ∈ (Set.make vs).elts := by
      rw [Set.mem_elts_iff_mem_set, Set.mem_make]; exact hv
    obtain ⟨u', hu', hvu⟩ := List.forall₂_implies_all_left hf _ hv'
    simp only [Value.asEntityUID, Except.ok.injEq] at hvu
    exact hvu ▸ hu'

theorem mem_lit_sound {e : Expr} {xs : List Expr} {uid : EntityUID} {vs : List Value}
  {req : Request} {es : Entities}
  (he : evaluate e req es = .ok (.prim (.entityUID uid)))
  (hxs : xs.mapM (fun x => evaluate x req es) = .ok vs)
  (hent : ∀ v ∈ vs, ∃ u, v = .prim (.entityUID u)) :
  evaluate (orChain (xs.map (fun x => .binaryApp .mem e x))) req es =
    evaluate (.binaryApp .mem e (.set xs)) req es := by
  have hf := List.mapM_ok_iff_forall₂.mp hxs
  have hdisj : ∀ l vl, evaluate l req es = .ok vl → vl ∈ vs →
      ∃ u, vl = .prim (.entityUID u) ∧
        evaluate (.binaryApp .mem e l) req es = .ok (.prim (.bool (inₑ uid u es))) := by
    intro l vl hvl hmem
    obtain ⟨u, rfl⟩ := hent vl hmem
    exact ⟨u, rfl, by simp [evaluate, he, hvl, apply₂, Bind.bind, Except.bind]⟩
  have hbools : ∀ d ∈ xs.map (fun x => .binaryApp .mem e x),
      ∃ b, evaluate d req es = .ok (.prim (.bool b)) := by
    intro d hd
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hd
    obtain ⟨vl, hmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    obtain ⟨u, _, h⟩ := hdisj l vl hvl hmem
    exact ⟨_, h⟩
  rw [evaluate_orChain_bools hbools]
  obtain ⟨us, hus, hmem⟩ := mapOrErr_entities hent
  simp only [evaluate, he, evaluate_set_of_mapM hxs, apply₂, Bind.bind, Except.bind, inₛ, hus]
  congr 3
  rw [List.any_map, Bool.eq_iff_iff, List.any_eq_true, Set.any_eq_true]
  constructor
  · rintro ⟨l, hl, hl'⟩
    obtain ⟨vl, hvmem, hvl⟩ := List.forall₂_implies_all_left hf l hl
    obtain ⟨u, rfl, h⟩ := hdisj l vl hvl hvmem
    simp only [Function.comp, isTrue, h] at hl'
    refine ⟨u, (hmem u).mpr hvmem, ?_⟩
    rcases hb : inₑ uid u es with _ | _
    · simp [hb] at hl'
    · rfl
  · rintro ⟨u, hu, hin⟩
    have hvmem := (hmem u).mp hu
    obtain ⟨l, hl, hvl⟩ := List.forall₂_implies_all_right hf _ hvmem
    obtain ⟨u', hu', h⟩ := hdisj l _ hvl hvmem
    simp only [Value.prim.injEq, Prim.entityUID.injEq] at hu'
    subst hu'
    refine ⟨l, hl, ?_⟩
    simp only [Function.comp, isTrue, h, hin]
    rfl

end Cedar.DNF
