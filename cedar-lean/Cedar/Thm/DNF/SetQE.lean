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

import Cedar.Thm.Data.Set

/-!
The set quantifier-elimination matrix (Phase 4; plan 13): two ANDed Cedar set
atoms share a variable, the variable is existentially quantified away, and the
pair is replaced by one Cedar operation over the remaining variables. Every
cell below is either **exact** (`↔`, a theorem), or **inexpressible** — no
boolean combination of the Cedar atoms over the remaining variables agrees
with it on every well-formed input (a theorem too, by a distinguishing pair)
— with the tightest implied over-approximation (`⇒`) proved alongside.

The atoms are the Bool functions `Spec.apply₁`/`apply₂` use, on well-formed
sets (every evaluated set is: `Set.make_wf`): `S.isEmpty()` is `S.isEmpty`,
`S == T` is `S == T` (list equality; "same members" for well-formed sets),
`S.contains(e)` is `S.contains e`, `S.containsAll(T)` is `T.subset S`, and
`S.containsAny(T)` is `S.intersects T`. Validated Cedar fixes the types, so the
quantified variable is a set `X` (in any atom but the element position of
`contains`) or an element `x` (only in `A.contains(x)`). Up to the symmetry of
`&&`, that leaves 12 literals over `X` — 78 unordered pairs — and 3 pairs over
`x`: **81 cells**.

| id            | Cedar              | meaning                     |
| ------------- | ------------------ | --------------------------- |
| `E` / `¬E`    | `X.isEmpty()`      | `X = ∅` / `X ≠ ∅`           |
| `Q` / `¬Q`    | `X == A`           | `X = A` / `X ≠ A`           |
| `C` / `¬C`    | `X.contains(e)`    | `e ∈ X` / `e ∉ X`           |
| `Sub` / `¬Sub`| `A.containsAll(X)` | `X ⊆ A` / `X ⊄ A`           |
| `Sup` / `¬Sup`| `X.containsAll(A)` | `A ⊆ X` / `A ⊄ X`           |
| `I` / `¬I`    | `X.containsAny(A)` | `X ∩ A ≠ ∅` / `X ∩ A = ∅`   |
| `M` / `¬M`    | `A.contains(x)`    | `x ∈ A` / `x ∉ A`           |

A repeated shape uses `B` (or `f`) for its second operand. Some cells depend
on the size of the element type: `H1` = `Nonempty α`; `H2` = two distinct
elements (`TwoElems α`; `Bool` has them, a one-member enum entity type does
not); `H∞` = every finite set misses an element (`Unbounded α`; strings and
entity types, not `Bool`/`Long`/the extension types). A hypothesis is needed
for exactness only; the `⇒` direction is unconditional, and where the cell has
a hypothesis-free characterization it is the `_iff` theorem the `H∞` corollary
follows from.

| #  | pair              | result                                    | theorem |
| -- | ----------------- | ----------------------------------------- | ------- |
| 1  | `E ∧ E`           | `true`                                    | `qe_e_e` |
| 2  | `E ∧ ¬E`          | `false`                                   | `qe_e_ne` |
| 3  | `E ∧ Q`           | `A.isEmpty()`                             | `qe_e_q` |
| 4  | `E ∧ ¬Q`          | `!A.isEmpty()`                            | `qe_e_nq` |
| 5  | `E ∧ C`           | `false`                                   | `qe_e_c` |
| 6  | `E ∧ ¬C`          | `true`                                    | `qe_e_nc` |
| 7  | `E ∧ Sub`         | `true`                                    | `qe_e_sub` |
| 8  | `E ∧ ¬Sub`        | `false`                                   | `qe_e_nsub` |
| 9  | `E ∧ Sup`         | `A.isEmpty()`                             | `qe_e_sup` |
| 10 | `E ∧ ¬Sup`        | `!A.isEmpty()`                            | `qe_e_nsup` |
| 11 | `E ∧ I`           | `false`                                   | `qe_e_i` |
| 12 | `E ∧ ¬I`          | `true`                                    | `qe_e_ni` |
| 13 | `¬E ∧ ¬E`         | `true` [H1]                               | `qe_ne_ne` |
| 14 | `¬E ∧ Q`          | `!A.isEmpty()`                            | `qe_ne_q` |
| 15 | `¬E ∧ ¬Q`         | `true` [H2]                               | `qe_ne_nq` |
| 16 | `¬E ∧ C`          | `true`                                    | `qe_ne_c` |
| 17 | `¬E ∧ ¬C`         | `true` [H2]                               | `qe_ne_nc` |
| 18 | `¬E ∧ Sub`        | `!A.isEmpty()`                            | `qe_ne_sub` |
| 19 | `¬E ∧ ¬Sub`       | `true` [H∞] (`∃ u ∉ A`)                   | `qe_ne_nsub`, `_iff` |
| 20 | `¬E ∧ Sup`        | `true` [H1]                               | `qe_ne_sup` |
| 21 | `¬E ∧ ¬Sup`       | `!A.isEmpty()` [H2]                       | `qe_ne_nsup`, `_over` |
| 22 | `¬E ∧ I`          | `!A.isEmpty()`                            | `qe_ne_i` |
| 23 | `¬E ∧ ¬I`         | `true` [H∞] (`∃ u ∉ A`)                   | `qe_ne_ni`, `_iff` |
| 24 | `Q_A ∧ Q_B`       | `A == B`                                  | `qe_q_q` |
| 25 | `Q_A ∧ ¬Q_B`      | `A != B`                                  | `qe_q_nq` |
| 26 | `Q ∧ C`           | `A.contains(e)`                           | `qe_q_c` |
| 27 | `Q ∧ ¬C`          | `!A.contains(e)`                          | `qe_q_nc` |
| 28 | `Q_A ∧ Sub_B`     | `B.containsAll(A)`                        | `qe_q_sub` |
| 29 | `Q_A ∧ ¬Sub_B`    | `!B.containsAll(A)`                       | `qe_q_nsub` |
| 30 | `Q_A ∧ Sup_B`     | `A.containsAll(B)`                        | `qe_q_sup` |
| 31 | `Q_A ∧ ¬Sup_B`    | `!A.containsAll(B)`                       | `qe_q_nsup` |
| 32 | `Q_A ∧ I_B`       | `A.containsAny(B)`                        | `qe_q_i` |
| 33 | `Q_A ∧ ¬I_B`      | `!A.containsAny(B)`                       | `qe_q_ni` |
| 34 | `¬Q_A ∧ ¬Q_B`     | `true` [H2]                               | `qe_nq_nq` |
| 35 | `¬Q ∧ C`          | `true` [H2]                               | `qe_nq_c` |
| 36 | `¬Q ∧ ¬C`         | `true` [H2]                               | `qe_nq_nc` |
| 37 | `¬Q_A ∧ Sub_B`    | `!A.isEmpty() \|\| !B.isEmpty()` (compound) | `qe_nq_sub` |
| 38 | `¬Q_A ∧ ¬Sub_B`   | `true` [H∞]                               | `qe_nq_nsub` |
| 39 | `¬Q_A ∧ Sup_B`    | `true` [H∞]                               | `qe_nq_sup` |
| 40 | `¬Q_A ∧ ¬Sup_B`   | `!B.isEmpty()` [H2]                       | `qe_nq_nsup`, `_over` |
| 41 | `¬Q_A ∧ I_B`      | `!B.isEmpty()` [H2]                       | `qe_nq_i`, `_over` |
| 42 | `¬Q_A ∧ ¬I_B`     | `true` [H∞]                               | `qe_nq_ni` |
| 43 | `C_e ∧ C_f`       | `true`                                    | `qe_c_c` |
| 44 | `C_e ∧ ¬C_f`      | `e != f`                                  | `qe_c_nc` |
| 45 | `C ∧ Sub`         | `A.contains(e)`                           | `qe_c_sub` |
| 46 | `C ∧ ¬Sub`        | `true` [H∞] (`∃ u ∉ A`)                   | `qe_c_nsub`, `_iff` |
| 47 | `C ∧ Sup`         | `true`                                    | `qe_c_sup` |
| 48 | `C ∧ ¬Sup`        | `![e].containsAll(A)` (literal); literal-free: **inexpressible**, `⇒ !A.isEmpty()` | `qe_c_nsup_lit`, `_inexpressible`, `_over` |
| 49 | `C ∧ I`           | `!A.isEmpty()`                            | `qe_c_i` |
| 50 | `C ∧ ¬I`          | `!A.contains(e)`                          | `qe_c_ni` |
| 51 | `¬C_e ∧ ¬C_f`     | `true`                                    | `qe_nc_nc` |
| 52 | `¬C ∧ Sub`        | `true`                                    | `qe_nc_sub` |
| 53 | `¬C ∧ ¬Sub`       | `true` [H∞] (`∃ u ∉ A, u ≠ e`)            | `qe_nc_nsub`, `_iff` |
| 54 | `¬C ∧ Sup`        | `!A.contains(e)`                          | `qe_nc_sup` |
| 55 | `¬C ∧ ¬Sup`       | `!A.isEmpty()`                            | `qe_nc_nsup` |
| 56 | `¬C ∧ I`          | `![e].containsAll(A)` (literal); literal-free: **inexpressible**, `⇒ !A.isEmpty()` | `qe_nc_i_lit`, `_inexpressible`, `_over` |
| 57 | `¬C ∧ ¬I`         | `true`                                    | `qe_nc_ni` |
| 58 | `Sub_A ∧ Sub_B`   | `true`                                    | `qe_sub_sub` |
| 59 | `Sub_A ∧ ¬Sub_B`  | `!B.containsAll(A)`                       | `qe_sub_nsub` |
| 60 | `Sub_A ∧ Sup_B`   | `A.containsAll(B)`                        | `qe_sub_sup` |
| 61 | `Sub_A ∧ ¬Sup_B`  | `!B.isEmpty()`                            | `qe_sub_nsup` |
| 62 | `Sub_A ∧ I_B`     | `A.containsAny(B)`                        | `qe_sub_i` |
| 63 | `Sub_A ∧ ¬I_B`    | `true`                                    | `qe_sub_ni` |
| 64 | `¬Sub_A ∧ ¬Sub_B` | `true` [H∞] (`∃ u ∉ A, ∃ v ∉ B`)          | `qe_nsub_nsub`, `_iff` |
| 65 | `¬Sub_A ∧ Sup_B`  | `true` [H∞]                               | `qe_nsub_sup` |
| 66 | `¬Sub_A ∧ ¬Sup_B` | `!B.isEmpty()` [H∞]                       | `qe_nsub_nsup`, `_over` |
| 67 | `¬Sub_A ∧ I_B`    | `!B.isEmpty()` [H∞]                       | `qe_nsub_i`, `_over` |
| 68 | `¬Sub_A ∧ ¬I_B`   | `true` [H∞] (`∃ u ∉ A ∪ B`)               | `qe_nsub_ni`, `_iff` |
| 69 | `Sup_A ∧ Sup_B`   | `true`                                    | `qe_sup_sup` |
| 70 | `Sup_A ∧ ¬Sup_B`  | `!A.containsAll(B)`                       | `qe_sup_nsup` |
| 71 | `Sup_A ∧ I_B`     | `!B.isEmpty()`                            | `qe_sup_i` |
| 72 | `Sup_A ∧ ¬I_B`    | `!A.containsAny(B)`                       | `qe_sup_ni` |
| 73 | `¬Sup_A ∧ ¬Sup_B` | `!A.isEmpty() && !B.isEmpty()` (compound) | `qe_nsup_nsup` |
| 74 | `¬Sup_A ∧ I_B`    | **inexpressible** (exact: `A ≠ ∅ ∧ B ≠ ∅ ∧ ¬(A = B ∧ A = {a})`); `⇒ !A.isEmpty() && !B.isEmpty()` | `qe_nsup_i_iff`, `_inexpressible`, `_over` |
| 75 | `¬Sup_A ∧ ¬I_B`   | `!A.isEmpty()`                            | `qe_nsup_ni` |
| 76 | `I_A ∧ I_B`       | `!A.isEmpty() && !B.isEmpty()` (compound) | `qe_i_i` |
| 77 | `I_A ∧ ¬I_B`      | `!B.containsAll(A)`                       | `qe_i_ni` |
| 78 | `¬I_A ∧ ¬I_B`     | `true`                                    | `qe_ni_ni` |
| 79 | `M_A ∧ M_B`       | `A.containsAny(B)`                        | `qe_m_m` |
| 80 | `M_A ∧ ¬M_B`      | `!B.containsAll(A)`                       | `qe_m_nm` |
| 81 | `¬M_A ∧ ¬M_B`     | `true` [H∞] (`∃ u ∉ A ∪ B`)               | `qe_nm_nm`, `_iff` |

Inexpressibility is stated against the *atom vector* of the free variables
(`atoms2 A B`: the six Cedar atoms typeable over two sets; `atoms1e A e`: the
two over a set and an element): a target no `f : Atoms → Bool` matches on all
well-formed inputs is beyond every boolean combination of Cedar atoms, not
just beyond a single one. The over-approximations of those cells are tight in
that language: the atom vector of every positive instance already forces them.
-/

namespace Cedar.DNF

open Cedar.Data

/-! ### Domain hypotheses -/

/-- `H2`: two distinct elements. -/
abbrev TwoElems (α : Type) : Prop := ∃ a b : α, a ≠ b

/-- `H∞`: every (finite) set misses some element. -/
def Unbounded (α : Type) : Prop := ∀ S : Set α, ∃ u : α, u ∉ S

theorem TwoElems.exists_ne {α : Type} (h2 : TwoElems α) (b : α) : ∃ u : α, u ≠ b := by
  obtain ⟨a, a', haa'⟩ := h2
  by_cases hab : a = b
  · exact ⟨a', fun h => haa' (hab.trans h.symm)⟩
  · exact ⟨a, hab⟩

/-! ### Atoms as membership

The Cedar atoms in `= true` / `= false` form, rewritten to their membership
meaning; `unfold_atoms` applies them all. -/

theorem isEmpty_true_iff {α : Type} [DecidableEq α] {S : Set α} :
  S.isEmpty = true ↔ ∀ x, x ∉ S := by
  rw [Set.empty_iff_not_exists, not_exists]

theorem isEmpty_false_iff {α : Type} [DecidableEq α] {S : Set α} :
  S.isEmpty = false ↔ ∃ x, x ∈ S := by
  rw [← Bool.not_eq_true, Set.non_empty_iff_exists]

theorem beq_true_iff_eq {α : Type} [DecidableEq α] {S T : Set α} :
  (S == T) = true ↔ S = T := beq_iff_eq

theorem beq_false_iff_ne {α : Type} [DecidableEq α] {S T : Set α} :
  (S == T) = false ↔ S ≠ T := by
  rw [← Bool.not_eq_true, beq_iff_eq]

theorem subset_true_iff {α : Type} [DecidableEq α] {S T : Set α} :
  S.subset T = true ↔ ∀ x, x ∈ S → x ∈ T :=
  Set.subset_def

theorem subset_false_iff {α : Type} [DecidableEq α] {S T : Set α} :
  S.subset T = false ↔ ∃ x, x ∈ S ∧ x ∉ T := by
  rw [← Bool.not_eq_true, subset_true_iff]
  constructor
  · intro h
    by_contra hc
    exact h fun x hx => Classical.byContradiction fun hnT => hc ⟨x, hx, hnT⟩
  · rintro ⟨x, hx, hxT⟩ h
    exact hxT (h x hx)

theorem intersects_true_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {S T : Set α} :
  S.intersects T = true ↔ ∃ x, x ∈ S ∧ x ∈ T :=
  Set.intersects_iff_exists

theorem intersects_false_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {S T : Set α} :
  S.intersects T = false ↔ ∀ x, x ∈ S → x ∉ T := by
  rw [← Bool.not_eq_true, Set.intersects_iff_exists]
  simp only [not_exists, not_and]

/-- Every Cedar atom of the goal, as membership. -/
macro "unfold_atoms" : tactic =>
  `(tactic| simp only [isEmpty_true_iff, isEmpty_false_iff, beq_true_iff_eq, beq_false_iff_ne,
      Set.contains_prop_bool_equiv, Set.not_contains_prop_bool_equiv,
      subset_true_iff, subset_false_iff, intersects_true_iff, intersects_false_iff])

/-! ### Witnesses -/

theorem forall_mem_empty {α : Type} {P : α → Prop} : ∀ x, x ∈ (Set.empty : Set α) → P x :=
  fun x hx => absurd hx (Set.not_mem_empty x)

theorem eq_empty_of_forall_not_mem {α : Type} [DecidableEq α] {S : Set α}
  (h : ∀ x, x ∉ S) : S = Set.empty :=
  Set.isEmpty_iff_eq_empty.mp (isEmpty_true_iff.mpr h)

theorem ne_empty_of_mem {α : Type} {S : Set α} {x : α} (h : x ∈ S) : S ≠ Set.empty :=
  fun heq => Set.not_mem_empty x (heq ▸ h)

theorem ne_of_mem_of_not_mem {α : Type} {S T : Set α} {x : α} (h₁ : x ∈ S) (h₂ : x ∉ T) :
  S ≠ T :=
  fun heq => h₂ (heq ▸ h₁)

theorem mem_singleton_iff {α : Type} [DecidableEq α] {x e : α} :
  x ∈ Set.singleton e ↔ x = e := Set.mem_singleton x e

theorem not_mem_singleton {α : Type} [DecidableEq α] {x e : α} (h : x ≠ e) :
  x ∉ Set.singleton e :=
  fun hx => h (mem_singleton_iff.mp hx)

theorem singleton_subset_of_mem {α : Type} [DecidableEq α] {A : Set α} {e : α} (h : e ∈ A) :
  ∀ x, x ∈ Set.singleton e → x ∈ A := by
  intro x hx
  rw [mem_singleton_iff.mp hx]
  exact h

theorem mem_make_pair {α : Type} [LT α] [DecidableLT α] [StrictLT α] {e f x : α} :
  x ∈ Set.make [e, f] ↔ x = e ∨ x = f := by
  rw [Set.mem_make]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem mem_union_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] {A B : Set α} {x : α} :
  x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Set.mem_union A B x

theorem mem_union_singleton {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A : Set α} {e x : α} :
  x ∈ A ∪ Set.singleton e ↔ x ∈ A ∨ x = e := by
  rw [Set.mem_union, Set.mem_singleton]

theorem mem_difference_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} {x : α} :
  x ∈ A.difference B ↔ x ∈ A ∧ x ∉ B := Set.mem_difference A B x

/-- A well-formed set that is not the singleton `{a}` but contains `a` has another element. -/
theorem exists_ne_of_mem_of_ne_singleton {α : Type} [LT α] [DecidableLT α] [StrictLT α]
  [DecidableEq α] {A : Set α} {a : α} (hA : A.WellFormed) (ha : a ∈ A)
  (hne : A ≠ Set.singleton a) : ∃ x, x ∈ A ∧ x ≠ a := by
  by_contra hcon
  apply hne
  rw [← Set.subset_iff_eq hA (Set.singleton_wf a), Set.subset_def, Set.subset_def]
  refine ⟨?_, singleton_subset_of_mem ha⟩
  intro x hx
  rw [Set.mem_singleton]
  exact Classical.byContradiction fun hxa => hcon ⟨x, hx, hxa⟩

/-- A nonempty well-formed set other than `A` (H2). -/
theorem exists_nonempty_ne {α : Type} [LT α] [DecidableLT α] [DecidableEq α]
  (h2 : TwoElems α) (A : Set α) :
  ∃ X : Set α, X.WellFormed ∧ (∃ x, x ∈ X) ∧ X ≠ A := by
  obtain ⟨a, b, hab⟩ := h2
  by_cases ha : a ∈ A
  · by_cases hb : b ∈ A
    · exact ⟨Set.singleton a, Set.singleton_wf a, ⟨a, Set.mem_singleton_self a⟩,
        (ne_of_mem_of_not_mem hb (not_mem_singleton hab.symm)).symm⟩
    · exact ⟨Set.singleton b, Set.singleton_wf b, ⟨b, Set.mem_singleton_self b⟩,
        ne_of_mem_of_not_mem (Set.mem_singleton_self b) hb⟩
  · exact ⟨Set.singleton a, Set.singleton_wf a, ⟨a, Set.mem_singleton_self a⟩,
      ne_of_mem_of_not_mem (Set.mem_singleton_self a) ha⟩

/-- A well-formed set containing `e` other than `A` (H2). -/
theorem exists_mem_ne {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h2 : TwoElems α) (A : Set α) (e : α) :
  ∃ X : Set α, X.WellFormed ∧ e ∈ X ∧ X ≠ A := by
  by_cases he : e ∈ A
  · obtain ⟨u, hu⟩ := h2.exists_ne e
    by_cases huA : u ∈ A
    · exact ⟨Set.singleton e, Set.singleton_wf e, Set.mem_singleton_self e,
        (ne_of_mem_of_not_mem huA (not_mem_singleton hu)).symm⟩
    · exact ⟨Set.make [e, u], Set.make_wf _, mem_make_pair.mpr (Or.inl rfl),
        ne_of_mem_of_not_mem (mem_make_pair.mpr (Or.inr rfl)) huA⟩
  · exact ⟨Set.singleton e, Set.singleton_wf e, Set.mem_singleton_self e,
      ne_of_mem_of_not_mem (Set.mem_singleton_self e) he⟩

/-! ### Row `E`: `X.isEmpty()` -/

/-- #1 `E ∧ E` ⟺ `true`. -/
theorem qe_e_e {α : Type} [LT α] [DecidableLT α] [DecidableEq α] :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.isEmpty = true :=
  ⟨Set.empty, Set.empty_wf, Set.isEmpty_empty, Set.isEmpty_empty⟩

/-- #2 `E ∧ ¬E` ⟺ `false`. -/
theorem qe_e_ne {α : Type} [LT α] [DecidableLT α] [DecidableEq α] :
  ¬ ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.isEmpty = false := by
  rintro ⟨X, _, h₁, h₂⟩
  simp [h₁] at h₂

/-- #3 `E ∧ Q` ⟺ `A.isEmpty()`. -/
theorem qe_e_q {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ (X == A) = true) ↔ A.isEmpty = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, h, rfl⟩
    exact h
  · intro h
    exact ⟨A, hA, h, rfl⟩

/-- #4 `E ∧ ¬Q` ⟺ `!A.isEmpty()`. -/
theorem qe_e_nq {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ (X == A) = false) ↔ A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hX, hne⟩
    by_contra hcon
    apply hne
    rw [eq_empty_of_forall_not_mem hX, eq_empty_of_forall_not_mem fun x hx => hcon ⟨x, hx⟩]
  · rintro ⟨x, hx⟩
    exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty, (ne_empty_of_mem hx).symm⟩

/-- #5 `E ∧ C` ⟺ `false`. -/
theorem qe_e_c {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {e : α} :
  ¬ ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.contains e = true := by
  unfold_atoms
  rintro ⟨X, _, h, he⟩
  exact h e he

/-- #6 `E ∧ ¬C` ⟺ `true`. -/
theorem qe_e_nc {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {e : α} :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.contains e = false := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty, Set.not_mem_empty e⟩

/-- #7 `E ∧ Sub` ⟺ `true`. -/
theorem qe_e_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.subset A = true := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty, forall_mem_empty⟩

/-- #8 `E ∧ ¬Sub` ⟺ `false`. -/
theorem qe_e_nsub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  ¬ ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.subset A = false := by
  unfold_atoms
  rintro ⟨X, _, h, x, hx, _⟩
  exact h x hx

/-- #9 `E ∧ Sup` ⟺ `A.isEmpty()`. -/
theorem qe_e_sup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ A.subset X = true) ↔ A.isEmpty = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, h, hAX⟩ x hx
    exact h x (hAX x hx)
  · intro h
    exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty, fun x hx => absurd hx (h x)⟩

/-- #10 `E ∧ ¬Sup` ⟺ `!A.isEmpty()`. -/
theorem qe_e_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ A.subset X = false) ↔ A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, hx, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty, x, hx, Set.not_mem_empty x⟩

/-- #11 `E ∧ I` ⟺ `false`. -/
theorem qe_e_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  ¬ ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.intersects A = true := by
  unfold_atoms
  rintro ⟨X, _, h, x, hx, _⟩
  exact h x hx

/-- #12 `E ∧ ¬I` ⟺ `true`. -/
theorem qe_e_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = true ∧ X.intersects A = false := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty, forall_mem_empty⟩

/-! ### Row `¬E`: `!X.isEmpty()` -/

/-- #13 `¬E ∧ ¬E` ⟺ `true` [H1]. -/
theorem qe_ne_ne {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h1 : Nonempty α) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.isEmpty = false := by
  obtain ⟨u⟩ := h1
  unfold_atoms
  exact ⟨Set.singleton u, Set.singleton_wf u, ⟨u, Set.mem_singleton_self u⟩,
    ⟨u, Set.mem_singleton_self u⟩⟩

/-- #14 `¬E ∧ Q` ⟺ `!A.isEmpty()`. -/
theorem qe_ne_q {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ (X == A) = true) ↔ A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, h, rfl⟩
    exact h
  · intro h
    exact ⟨A, hA, h, rfl⟩

/-- #15 `¬E ∧ ¬Q` ⟺ `true` [H2]. -/
theorem qe_ne_nq {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h2 : TwoElems α)
  {A : Set α} (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ (X == A) = false := by
  unfold_atoms
  exact exists_nonempty_ne h2 A

/-- #16 `¬E ∧ C` ⟺ `true`. -/
theorem qe_ne_c {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {e : α} :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.contains e = true := by
  unfold_atoms
  exact ⟨Set.singleton e, Set.singleton_wf e, ⟨e, Set.mem_singleton_self e⟩,
    Set.mem_singleton_self e⟩

/-- #17 `¬E ∧ ¬C` ⟺ `true` [H2]. -/
theorem qe_ne_nc {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h2 : TwoElems α) {e : α} :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.contains e = false := by
  unfold_atoms
  obtain ⟨u, hu⟩ := h2.exists_ne e
  exact ⟨Set.singleton u, Set.singleton_wf u, ⟨u, Set.mem_singleton_self u⟩,
    not_mem_singleton (Ne.symm hu)⟩

/-- #18 `¬E ∧ Sub` ⟺ `!A.isEmpty()`. -/
theorem qe_ne_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.subset A = true) ↔ A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hx⟩, hXA⟩
    exact ⟨x, hXA x hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨A, hA, ⟨x, hx⟩, fun y hy => hy⟩

/-- #19 `¬E ∧ ¬Sub`, hypothesis-free: ⟺ some element is outside `A`. -/
theorem qe_ne_nsub_iff {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.subset A = false) ↔ ∃ u, u ∉ A := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, _, hxA⟩
    exact ⟨x, hxA⟩
  · rintro ⟨u, hu⟩
    exact ⟨Set.singleton u, Set.singleton_wf u, ⟨u, Set.mem_singleton_self u⟩, u,
      Set.mem_singleton_self u, hu⟩

/-- #19 `¬E ∧ ¬Sub` ⟺ `true` [H∞]. -/
theorem qe_ne_nsub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (hU : Unbounded α)
  {A : Set α} (hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.subset A = false :=
  (qe_ne_nsub_iff hA).mpr (hU A)

/-- #20 `¬E ∧ Sup` ⟺ `true` [H1]. -/
theorem qe_ne_sup {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h1 : Nonempty α) {A : Set α} (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ A.subset X = true := by
  obtain ⟨u⟩ := h1
  unfold_atoms
  exact ⟨A ∪ Set.singleton u, Set.union_wf A _, ⟨u, mem_union_singleton.mpr (Or.inr rfl)⟩,
    fun x hx => mem_union_singleton.mpr (Or.inl hx)⟩

/-- #21 `¬E ∧ ¬Sup` ⇒ `!A.isEmpty()`. -/
theorem qe_ne_nsup_over {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ A.subset X = false) → A.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, hx, _⟩
  exact ⟨x, hx⟩

/-- #21 `¬E ∧ ¬Sup` ⟺ `!A.isEmpty()` [H2]. -/
theorem qe_ne_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h2 : TwoElems α)
  {A : Set α} (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ A.subset X = false) ↔ A.isEmpty = false := by
  refine ⟨qe_ne_nsup_over, ?_⟩
  unfold_atoms
  rintro ⟨a, ha⟩
  obtain ⟨u, hu⟩ := h2.exists_ne a
  exact ⟨Set.singleton u, Set.singleton_wf u, ⟨u, Set.mem_singleton_self u⟩, a, ha,
    not_mem_singleton (Ne.symm hu)⟩

/-- #22 `¬E ∧ I` ⟺ `!A.isEmpty()`. -/
theorem qe_ne_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.intersects A = true) ↔
    A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, _, hxA⟩
    exact ⟨x, hxA⟩
  · rintro ⟨x, hx⟩
    exact ⟨A, hA, ⟨x, hx⟩, x, hx, hx⟩

/-- #23 `¬E ∧ ¬I`, hypothesis-free: ⟺ some element is outside `A`. -/
theorem qe_ne_ni_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A : Set α} (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.intersects A = false) ↔ ∃ u, u ∉ A := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hx⟩, h⟩
    exact ⟨x, h x hx⟩
  · rintro ⟨u, hu⟩
    exact ⟨Set.singleton u, Set.singleton_wf u, ⟨u, Set.mem_singleton_self u⟩,
      fun x hx => (mem_singleton_iff.mp hx).symm ▸ hu⟩

/-- #23 `¬E ∧ ¬I` ⟺ `true` [H∞]. -/
theorem qe_ne_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A : Set α} (hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.isEmpty = false ∧ X.intersects A = false :=
  (qe_ne_ni_iff hA).mpr (hU A)

/-! ### Row `Q`: `X == A` (substitution) -/

/-- #24 `Q_A ∧ Q_B` ⟺ `A == B`. -/
theorem qe_q_q {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ (X == B) = true) ↔ (A == B) = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #25 `Q_A ∧ ¬Q_B` ⟺ `A != B`. -/
theorem qe_q_nq {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ (X == B) = false) ↔ (A == B) = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #26 `Q ∧ C` ⟺ `A.contains(e)`. -/
theorem qe_q_c {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ X.contains e = true) ↔ A.contains e = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #27 `Q ∧ ¬C` ⟺ `!A.contains(e)`. -/
theorem qe_q_nc {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ X.contains e = false) ↔
    A.contains e = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #28 `Q_A ∧ Sub_B` ⟺ `B.containsAll(A)`. -/
theorem qe_q_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ X.subset B = true) ↔ A.subset B = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #29 `Q_A ∧ ¬Sub_B` ⟺ `!B.containsAll(A)`. -/
theorem qe_q_nsub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ X.subset B = false) ↔ A.subset B = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #30 `Q_A ∧ Sup_B` ⟺ `A.containsAll(B)`. -/
theorem qe_q_sup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ B.subset X = true) ↔ B.subset A = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #31 `Q_A ∧ ¬Sup_B` ⟺ `!A.containsAll(B)`. -/
theorem qe_q_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ B.subset X = false) ↔ B.subset A = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #32 `Q_A ∧ I_B` ⟺ `A.containsAny(B)`. -/
theorem qe_q_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ X.intersects B = true) ↔
    A.intersects B = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-- #33 `Q_A ∧ ¬I_B` ⟺ `!A.containsAny(B)`. -/
theorem qe_q_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = true ∧ X.intersects B = false) ↔
    A.intersects B = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, rfl, h⟩
    exact h
  · intro h
    exact ⟨A, hA, rfl, h⟩

/-! ### Row `¬Q`: `X != A` -/

/-- #34 `¬Q_A ∧ ¬Q_B` ⟺ `true` [H2]. -/
theorem qe_nq_nq {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h2 : TwoElems α)
  {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ (X == B) = false := by
  unfold_atoms
  by_cases hA' : ∃ x, x ∈ A
  · by_cases hB' : ∃ x, x ∈ B
    · obtain ⟨x, hx⟩ := hA'
      obtain ⟨y, hy⟩ := hB'
      exact ⟨Set.empty, Set.empty_wf, (ne_empty_of_mem hx).symm, (ne_empty_of_mem hy).symm⟩
    · obtain ⟨X, hX, ⟨x, hx⟩, hXA⟩ := exists_nonempty_ne h2 A
      exact ⟨X, hX, hXA, ne_of_mem_of_not_mem hx fun h => hB' ⟨x, h⟩⟩
  · obtain ⟨X, hX, ⟨x, hx⟩, hXB⟩ := exists_nonempty_ne h2 B
    exact ⟨X, hX, ne_of_mem_of_not_mem hx fun h => hA' ⟨x, h⟩, hXB⟩

/-- #35 `¬Q ∧ C` ⟺ `true` [H2]. -/
theorem qe_nq_c {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h2 : TwoElems α) {A : Set α} {e : α} (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.contains e = true := by
  unfold_atoms
  obtain ⟨X, hX, he, hne⟩ := exists_mem_ne h2 A e
  exact ⟨X, hX, hne, he⟩

/-- #36 `¬Q ∧ ¬C` ⟺ `true` [H2]. -/
theorem qe_nq_nc {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h2 : TwoElems α)
  {A : Set α} {e : α} (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.contains e = false := by
  unfold_atoms
  by_cases hA' : ∃ x, x ∈ A
  · obtain ⟨x, hx⟩ := hA'
    exact ⟨Set.empty, Set.empty_wf, (ne_empty_of_mem hx).symm, Set.not_mem_empty e⟩
  · obtain ⟨u, hu⟩ := h2.exists_ne e
    exact ⟨Set.singleton u, Set.singleton_wf u,
      ne_of_mem_of_not_mem (Set.mem_singleton_self u) fun h => hA' ⟨u, h⟩,
      not_mem_singleton (Ne.symm hu)⟩

/-- #37 `¬Q_A ∧ Sub_B` ⟺ `!A.isEmpty() || !B.isEmpty()`. -/
theorem qe_nq_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.subset B = true) ↔
    (A.isEmpty = false ∨ B.isEmpty = false) := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hne, hXB⟩
    by_contra hcon
    apply hne
    rw [eq_empty_of_forall_not_mem fun x hx => hcon (Or.inr ⟨x, hXB x hx⟩),
      eq_empty_of_forall_not_mem fun x hx => hcon (Or.inl ⟨x, hx⟩)]
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨Set.empty, Set.empty_wf, (ne_empty_of_mem hx).symm, forall_mem_empty⟩
    · by_cases hA' : ∃ y, y ∈ A
      · obtain ⟨y, hy⟩ := hA'
        exact ⟨Set.empty, Set.empty_wf, (ne_empty_of_mem hy).symm, forall_mem_empty⟩
      · exact ⟨Set.singleton x, Set.singleton_wf x,
          ne_of_mem_of_not_mem (Set.mem_singleton_self x) fun h => hA' ⟨x, h⟩,
          singleton_subset_of_mem hx⟩

/-- #38 `¬Q_A ∧ ¬Sub_B` ⟺ `true` [H∞]. -/
theorem qe_nq_nsub {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.subset B = false := by
  unfold_atoms
  obtain ⟨u, hu⟩ := hU B
  by_cases huA : u ∈ A
  · obtain ⟨v, hv⟩ := hU (B ∪ Set.singleton u)
    have hvB : v ∉ B := fun h => hv (mem_union_singleton.mpr (Or.inl h))
    have hvu : v ≠ u := fun h => hv (mem_union_singleton.mpr (Or.inr h))
    by_cases hvA : v ∈ A
    · exact ⟨Set.singleton u, Set.singleton_wf u,
        (ne_of_mem_of_not_mem hvA (not_mem_singleton hvu)).symm, u, Set.mem_singleton_self u, hu⟩
    · exact ⟨Set.singleton v, Set.singleton_wf v,
        ne_of_mem_of_not_mem (Set.mem_singleton_self v) hvA, v, Set.mem_singleton_self v, hvB⟩
  · exact ⟨Set.singleton u, Set.singleton_wf u,
      ne_of_mem_of_not_mem (Set.mem_singleton_self u) huA, u, Set.mem_singleton_self u, hu⟩

/-- #39 `¬Q_A ∧ Sup_B` ⟺ `true` [H∞]. -/
theorem qe_nq_sup {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (_hA : A.WellFormed) (hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ B.subset X = true := by
  unfold_atoms
  by_cases hBA : B = A
  · obtain ⟨u, hu⟩ := hU B
    exact ⟨B ∪ Set.singleton u, Set.union_wf B _,
      ne_of_mem_of_not_mem (mem_union_singleton.mpr (Or.inr rfl)) (hBA ▸ hu),
      fun x hx => mem_union_singleton.mpr (Or.inl hx)⟩
  · exact ⟨B, hB, hBA, fun x hx => hx⟩

/-- #40 `¬Q_A ∧ ¬Sup_B` ⇒ `!B.isEmpty()`. -/
theorem qe_nq_nsup_over {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α} :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ B.subset X = false) → B.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, hx, _⟩
  exact ⟨x, hx⟩

/-- #40 `¬Q_A ∧ ¬Sup_B` ⟺ `!B.isEmpty()` [H2]. -/
theorem qe_nq_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] (h2 : TwoElems α)
  {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ B.subset X = false) ↔ B.isEmpty = false := by
  refine ⟨qe_nq_nsup_over, ?_⟩
  unfold_atoms
  rintro ⟨b, hb⟩
  by_cases hA' : ∃ x, x ∈ A
  · obtain ⟨x, hx⟩ := hA'
    exact ⟨Set.empty, Set.empty_wf, (ne_empty_of_mem hx).symm, b, hb, Set.not_mem_empty b⟩
  · obtain ⟨u, hu⟩ := h2.exists_ne b
    exact ⟨Set.singleton u, Set.singleton_wf u,
      ne_of_mem_of_not_mem (Set.mem_singleton_self u) fun h => hA' ⟨u, h⟩,
      b, hb, not_mem_singleton (Ne.symm hu)⟩

/-- #41 `¬Q_A ∧ I_B` ⇒ `!B.isEmpty()`. -/
theorem qe_nq_i_over {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.intersects B = true) →
    B.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, _, hxB⟩
  exact ⟨x, hxB⟩

/-- #41 `¬Q_A ∧ I_B` ⟺ `!B.isEmpty()` [H2]. -/
theorem qe_nq_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h2 : TwoElems α) {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.intersects B = true) ↔
    B.isEmpty = false := by
  refine ⟨qe_nq_i_over, ?_⟩
  unfold_atoms
  rintro ⟨b, hb⟩
  obtain ⟨X, hX, hbX, hne⟩ := exists_mem_ne h2 A b
  exact ⟨X, hX, hne, b, hbX, hb⟩

/-- #42 `¬Q_A ∧ ¬I_B` ⟺ `true` [H∞]. -/
theorem qe_nq_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ (X == A) = false ∧ X.intersects B = false := by
  unfold_atoms
  by_cases hA' : ∃ x, x ∈ A
  · obtain ⟨x, hx⟩ := hA'
    exact ⟨Set.empty, Set.empty_wf, (ne_empty_of_mem hx).symm, forall_mem_empty⟩
  · obtain ⟨u, hu⟩ := hU B
    exact ⟨Set.singleton u, Set.singleton_wf u,
      ne_of_mem_of_not_mem (Set.mem_singleton_self u) fun h => hA' ⟨u, h⟩,
      fun x hx => (mem_singleton_iff.mp hx).symm ▸ hu⟩

/-! ### Row `C`: `X.contains(e)` -/

/-- #43 `C_e ∧ C_f` ⟺ `true`. -/
theorem qe_c_c {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {e f : α} :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.contains f = true := by
  unfold_atoms
  exact ⟨Set.make [e, f], Set.make_wf _, mem_make_pair.mpr (Or.inl rfl),
    mem_make_pair.mpr (Or.inr rfl)⟩

/-- #44 `C_e ∧ ¬C_f` ⟺ `e != f`. -/
theorem qe_c_nc {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {e f : α} :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.contains f = false) ↔ e ≠ f := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, hf⟩ h
    exact hf (h ▸ he)
  · intro h
    exact ⟨Set.singleton e, Set.singleton_wf e, Set.mem_singleton_self e,
      not_mem_singleton (Ne.symm h)⟩

/-- #45 `C ∧ Sub` ⟺ `A.contains(e)`. -/
theorem qe_c_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.subset A = true) ↔
    A.contains e = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, hXA⟩
    exact hXA e he
  · intro h
    exact ⟨Set.singleton e, Set.singleton_wf e, Set.mem_singleton_self e,
      singleton_subset_of_mem h⟩

/-- #46 `C ∧ ¬Sub`, hypothesis-free: ⟺ some element is outside `A`. -/
theorem qe_c_nsub_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A : Set α} {e : α} (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.subset A = false) ↔ ∃ u, u ∉ A := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, _, hxA⟩
    exact ⟨x, hxA⟩
  · rintro ⟨u, hu⟩
    exact ⟨Set.make [e, u], Set.make_wf _, mem_make_pair.mpr (Or.inl rfl), u,
      mem_make_pair.mpr (Or.inr rfl), hu⟩

/-- #46 `C ∧ ¬Sub` ⟺ `true` [H∞]. -/
theorem qe_c_nsub {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A : Set α} {e : α} (hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.subset A = false :=
  (qe_c_nsub_iff (e := e) hA).mpr (hU A)

/-- #47 `C ∧ Sup` ⟺ `true`. -/
theorem qe_c_sup {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  {e : α} (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ A.subset X = true := by
  unfold_atoms
  exact ⟨A ∪ Set.singleton e, Set.union_wf A _, mem_union_singleton.mpr (Or.inr rfl),
    fun x hx => mem_union_singleton.mpr (Or.inl hx)⟩

/-- #48 `C ∧ ¬Sup` ⟺ `![e].containsAll(A)` (with the singleton literal). -/
theorem qe_c_nsup_lit {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ A.subset X = false) ↔
    A.subset (Set.singleton e) = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, x, hx, hxX⟩
    exact ⟨x, hx, fun h => hxX ((mem_singleton_iff.mp h).symm ▸ he)⟩
  · rintro ⟨x, hx, hxe⟩
    exact ⟨Set.singleton e, Set.singleton_wf e, Set.mem_singleton_self e, x, hx, hxe⟩

/-- #48 `C ∧ ¬Sup` ⇒ `!A.isEmpty()`. -/
theorem qe_c_nsup_over {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α} :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ A.subset X = false) →
    A.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, hx, _⟩
  exact ⟨x, hx⟩

/-- #49 `C ∧ I` ⟺ `!A.isEmpty()`. -/
theorem qe_c_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  {e : α} (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.intersects A = true) ↔
    A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, _, hxA⟩
    exact ⟨x, hxA⟩
  · rintro ⟨a, ha⟩
    exact ⟨A ∪ Set.singleton e, Set.union_wf A _, mem_union_singleton.mpr (Or.inr rfl), a,
      mem_union_singleton.mpr (Or.inl ha), ha⟩

/-- #50 `C ∧ ¬I` ⟺ `!A.contains(e)`. -/
theorem qe_c_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  {e : α} (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ X.intersects A = false) ↔
    A.contains e = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, h⟩
    exact h e he
  · intro h
    exact ⟨Set.singleton e, Set.singleton_wf e, Set.mem_singleton_self e,
      fun x hx => (mem_singleton_iff.mp hx).symm ▸ h⟩

/-! ### Row `¬C`: `!X.contains(e)` -/

/-- #51 `¬C_e ∧ ¬C_f` ⟺ `true`. -/
theorem qe_nc_nc {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {e f : α} :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.contains f = false := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty e, Set.not_mem_empty f⟩

/-- #52 `¬C ∧ Sub` ⟺ `true`. -/
theorem qe_nc_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.subset A = true := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty e, forall_mem_empty⟩

/-- #53 `¬C ∧ ¬Sub`, hypothesis-free: ⟺ some element other than `e` is outside `A`. -/
theorem qe_nc_nsub_iff {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.subset A = false) ↔
    ∃ u, u ∉ A ∧ u ≠ e := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, x, hx, hxA⟩
    exact ⟨x, hxA, fun h => he (h ▸ hx)⟩
  · rintro ⟨u, hu, hue⟩
    exact ⟨Set.singleton u, Set.singleton_wf u, not_mem_singleton (Ne.symm hue), u,
      Set.mem_singleton_self u, hu⟩

/-- #53 `¬C ∧ ¬Sub` ⟺ `true` [H∞]. -/
theorem qe_nc_nsub {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A : Set α} {e : α} (hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.subset A = false := by
  obtain ⟨u, hu⟩ := hU (A ∪ Set.singleton e)
  exact (qe_nc_nsub_iff hA).mpr ⟨u, fun h => hu (mem_union_singleton.mpr (Or.inl h)),
    fun h => hu (mem_union_singleton.mpr (Or.inr h))⟩

/-- #54 `¬C ∧ Sup` ⟺ `!A.contains(e)`. -/
theorem qe_nc_sup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ A.subset X = true) ↔
    A.contains e = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, hAX⟩ h
    exact he (hAX e h)
  · intro h
    exact ⟨A, hA, h, fun x hx => hx⟩

/-- #55 `¬C ∧ ¬Sup` ⟺ `!A.isEmpty()`. -/
theorem qe_nc_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A : Set α} {e : α}
  (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ A.subset X = false) ↔
    A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, hx, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty e, x, hx, Set.not_mem_empty x⟩

/-- #56 `¬C ∧ I` ⟺ `![e].containsAll(A)` (with the singleton literal). -/
theorem qe_nc_i_lit {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A : Set α} {e : α} (_hA : A.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.intersects A = true) ↔
    A.subset (Set.singleton e) = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, he, x, hxX, hxA⟩
    exact ⟨x, hxA, fun h => he ((mem_singleton_iff.mp h) ▸ hxX)⟩
  · rintro ⟨x, hx, hxe⟩
    exact ⟨Set.singleton x, Set.singleton_wf x,
      not_mem_singleton fun h => hxe (mem_singleton_iff.mpr h.symm),
      x, Set.mem_singleton_self x, hx⟩

/-- #56 `¬C ∧ I` ⇒ `!A.isEmpty()`. -/
theorem qe_nc_i_over {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A : Set α} {e : α} :
  (∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.intersects A = true) →
    A.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, _, hxA⟩
  exact ⟨x, hxA⟩

/-- #57 `¬C ∧ ¬I` ⟺ `true`. -/
theorem qe_nc_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A : Set α}
  {e : α} (_hA : A.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.intersects A = false := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, Set.not_mem_empty e, forall_mem_empty⟩

/-! ### Row `Sub`: `A.containsAll(X)` -/

/-- #58 `Sub_A ∧ Sub_B` ⟺ `true`. -/
theorem qe_sub_sub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ X.subset B = true := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, forall_mem_empty, forall_mem_empty⟩

/-- #59 `Sub_A ∧ ¬Sub_B` ⟺ `!B.containsAll(A)`. -/
theorem qe_sub_nsub {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ X.subset B = false) ↔
    A.subset B = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hXA, x, hx, hxB⟩
    exact ⟨x, hXA x hx, hxB⟩
  · rintro ⟨x, hx, hxB⟩
    exact ⟨A, hA, fun y hy => hy, x, hx, hxB⟩

/-- #60 `Sub_A ∧ Sup_B` ⟺ `A.containsAll(B)`. -/
theorem qe_sub_sup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ B.subset X = true) ↔
    B.subset A = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hXA, hBX⟩ x hx
    exact hXA x (hBX x hx)
  · intro h
    exact ⟨B, hB, h, fun x hx => hx⟩

/-- #61 `Sub_A ∧ ¬Sup_B` ⟺ `!B.isEmpty()`. -/
theorem qe_sub_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ B.subset X = false) ↔
    B.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, hx, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨Set.empty, Set.empty_wf, forall_mem_empty, x, hx, Set.not_mem_empty x⟩

/-- #62 `Sub_A ∧ I_B` ⟺ `A.containsAny(B)`. -/
theorem qe_sub_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ X.intersects B = true) ↔
    A.intersects B = true := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hXA, x, hxX, hxB⟩
    exact ⟨x, hXA x hxX, hxB⟩
  · rintro ⟨x, hxA, hxB⟩
    exact ⟨A, hA, fun y hy => hy, x, hxA, hxB⟩

/-- #63 `Sub_A ∧ ¬I_B` ⟺ `true`. -/
theorem qe_sub_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.subset A = true ∧ X.intersects B = false := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, forall_mem_empty, forall_mem_empty⟩

/-! ### Row `¬Sub`: `!A.containsAll(X)` -/

/-- #64 `¬Sub_A ∧ ¬Sub_B`, hypothesis-free: ⟺ each of `A`, `B` misses an element. -/
theorem qe_nsub_nsub_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ X.subset B = false) ↔
    (∃ u, u ∉ A) ∧ (∃ v, v ∉ B) := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, _, hxA⟩, ⟨y, _, hyB⟩⟩
    exact ⟨⟨x, hxA⟩, ⟨y, hyB⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨Set.make [u, v], Set.make_wf _, ⟨u, mem_make_pair.mpr (Or.inl rfl), hu⟩,
      ⟨v, mem_make_pair.mpr (Or.inr rfl), hv⟩⟩

/-- #64 `¬Sub_A ∧ ¬Sub_B` ⟺ `true` [H∞]. -/
theorem qe_nsub_nsub {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (hA : A.WellFormed) (hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ X.subset B = false :=
  (qe_nsub_nsub_iff hA hB).mpr ⟨hU A, hU B⟩

/-- #65 `¬Sub_A ∧ Sup_B` ⟺ `true` [H∞]. -/
theorem qe_nsub_sup {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ B.subset X = true := by
  unfold_atoms
  obtain ⟨u, hu⟩ := hU A
  exact ⟨B ∪ Set.singleton u, Set.union_wf B _, ⟨u, mem_union_singleton.mpr (Or.inr rfl), hu⟩,
    fun x hx => mem_union_singleton.mpr (Or.inl hx)⟩

/-- #66 `¬Sub_A ∧ ¬Sup_B` ⇒ `!B.isEmpty()`. -/
theorem qe_nsub_nsup_over {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α} :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ B.subset X = false) →
    B.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, hx, _⟩
  exact ⟨x, hx⟩

/-- #66 `¬Sub_A ∧ ¬Sup_B` ⟺ `!B.isEmpty()` [H∞]. -/
theorem qe_nsub_nsup {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ B.subset X = false) ↔
    B.isEmpty = false := by
  refine ⟨qe_nsub_nsup_over, ?_⟩
  unfold_atoms
  rintro ⟨b, hb⟩
  obtain ⟨u, hu⟩ := hU (A ∪ B)
  refine ⟨Set.singleton u, Set.singleton_wf u,
    ⟨u, Set.mem_singleton_self u, fun h => hu (mem_union_iff.mpr (Or.inl h))⟩, b, hb, ?_⟩
  exact not_mem_singleton fun h => hu (mem_union_iff.mpr (Or.inr (h ▸ hb)))

/-- #67 `¬Sub_A ∧ I_B` ⇒ `!B.isEmpty()`. -/
theorem qe_nsub_i_over {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ X.intersects B = true) →
    B.isEmpty = false := by
  unfold_atoms
  rintro ⟨X, _, _, x, _, hxB⟩
  exact ⟨x, hxB⟩

/-- #67 `¬Sub_A ∧ I_B` ⟺ `!B.isEmpty()` [H∞]. -/
theorem qe_nsub_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ X.intersects B = true) ↔
    B.isEmpty = false := by
  refine ⟨qe_nsub_i_over, ?_⟩
  unfold_atoms
  rintro ⟨b, hb⟩
  obtain ⟨u, hu⟩ := hU A
  exact ⟨B ∪ Set.singleton u, Set.union_wf B _, ⟨u, mem_union_singleton.mpr (Or.inr rfl), hu⟩,
    b, mem_union_singleton.mpr (Or.inl hb), hb⟩

/-- #68 `¬Sub_A ∧ ¬I_B`, hypothesis-free: ⟺ some element is outside `A ∪ B`. -/
theorem qe_nsub_ni_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ X.intersects B = false) ↔
    ∃ u, u ∉ A ∧ u ∉ B := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hxX, hxA⟩, h⟩
    exact ⟨x, hxA, h x hxX⟩
  · rintro ⟨u, huA, huB⟩
    exact ⟨Set.singleton u, Set.singleton_wf u, ⟨u, Set.mem_singleton_self u, huA⟩,
      fun x hx => (mem_singleton_iff.mp hx).symm ▸ huB⟩

/-- #68 `¬Sub_A ∧ ¬I_B` ⟺ `true` [H∞]. -/
theorem qe_nsub_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (hA : A.WellFormed) (hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.subset A = false ∧ X.intersects B = false := by
  obtain ⟨u, hu⟩ := hU (A ∪ B)
  exact (qe_nsub_ni_iff hA hB).mpr ⟨u, fun h => hu (mem_union_iff.mpr (Or.inl h)),
    fun h => hu (mem_union_iff.mpr (Or.inr h))⟩

/-! ### Row `Sup`: `X.containsAll(A)` -/

/-- #69 `Sup_A ∧ Sup_B` ⟺ `true`. -/
theorem qe_sup_sup {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ A.subset X = true ∧ B.subset X = true := by
  unfold_atoms
  exact ⟨A ∪ B, Set.union_wf A B, fun x hx => mem_union_iff.mpr (Or.inl hx),
    fun x hx => mem_union_iff.mpr (Or.inr hx)⟩

/-- #70 `Sup_A ∧ ¬Sup_B` ⟺ `!A.containsAll(B)`. -/
theorem qe_sup_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = true ∧ B.subset X = false) ↔
    B.subset A = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hAX, x, hxB, hxX⟩
    exact ⟨x, hxB, fun h => hxX (hAX x h)⟩
  · rintro ⟨x, hxB, hxA⟩
    exact ⟨A, hA, fun y hy => hy, x, hxB, hxA⟩

/-- #71 `Sup_A ∧ I_B` ⟺ `!B.isEmpty()`. -/
theorem qe_sup_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = true ∧ X.intersects B = true) ↔
    B.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, _, x, _, hxB⟩
    exact ⟨x, hxB⟩
  · rintro ⟨b, hb⟩
    exact ⟨A ∪ B, Set.union_wf A B, fun x hx => mem_union_iff.mpr (Or.inl hx), b,
      mem_union_iff.mpr (Or.inr hb), hb⟩

/-- #72 `Sup_A ∧ ¬I_B` ⟺ `!A.containsAny(B)`. -/
theorem qe_sup_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = true ∧ X.intersects B = false) ↔
    A.intersects B = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, hAX, h⟩ x hx
    exact h x (hAX x hx)
  · intro h
    exact ⟨A, hA, fun y hy => hy, h⟩

/-! ### Row `¬Sup`: `!X.containsAll(A)` -/

/-- #73 `¬Sup_A ∧ ¬Sup_B` ⟺ `!A.isEmpty() && !B.isEmpty()`. -/
theorem qe_nsup_nsup {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = false ∧ B.subset X = false) ↔
    (A.isEmpty = false ∧ B.isEmpty = false) := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hx, _⟩, ⟨y, hy, _⟩⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨Set.empty, Set.empty_wf, ⟨x, hx, Set.not_mem_empty x⟩, ⟨y, hy, Set.not_mem_empty y⟩⟩

/-- #74 `¬Sup_A ∧ I_B` ⇒ `!A.isEmpty() && !B.isEmpty()`. -/
theorem qe_nsup_i_over {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = false ∧ X.intersects B = true) →
    (A.isEmpty = false ∧ B.isEmpty = false) := by
  unfold_atoms
  rintro ⟨X, _, ⟨x, hx, _⟩, ⟨y, _, hy⟩⟩
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

/-- #74 `¬Sup_A ∧ I_B`, the exact set-theoretic condition: both nonempty, and not the
same singleton. -/
theorem qe_nsup_i_iff {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  {A B : Set α} (hA : A.WellFormed) (hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = false ∧ X.intersects B = true) ↔
    ((∃ a, a ∈ A) ∧ (∃ b, b ∈ B) ∧ ¬ (A = B ∧ ∃ a, A = Set.singleton a)) := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hxA, hxX⟩, ⟨y, hyX, hyB⟩⟩
    refine ⟨⟨x, hxA⟩, ⟨y, hyB⟩, ?_⟩
    rintro ⟨rfl, a, rfl⟩
    rw [Set.mem_singleton] at hxA hyB
    subst hxA hyB
    exact hxX hyX
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hne⟩
    by_cases hBA : ∃ x, x ∈ B ∧ x ∉ A
    · obtain ⟨x, hxB, hxA⟩ := hBA
      exact ⟨B.difference A, Set.difference_wf B A hB, ⟨a, ha, fun h => (mem_difference_iff.mp h).2 ha⟩,
        x, mem_difference_iff.mpr ⟨hxB, hxA⟩, hxB⟩
    · -- `B ⊆ A`
      have hBsub : ∀ x, x ∈ B → x ∈ A := fun x hx =>
        Classical.byContradiction fun h => hBA ⟨x, hx, h⟩
      by_cases hAb : A = Set.singleton b
      · -- then `A = B = {b}` is excluded, so `A ≠ B`, i.e. some `a ∈ A \ B`
        have hAB : A ≠ B := fun h => hne ⟨h, b, hAb⟩
        have hbA : b ∈ A := hBsub b hb
        have : ∃ x, x ∈ A ∧ x ∉ B := by
          by_contra hcon
          apply hAB
          rw [← Set.subset_iff_eq hA hB, Set.subset_def, Set.subset_def]
          exact ⟨fun x hx => Classical.byContradiction fun h => hcon ⟨x, hx, h⟩, hBsub⟩
        obtain ⟨x, hxA, hxB⟩ := this
        exact ⟨B, hB, ⟨x, hxA, hxB⟩, b, hb, hb⟩
      · obtain ⟨x, hxA, hxb⟩ := exists_ne_of_mem_of_ne_singleton hA (hBsub b hb) hAb
        exact ⟨Set.singleton b, Set.singleton_wf b, ⟨x, hxA, not_mem_singleton hxb⟩, b,
          Set.mem_singleton_self b, hb⟩

/-- #75 `¬Sup_A ∧ ¬I_B` ⟺ `!A.isEmpty()`. -/
theorem qe_nsup_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ A.subset X = false ∧ X.intersects B = false) ↔
    A.isEmpty = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hx, _⟩, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨Set.empty, Set.empty_wf, ⟨x, hx, Set.not_mem_empty x⟩, forall_mem_empty⟩

/-! ### Row `I`: `X.containsAny(A)` -/

/-- #76 `I_A ∧ I_B` ⟺ `!A.isEmpty() && !B.isEmpty()`. -/
theorem qe_i_i {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.intersects A = true ∧ X.intersects B = true) ↔
    (A.isEmpty = false ∧ B.isEmpty = false) := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, _, hx⟩, ⟨y, _, hy⟩⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨A ∪ B, Set.union_wf A B, ⟨x, mem_union_iff.mpr (Or.inl hx), hx⟩,
      ⟨y, mem_union_iff.mpr (Or.inr hy), hy⟩⟩

/-- #77 `I_A ∧ ¬I_B` ⟺ `!B.containsAll(A)`. -/
theorem qe_i_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ X : Set α, X.WellFormed ∧ X.intersects A = true ∧ X.intersects B = false) ↔
    A.subset B = false := by
  unfold_atoms
  constructor
  · rintro ⟨X, _, ⟨x, hxX, hxA⟩, h⟩
    exact ⟨x, hxA, h x hxX⟩
  · rintro ⟨x, hxA, hxB⟩
    exact ⟨A.difference B, Set.difference_wf A B hA, ⟨x, mem_difference_iff.mpr ⟨hxA, hxB⟩, hxA⟩,
      fun y hy => (mem_difference_iff.mp hy).2⟩

/-- #78 `¬I_A ∧ ¬I_B` ⟺ `true`. -/
theorem qe_ni_ni {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  ∃ X : Set α, X.WellFormed ∧ X.intersects A = false ∧ X.intersects B = false := by
  unfold_atoms
  exact ⟨Set.empty, Set.empty_wf, forall_mem_empty, forall_mem_empty⟩

/-! ### The element quantified: `A.contains(x)` -/

/-- #79 `M_A ∧ M_B` ⟺ `A.containsAny(B)`. -/
theorem qe_m_m {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ x : α, A.contains x = true ∧ B.contains x = true) ↔ A.intersects B = true := by
  unfold_atoms

/-- #80 `M_A ∧ ¬M_B` ⟺ `!B.containsAll(A)`. -/
theorem qe_m_nm {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ x : α, A.contains x = true ∧ B.contains x = false) ↔ A.subset B = false := by
  unfold_atoms

/-- #81 `¬M_A ∧ ¬M_B`, hypothesis-free: ⟺ some element is outside `A ∪ B`. -/
theorem qe_nm_nm_iff {α : Type} [LT α] [DecidableLT α] [DecidableEq α] {A B : Set α}
  (_hA : A.WellFormed) (_hB : B.WellFormed) :
  (∃ x : α, A.contains x = false ∧ B.contains x = false) ↔ ∃ u, u ∉ A ∧ u ∉ B := by
  unfold_atoms

/-- #81 `¬M_A ∧ ¬M_B` ⟺ `true` [H∞]. -/
theorem qe_nm_nm {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (hU : Unbounded α) {A B : Set α} (hA : A.WellFormed) (hB : B.WellFormed) :
  ∃ x : α, A.contains x = false ∧ B.contains x = false := by
  obtain ⟨u, hu⟩ := hU (A ∪ B)
  exact (qe_nm_nm_iff hA hB).mpr ⟨u, fun h => hu (mem_union_iff.mpr (Or.inl h)),
    fun h => hu (mem_union_iff.mpr (Or.inr h))⟩

/-! ### What no Cedar atom expresses

The atoms typeable over the free variables, as a vector. A target is
inexpressible when no function of the vector agrees with it on every
well-formed input; two instances with the same vector and different targets
prove it. -/

/-- The six Cedar atoms over two sets (`B.containsAny(A)` is `A.containsAny(B)`;
`contains` needs an element). -/
structure Atoms2 where
  aEmpty : Bool
  bEmpty : Bool
  aEqB : Bool
  aAllB : Bool
  bAllA : Bool
  aAnyB : Bool
deriving DecidableEq, Repr

def atoms2 {α : Type} [DecidableEq α] (A B : Set α) : Atoms2 :=
  ⟨A.isEmpty, B.isEmpty, A == B, B.subset A, A.subset B, A.intersects B⟩

/-- The two Cedar atoms over a set and an element. -/
structure Atoms1e where
  aEmpty : Bool
  aHasE : Bool
deriving DecidableEq, Repr

def atoms1e {α : Type} [DecidableEq α] (A : Set α) (e : α) : Atoms1e :=
  ⟨A.isEmpty, A.contains e⟩

/-- A nonempty set paired with itself fixes every atom. -/
theorem atoms2_self {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α] {S : Set α}
  {x : α} (hx : x ∈ S) :
  atoms2 S S = ⟨false, false, true, true, true, true⟩ := by
  have hne : S.isEmpty = false := isEmpty_false_iff.mpr ⟨x, hx⟩
  have hsub : S.subset S = true := Set.subset_refl
  have hint : S.intersects S = true := intersects_true_iff.mpr ⟨x, hx, hx⟩
  simp only [atoms2, hne, hsub, hint, beq_self_eq_true]

/-- A set containing `e` fixes both atoms. -/
theorem atoms1e_of_mem {α : Type} [DecidableEq α] {A : Set α} {e : α} (he : e ∈ A) :
  atoms1e A e = ⟨false, true⟩ := by
  have hne : A.isEmpty = false := isEmpty_false_iff.mpr ⟨e, he⟩
  have hc : A.contains e = true := Set.contains_prop_bool_equiv.mpr he
  simp only [atoms1e, hne, hc]

/-- #74 `¬Sup_A ∧ I_B` is beyond every boolean combination of the atoms over `A`, `B`
[H2]: `A = B = {a}` and `A = B = {a, b}` share the vector, but only the second has a
witness. -/
theorem qe_nsup_i_inexpressible {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h2 : TwoElems α) :
  ¬ ∃ f : Atoms2 → Bool, ∀ A B : Set α, A.WellFormed → B.WellFormed →
    (f (atoms2 A B) = true ↔
      ∃ X : Set α, X.WellFormed ∧ A.subset X = false ∧ X.intersects B = true) := by
  rintro ⟨f, hf⟩
  obtain ⟨a, b, hab⟩ := h2
  have h₁ := hf (Set.singleton a) (Set.singleton a) (Set.singleton_wf a) (Set.singleton_wf a)
  have h₂ := hf (Set.make [a, b]) (Set.make [a, b]) (Set.make_wf _) (Set.make_wf _)
  rw [atoms2_self (Set.mem_singleton_self a)] at h₁
  rw [atoms2_self (mem_make_pair.mpr (Or.inl rfl))] at h₂
  have hfalse : ¬ ∃ X : Set α, X.WellFormed ∧
      (Set.singleton a).subset X = false ∧ X.intersects (Set.singleton a) = true := by
    rintro ⟨X, _, hsub, hint⟩
    rw [subset_false_iff] at hsub
    rw [intersects_true_iff] at hint
    obtain ⟨x, hx, hxX⟩ := hsub
    obtain ⟨y, hyX, hy⟩ := hint
    rw [Set.mem_singleton] at hx hy
    subst hx hy
    exact hxX hyX
  have htrue : ∃ X : Set α, X.WellFormed ∧
      (Set.make [a, b]).subset X = false ∧ X.intersects (Set.make [a, b]) = true := by
    refine ⟨Set.singleton a, Set.singleton_wf a, ?_, ?_⟩
    · rw [subset_false_iff]
      exact ⟨b, mem_make_pair.mpr (Or.inr rfl), not_mem_singleton (Ne.symm hab)⟩
    · rw [intersects_true_iff]
      exact ⟨a, Set.mem_singleton_self a, mem_make_pair.mpr (Or.inl rfl)⟩
  exact hfalse (h₁.mp (h₂.mpr htrue))

/-- #48 `C ∧ ¬Sup` is beyond every boolean combination of the atoms over `A`, `e` [H2]:
`A = {e}` and `A = {e, u}` share the vector, but only the second has a witness. -/
theorem qe_c_nsup_inexpressible {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h2 : TwoElems α) (e : α) :
  ¬ ∃ f : Atoms1e → Bool, ∀ A : Set α, A.WellFormed →
    (f (atoms1e A e) = true ↔
      ∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧ A.subset X = false) := by
  rintro ⟨f, hf⟩
  obtain ⟨u, hu⟩ := h2.exists_ne e
  have h₁ := hf (Set.singleton e) (Set.singleton_wf e)
  have h₂ := hf (Set.make [e, u]) (Set.make_wf _)
  rw [atoms1e_of_mem (Set.mem_singleton_self e)] at h₁
  rw [atoms1e_of_mem (mem_make_pair.mpr (Or.inl rfl))] at h₂
  have hfalse : ¬ ∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧
      (Set.singleton e).subset X = false := by
    rw [qe_c_nsup_lit (Set.singleton_wf e), subset_false_iff]
    rintro ⟨x, hx, hxe⟩
    exact hxe hx
  have htrue : ∃ X : Set α, X.WellFormed ∧ X.contains e = true ∧
      (Set.make [e, u]).subset X = false := by
    rw [qe_c_nsup_lit (Set.make_wf _), subset_false_iff]
    exact ⟨u, mem_make_pair.mpr (Or.inr rfl), not_mem_singleton hu⟩
  exact hfalse (h₁.mp (h₂.mpr htrue))

/-- #56 `¬C ∧ I` is beyond every boolean combination of the atoms over `A`, `e` [H2]:
the same pair as #48. -/
theorem qe_nc_i_inexpressible {α : Type} [LT α] [DecidableLT α] [StrictLT α] [DecidableEq α]
  (h2 : TwoElems α) (e : α) :
  ¬ ∃ f : Atoms1e → Bool, ∀ A : Set α, A.WellFormed →
    (f (atoms1e A e) = true ↔
      ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧ X.intersects A = true) := by
  rintro ⟨f, hf⟩
  obtain ⟨u, hu⟩ := h2.exists_ne e
  have h₁ := hf (Set.singleton e) (Set.singleton_wf e)
  have h₂ := hf (Set.make [e, u]) (Set.make_wf _)
  rw [atoms1e_of_mem (Set.mem_singleton_self e)] at h₁
  rw [atoms1e_of_mem (mem_make_pair.mpr (Or.inl rfl))] at h₂
  have hfalse : ¬ ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧
      X.intersects (Set.singleton e) = true := by
    rw [qe_nc_i_lit (Set.singleton_wf e), subset_false_iff]
    rintro ⟨x, hx, hxe⟩
    exact hxe hx
  have htrue : ∃ X : Set α, X.WellFormed ∧ X.contains e = false ∧
      X.intersects (Set.make [e, u]) = true := by
    rw [qe_nc_i_lit (Set.make_wf _), subset_false_iff]
    exact ⟨u, mem_make_pair.mpr (Or.inr rfl), not_mem_singleton hu⟩
  exact hfalse (h₁.mp (h₂.mpr htrue))

end Cedar.DNF
