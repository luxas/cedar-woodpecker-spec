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

module

public import Cedar.DNF

/-!
This file models the atom splitter implemented in Rust in
`cedar-policy-symcc/src/dnf/split.rs` (the `cedar-spec/cedar/` checkout,
branch `split-atoms-error-order`, Phase 3 Step 2). The splitter rewrites a
boolean expression so that no atom contains any `&&`/`||`/`!`/`if` node
outside an `iferror` call or an equality of booleans (both opaque, see
`hoist`): the first
offending node `B` inside an atom `A[B]` — in pre-order, children in
evaluation order — is hoisted to the top, `A[if c then x else y]` becoming
`if c then A[x] else A[y]` and a boolean `B` becoming
`if B then A[true] else A[false]`, guarded by `B`'s left siblings `g` — the
subterms evaluated before `B`, whose errors must keep surfacing before
`c`'s — as `if (g₁ == g₁ && …) then … else false` (`guarded`); the
substituted atoms are strictly smaller and are split further until clean,
at which point equalities of two literals (`true == false`, `1 == 3`) are
folded to their boolean value.

The definitions mirror the Rust code case-for-case, in the same child order
(`expr_util::children` equals the constructor argument order here; for record
children that means fidelity to Rust's key-sorted `BTreeMap` order holds on
key-sorted inputs, which the DRT's canonicalization guarantees — the theorems
themselves hold for any order). Differences by design, as for the Step 1
model in `Cedar.DNF`:

* no node budget (`max_nodes`) and no `stack_size_check` — resource limits,
  not semantics; recursion here is well-founded on the strictly shrinking
  substituted atoms;
* no erasure (Rust's `erase_and_fold` erases per-node data; Lean's `Expr`
  carries none, so only the fold remains).

The equivalence and cleanliness theorems are in `Cedar.Thm.DNF`.
-/

namespace Cedar.DNF

open Cedar.Spec

@[expose] public section

/-- Whether the node is boolean structure that must not appear inside an
atom: `&&`, `||`, `!` or `if`. -/
def isOffender : Expr → Bool
  | .and _ _ | .or _ _ | .ite _ _ _ | .unaryApp .not _ => true
  | _ => false

/-- Folds every equality of two literals to its boolean value, bottom-up
(Rust `erase_and_fold`, minus the erasure): literal equality is decided by
total value equality across types and never errors. -/
def foldEq : Expr → Expr
  | .lit p => .lit p
  | .var v => .var v
  | .ite x₁ x₂ x₃ => .ite (foldEq x₁) (foldEq x₂) (foldEq x₃)
  | .and x₁ x₂ => .and (foldEq x₁) (foldEq x₂)
  | .or x₁ x₂ => .or (foldEq x₁) (foldEq x₂)
  | .unaryApp op x => .unaryApp op (foldEq x)
  | .binaryApp op x₁ x₂ =>
    match op, foldEq x₁, foldEq x₂ with
    | .eq, .lit p₁, .lit p₂ => boolLit (p₁ == p₂)
    | op, y₁, y₂ => .binaryApp op y₁ y₂
  | .getAttr x a => .getAttr (foldEq x) a
  | .hasAttr x a => .hasAttr (foldEq x) a
  | .set xs => .set (xs.map₁ (fun ⟨x, _⟩ => foldEq x))
  | .record axs => .record (axs.map₂ (fun ⟨(a, x), _⟩ => (a, foldEq x)))
  | .call xfn xs => .call xfn (xs.map₁ (fun ⟨x, _⟩ => foldEq x))

/-- `g == g`: `true` whenever `g` evaluates, `g`'s own error otherwise (Rust
`self_eq`). -/
def selfEq (g : Expr) : Expr := .binaryApp .eq g g

/-- Whether a node cannot err once its children have evaluated: a literal, a
variable, set and record construction, and `==` (total value equality). Such
a node needs no guard of its own; its children's guards speak for it (Rust
`never_errs_itself`). -/
def neverErrsItself : Expr → Bool
  | .lit _ | .var _ | .set _ | .record _ | .binaryApp .eq _ _ => true
  | _ => false

mutual

/-- Prepends the guards for a left sibling `x` (already folded): a node that
never errs by itself contributes its children's guards in order (so a
literal or a variable contributes none); anything else is a guard itself
(Rust `add_guards`). -/
def addGuards : Expr → List Expr → List Expr
  | .lit _, gs => gs
  | .var _, gs => gs
  | .set xs, gs => addGuardsList xs gs
  | .record axs, gs => addGuardsRecord axs gs
  | .binaryApp .eq a b, gs => addGuards a (addGuards b gs)
  | x, gs => x :: gs
termination_by x => sizeOf x

def addGuardsList : List Expr → List Expr → List Expr
  | [], gs => gs
  | x :: rest, gs => addGuards x (addGuardsList rest gs)
termination_by xs => sizeOf xs

def addGuardsRecord : List (Attr × Expr) → List Expr → List Expr
  | [], gs => gs
  | (_, x) :: rest, gs => addGuards x (addGuardsRecord rest gs)
termination_by axs => sizeOf axs

end

/-- Prepends a left sibling to the guards, folded (Rust `erase_and_fold`, so
a literal equality an earlier substitution produced counts as the literal
it is) and decomposed (`addGuards`; Rust `guards_of`). -/
def addGuard (x : Expr) (gs : List Expr) : List Expr :=
  addGuards (foldEq x) gs

/-- The `&&`-spine of an expression, left to right, without `true` literals
(Rust `conjuncts`). -/
def conjuncts : Expr → List Expr
  | .and x₁ x₂ => conjuncts x₁ ++ conjuncts x₂
  | .lit (.bool true) => []
  | e => [e]

/-- The `||`-spine of an expression, left to right, without `false` literals
(Rust `disjuncts`). -/
def disjuncts : Expr → List Expr
  | .or x₁ x₂ => disjuncts x₁ ++ disjuncts x₂
  | .lit (.bool false) => []
  | e => [e]

mutual

/-- The subterms `e` evaluates whenever it evaluates at all, to any value,
prepended to `gs`: `e` itself, and recursively every child of a strict node,
the test or left operand of an `if`/`&&`/`||`, and nothing inside an
`iferror` call — without the nodes that never err by themselves
(`neverErrsItself`), which no guard ever is (Rust `evaluated`). -/
def evaluated : Expr → List Expr → List Expr
  | .lit _, gs => gs
  | .var _, gs => gs
  | e@(.ite c _ _), gs => e :: evaluated c gs
  | e@(.and l _), gs => e :: evaluated l gs
  | e@(.or l _), gs => e :: evaluated l gs
  | e@(.unaryApp _ x), gs => e :: evaluated x gs
  | .binaryApp .eq a b, gs => evaluated a (evaluated b gs)
  | e@(.binaryApp _ a b), gs => e :: evaluated a (evaluated b gs)
  | e@(.getAttr x _), gs => e :: evaluated x gs
  | e@(.hasAttr x _), gs => e :: evaluated x gs
  | .set xs, gs => evaluatedList xs gs
  | .record axs, gs => evaluatedRecord axs gs
  | e@(.call xfn xs), gs => if xfn = .ifError then e :: gs else e :: evaluatedList xs gs
termination_by e => sizeOf e

def evaluatedList : List Expr → List Expr → List Expr
  | [], gs => gs
  | x :: rest, gs => evaluated x (evaluatedList rest gs)
termination_by xs => sizeOf xs

def evaluatedRecord : List (Attr × Expr) → List Expr → List Expr
  | [], gs => gs
  | (_, x) :: rest, gs => evaluated x (evaluatedRecord rest gs)
termination_by axs => sizeOf axs

end

/-- What a true condition establishes: every conjunct of its `&&`-spine
evaluated, and so did their strict subterms (Rust `learn_true`). -/
def learnTrue (c : Expr) : List Expr :=
  (conjuncts c).foldr evaluated []

/-- What a false condition establishes: every disjunct of its `||`-spine
evaluated, and so did their strict subterms (Rust `learn_false`). -/
def learnFalse (c : Expr) : List Expr :=
  (disjuncts c).foldr evaluated []

/-- The guards not already established by `ctx`, in order and without
repetition (Rust `new_guards`). -/
def newGuards (ctx : List Expr) : List Expr → List Expr
  | [] => []
  | g :: rest => if g ∈ ctx then newGuards ctx rest else g :: newGuards (g :: ctx) rest

/-- The chain `d₁ && (d₂ && … dₖ)`; the empty chain is `true` (also the
model of Rust `deny_witness`'s chains in `Cedar.DNF.Combine`). -/
def andChain : List Expr → Expr
  | [] => boolLit true
  | [d] => d
  | d :: rest => .and d (andChain rest)

/-- `if (g₁ == g₁ && (g₂ == g₂ && …)) then e else false` over the guards, in
order; `e` itself without guards (Rust `guard`). -/
def guarded (gs : List Expr) (e : Expr) : Expr :=
  match gs with
  | [] => e
  | gs => .ite (andChain (gs.map selfEq)) e (boolLit false)

/-- What `hoist` finds: the guards (the offending node's left siblings — the
subterms evaluated before it — in evaluation order, folded, without the ones
that cannot err, `neverErrs`), the condition, and the two substituted
copies. -/
abbrev Hoisted := List Expr × Expr × Expr × Expr

mutual

/-- What hoisting one child yields: an `if` child contributes its test and
its two branches; a boolean child is replaced by the two boolean literals;
anything else is searched inside. -/
def hoistStep : Expr → Option Hoisted
  | .ite cc tt ee => some ([], cc, tt, ee)
  | c@(.and _ _) | c@(.or _ _) | c@(.unaryApp .not _) =>
    some ([], c, boolLit true, boolLit false)
  | c => hoist c
termination_by c => (sizeOf c, 1)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; omega)

/-- The first offending node strictly inside `e` (pre-order, children in
evaluation order), as `(guards, cond, when_true, when_false)`: once every
guard evaluates without error, `e` evaluates like
`if cond then when_true else when_false`; `none` when `e` is clean (Rust
`hoist`). A child searched without finding the node is evaluated before it
and becomes a guard (`addGuard`). -/
def hoist : Expr → Option Hoisted
  | .lit _ => none
  | .var _ => none
  | .ite x₁ x₂ x₃ =>
    match hoistStep x₁ with
    | some (gs, cond, t, f) => some (gs, cond, .ite t x₂ x₃, .ite f x₂ x₃)
    | none =>
      match hoistStep x₂ with
      | some (gs, cond, t, f) => some (addGuard x₁ gs, cond, .ite x₁ t x₃, .ite x₁ f x₃)
      | none =>
        match hoistStep x₃ with
        | some (gs, cond, t, f) =>
          some (addGuard x₁ (addGuard x₂ gs), cond, .ite x₁ x₂ t, .ite x₁ x₂ f)
        | none => none
  | .and x₁ x₂ =>
    match hoistStep x₁ with
    | some (gs, cond, t, f) => some (gs, cond, .and t x₂, .and f x₂)
    | none =>
      match hoistStep x₂ with
      | some (gs, cond, t, f) => some (addGuard x₁ gs, cond, .and x₁ t, .and x₁ f)
      | none => none
  | .or x₁ x₂ =>
    match hoistStep x₁ with
    | some (gs, cond, t, f) => some (gs, cond, .or t x₂, .or f x₂)
    | none =>
      match hoistStep x₂ with
      | some (gs, cond, t, f) => some (addGuard x₁ gs, cond, .or x₁ t, .or x₁ f)
      | none => none
  | .unaryApp op x =>
    match hoistStep x with
    | some (gs, cond, t, f) => some (gs, cond, .unaryApp op t, .unaryApp op f)
    | none => none
  | .binaryApp op x₁ x₂ =>
    match hoistStep x₁ with
    | some (gs, cond, t, f) => some (gs, cond, .binaryApp op t x₂, .binaryApp op f x₂)
    | none =>
      match hoistStep x₂ with
      | some (gs, cond, t, f) =>
        some (addGuard x₁ gs, cond, .binaryApp op x₁ t, .binaryApp op x₁ f)
      | none => none
  | .getAttr x a =>
    match hoistStep x with
    | some (gs, cond, t, f) => some (gs, cond, .getAttr t a, .getAttr f a)
    | none => none
  | .hasAttr x a =>
    match hoistStep x with
    | some (gs, cond, t, f) => some (gs, cond, .hasAttr t a, .hasAttr f a)
    | none => none
  | .set xs =>
    match hoistList xs with
    | some (gs, cond, ts, fs) => some (gs, cond, .set ts, .set fs)
    | none => none
  | .record axs =>
    match hoistRecord axs with
    | some (gs, cond, ts, fs) => some (gs, cond, .record ts, .record fs)
    | none => none
  -- `iferror(e, d)` catches `e`'s error: hoisting a node out of it would move
  -- that node's error outside the coalescing scope, so the call is opaque.
  | .call xfn xs =>
    if xfn = .ifError then none else
    match hoistList xs with
    | some (gs, cond, ts, fs) => some (gs, cond, .call xfn ts, .call xfn fs)
    | none => none
termination_by e => (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

/-- `hoist` over a child list: the first child with an offending node is
substituted, the others are kept — the earlier ones as guards. -/
def hoistList : List Expr → Option (List Expr × Expr × List Expr × List Expr)
  | [] => none
  | x :: rest =>
    match hoistStep x with
    | some (gs, cond, t, f) => some (gs, cond, t :: rest, f :: rest)
    | none =>
      match hoistList rest with
      | some (gs, cond, ts, fs) => some (addGuard x gs, cond, x :: ts, x :: fs)
      | none => none
termination_by xs => (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

/-- `hoistList` for record fields. -/
def hoistRecord :
  List (Attr × Expr) → Option (List Expr × Expr × List (Attr × Expr) × List (Attr × Expr))
  | [] => none
  | (a, x) :: rest =>
    match hoistStep x with
    | some (gs, cond, t, f) => some (gs, cond, (a, t) :: rest, (a, f) :: rest)
    | none =>
      match hoistRecord rest with
      | some (gs, cond, ts, fs) => some (addGuard x gs, cond, (a, x) :: ts, (a, x) :: fs)
      | none => none
termination_by axs => (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)
end

/-! ### Sizes: the substituted copies are strictly smaller -/

theorem prim_one_le_sizeOf (p : Prim) : 1 ≤ sizeOf p := by
  cases p <;> simp +arith

theorem var_one_le_sizeOf (v : Var) : 1 ≤ sizeOf v := by
  cases v <;> simp +arith

theorem list_one_le_sizeOf {α} [SizeOf α] (xs : List α) : 1 ≤ sizeOf xs := by
  cases xs <;> simp +arith

/-- Every expression has size at least 2 (`.var` is the smallest). -/
theorem expr_two_le_sizeOf : (e : Expr) → 2 ≤ sizeOf e
  | .lit p => by have := prim_one_le_sizeOf p; simp +arith; omega
  | .var v => by have := var_one_le_sizeOf v; simp +arith; omega
  | .ite x₁ _ _ => by have := expr_two_le_sizeOf x₁; simp +arith; omega
  | .and x₁ _ => by have := expr_two_le_sizeOf x₁; simp +arith; omega
  | .or x₁ _ => by have := expr_two_le_sizeOf x₁; simp +arith; omega
  | .unaryApp _ x => by have := expr_two_le_sizeOf x; simp +arith; omega
  | .binaryApp _ x₁ _ => by have := expr_two_le_sizeOf x₁; simp +arith; omega
  | .getAttr x _ => by have := expr_two_le_sizeOf x; simp +arith; omega
  | .hasAttr x _ => by have := expr_two_le_sizeOf x; simp +arith; omega
  | .set xs => by have := list_one_le_sizeOf xs; simp +arith; omega
  | .record axs => by have := list_one_le_sizeOf axs; simp +arith; omega
  | .call _ xs => by have := list_one_le_sizeOf xs; simp +arith; omega

theorem boolLit_sizeOf (b : Bool) : sizeOf (boolLit b) = 3 := by
  cases b <;> simp [boolLit]

mutual

theorem hoistStep_size {c cond t f : Expr} {gs : List Expr}
  (h : hoistStep c = some (gs, cond, t, f)) :
  sizeOf cond ≤ sizeOf c ∧ sizeOf t < sizeOf c ∧ sizeOf f < sizeOf c
:= by
  match c with
  | .ite cc tt ee =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h₀, h₁, h₂, h₃⟩ := h
    subst h₀ h₁ h₂ h₃
    simp +arith
  | .and x₁ x₂ =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h₀, h₁, h₂, h₃⟩ := h
    subst h₀ h₁ h₂ h₃
    have e₁ := expr_two_le_sizeOf x₁
    have e₂ := expr_two_le_sizeOf x₂
    simp +arith [boolLit_sizeOf]
    omega
  | .or x₁ x₂ =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h₀, h₁, h₂, h₃⟩ := h
    subst h₀ h₁ h₂ h₃
    have e₁ := expr_two_le_sizeOf x₁
    have e₂ := expr_two_le_sizeOf x₂
    simp +arith [boolLit_sizeOf]
    omega
  | .unaryApp .not x =>
    simp only [hoistStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h₀, h₁, h₂, h₃⟩ := h
    subst h₀ h₁ h₂ h₃
    have e₁ := expr_two_le_sizeOf x
    simp +arith [boolLit_sizeOf]
    omega
  | .lit p =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .var v =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .unaryApp .neg x =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .unaryApp .isEmpty x =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .unaryApp (.like _) x =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .unaryApp (.is _) x =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .binaryApp _ _ _ =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .getAttr _ _ =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .hasAttr _ _ =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .set _ =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .record _ =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
  | .call _ _ =>
    have hs := hoist_size (by simpa [hoistStep] using h)
    exact ⟨Nat.le_of_lt hs.1, hs.2⟩
termination_by (sizeOf c, 1)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.right; omega)

theorem hoist_size {e cond t f : Expr} {gs : List Expr}
  (h : hoist e = some (gs, cond, t, f)) :
  sizeOf cond < sizeOf e ∧ sizeOf t < sizeOf e ∧ sizeOf f < sizeOf e
:= by
  match e with
  | .lit _ => simp [hoist] at h
  | .var _ => simp [hoist] at h
  | .ite x₁ x₂ x₃ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have hs := hoistStep_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next =>
        split at h
        next gs' cond' t' f' heq =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hg, hc, ht, hf⟩ := h
          subst hg hc ht hf
          have hs := hoistStep_size heq
          refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
        next => simp at h
  | .and x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have hs := hoistStep_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next => simp at h
  | .or x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have hs := hoistStep_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next => simp at h
  | .binaryApp op x₁ x₂ =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next =>
      split at h
      next gs' cond' t' f' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have hs := hoistStep_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next => simp at h
  | .unaryApp op x =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next => simp at h
  | .getAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next => simp at h
  | .hasAttr x a =>
    simp only [hoist] at h
    split at h
    next gs' cond' t' f' heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next => simp at h
  | .set xs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistList_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next => simp at h
  | .record axs =>
    simp only [hoist] at h
    split at h
    next gs' cond' ts fs heq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hc, ht, hf⟩ := h
      subst hg hc ht hf
      have hs := hoistRecord_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
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
        have hs := hoistList_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next => simp at h
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem hoistList_size {xs : List Expr} {cond : Expr} {ts fs gs : List Expr}
  (h : hoistList xs = some (gs, cond, ts, fs)) :
  sizeOf cond < sizeOf xs ∧ sizeOf ts < sizeOf xs ∧ sizeOf fs < sizeOf xs
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
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next =>
      split at h
      next gs' cond' ts' fs' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have hs := hoistList_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next => simp at h
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

theorem hoistRecord_size {axs : List (Attr × Expr)} {cond : Expr} {gs : List Expr}
  {ts fs : List (Attr × Expr)}
  (h : hoistRecord axs = some (gs, cond, ts, fs)) :
  sizeOf cond < sizeOf axs ∧ sizeOf ts < sizeOf axs ∧ sizeOf fs < sizeOf axs
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
      have hs := hoistStep_size heq
      refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
    next =>
      split at h
      next gs' cond' ts' fs' heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hg, hc, ht, hf⟩ := h
        subst hg hc ht hf
        have hs := hoistRecord_size heq
        refine ⟨?_, ?_, ?_⟩ <;> (simp +arith; omega)
      next => simp at h
termination_by (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

end

/-! ### The splitter -/

mutual

/-- Splits the atoms of a boolean expression, recursing through its
`&&`/`||`/`!`/`if` structure (Rust `split_structure`). `ctx` holds the guards
already established by enclosing wrappers: they have evaluated without error
wherever this expression is evaluated, so they need no repeating. Inside the
then branch of an `if` and the right operand of an `&&`, the test / left
operand was true (`learnTrue`); inside the else branch and the right operand
of an `||`, it was false (`learnFalse`). -/
def splitStructure (ctx : List Expr) : Expr → Expr
  | .lit (.bool b) => boolLit b
  | .and x₁ x₂ => .and (splitStructure ctx x₁) (splitStructure (ctx ++ learnTrue x₁) x₂)
  | .or x₁ x₂ => .or (splitStructure ctx x₁) (splitStructure (ctx ++ learnFalse x₁) x₂)
  | .unaryApp .not x => .unaryApp .not (splitStructure ctx x)
  | .ite x₁ x₂ x₃ =>
    .ite (splitStructure ctx x₁) (splitStructure (ctx ++ learnTrue x₁) x₂)
      (splitStructure (ctx ++ learnFalse x₁) x₃)
  | e => splitAtom ctx e
termination_by e => (sizeOf e, 1)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; simp +arith)

/-- Splits one atom: hoists its first offending node, if any, guarded by the
node's left siblings not already established by `ctx`, and recurses under the
extended context; a clean atom has its literal equalities folded (Rust
`split_atom`). -/
def splitAtom (ctx : List Expr) (e : Expr) : Expr :=
  match _h : hoist e with
  | none => foldEq e
  | some (gs, cond, t, f) =>
    -- the hoisted condition is at structure position now; the guards make
    -- the left siblings' errors surface before it, as in the original
    let fresh := newGuards ctx gs
    let inner := ctx ++ fresh
    -- the hoisted condition ran before either copy: its strict subterms
    -- need no guard inside them
    let copies := inner ++ evaluated cond []
    guarded fresh (.ite (splitStructure inner cond) (splitAtom copies t) (splitAtom copies f))
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  · have := (hoist_size _h).1
    apply Prod.Lex.left
    omega
  · have := (hoist_size _h).2.1
    apply Prod.Lex.left
    omega
  · have := (hoist_size _h).2.2
    apply Prod.Lex.left
    omega

end

/-- Rewrites the boolean expression `e` so that no atom contains any
`&&`/`||`/`!`/`if` node outside an opaque atom — an `iferror` call or an
equality of booleans (Rust `split_atoms`, without the node budget),
preserving evaluation exactly — the same value or the same error,
`Cedar.Thm.DNF.evaluate_splitAtoms`. -/
def splitAtoms (e : Expr) : Expr :=
  splitStructure [] e

/-! ### Cleanliness: the postcondition of splitting -/

/-- No `&&`/`||`/`!`/`if` node anywhere in the expression outside an `iferror`
call or an equality of booleans (whose insides the splitter never looks at,
so they count as clean). -/
def offFree : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .and _ _ | .or _ _ | .ite _ _ _ => false
  | .unaryApp op x => op != .not && offFree x
  | .binaryApp _ x₁ x₂ => offFree x₁ && offFree x₂
  | .getAttr x _ => offFree x
  | .hasAttr x _ => offFree x
  | .set xs => xs.attach.all (fun ⟨x, _⟩ => offFree x)
  | .record axs => axs.attach.all (fun ⟨(_, x), _⟩ => offFree x)
  -- an `iferror` call is opaque: its inside is never split, so it counts as
  -- offender-free whatever it contains
  | .call xfn xs => xfn = .ifError || xs.attach.all (fun ⟨x, _⟩ => offFree x)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem
       simp +arith at this
       omega))

/-- Every atom of the expression — its maximal non-structure subterms — is
free of `&&`/`||`/`!`/`if` nodes (the test suite's `atoms_are_clean`). -/
def cleanAtoms : Expr → Bool
  | .lit (.bool _) => true
  | .and x₁ x₂ => cleanAtoms x₁ && cleanAtoms x₂
  | .or x₁ x₂ => cleanAtoms x₁ && cleanAtoms x₂
  | .unaryApp .not x => cleanAtoms x
  | .ite x₁ x₂ x₃ => cleanAtoms x₁ && cleanAtoms x₂ && cleanAtoms x₃
  | e => offFree e

end

end Cedar.DNF
