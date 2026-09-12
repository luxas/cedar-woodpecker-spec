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

public import Cedar.DNF.Split

/-!
This file models the record- and set-literal elimination implemented in Rust
in `cedar-policy-symcc/src/dnf/elim.rs` (the `cedar-spec/cedar/` checkout,
branch `eliminate-aggregates`, Phase 4 Step 1). One bottom-up pass over every
atom rewrites the structure a literal hides under `.attr` / `has` / `==` (a
record on both sides, a set on either) / `contains` / `containsAll` /
`containsAny` / `isEmpty` / `in` into the operations on its elements
(`rewrite`, over already-rewritten children), and
guards the rewritten atom with the subterms the original evaluated, in
evaluation order — every maximal unrewritten subterm (a leaf region, decomposed
like a split guard) and, for an unrewritten node above a rewritten one, the
node itself — so that the pass is exact under the typing the Rust entry point
enforces (`Cedar.Thm.DNF.evaluate_eliminate`); guards the rewritten atom
evaluates first itself, in the same order, are dropped again (`dropRepeated`).
The pipeline `normalize` is `splitAtoms ∘ eliminate ∘ splitAtoms`: an
`iferror` call and any `&&`/`||`/`!`/`if` inside an atom are opaque, so the
pass is exact on any input but complete only on split input (the first split
exposes every literal); the second split hoists the `&&`/`||` the rules
introduce.

The definitions mirror the Rust code case-for-case; the differences by design
are those of `Cedar.DNF.Split` (no stack check, no erasure) plus: the Rust
entry point typechecks its input, which the model does not (the theorems
carry the typing facts as a hypothesis instead), and record equality compares
the two records' key *lists* where Rust compares its `BTreeMap`s' key sets —
the same thing on key-sorted inputs, which the DRT's canonicalization
guarantees (the rule is exact either way).
-/

namespace Cedar.DNF

open Cedar.Spec

@[expose] public section

/-- The chain `d₁ || (d₂ || … dₖ)`; the empty chain is `false` (Rust
`or_chain`). -/
def orChain : List Expr → Expr
  | [] => boolLit false
  | [d] => d
  | d :: rest => .or d (orChain rest)

/-- The first field named `a` (Rust `map.get`; Rust records have unique
keys). -/
def recordGet (axs : List (Attr × Expr)) (a : Attr) : Option Expr :=
  (axs.find? (fun ax => ax.1 == a)).map Prod.snd

/-- Whether a field is named `a` (Rust `map.contains_key`). -/
def recordHas (axs : List (Attr × Expr)) (a : Attr) : Bool :=
  axs.any (fun ax => ax.1 == a)

/-- The termination argument of the equality block: the operands' sizes
shrink into a list element or a record field, or stay while the function
index drops (`elimEq` → `elimSetEq` → `elimContainsAll` → `elimContains`). -/
macro "elim_decreasing" : tactic => `(tactic|
  (simp_wf
   subst_vars
   try have := List.sizeOf_lt_of_mem ‹_ ∈ _›
   simp only [Prod.lex_def, Prod.mk.injEq]
   try simp +arith
   try omega
   done))

mutual

/-- `a == b`, rewritten key by key when both are record literals with the
same, duplicate-free keys, and as `containsAll` both ways when either is a
set literal (Rust `eq`; Rust records have unique keys). -/
def elimEq (a b : Expr) : Expr :=
  match a, b with
  | .record axs, .record bys =>
    if axs.map Prod.fst = bys.map Prod.fst ∧ (axs.map Prod.fst).Nodup then
      andChain (eqFields axs bys)
    else .binaryApp .eq a b
  | .set ls, b => elimSetEq (.set ls) b
  | a, .set ls => elimSetEq a (.set ls)
  | a, b => .binaryApp .eq a b
termination_by (sizeOf a + sizeOf b, 3)
decreasing_by all_goals elim_decreasing

/-- The per-key value equalities of two records with the same keys. -/
def eqFields : List (Attr × Expr) → List (Attr × Expr) → List Expr
  | (_, v₁) :: r₁, (_, v₂) :: r₂ => elimEq v₁ v₂ :: eqFields r₁ r₂
  | _, _ => []
termination_by l₁ l₂ => (sizeOf l₁ + sizeOf l₂, 0)
decreasing_by all_goals elim_decreasing

/-- `a == b` with a set literal on either side: `a.containsAll(b) &&
b.containsAll(a)`, each rewritten where its right operand is the literal
(Rust `set_eq`). Exact for two well-formed set values
(`Cedar.Thm.DNF.elimSetEq_sound`). -/
def elimSetEq (a b : Expr) : Expr :=
  .and (elimContainsAll a b) (elimContainsAll b a)
termination_by (sizeOf a + sizeOf b, 2)
decreasing_by all_goals elim_decreasing

/-- `s.containsAll(t)`, rewritten when `t` is a set literal (Rust
`contains_all`). -/
def elimContainsAll (s t : Expr) : Expr :=
  match t with
  | .set ls => andChain (ls.map (elimContains s))
  | t => .binaryApp .containsAll s t
termination_by (sizeOf s + sizeOf t, 1)
decreasing_by all_goals elim_decreasing

/-- `s.contains(x)`, rewritten when `s` is a set literal (Rust `contains`). -/
def elimContains (s x : Expr) : Expr :=
  match s with
  | .set ls => orChain (ls.map (fun l => elimEq l x))
  | s => .binaryApp .contains s x
termination_by (sizeOf s + sizeOf x, 0)
decreasing_by all_goals elim_decreasing

end

/-- The rule for a node whose children are already rewritten, if one applies
(Rust `rewrite`); the empty chains are `true` and `false`, exact under the
typing hypothesis (`s.containsAll([])` is `true` for a set-typed `s`). -/
def rewrite : Expr → Option Expr
  | .getAttr (.record axs) a => recordGet axs a
  | .hasAttr (.record axs) a => some (boolLit (recordHas axs a))
  | .unaryApp .isEmpty (.set ls) => some (boolLit ls.isEmpty)
  | .binaryApp .eq (.record axs) (.record bys) =>
    if axs.map Prod.fst = bys.map Prod.fst ∧ (axs.map Prod.fst).Nodup then
      some (andChain (eqFields axs bys))
    else none
  | .binaryApp .eq (.set ls) x => some (elimSetEq (.set ls) x)
  | .binaryApp .eq x (.set ls) => some (elimSetEq x (.set ls))
  | .binaryApp .contains (.set ls) x => some (orChain (ls.map (fun l => elimEq l x)))
  | .binaryApp .containsAll s (.set ls) => some (andChain (ls.map (elimContains s)))
  | .binaryApp .containsAny s (.set ls) => some (orChain (ls.map (elimContains s)))
  | .binaryApp .containsAny (.set ls) s => some (orChain (ls.map (elimContains s)))
  | .binaryApp .mem e (.set xs) => some (orChain (xs.map (fun x => .binaryApp .mem e x)))
  | _ => none

/-- What a child contributes: its rewrite, or — as a leaf region — its
decomposed guard and itself. -/
def childOf (x : Expr) : Option (List Expr × Expr) → Bool × List Expr × Expr
  | some (gs, t) => (true, gs, t)
  | none => (false, addGuard x [], x)

/-- Finishes a node rebuilt over its children's results: the rule's result
if one applies; else, when a child changed, the node with its own guard
unless it cannot err (Rust `elim`'s tail). -/
def finish (rebuilt : Expr) (changed : Bool) (gs : List Expr) : Option (List Expr × Expr) :=
  match rewrite rebuilt with
  | some r => some (gs, r)
  | none =>
    if changed then some (if neverErrsItself rebuilt then gs else gs ++ [rebuilt], rebuilt)
    else none

mutual

/-- Eliminates inside `e`: `none` when nothing inside was rewritten (a leaf
region), else the guards — the subterms the original evaluates before the
rewritten term would, in evaluation order — and the rewritten term (Rust
`elim`). An `iferror` call and any `&&`/`||`/`!`/`if` inside an atom are
opaque. -/
def elim : Expr → Option (List Expr × Expr)
  | .lit _ => none
  | .var _ => none
  | .and _ _ => none
  | .or _ _ => none
  | .ite _ _ _ => none
  | .unaryApp .not _ => none
  | .unaryApp op x =>
    let r := childOf x (elim x)
    finish (.unaryApp op r.2.2) r.1 r.2.1
  | .binaryApp op x₁ x₂ =>
    let r₁ := childOf x₁ (elim x₁)
    let r₂ := childOf x₂ (elim x₂)
    finish (.binaryApp op r₁.2.2 r₂.2.2) (r₁.1 || r₂.1) (r₁.2.1 ++ r₂.2.1)
  | .getAttr x a =>
    let r := childOf x (elim x)
    finish (.getAttr r.2.2 a) r.1 r.2.1
  | .hasAttr x a =>
    let r := childOf x (elim x)
    finish (.hasAttr r.2.2 a) r.1 r.2.1
  | .set xs =>
    let r := elimList xs
    finish (.set r.2.2) r.1 r.2.1
  | .record axs =>
    let r := elimRecord axs
    finish (.record r.2.2) r.1 r.2.1
  | .call xfn xs =>
    if xfn = .ifError then none else
    let r := elimList xs
    finish (.call xfn r.2.2) r.1 r.2.1
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals simp +arith

/-- `elim` over a child list: whether any changed, all guards in order, the
terms. -/
def elimList : List Expr → Bool × List Expr × List Expr
  | [] => (false, [], [])
  | x :: rest =>
    let r := childOf x (elim x)
    let rs := elimList rest
    (r.1 || rs.1, r.2.1 ++ rs.2.1, r.2.2 :: rs.2.2)
termination_by xs => sizeOf xs
decreasing_by
  all_goals simp_wf
  all_goals simp +arith

/-- `elimList` for record fields. -/
def elimRecord : List (Attr × Expr) → Bool × List Expr × List (Attr × Expr)
  | [] => (false, [], [])
  | (a, x) :: rest =>
    let r := childOf x (elim x)
    let rs := elimRecord rest
    (r.1 || rs.1, r.2.1 ++ rs.2.1, (a, r.2.2) :: rs.2.2)
termination_by axs => sizeOf axs
decreasing_by
  all_goals simp_wf
  all_goals simp +arith

end

mutual

/-- The subterms of `e` that can err, in evaluation order and at the
granularity of guards — a node that can err is a unit, one that never errs by
itself contributes its children's — as far as evaluation is certain to
proceed: the test or left operand of an `if`/`&&`/`||` only, after which the
list is *incomplete* (`false`; a strict parent lists nothing past an
incomplete child). An error in any of them is `e`'s error, and it is the
first in this order (`Cedar.Thm.DNF.underGuards_evalList_prefix`); a complete
list that evaluates means `e` does (`transparent_evalList_ok`). Rust
`eval_list`. -/
def evalList : Expr → List Expr × Bool
  | .ite c _ _ => ((evalList c).1, false)
  | .and l _ => ((evalList l).1, false)
  | .or l _ => ((evalList l).1, false)
  | .binaryApp .eq a b =>
    let ra := evalList a
    if ra.2 then let rb := evalList b; (ra.1 ++ rb.1, rb.2) else (ra.1, false)
  | .set xs => evalListList xs
  | .record axs => evalListRecord axs
  | .lit _ => ([], true)
  | .var _ => ([], true)
  | e => ([e], true)
termination_by e => sizeOf e

def evalListList : List Expr → List Expr × Bool
  | [] => ([], true)
  | x :: rest =>
    let r := evalList x
    if r.2 then let rs := evalListList rest; (r.1 ++ rs.1, rs.2) else (r.1, false)
termination_by xs => sizeOf xs

def evalListRecord : List (Attr × Expr) → List Expr × Bool
  | [] => ([], true)
  | (_, x) :: rest =>
    let r := evalList x
    if r.2 then let rs := evalListRecord rest; (r.1 ++ rs.1, rs.2) else (r.1, false)
termination_by axs => sizeOf axs

end

/-- Drops the guards that `t` evaluates itself, first and in the same order:
the longest suffix of `gs` that is a prefix of `evalList t` (Rust
`drop_repeated`). -/
def dropRepeated (gs : List Expr) (t : Expr) : List Expr :=
  let l := (evalList t).1
  match (List.range (gs.length + 1)).find? (fun keep => (gs.drop keep).isPrefixOf l) with
  | some keep => gs.take keep
  | none => gs

/-- Eliminates in one atom: a rewritten atom is guarded by the guards the
context does not already establish (deduped first) and that it does not
evaluate first itself, an untouched one is kept (Rust `elim_structure`'s
atom arm). -/
def elimAtom (ctx : List Expr) (e : Expr) : Expr :=
  match elim e with
  | none => e
  | some (gs, t) => guarded (dropRepeated (newGuards ctx gs) t) t

/-- Eliminates in every atom, recursing through the `&&`/`||`/`!`/`if`
structure with the splitter's context (Rust `elim_structure`): the subterms
known to have evaluated here need no guard. -/
def elimStructure (ctx : List Expr) : Expr → Expr
  | .lit (.bool b) => boolLit b
  | .and x₁ x₂ => .and (elimStructure ctx x₁) (elimStructure (ctx ++ learnTrue x₁) x₂)
  | .or x₁ x₂ => .or (elimStructure ctx x₁) (elimStructure (ctx ++ learnFalse x₁) x₂)
  | .unaryApp .not x => .unaryApp .not (elimStructure ctx x)
  | .ite x₁ x₂ x₃ =>
    .ite (elimStructure ctx x₁) (elimStructure (ctx ++ learnTrue x₁) x₂)
      (elimStructure (ctx ++ learnFalse x₁) x₃)
  | e => elimAtom ctx e

/-- Rewrites every atom of the boolean expression `e` so that no record
literal sits under `.attr`, `has` or `==` and no set literal under
`contains`, `containsAll`, `containsAny`, `isEmpty` or `in` (Rust
`eliminate_aggregates`, without the typecheck), preserving evaluation exactly
under the typing hypothesis — `Cedar.Thm.DNF.evaluate_eliminate`. -/
def eliminate (e : Expr) : Expr :=
  elimStructure [] e

/-- The pipeline `splitAtoms → eliminate → splitAtoms` (Rust
`normalize_atoms`, without the typecheck). -/
def normalize (e : Expr) : Expr :=
  splitAtoms (eliminate (splitAtoms e))

end

end Cedar.DNF
