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

public import Cedar.Spec.Evaluator

/-!
This file models the DNF converter implemented in Rust in
`cedar-policy-symcc/src/dnf` (the `cedar-spec/cedar/` checkout, branch `dnf`,
Phase 3 Step 1). The converter linearises the evaluation *decision tree* of
the `&&`/`||`/`!`/`if` structure of a boolean expression: every root-to-leaf
path becomes a cube (its literals in evaluation order, negated on a `false`
edge); paths to a `true` leaf are the cubes that can be true, and every other
path — a `false` leaf, or a truncation at a contradicting literal — is a
never-true cube (`… && false`) kept only where it reproduces an error no
other cube does.

The definitions mirror the Rust code case-for-case (`paths.rs`, `mod.rs`,
`interpret.rs`), in the same depth-first order. Differences by design:

* no cube budget (`max_cubes`) and no `stack_size_check` — resource limits of
  the Rust implementation, not semantics; recursion here is structural;
* `graft` always receives the sub-paths (Rust computes them lazily when a
  leaf matches; the output is identical);
* Lean's `Expr` carries no source locations or per-node data, so the Rust
  "erased key" of an atom is the atom itself, and dedup compares expressions
  directly;
* `canError` is a pure function of the (erased) atom, where Rust's
  `can_error` is an `FnMut` applied to the un-erased atom — the verification
  covers answerers that depend only on the atom expression, which every
  intended caller (including `Dnf::of_expr`'s `|_| true`) satisfies.

The equivalence theorems are in `Cedar.Thm.DNF`.
-/

namespace Cedar.DNF

open Cedar.Spec

@[expose] public section

/-- One of the three outcomes of a boolean (sub-)expression. -/
inductive Outcome where
  | tt | ff | err
deriving Repr, DecidableEq

/-- The outcome of `!x` given that of `x`. -/
def Outcome.negated : Outcome → Outcome
  | .tt  => .ff
  | .ff  => .tt
  | .err => .err

/--
Three-valued, short-circuiting semantics of the boolean structure of an
expression over an atom valuation `v` (Rust `interpret.rs`). A valuation is a
function, so an atom has the same outcome wherever it occurs — the purity of
Cedar evaluation, by construction. `Cedar.Thm.DNF` shows that `interp`
agrees with `Cedar.Spec.evaluate` when `v` is the outcome of evaluating the
atom.
-/
def interp (v : Expr → Outcome) : Expr → Outcome
  | .lit (.bool b)   => if b then .tt else .ff
  | .unaryApp .not x => (interp v x).negated
  | .and l r         =>
    match interp v l with
    | .tt  => interp v r
    | .ff  => .ff
    | .err => .err
  | .or l r          =>
    match interp v l with
    | .tt  => .tt
    | .ff  => interp v r
    | .err => .err
  | .ite c t e       =>
    match interp v c with
    | .tt  => interp v t
    | .ff  => interp v e
    | .err => .err
  | x                => v x

/-- An atom (an expression that is not `&&`, `||`, `!`, `if` or a boolean
literal) or its negation. -/
structure Literal where
  atom    : Expr
  negated : Bool
deriving Repr, DecidableEq

/-- Where a path of the decision tree ends. -/
inductive Leaf where
  | tt | ff
  /-- The path reached a literal contradicting an earlier one; whatever the
  tree does after that point is unreachable. -/
  | contradiction
deriving Repr, DecidableEq

/-- A root-to-leaf path of the decision tree: the literals in evaluation
order, with repeated atoms removed. -/
structure Path where
  literals : List Literal
  leaf     : Leaf
deriving Repr, DecidableEq

/-- The path of the expression `true` or `false`: no literals, just a leaf. -/
def Path.ofLeaf (b : Bool) : Path :=
  ⟨[], if b then .tt else .ff⟩

/-- Swaps the `true` and `false` leaves (the paths of `!x` are those of `x`
flipped). -/
def Path.flipped (p : Path) : Path :=
  ⟨p.literals,
    match p.leaf with
    | .tt            => .ff
    | .ff            => .tt
    | .contradiction => .contradiction⟩

/-- Appends literals to `acc`, dropping any whose atom `acc` already
determined with the same polarity, and truncating to a contradiction leaf on
the opposite polarity (Rust `Path::extended`). -/
def extendLits (acc : List Literal) (leaf : Leaf) : List Literal → Path
  | []        => ⟨acc, leaf⟩
  | l :: rest =>
    match acc.find? (fun l' => l'.atom == l.atom) with
    | .none      => extendLits (acc ++ [l]) leaf rest
    | .some seen =>
      if seen.negated == l.negated
      then extendLits acc leaf rest
      else ⟨acc, .contradiction⟩

/-- `p` continued by `rest`. -/
def Path.extended (p rest : Path) : Path :=
  extendLits p.literals rest.leaf rest.literals

/-- Replaces every `at_` leaf of `ps` by the paths of `sub`, keeping other
paths in place (Rust `graft`). -/
def graft (ps : List Path) (at_ : Leaf) (sub : List Path) : List Path :=
  ps.flatMap fun p => if p.leaf == at_ then sub.map p.extended else [p]

/-- The paths of the decision tree of an expression, in depth-first order
with the `true` edge first (Rust `paths`). -/
def paths : Expr → List Path
  | .lit (.bool b)   => [.ofLeaf b]
  | .unaryApp .not x => (paths x).map .flipped
  | .and l r         => graft (paths l) .tt (paths r)
  | .or l r          => graft (paths l) .ff (paths r)
  | .ite c t e       =>
    -- both branches are grafted in one pass: grafting the else branch after
    -- the then branch would also extend the `false` leaves the then branch
    -- brought in
    (paths c).flatMap fun p =>
      match p.leaf with
      | .tt            => (paths t).map p.extended
      | .ff            => (paths e).map p.extended
      | .contradiction => [p]
  | x                =>
    [⟨[⟨x, false⟩], .tt⟩, ⟨[⟨x, true⟩], .ff⟩]

/-- A node of the decision tree: an atom together with the prefix of literal
decisions under which the tree evaluates it — the node's identity. -/
structure Node where
  pre  : List (Expr × Bool)
  atom : Expr
deriving Repr, DecidableEq

/-- The nodes a literal list visits when started under `pre`, each paired
with its literal. -/
def nodesFrom (pre : List (Expr × Bool)) : List Literal → List (Node × Literal)
  | []        => []
  | l :: rest => (⟨pre, l.atom⟩, l) :: nodesFrom (pre ++ [(l.atom, l.negated)]) rest

/-- The nodes a path visits, in order (Rust `Path::nodes`). -/
def Path.nodes (p : Path) : List (Node × Literal) :=
  nodesFrom [] p.literals

/-- A conjunction of literals, evaluated left to right; `neverTrue` renders a
trailing `&& false`. -/
structure Cube where
  literals  : List Literal
  neverTrue : Bool
deriving Repr, DecidableEq

/-- The cube of a path: never true unless the path ends in a `true` leaf. -/
def Path.cube (p : Path) : Cube :=
  ⟨p.literals, p.leaf != .tt⟩

/-- The covered-set fold of Rust `prune`: every may-be-true path is kept, and
a never-true path only when it has a node whose atom `canError` and that no
kept cube already covers. -/
def pruneGo (canError : Expr → Bool) (covered : List Node) : List Path → List Cube
  | []        => []
  | p :: rest =>
    if p.leaf == .tt then
      p.cube :: pruneGo canError covered rest
    else
      let uncovered :=
        (p.nodes.filter fun (n, l) => !covered.contains n && canError l.atom).map Prod.fst
      if uncovered.isEmpty then pruneGo canError covered rest
      else p.cube :: pruneGo canError (covered ++ uncovered) rest

/-- Turns paths into cubes, dropping the never-true ones that reproduce no
error the remaining cubes do not already reproduce (Rust `prune`): every node
of a may-be-true path is covered first; then, in order, a never-true path is
kept iff it has a node whose atom `canError` and that is not yet covered. -/
def prune (ps : List Path) (canError : Expr → Bool) : List Cube :=
  let covered := (ps.filter fun p => p.leaf == .tt).flatMap fun p => p.nodes.map Prod.fst
  pruneGo canError covered ps

/-- The boolean literal expression. -/
def boolLit (b : Bool) : Expr :=
  .lit (.bool b)

/-- The literal as an expression: the atom, or `!atom`. -/
def Literal.toExpr (l : Literal) : Expr :=
  if l.negated then .unaryApp .not l.atom else l.atom

/-- The cube as an expression: a left-associative `&&` chain of its literals,
followed by `&& false` if it is never true; `true`/`false` if empty (Rust
`Cube::to_expr`). -/
def Cube.toExpr (c : Cube) : Expr :=
  match c.literals with
  | []        => boolLit (!c.neverTrue)
  | l :: rest =>
    let conj := rest.foldl (fun acc l' => .and acc l'.toExpr) l.toExpr
    if c.neverTrue then .and conj (boolLit false) else conj

/-- The cubes as an expression: a left-associative `||` chain; `false` if
there are none (Rust `Dnf::to_expr`). -/
def toExpr : List Cube → Expr
  | []        => boolLit false
  | c :: rest => rest.foldl (fun acc c' => .or acc c'.toExpr) c.toExpr

/-- The DNF of (the boolean structure of) `e`, asking `canError` whether an
atom may evaluate to an error (Rust `Dnf::of` + `to_expr`). Equivalent to `e`
up to the kind of error wherever the `canError` answers are correct and every
atom evaluates to a boolean or an error — `Cedar.Thm.DNF.evaluate_dnf`. -/
def dnf (e : Expr) (canError : Expr → Bool) : Expr :=
  toExpr (prune (paths e) canError)

/-- `dnf` with every atom assumed able to error (Rust `Dnf::of_expr`). -/
def dnfOfExpr (e : Expr) : Expr :=
  dnf e fun _ => true

/-- The atoms of `e`: its maximal non-structure subexpressions, in evaluation
order (with repetitions). -/
def atoms : Expr → List Expr
  | .lit (.bool _)   => []
  | .unaryApp .not x => atoms x
  | .and l r
  | .or l r          => atoms l ++ atoms r
  | .ite c t e       => atoms c ++ atoms t ++ atoms e
  | x                => [x]

end

end Cedar.DNF
