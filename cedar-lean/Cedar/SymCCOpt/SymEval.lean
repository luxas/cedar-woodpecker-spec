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

public import Cedar.SymCCOpt.Compiler
public import Cedar.SymCC.Enforcer
public import Cedar.SymCC.Verifier

/-!
This file defines a model of the *symbolic Cedar evaluator* implemented in Rust
in `cedar-policy-symcc/src/evaluator/` (the `cedar-spec/cedar/` checkout). The
evaluator simplifies a boolean expression under logical assumptions: for every
boolean-structure node (`&&`/`||`/`if`/`!` chains from the root) it decides,
with unsatisfiability queries, which of the outcomes {true, false, error} the
node can still produce, and folds nodes that are fully determined.

Where the Rust implementation calls an SMT solver, this model takes an abstract
oracle `unsat? : Asserts → m Bool`. The model is monad-parametric so that one
definition serves three uses:

* `m := Id` with a pure oracle — the form the soundness theorems in
  `Cedar.Thm.SymCC.Evaluator` are stated about;
* a replay monad that pops recorded (asserts, answer) pairs — used by the
  `symcc-evaluator-lean-drt` differential test, which re-runs a Rust evaluation
  through this model and fails at the first query whose asserts diverge;
* `m := SolverM` with `checkUnsatAsserts` — a live evaluator against cvc5,
  used by the unit tests in `SymTest/SymEval.lean`.

The definitions deliberately mirror the Rust code case-for-case and in query
order (`build_tree` in `evaluator/compile.rs`; `eval_node`, `atom_outcomes` and
`Ctx::unsat` in `evaluator/mod.rs`): the differential test depends on the
queries being *identical*, including their order and the exact `Term`s, which
is why everything is built from the optimized per-node compilers
(`Opt.compileAnd/Or/If`, `Opt.compile`) that the Rust side also mirrors.

Differences from Rust, by design:
* no recursion-depth check (`stack_size_check`) — recursion here is structural;
* the expression is assumed to be the *typechecked-then-erased* form (Rust
  typechecks first; the DRT ships Rust's erased expression). Whether an `if` is
  boolean structure is decided from its compiled term's type, where Rust
  consults the typed AST — equivalent for well-typed input;
* solver management (timeouts, restarts) is out of scope.
-/

@[expose] public section

namespace Cedar.SymCC.Opt

open Cedar.Data Cedar.Spec
open Factory

/-- One of the three outcomes a boolean expression can evaluate to. -/
inductive EvalOutcome where
  | tt | ff | err
  deriving Repr, DecidableEq

/-- The outcome of `!x` given that of `x`. -/
def EvalOutcome.negated : EvalOutcome → EvalOutcome
  | .tt  => .ff
  | .ff  => .tt
  | .err => .err

/--
The set of outcomes a (sub-)expression can still take — the model of the Rust
`EvaluationMetadata` (`evaluator/mod.rs`). Unlike the Rust nonempty set, the
all-`false` value is representable; the evaluator never produces it (it raises
`.internal` where Rust does).
-/
structure Outcomes where
  canTrue : Bool
  canFalse : Bool
  canError : Bool
  deriving Repr, DecidableEq

namespace Outcomes

/-- All three outcomes: what an unvisited node gets. -/
def all : Outcomes := ⟨true, true, true⟩

/-- The empty set; only used as a unit in combinators. -/
def empty : Outcomes := ⟨false, false, false⟩

/-- The singleton set of a boolean literal. -/
def lit (b : Bool) : Outcomes := ⟨b, !b, false⟩

def single : EvalOutcome → Outcomes
  | .tt  => ⟨true, false, false⟩
  | .ff  => ⟨false, true, false⟩
  | .err => ⟨false, false, true⟩

def union (o₁ o₂ : Outcomes) : Outcomes :=
  ⟨o₁.canTrue || o₂.canTrue, o₁.canFalse || o₂.canFalse, o₁.canError || o₂.canError⟩

def subset (o₁ o₂ : Outcomes) : Bool :=
  (!o₁.canTrue || o₂.canTrue) && (!o₁.canFalse || o₂.canFalse) && (!o₁.canError || o₂.canError)

def mem (o : Outcomes) : EvalOutcome → Bool
  | .tt  => o.canTrue
  | .ff  => o.canFalse
  | .err => o.canError

/-- Whether the only possible outcome is an error. -/
def isOnlyError (o : Outcomes) : Bool := o = ⟨false, false, true⟩

/-- Whether an error is impossible. -/
def isErrorFree (o : Outcomes) : Bool := !o.canError

/-- Outcomes of `!x` given those of `x`. -/
def negated (o : Outcomes) : Outcomes := ⟨o.canFalse, o.canTrue, o.canError⟩

/--
Outcomes of `l && r`, where `r`'s outcomes were computed under the assumption
that `l` is true: `⋃ { r if o = tt, {ff} if o = ff, {err} if o = err | o ∈ l }`.
-/
def and (l r : Outcomes) : Outcomes :=
  ⟨l.canTrue && r.canTrue,
   l.canFalse || (l.canTrue && r.canFalse),
   l.canError || (l.canTrue && r.canError)⟩

/-- Outcomes of `l || r`, dual to `Outcomes.and`. -/
def or (l r : Outcomes) : Outcomes :=
  ⟨l.canTrue || (l.canFalse && r.canTrue),
   l.canFalse && r.canFalse,
   l.canError || (l.canFalse && r.canError)⟩

/--
Outcomes of `if c then a else b`, where a branch is `none` when `c` cannot
reach it (and was therefore not visited). Mirrors the Rust rule including the
fall-back to `.all` for the (unreachable) empty result.
-/
def ite (c : Outcomes) (a b : Option Outcomes) : Outcomes :=
  let ta := if c.canTrue then a.getD empty else empty
  let tb := if c.canFalse then b.getD empty else empty
  let r : Outcomes :=
    ⟨ta.canTrue || tb.canTrue,
     ta.canFalse || tb.canFalse,
     c.canError || ta.canError || tb.canError⟩
  if r = empty then all else r

end Outcomes

/--
The outcome denoted by a literal `.option .bool` term, if it is one
(Rust `term_literal`, `evaluator/compile.rs`).
-/
def termLit : Term → Option EvalOutcome
  | .some (.prim (.bool true))  => .some .tt
  | .some (.prim (.bool false)) => .some .ff
  | .none _                     => .some .err
  | _                           => .none

/--
Compiles `!arg` for an already-compiled `Option Bool` operand: exactly the
`.not` slice of `Opt.compile`'s `unaryApp` arm, factored out so the evaluator
can compile boolean structure node by node (Rust `compile_not`,
`symccopt/compiler.rs`).
-/
def compileNot (arg : CompileResult) : Result CompileResult := do
  let res ← compileApp₁ .not (arg.mapTerm option.get)
  .ok (res.mapTerm (ifSome arg.term ·))

/--
An access inside an atom whose concrete result depends on the receiver entity
*existing*, which the symbolic encoding does not model (every entity type's
attribute map is a total function): `getAttr` and `getTag` error on a missing
entity, `has` of a required attribute is `false` (Rust `Existence`,
`evaluator/compile.rs`).
-/
structure Existence where
  /-- The receiver, of type `.option (.entity ety)`. -/
  receiver : Term
  ety : EntityType
  /-- The outcomes the *atom* may take when the receiver is missing (empty
  for an access that only serves as a fact). -/
  adds : Outcomes
  /-- Whether the receiver is known to exist whenever the enclosing
  expression evaluates as assumed. -/
  isFact : Bool
  deriving Repr

/--
`exists[E]`: the evaluator's own uninterpreted existence predicate for the
entity type `ety` (Rust `exists`, `evaluator/mod.rs`). The symbolic store has
no notion of an entity being absent, so the evaluator tracks existence
itself; the predicate appears only in asserts it adds.
-/
def existsUUF (ety : EntityType) : UnaryFunction :=
  .uuf { id := s!"exists[{toString ety}]", arg := .entity ety, out := .bool }

/-- The fact that `e`'s receiver exists, `exists[E](option.get r)`. -/
def Existence.fact (e : Existence) : Term :=
  app (existsUUF e.ety) (option.get e.receiver)

/-- The constraint that `e`'s receiver is an entity that does not exist. -/
def Existence.missing (e : Existence) : Term :=
  and (isSome e.receiver) (not e.fact)

/-- Whether `ety` declares `a` as a required attribute. -/
def requiredAttr (εs : SymEntities) (ety : EntityType) (a : Attr) : Bool :=
  match εs.attrs ety with
  | .some f =>
    match f.outType with
    | .record rty =>
      match rty.find? a with
      | .some (.option _) => false
      | .some _           => true
      | .none             => false
    | _ => false
  | .none => false

/--
The compiled receiver, if it compiles and is entity-typed. (A receiver that
does not compile sits in a dead operand of an atom whose own compilation
succeeded, or in an atom that fails anyway; either way it is not
existence-sensitive.)
-/
def entityReceiver (x : Expr) (εnv : SymEnv) : Option (Term × EntityType) :=
  match compile x εnv with
  | .ok cr =>
    match cr.term.typeOf with
    | .option (.prim (.entity ety)) => .some (cr.term, ety)
    | _ => .none
  | .error _ => .none

/--
Where an access sits with respect to `iferror`: plainly, or under the first
argument of one — whose fallback, when the `iferror` is the atom itself and
the fallback a boolean literal, is what the atom takes when the access hits a
missing entity (Rust `Mode`).
-/
inductive Mode where
  | plain
  | coalesced (lit : Option Bool)
  deriving DecidableEq, Repr

/--
Whether the symbolic value of `x` may differ from its concrete value
*without* an error on a missing entity — an `iferror` or a `has` anywhere
inside (Rust `phantom`). No fact is derived from an access on such a
receiver.
-/
def phantom : Expr → Bool
  | .hasAttr _ _ => true
  | .call .ifError _ => true
  | .ite c a b => phantom c || phantom a || phantom b
  | .and l r | .or l r | .binaryApp _ l r => phantom l || phantom r
  | .unaryApp _ a | .getAttr a _ => phantom a
  | .set xs => xs.attach.any (fun ⟨x, _⟩ => phantom x)
  | .record axs => axs.attach.any (fun ⟨(_, x), _⟩ => phantom x)
  | .call _ xs => xs.attach.any (fun ⟨x, _⟩ => phantom x)
  | .lit _ | .var _ => false
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem
       simp +arith at this
       omega))

def boolLiteral : Expr → Option Bool
  | .lit (.bool b) => .some b
  | _ => .none

/-- The outcomes a `getAttr`/`getTag` on a missing entity gives the atom. -/
def erroringAdds : Mode → Outcomes
  | .plain => Outcomes.single .err
  | .coalesced (.some b) => Outcomes.lit b
  | .coalesced .none => Outcomes.all

mutual
/--
The existence-sensitive accesses of `x`, in evaluation order (a receiver's
own accesses before the access on it; Rust `existence_checks`/`walk`).
`strict` says whether `x` is evaluated whenever the enclosing expression is;
`truth` what the enclosing evaluation is assumed to have produced (`some b`:
the value `b`; `none`: some value, or nothing is assumed); `root` whether `x`
is the atom itself. A fact is a strict plain `getAttr`/`getTag` (it evaluated
without error) or a `has`/`hasTag` known to be `true` (only a present entity
has attributes or tags), on a receiver that is not `phantom`.
-/
def existenceWalk (εnv : SymEnv) : Expr → Bool → Mode → Option Bool → Bool → List Existence
  | .lit _, _, _, _, _ | .var _, _, _, _, _ => []
  | .ite c a b, strict, mode, _, _ =>
    existenceWalk εnv c strict mode none false ++ existenceWalk εnv a false mode none false
      ++ existenceWalk εnv b false mode none false
  | .and l r, strict, mode, truth, _ =>
    let (rs, rt) :=
      if truth == some true then (strict, some true)
      else if boolLiteral l == some true then (strict, truth)
      else (false, none)
    existenceWalk εnv l strict mode (if truth == some true then truth else none) false
      ++ existenceWalk εnv r rs mode rt false
  | .or l r, strict, mode, truth, _ =>
    let (rs, rt) :=
      if truth == some false then (strict, some false)
      else if boolLiteral l == some false then (strict, truth)
      else (false, none)
    existenceWalk εnv l strict mode (if truth == some false then truth else none) false
      ++ existenceWalk εnv r rs mode rt false
  | .unaryApp .not a, strict, mode, truth, _ => existenceWalk εnv a strict mode (truth.map Bool.not) false
  | .unaryApp _ a, strict, mode, _, _ => existenceWalk εnv a strict mode none false
  | .binaryApp .getTag x t, strict, mode, _, _ =>
    let inner := existenceWalk εnv x strict mode none false ++ existenceWalk εnv t strict mode none false
    match entityReceiver x εnv with
    | .some (r, ety) =>
      inner ++ [⟨r, ety, erroringAdds mode, strict && mode == .plain && !phantom x⟩]
    | .none => inner
  | .binaryApp .hasTag x t, strict, mode, truth, _ =>
    let inner := existenceWalk εnv x strict mode none false ++ existenceWalk εnv t strict mode none false
    if strict && mode == .plain && truth == some true && !phantom x then
      match entityReceiver x εnv with
      | .some (r, ety) => inner ++ [⟨r, ety, Outcomes.empty, true⟩]
      | .none => inner
    else inner
  | .binaryApp _ a b, strict, mode, _, _ =>
    existenceWalk εnv a strict mode none false ++ existenceWalk εnv b strict mode none false
  | .getAttr x _, strict, mode, _, _ =>
    let inner := existenceWalk εnv x strict mode none false
    match entityReceiver x εnv with
    | .some (r, ety) =>
      inner ++ [⟨r, ety, erroringAdds mode, strict && mode == .plain && !phantom x⟩]
    | .none => inner
  | .hasAttr x a, strict, mode, truth, root =>
    let inner := existenceWalk εnv x strict mode none false
    match entityReceiver x εnv with
    | .some (r, ety) =>
      let adds :=
        if requiredAttr εnv.entities ety a then
          match mode, root with
          | .plain, true => Outcomes.lit false
          | .coalesced (.some _), _ => ⟨true, true, false⟩
          | _, _ => Outcomes.all
        else Outcomes.empty
      let fact := strict && mode == .plain && truth == some true && !phantom x
      if adds != Outcomes.empty || fact then inner ++ [⟨r, ety, adds, fact⟩] else inner
    | .none => inner
  | .set xs, strict, mode, _, _ => existenceWalkList εnv xs strict mode
  | .record axs, strict, mode, _, _ => existenceWalkRecord εnv axs strict mode
  -- `e`'s error is coalesced (symbolically its value survives); `d` runs
  -- only when `e` errs
  | .call .ifError [e, d], _, mode, _, root =>
    let fallback := if root then boolLiteral d else none
    existenceWalk εnv e false (.coalesced fallback) none false
      ++ existenceWalk εnv d false mode none false
  | .call _ xs, strict, mode, _, _ => existenceWalkList εnv xs strict mode
termination_by e _ _ _ _ => (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

def existenceWalkList (εnv : SymEnv) : List Expr → Bool → Mode → List Existence
  | [], _, _ => []
  | x :: rest, strict, mode =>
    existenceWalk εnv x strict mode none false ++ existenceWalkList εnv rest strict mode
termination_by xs _ _ => (sizeOf xs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)

def existenceWalkRecord (εnv : SymEnv) : List (Attr × Expr) → Bool → Mode → List Existence
  | [], _, _ => []
  | (_, x) :: rest, strict, mode =>
    existenceWalk εnv x strict mode none false ++ existenceWalkRecord εnv rest strict mode
termination_by axs _ _ => (sizeOf axs, 0)
decreasing_by
  all_goals simp_wf
  all_goals (apply Prod.Lex.left; simp +arith)
end

/-- The existence-sensitive accesses of the atom `x` (Rust `existence_checks`). -/
def existenceChecks (εnv : SymEnv) (x : Expr) : List Existence :=
  existenceWalk εnv x true .plain none true

/--
The facts of `x` under `truth`: the accesses whose receivers must exist when
`x` evaluates as `truth` says (Rust `existence_facts`).
-/
def existenceFacts (εnv : SymEnv) (x : Expr) (truth : Option Bool) : List Existence :=
  (existenceWalk εnv x true .plain truth true).filter (·.isFact)

/--
The boolean structure of an expression, with every node compiled to a `Term`
(Rust `Node`/`NodeKind`, `evaluator/compile.rs`). A child that is `none`
failed to compile on its own; the sibling to its left compiled to a literal
that makes it dead, and the evaluator never visits it. An atom carries its
existence-sensitive accesses and, after `markKept`, whether it is a guard
the evaluator keeps (plan 5).
-/
inductive SENode where
  | atom (x : Expr) (t : Term) (checks ft ff fn : List Existence) (keep : Bool)
  | not  (x : Expr) (t : Term) (c : SENode)
  | and  (x : Expr) (t : Term) (l : SENode) (r : Option SENode)
  | or   (x : Expr) (t : Term) (l : SENode) (r : Option SENode)
  | ite  (x : Expr) (t : Term) (c : SENode) (a : Option SENode) (b : Option SENode)
  deriving Repr

/-- The original (sub-)expression this node was built from. -/
def SENode.expr : SENode → Expr
  | .atom x _ _ _ _ _ _ | .not x _ _ | .and x _ _ _ | .or x _ _ _ | .ite x _ _ _ _ => x

/-- The term for the whole sub-expression, of type `.option .bool`. -/
def SENode.term : SENode → Term
  | .atom _ t _ _ _ _ _ | .not _ t _ | .and _ t _ _ | .or _ t _ _ | .ite _ t _ _ _ => t

/--
The accesses whose receivers exist when this node evaluates to `truth`
(`some b`: the value `b`; `none`: some value): an atom stores its three
lists; an `&&` that is true ran both operands to `true`, an `||` that is
false both to `false`; otherwise only the left operand (or the `if` test) is
known to have run (Rust `Node::facts`, `structure_facts`).
-/
def SENode.facts : SENode → Option Bool → List Existence
  | .atom _ _ _ ft ff fn _, truth =>
    match truth with
    | some true => ft
    | some false => ff
    | none => fn
  | .not _ _ c, truth => c.facts (truth.map Bool.not)
  | .and _ _ l r, truth =>
    if truth == some true then
      l.facts (some true) ++ (match r with | some rn => rn.facts (some true) | none => [])
    else l.facts none
  | .or _ _ l r, truth =>
    if truth == some false then
      l.facts (some false) ++ (match r with | some rn => rn.facts (some false) | none => [])
    else l.facts none
  | .ite _ _ c _ _, _ => c.facts none
termination_by n _ => sizeOf n

/-- The trail terms of a node's facts when it evaluated to `b`. -/
def SENode.factTerms (n : SENode) (b : Bool) : List Term :=
  (n.facts (some b)).map Existence.fact

/--
Builds the evaluation tree for `x`, returning the root node and the union of
the footprints of all atoms (dead-branch atoms included: children are built
eagerly, exactly as in Rust). Every node's term is what a single top-level
`Opt.compile` produces for that sub-expression, because the same per-node
compilers are applied in the same order.

An `ite` is a structure node iff its compiled term has type `.option .bool`
(Rust decides this from the typed AST); otherwise it is an atom whose full
`Opt.compile` footprint is used.

Error precedence on a structure node mirrors Rust `sub_err`: a child's own
compilation error is reported before the node compiler's.
-/
def buildTree (x : Expr) (εnv : SymEnv) : Result (SENode × Set Term) :=
  match x with
  | .and x₁ x₂ => do
    let (l, fp₁) ← buildTree x₁ εnv
    let r := buildTree x₂ εnv
    match compileAnd ⟨l.term, ∅⟩ (r.map λ (n, _) => ⟨n.term, ∅⟩) with
    | .error e => .error (childErr r e)
    | .ok res =>
      let (rn, fp₂) := childParts r
      .ok (.and x res.term l rn, fp₁ ∪ fp₂)
  | .or x₁ x₂ => do
    let (l, fp₁) ← buildTree x₁ εnv
    let r := buildTree x₂ εnv
    match compileOr ⟨l.term, ∅⟩ (r.map λ (n, _) => ⟨n.term, ∅⟩) with
    | .error e => .error (childErr r e)
    | .ok res =>
      let (rn, fp₂) := childParts r
      .ok (.or x res.term l rn, fp₁ ∪ fp₂)
  | .ite x₁ x₂ x₃ => do
    let cr ← compile x εnv
    if cr.term.typeOf = .option .bool then do
      let (c, fpc) ← buildTree x₁ εnv
      let a := buildTree x₂ εnv
      let b := buildTree x₃ εnv
      match compileIf ⟨c.term, ∅⟩ (a.map λ (n, _) => ⟨n.term, ∅⟩) (b.map λ (n, _) => ⟨n.term, ∅⟩) with
      | .error e => .error (childErr a (childErr b e))
      | .ok res =>
        let (an, fpa) := childParts a
        let (bn, fpb) := childParts b
        .ok (.ite x res.term c an bn, fpc ∪ fpa ∪ fpb)
    else
      .ok (.atom x cr.term (existenceChecks εnv x) (existenceFacts εnv x (some true))
        (existenceFacts εnv x (some false)) (existenceFacts εnv x none) false, cr.footprint)
  | .unaryApp .not x₁ => do
    let (c, fp) ← buildTree x₁ εnv
    let res ← compileNot ⟨c.term, ∅⟩
    .ok (.not x res.term c, fp)
  | _ => do
    let cr ← compile x εnv
    .ok (.atom x cr.term (existenceChecks εnv x) (existenceFacts εnv x (some true))
      (existenceFacts εnv x (some false)) (existenceFacts εnv x none) false, cr.footprint)
where
  childErr (r : Result (SENode × Set Term)) (e : Error) : Error :=
    match r with
    | .error e' => e'
    | .ok _     => e
  childParts (r : Result (SENode × Set Term)) : Option SENode × Set Term :=
    match r with
    | .ok (n, fp) => (.some n, fp)
    | .error _    => (.none, ∅)

/-- Every sub-expression of `x`, `x` included (Rust `Expr::subexpressions`). -/
partial def subexprs (x : Expr) : List Expr :=
  x :: match x with
  | .lit _ | .var _ => []
  | .ite a b c => subexprs a ++ subexprs b ++ subexprs c
  | .and a b | .or a b | .binaryApp _ a b => subexprs a ++ subexprs b
  | .unaryApp _ a | .getAttr a _ | .hasAttr a _ => subexprs a
  | .set xs | .call _ xs => xs.flatMap subexprs
  | .record axs => axs.flatMap (λ p => subexprs p.2)

/-- The access a `has`/`hasTag` guard makes safe (Rust `guard_access`). -/
def guardAccess : Expr → Option Expr
  | .hasAttr e a => .some (.getAttr e a)
  | .binaryApp .hasTag e t => .some (.binaryApp .getTag e t)
  | _ => .none

/--
Whether the guard `g` is needed for its access to validate (Rust
`optional_guard`): a `has` of an attribute the schema declares optional on
the receiver's type (an `.option`-typed field of the entity's attribute
record, or of the receiver's own record type), or any `hasTag`.
-/
def optionalGuard (εnv : SymEnv) : Expr → Bool
  | .hasAttr e a =>
    match compile e εnv with
    | .ok cr =>
      match cr.term.typeOf with
      | .option (.prim (.entity ety)) =>
        match εnv.entities.attrs ety with
        | .some f =>
          match f.outType with
          | .record rty => optionalIn rty a
          | _ => false
        | .none => false
      | .option (.record rty) => optionalIn rty a
      | _ => false
    | .error _ => false
  | .binaryApp .hasTag _ _ => true
  | _ => false
where
  optionalIn (rty : Map Attr TermType) (a : Attr) : Bool :=
    match rty.find? a with
    | .some (.option _) => true
    | _ => false

/--
The guards of `root` the evaluator keeps (plan 5, Rust `kept_guards`): a
`has`/`hasTag` that is `optionalGuard` and whose access occurs in the scope
it guards — the right operand of an `&&` whose left operand contains it, or
the `then` branch of an `if` whose test does. Any sub-expression of the left
operand/test counts: keeping a guard that guards nothing only loses a fold.
-/
def keptGuards (root : Expr) (εnv : SymEnv) : List Expr :=
  (subexprs root).foldl (init := []) λ acc n =>
    match scope n with
    | .none => acc
    | .some (guarding, guarded) =>
      (subexprs guarding).foldl (init := acc) λ acc g =>
        match guardAccess g with
        | .none => acc
        | .some access =>
          if acc.contains g || !optionalGuard εnv g then acc
          else if (subexprs guarded).contains access then acc ++ [g] else acc
where
  scope : Expr → Option (Expr × Expr)
    | .and l r => .some (l, r)
    | .ite c a _ => .some (c, a)
    | _ => .none

/-- Marks the atoms of `n` that are among `ks` (Rust `mark_kept`). -/
def markKept (ks : List Expr) : SENode → SENode
  | .atom x t cs ft ff fn _ => .atom x t cs ft ff fn (decide (x ∈ ks))
  | .not x t c => .not x t (markKept ks c)
  | .and x t l r =>
    .and x t (markKept ks l) (match r with | .some n => .some (markKept ks n) | .none => .none)
  | .or x t l r =>
    .or x t (markKept ks l) (match r with | .some n => .some (markKept ks n) | .none => .none)
  | .ite x t c a b =>
    .ite x t (markKept ks c) (match a with | .some n => .some (markKept ks n) | .none => .none)
      (match b with | .some n => .some (markKept ks n) | .none => .none)
termination_by n => sizeOf n

/--
The evaluator's result: the Rust `Expr<EvaluationMetadata>`, restricted to the
shapes the evaluator produces. `unvisited` is a dead `if` branch, kept
structurally intact with all-outcomes metadata.
-/
inductive SEExpr where
  | lit (b : Bool)
  | atom (x : Expr) (o : Outcomes)
  | unvisited (x : Expr)
  | not (c : SEExpr) (o : Outcomes)
  | and (l : SEExpr) (r : SEExpr) (o : Outcomes)
  | or  (l : SEExpr) (r : SEExpr) (o : Outcomes)
  | ite (c : SEExpr) (a : SEExpr) (b : SEExpr) (o : Outcomes)
  deriving Repr, DecidableEq

/-- The possible outcomes of the root node. -/
def SEExpr.outcomes : SEExpr → Outcomes
  | .lit b       => .lit b
  | .atom _ o    => o
  | .unvisited _ => .all
  | .not _ o     => o
  | .and _ _ o   => o
  | .or _ _ o    => o
  | .ite _ _ _ o => o

/-- The boolean literal this result folded to, if it did. -/
def SEExpr.asLit : SEExpr → Option Bool
  | .lit b => .some b
  | _      => .none

/-- The simplified expression, with the metadata erased. -/
def SEExpr.toExpr : SEExpr → Expr
  | .lit b       => .lit (.bool b)
  | .atom x _    => x
  | .unvisited x => x
  | .not c _     => .unaryApp .not c.toExpr
  | .and l r _   => .and l.toExpr r.toExpr
  | .or l r _    => .or l.toExpr r.toExpr
  | .ite c a b _ => .ite c.toExpr a.toExpr b.toExpr

/--
A kept guard (plan 5) whose scope folded to a literal guards nothing any
more: the literal `true` it stands for (Rust `unguard`). Every other value
is itself — an atom with outcomes `{True}` that is not a literal is always
a kept guard, every other such atom having been folded.
-/
def SEExpr.unguard : SEExpr → SEExpr
  | .atom x o => if o = Outcomes.lit true then .lit true else .atom x o
  | e => e

/--
The result of an `if` whose test was not a literal (the tail of Rust's `If`
arm): the node with the visited branches — unless the test's outcomes are
`{True}` (a kept guard) and the then-branch folded to a literal, when that
branch alone is the result (plan 5).
-/
def iteResult (cv : SEExpr) (av bv : Option SEExpr) (ax bx : Expr) : SEExpr :=
  match av with
  | .some avv =>
    if cv.outcomes = Outcomes.lit true ∧ avv.asLit.isSome = true then avv
    else .ite cv avv (bv.getD (.unvisited bx))
      (cv.outcomes.ite (.some avv.outcomes) (bv.map SEExpr.outcomes))
  | .none =>
    .ite cv (.unvisited ax) (bv.getD (.unvisited bx))
      (cv.outcomes.ite .none (bv.map SEExpr.outcomes))

/--
Infrastructure errors of the evaluator (Rust `EvaluationError`, minus the
solver/typechecker variants that do not exist in this model).
-/
inductive EvalError where
  | compile (e : Error)
  | notBoolean
  | unsatisfiableAssumptions
  | internal (msg : String)
  deriving Repr

/--
The n-ary hierarchy enforcement over a bare footprint (Rust
`enforce_footprint`, `symccopt/enforcer.rs`): acyclicity of every term plus
transitivity of every ordered pair. `Set.make` gives the same sorted, deduped
order as the Rust `BTreeSet`.
-/
def enforceFootprint (fp : Set Term) (εs : SymEntities) : Asserts :=
  (Set.make (fp.elts.map (acyclicity · εs)
    ++ fp.elts.flatMap (λ t₁ => fp.elts.map (transitivity t₁ · εs)))).elts

/--
The exact outcome set of the `.option .bool` term `t` under `trail` (Rust
`Ctx::term_outcomes`): a literal term needs no query; otherwise one
satisfiability question per outcome, with the error question skipped when
`isNone t` already folds to `false`. The three questions are mutually
exclusive and exhaustive for an `.option .bool` term, so the answers are the
set. All three `false` means the trail is unsatisfiable, which the gating in
`evalNode` rules out — hence `.internal`.
-/
def termOutcomes [Monad m] (unsat? : Asserts → m Bool) (base : Asserts)
    (t : Term) (trail : List Term) : ExceptT EvalError m Outcomes := do
  match termLit t with
  | .some o => return Outcomes.single o
  | .none =>
    let canTrue ← Bool.not <$> liftM (unsat? (base ++ trail ++ [eq t (⊙ true)]))
    let canFalse ← Bool.not <$> liftM (unsat? (base ++ trail ++ [eq t (⊙ false)]))
    let isNoneT := isNone t
    let canError ←
      if isNoneT = Term.bool false then pure false
      else Bool.not <$> liftM (unsat? (base ++ trail ++ [isNoneT]))
    if !canTrue && !canFalse && !canError then
      throw (.internal "no possible outcome for an atom under a satisfiable trail")
    return ⟨canTrue, canFalse, canError⟩

/--
The existence questions of an atom (Rust `Ctx::atom_outcomes`, second half):
for each access in order whose missing-entity outcomes are not all in the
set yet, whether the receiver can be an entity that does not exist under
the trail; if it can, the outcomes join the set.
-/
def addMissing [Monad m] (unsat? : Asserts → m Bool) (base : Asserts)
    (trail : List Term) : List Existence → Outcomes → m Outcomes
  | [], o => pure o
  | c :: cs, o => do
    if c.adds.subset o then addMissing unsat? base trail cs o
    else
      let u ← unsat? (base ++ trail ++ [c.missing])
      addMissing unsat? base trail cs (if u then o else o.union c.adds)

/--
The outcome set of an atom with term `t` and accesses `checks` under
`trail` (Rust `Ctx::atom_outcomes`): the three outcome questions, then the
existence questions.
-/
def atomOutcomes [Monad m] (unsat? : Asserts → m Bool) (base : Asserts)
    (t : Term) (checks : List Existence) (trail : List Term) :
    ExceptT EvalError m Outcomes := do
  let o ← termOutcomes unsat? base t trail
  liftM (addMissing unsat? base trail checks o)

/--
The evaluation proper (Rust `eval_node`). `trail` holds the assumptions that
follow from the path taken to the node (`eq (term l) (⊙ true)` for the right
operand of `&&`, etc., each followed by the existence facts of the sibling
that evaluated) and is kept satisfiable together with `base` by the
gating: a child is evaluated under an extended trail only when the required
outcome is in its sibling's set. Trail terms always use the *original* child
node's term, not its simplified form.
-/
def evalNode [Monad m] (unsat? : Asserts → m Bool) (base : Asserts) :
    SENode → List Term → ExceptT EvalError m SEExpr
  | .atom x t cs _ _ _ keep, trail => do
    let o ← atomOutcomes unsat? base t cs trail
    -- a kept guard stays itself, with its `{True}` outcomes (plan 5)
    if o = Outcomes.lit true ∧ keep = false then return .lit true
    else if o = Outcomes.lit false then return .lit false
    else return .atom x o
  | .not _ _ c, trail => do
    let cv ← evalNode unsat? base c trail
    match cv.asLit with
    | .some b => return .lit !b
    | .none =>
      if cv.outcomes.isOnlyError then return cv
      return .not cv cv.outcomes.negated
  | .and _ _ l r, trail => do
    let lv ← evalNode unsat? base l trail
    if lv.outcomes.isOnlyError then return lv
    match lv.asLit with
    | .some false => return .lit false
    | .some true =>
      let .some r := r
        | throw (.internal "right operand of `&&` missing although the left one is true")
      evalNode unsat? base r trail
    | .none =>
      if !lv.outcomes.canTrue then return lv
      let .some r := r
        | throw (.internal "right operand of `&&` missing although the left one can be true")
      let rv ← evalNode unsat? base r (trail ++ [eq l.term (⊙ true)] ++ l.factTerms true)
      match rv.asLit with
      | .some true => return lv.unguard
      | .some false =>
        if lv.outcomes.isErrorFree then return .lit false
        return .and lv rv (lv.outcomes.and rv.outcomes)
      | .none => return .and lv rv (lv.outcomes.and rv.outcomes)
  | .or _ _ l r, trail => do
    let lv ← evalNode unsat? base l trail
    if lv.outcomes.isOnlyError then return lv
    match lv.asLit with
    | .some true => return .lit true
    | .some false =>
      let .some r := r
        | throw (.internal "right operand of `||` missing although the left one is false")
      evalNode unsat? base r trail
    | .none =>
      if !lv.outcomes.canFalse then return lv
      let .some r := r
        | throw (.internal "right operand of `||` missing although the left one can be false")
      let rv ← evalNode unsat? base r (trail ++ [eq l.term (⊙ false)] ++ l.factTerms false)
      match rv.asLit with
      | .some false => return lv
      | .some true =>
        if lv.outcomes.isErrorFree then return .lit true
        return .or lv rv (lv.outcomes.or rv.outcomes)
      | .none => return .or lv rv (lv.outcomes.or rv.outcomes)
  | .ite _ _ c a b, trail => do
    let cv ← evalNode unsat? base c trail
    if cv.outcomes.isOnlyError then return cv
    match cv.asLit with
    | .some true =>
      let .some a := a
        | throw (.internal "then-branch missing although the test is true")
      evalNode unsat? base a trail
    | .some false =>
      let .some b := b
        | throw (.internal "else-branch missing although the test is false")
      evalNode unsat? base b trail
    | .none =>
      let .some a := a
        | throw (.internal "branch missing although the test is not a literal")
      let .some b := b
        | throw (.internal "branch missing although the test is not a literal")
      let av : Option SEExpr ←
        if cv.outcomes.canTrue then
          Option.some <$> evalNode unsat? base a (trail ++ [eq c.term (⊙ true)] ++ c.factTerms true)
        else pure Option.none
      let bv : Option SEExpr ←
        if cv.outcomes.canFalse then
          Option.some <$> evalNode unsat? base b (trail ++ [eq c.term (⊙ false)] ++ c.factTerms false)
        else pure Option.none
      return iteResult cv av bv a.expr b.expr
termination_by n _ => sizeOf n

/--
Evaluates a built tree: requires the root to be boolean, checks the base
asserts are satisfiable (Rust `UnsatisfiableAssumptions`), then runs
`evalNode` with an empty trail.
-/
def evalRoot [Monad m] (unsat? : Asserts → m Bool) (root : SENode)
    (base : Asserts) : ExceptT EvalError m SEExpr := do
  if root.term.typeOf ≠ .option .bool then throw .notBoolean
  if (← liftM (unsat? base)) then throw .unsatisfiableAssumptions
  evalNode unsat? base root []

/--
Evaluates `x` under caller-provided base asserts, taken verbatim (assumption
constraints and hierarchy enforcement included). This is the entry point the
differential test replays: the Rust evaluator ships the base it used.
-/
def symEvalWithBase [Monad m] (unsat? : Asserts → m Bool) (x : Expr)
    (base : Asserts) (εnv : SymEnv) : ExceptT EvalError m SEExpr := do
  match buildTree x εnv with
  | .error e => throw (.compile e)
  | .ok (root, _) => evalRoot unsat? (markKept (keptGuards x εnv) root) base

/-- Compiles each expression, pairing it with its result. -/
def compileAll : List Expr → SymEnv → Result (List (Expr × CompileResult))
  | [], _ => .ok []
  | a :: as, εnv => do
    let cr ← compile a εnv
    let rest ← compileAll as εnv
    .ok ((a, cr) :: rest)

/--
Evaluates `x` under assumption expressions, each assumed to evaluate to
`true`: compiles the assumptions, asserts `eq aᵢ (⊙ true)` for each, and
appends the hierarchy enforcement `enforce (x :: assumptions)`. This is the
entry point the soundness theorems are stated about.

Note the enforcement differs from the Rust evaluator's (and from
`symEvalWithBase` fed with a Rust base): Rust enforces over the union of the
footprints of *all atoms* of the tree, including atoms in branches that a
literal made dead, which is a superset of `enforce`'s expression footprints.
The extra terms are acyclicity/transitivity facts about compiled sub-atoms,
true on strongly well-formed inputs, but their satisfaction is not part of
the proofs in `Cedar.Thm.SymCC.Evaluator`; see the plan for the follow-up.
-/
def symEvaluate [Monad m] (unsat? : Asserts → m Bool) (x : Expr)
    (assumptions : List Expr) (εnv : SymEnv) : ExceptT EvalError m SEExpr := do
  match buildTree x εnv with
  | .error e => throw (.compile e)
  | .ok (root, _) =>
    match compileAll assumptions εnv with
    | .error e => throw (.compile e)
    | .ok acrs =>
      let base := acrs.map (λ (_, cr) => eq cr.term (⊙ true))
        ++ (enforce (x :: assumptions) εnv).elts
      evalRoot unsat? (markKept (keptGuards x εnv) root) base

/--
Checks that `r` (as returned by the evaluator for the expression whose root
term is `t`) is equivalent to it under `base`, as a single query (Rust
`Evaluator::check_equivalent`). The result is compiled as is — it is not
typechecked again, and need not typecheck: a folded `has` may have removed the
capability an attribute access relied on.
-/
def checkEquivalent [Monad m] (unsat? : Asserts → m Bool) (base : Asserts)
    (t : Term) (r : SEExpr) (εnv : SymEnv) : ExceptT EvalError m Bool := do
  match compile r.toExpr εnv with
  | .error e => throw (.compile e)
  | .ok cr   => liftM (unsat? (base ++ [not (eq t cr.term)]))

end Cedar.SymCC.Opt
