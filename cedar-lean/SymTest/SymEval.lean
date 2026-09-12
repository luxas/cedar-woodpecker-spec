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

import SymTest.Util

/-!
This file unit tests the symbolic evaluator model (`Cedar.SymCC.Opt.symEvaluate`).

The expected results are hand-derived from Cedar's three-valued,
short-circuiting evaluation semantics and mirror cases from the Rust test
suite (`cedar-policy-symcc/tests/evaluator.rs`); they are not snapshots. Two
oracles are exercised: a hand-written pure oracle (`m := Id`) that only knows
one contradiction, and `checkUnsatAsserts` against cvc5 (`m := SolverM`).
-/

namespace SymTest.SymEval

open Cedar Data Spec SymCC Validation
open Cedar.SymCC.Opt
open UnitTest

/-- Context type: two booleans and a long. -/
private def ctxType : RecordType :=
  Map.make [
    ("x", .required (.bool .anyBool)),
    ("y", .required (.bool .anyBool)),
    ("n", .required .int),
  ]

private def Γ : TypeEnv := BasicTypes.env Map.empty Map.empty ctxType

private def εnv : SymEnv := SymEnv.ofTypeEnv Γ

private def cx : Expr := .getAttr (.var .context) "x"
private def cy : Expr := .getAttr (.var .context) "y"
private def cn : Expr := .getAttr (.var .context) "n"

/-- `context.n + 1 < 0` — a boolean atom that can error (overflow). -/
private def canErr : Expr :=
  .binaryApp .less (.binaryApp .add cn (.lit (.int 1))) (.lit (.int 0))

private def tf : Outcomes := ⟨true, true, false⟩
private def tfe : Outcomes := ⟨true, true, true⟩

/-- Runs `symEvaluate` with the given oracle and checks the result. -/
private def checkEval [Monad m] (unsat? : Asserts → m Bool)
    (x : Expr) (assumptions : List Expr) (expected : SEExpr) : m TestResult := do
  match (← (symEvaluate unsat? x assumptions εnv).run) with
  | .ok r    => checkEq r expected
  | .error e => pure (.error s!"symEvaluate failed: {reprStr e}")

/-- The solver-backed oracle. -/
private def solverUnsat? (ts : Asserts) : SolverM Bool := checkUnsatAsserts ts εnv

private def testEval (desc : String) (x : Expr) (assumptions : List Expr)
    (expected : SEExpr) : TestCase SolverM :=
  test desc ⟨λ _ => checkEval solverUnsat? x assumptions expected⟩

def testsForPureOracle : List (TestCase SolverM) :=
  -- The term `compile cx εnv` produces for the `context.x` atom.
  let tx := (Opt.compile cx εnv).toOption.map CompileResult.term |>.getD (.none .bool)
  -- A sound pure oracle: it only detects the direct contradiction on `tx`.
  let pure? : Asserts → Id Bool := λ ts =>
    ts.contains (Factory.eq tx (Factory.someOf (Term.bool true))) &&
    ts.contains (Factory.eq tx (Factory.someOf (Term.bool false)))
  [
    test "pure oracle: no assumptions leaves the atom undetermined" ⟨λ _ =>
      pure (Id.run (checkEval pure? cx [] (.atom cx tf)))⟩,

    test "pure oracle: `context.x` folds to true under the assumption `context.x`" ⟨λ _ =>
      pure (Id.run (checkEval pure? cx [cx] (.lit true)))⟩,

    test "pure oracle: an oracle that knows nothing keeps `x && y` whole" ⟨λ _ =>
      pure (Id.run (checkEval (λ _ => (false : Id Bool)) (.and cx cy) []
        (.and (.atom cx tf) (.atom cy tf) tf)))⟩,
  ]

def testsForSolverOracle : List (TestCase SolverM) :=
  [
    testEval "atom without assumptions is {True, False}" cx [] (.atom cx tf),

    testEval "arithmetic atom can error" canErr [] (.atom canErr tfe),

    testEval "assumption folds the atom" cx [cx] (.lit true),

    testEval "assumption folds through negation" (.unaryApp .not cx) [cx] (.lit false),

    testEval "<error-free> && false is false" (.and cx (.lit (.bool false))) [] (.lit false),

    testEval "<can-error> && false stays {False, Error}"
      (.and canErr (.lit (.bool false))) []
      (.and (.atom canErr tfe) (.lit false) ⟨false, true, true⟩),

    testEval "x && true is x" (.and cx (.lit (.bool true))) [] (.atom cx tf),

    testEval "<error-free> || true is true" (.or cx (.lit (.bool true))) [] (.lit true),

    testEval "trail: x || (!x && y) simplifies to x || y"
      (.or cx (.and (.unaryApp .not cx) cy)) []
      (.or (.atom cx tf) (.atom cy tf) tf),

    testEval "trail: (x && y) || (x && !x) drops the dead disjunct"
      (.or (.and cx cy) (.and cx (.unaryApp .not cx))) []
      (.and (.atom cx tf) (.atom cy tf) tf),

    testEval "if folds to the then-branch under the assumption"
      (.ite cx cy (.lit (.bool false))) [cx] (.atom cy tf),

    testEval "if keeps both branches when the test is open"
      (.ite cx cy (.lit (.bool true))) []
      (.ite (.atom cx tf) (.atom cy tf) (.lit true) tf),

    test "contradictory assumptions are reported" ⟨λ _ => do
      let r ← (symEvaluate solverUnsat? cx [cx, .unaryApp .not cx] εnv).run
      checkMatches (r matches .error .unsatisfiableAssumptions) r⟩,

    test "a non-boolean target is reported" ⟨λ _ => do
      let r ← (symEvaluate solverUnsat? cn [] εnv).run
      checkMatches (r matches .error .notBoolean) r⟩,

    test "checkEquivalent accepts the evaluator's own result" ⟨λ _ => do
      let x := .or cx (.and (.unaryApp .not cx) cy)
      match buildTree x εnv with
      | .error e => pure (.error s!"buildTree failed: {reprStr e}")
      | .ok (root, fp) =>
        let base := enforceFootprint fp εnv.entities
        let res ← (do
          let r ← symEvaluate solverUnsat? x [] εnv
          checkEquivalent solverUnsat? base root.term r εnv : ExceptT EvalError SolverM Bool).run
        match res with
        | .ok b    => checkEq b true
        | .error e => pure (.error s!"checkEquivalent failed: {reprStr e}")⟩,

    test "checkEquivalent rejects a wrong result" ⟨λ _ => do
      match buildTree cx εnv with
      | .error e => pure (.error s!"buildTree failed: {reprStr e}")
      | .ok (root, fp) =>
        let base := enforceFootprint fp εnv.entities
        let res ← (checkEquivalent solverUnsat? base root.term (.lit true) εnv
          : ExceptT EvalError SolverM Bool).run
        match res with
        | .ok b    => checkEq b false
        | .error e => pure (.error s!"checkEquivalent failed: {reprStr e}")⟩,
  ]

def tests := [suite "SymEval" (testsForPureOracle ++ testsForSolverOracle)]

end SymTest.SymEval
