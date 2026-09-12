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

import Cedar.SymCCOpt
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Expr
import CedarProto.RequestEnv
import CedarProto.SymCCRequest
import CedarProto.Term

open Proto

namespace Cedar.SymCC.Proto

/--
One query the Rust symbolic evaluator issued: the full assert list passed to
the solver and its answer.
-/
structure SymEvalQuery where
  asserts : Cedar.SymCC.Asserts := []
  unsat : Bool := false
deriving Inhabited

namespace SymEvalQuery

instance : Message SymEvalQuery where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t asserts (update asserts)
    | 2 => parseFieldElement t unsat (update unsat)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    asserts := Field.merge x.asserts y.asserts
    unsat := Field.merge x.unsat y.unsat
  }

end SymEvalQuery

/--
A recorded Rust symbolic evaluation to replay through the Lean model
(`Cedar.SymCC.Opt.symEvalWithBase`), plus the Rust result to compare with.
-/
structure SymEvalReplayRequest where
  request : Validation.Proto.RequestEnv := default
  /-- The typechecked-then-erased target expression the Rust evaluator walked. -/
  expr : Spec.Expr := .lit (.bool true)
  /-- The base asserts of the `evaluate` call, verbatim. -/
  base : Cedar.SymCC.Asserts := []
  /-- Every query, in order (`evaluate`'s first, then `check_equivalent`'s). -/
  queries : Repeated SymEvalQuery := #[]
  /-- The Rust result: the folded expression ... -/
  expected : Spec.Expr := .lit (.bool true)
  /-- ... and its root outcome set. -/
  expectedCanTrue : Bool := false
  expectedCanFalse : Bool := false
  expectedCanError : Bool := false
  /-- Whether a `check_equivalent` call was recorded (with base `ceBase`). -/
  checkEquivalent : Bool := false
  ceBase : Cedar.SymCC.Asserts := []
deriving Inhabited

namespace SymEvalReplayRequest

instance : Message SymEvalReplayRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t request (update request)
    | 2 => parseFieldElement t expr (update expr)
    | 3 => parseFieldElement t base (update base)
    | 4 => parseFieldElement t queries (update queries)
    | 5 => parseFieldElement t expected (update expected)
    | 6 => parseFieldElement t expectedCanTrue (update expectedCanTrue)
    | 7 => parseFieldElement t expectedCanFalse (update expectedCanFalse)
    | 8 => parseFieldElement t expectedCanError (update expectedCanError)
    | 9 => parseFieldElement t checkEquivalent (update checkEquivalent)
    | 10 => parseFieldElement t ceBase (update ceBase)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    request := Field.merge x.request y.request
    expr := Field.merge x.expr y.expr
    base := Field.merge x.base y.base
    queries := Field.merge x.queries y.queries
    expected := Field.merge x.expected y.expected
    expectedCanTrue := Field.merge x.expectedCanTrue y.expectedCanTrue
    expectedCanFalse := Field.merge x.expectedCanFalse y.expectedCanFalse
    expectedCanError := Field.merge x.expectedCanError y.expectedCanError
    checkEquivalent := Field.merge x.checkEquivalent y.checkEquivalent
    ceBase := Field.merge x.ceBase y.ceBase
  }

end SymEvalReplayRequest

end Cedar.SymCC.Proto
