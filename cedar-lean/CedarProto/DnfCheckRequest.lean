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

import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Expr

open Proto

namespace Cedar.DNF.Proto

/--
A Rust DNF conversion to check against the Lean model (`Cedar.DNF.dnf`): the
input expression, the Rust result (`Dnf::of(expr, can_error,
DEFAULT_MAX_CUBES).to_expr()`), and whether `can_error` answered `true` for
every atom (`Dnf::of_expr`) or `false` for every atom — the two closure-free
extremes.
-/
structure DnfCheckRequest where
  expr : Spec.Expr := .lit (.bool true)
  expected : Spec.Expr := .lit (.bool true)
  canErrorAll : Bool := false
deriving Inhabited

namespace DnfCheckRequest

instance : Message DnfCheckRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t expr (update expr)
    | 2 => parseFieldElement t expected (update expected)
    | 3 => parseFieldElement t canErrorAll (update canErrorAll)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    expr := Field.merge x.expr y.expr
    expected := Field.merge x.expected y.expected
    canErrorAll := Field.merge x.canErrorAll y.canErrorAll
  }

end DnfCheckRequest

end Cedar.DNF.Proto
