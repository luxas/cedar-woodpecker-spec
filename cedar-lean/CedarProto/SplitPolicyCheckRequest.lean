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
A Rust policy split to check against the Lean model
(`Cedar.DNF.splitCondExprs`): the policy's condition and the conditions of
the split policies `split_policy` produced, in order.
-/
structure SplitPolicyCheckRequest where
  expr : Spec.Expr := .lit (.bool true)
  expected : Repeated Spec.Expr := #[]
deriving Inhabited

namespace SplitPolicyCheckRequest

instance : Message SplitPolicyCheckRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t expr (update expr)
    | 2 => parseFieldElement t expected (update expected)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    expr := Field.merge x.expr y.expr
    expected := Field.merge x.expected y.expected
  }

end SplitPolicyCheckRequest

end Cedar.DNF.Proto
