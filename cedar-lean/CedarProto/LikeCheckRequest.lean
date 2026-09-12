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
A Rust like-rewrite to check against the Lean model (`Cedar.DNF.rewriteLike`):
the input and `rewrite_like(expr)`.
-/
structure LikeCheckRequest where
  expr : Spec.Expr := .lit (.bool true)
  expected : Spec.Expr := .lit (.bool true)
deriving Inhabited

namespace LikeCheckRequest

instance : Message LikeCheckRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t expr (update expr)
    | 2 => parseFieldElement t expected (update expected)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    expr := Field.merge x.expr y.expr
    expected := Field.merge x.expected y.expected
  }

end LikeCheckRequest

end Cedar.DNF.Proto
