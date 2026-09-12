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
import CedarProto.PolicySet

open Proto

namespace Cedar.DNF.Proto

/--
A Rust allow/deny combination to check against the Lean model
(`Cedar.DNF.combineAllowDeny` and `Cedar.DNF.allowCubes`): the policy set,
the allow-only set `combine_allow_deny` produced, and the cube policies
`allow_cubes` produced.
-/
structure CombineCheckRequest where
  policies : Spec.Policies := []
  expectedCombined : Spec.Policies := []
  expectedCubes : Spec.Policies := []
deriving Inhabited

namespace CombineCheckRequest

instance : Message CombineCheckRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t policies (update policies)
    | 2 => parseFieldElement t expectedCombined (update expectedCombined)
    | 3 => parseFieldElement t expectedCubes (update expectedCubes)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    policies := Field.merge x.policies y.policies
    expectedCombined := Field.merge x.expectedCombined y.expectedCombined
    expectedCubes := Field.merge x.expectedCubes y.expectedCubes
  }

end CombineCheckRequest

end Cedar.DNF.Proto
