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

public import Cedar.DNF.SplitPolicy

/-!
This file models `cedar-policy-symcc/src/dnf/combine.rs` (the `cedar-spec/cedar/`
checkout, branch `combine-allow-deny`, Phase 3 Step 4 part 2): rewriting a
policy set into allow policies only, with the same authorization decision.

A decision is `allow` exactly when some permit is `true` and no forbid is.
Every permit's condition is conjoined with, for every forbid `F = d₁ && … && dₖ`
(its full condition, scopes included), the witness that `F` is not `true`:
`!iferror(d₁, false) || (d₁ && (!iferror(d₂, false) || … !iferror(dₖ, false)))`
— the first non-true conjunct decides. The forbids are dropped. The theorems
are in `Cedar.Thm.DNF.Combine`.

Differences from Rust, by design: forbids are ordered by id with a stable
sort on both sides (Rust `sort_by`, here `List.mergeSort`), and `Spec.Policy`
carries structured scopes, so the chain is the `&&`-spine of `Policy.toExpr`.
`conjuncts` and the chain builder `andChain` live with the atom splitter
(`Cedar.DNF.Split`), which shares them.
-/

namespace Cedar.DNF

open Cedar.Spec

@[expose] public section

/-- `!iferror(d, false)`: `true` exactly when `d` is not `true`. -/
def notTrue (d : Expr) : Expr :=
  .unaryApp .not (.call .ifError [d, boolLit false])

/-- The witness that the chain `ds` is not true, nested right (Rust
`deny_witness`). -/
def denyWitness : List Expr → Expr
  | [] => boolLit false
  | [d] => notTrue d
  | d :: rest => .or (notTrue d) (.and d (denyWitness rest))

/-- The forbids of a set, in id order. -/
def forbidsOf (ps : Policies) : Policies :=
  (ps.filter (fun p => p.effect == .forbid)).mergeSort (fun a b => decide (a.id ≤ b.id))

/-- A permit with every forbid's witness appended to its conditions. -/
def combinePermit (forbids : Policies) (p : Policy) : Policy :=
  { p with condition := p.condition ++ forbids.map (fun f => ⟨.when, denyWitness (conjuncts f.toExpr)⟩) }

/-- Rewrites `ps` into permits only (Rust `combine_allow_deny`). -/
def combineAllowDeny (ps : Policies) : Policies :=
  (ps.filter (fun p => p.effect == .permit)).map (combinePermit (forbidsOf ps))

/-- The allow-only cube policies: `splitPolicySet` of the combined set (Rust
`allow_cubes`). -/
def allowCubes (ps : Policies) : Policies :=
  splitPolicySet (combineAllowDeny ps)

end

end Cedar.DNF
