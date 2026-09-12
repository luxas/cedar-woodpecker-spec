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

import Cedar.DNF.Elim
import Cedar.Thm.DNF.SplitSound

/-!
Boolean `&&`/`||` chains over operands that evaluate to booleans: the chain
evaluates to the conjunction / disjunction of its operands' truth, in order.
The elimination rules produce such chains (`andChain`, `orChain`).
-/

namespace Cedar.DNF

open Cedar.Spec

/-- Whether an expression evaluates to `true`, decidably. -/
def isTrue (e : Expr) (req : Request) (es : Entities) : Bool :=
  evaluate e req es == .ok (.prim (.bool true))

theorem isTrue_of_bool {d : Expr} {b : Bool} {req : Request} {es : Entities}
  (h : evaluate d req es = .ok (.prim (.bool b))) :
  isTrue d req es = b := by
  cases b <;> simp [isTrue, h]

theorem evaluate_andChain_bools {ds : List Expr} {req : Request} {es : Entities}
  (h : ∀ d ∈ ds, ∃ b, evaluate d req es = .ok (.prim (.bool b))) :
  evaluate (andChain ds) req es = .ok (.prim (.bool (ds.all (isTrue · req es)))) := by
  match ds with
  | [] => simp [andChain, boolLit, evaluate]
  | [d] =>
    obtain ⟨b, hb⟩ := h d (by simp)
    simp [andChain, hb, isTrue_of_bool hb]
  | d :: d' :: rest =>
    obtain ⟨b, hb⟩ := h d (by simp)
    have ih := evaluate_andChain_bools (ds := d' :: rest)
      (fun x hx => h x (List.mem_cons_of_mem d hx))
    simp only [andChain, evaluate, hb, List.all_cons, isTrue_of_bool hb]
    cases b with
    | false => simp [Result.as, Coe.coe, Value.asBool, Bind.bind, Except.bind]
    | true =>
      rw [ih]
      simp [Result.as, Coe.coe, Value.asBool, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem evaluate_orChain_bools {ds : List Expr} {req : Request} {es : Entities}
  (h : ∀ d ∈ ds, ∃ b, evaluate d req es = .ok (.prim (.bool b))) :
  evaluate (orChain ds) req es = .ok (.prim (.bool (ds.any (isTrue · req es)))) := by
  match ds with
  | [] => simp [orChain, boolLit, evaluate]
  | [d] =>
    obtain ⟨b, hb⟩ := h d (by simp)
    simp [orChain, hb, isTrue_of_bool hb]
  | d :: d' :: rest =>
    obtain ⟨b, hb⟩ := h d (by simp)
    have ih := evaluate_orChain_bools (ds := d' :: rest)
      (fun x hx => h x (List.mem_cons_of_mem d hx))
    simp only [orChain, evaluate, hb, List.any_cons, isTrue_of_bool hb]
    cases b with
    | true => simp [Result.as, Coe.coe, Value.asBool, Bind.bind, Except.bind]
    | false =>
      rw [ih]
      simp [Result.as, Coe.coe, Value.asBool, Bind.bind, Except.bind, Pure.pure, Except.pure]

end Cedar.DNF
