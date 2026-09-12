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

import Cedar.Thm.DNF.Interp
import Cedar.Thm.DNF.Extend
import Cedar.Thm.DNF.Invariant
import Cedar.Thm.DNF.Master
import Cedar.Thm.DNF.Pruning
import Cedar.Thm.DNF.Equivalence
import Cedar.Thm.DNF.SplitEquiv
import Cedar.Thm.DNF.HoistSpec
import Cedar.Thm.DNF.SplitSound
import Cedar.Thm.DNF.Wildcard
import Cedar.Thm.DNF.Like
import Cedar.Thm.DNF.IfError

/-!
Machine-checked equivalence of the DNF converter modeled in `Cedar.DNF`
(Phase 3.5 for Step 1; Rust: `cedar-policy-symcc/src/dnf`, branch `dnf`).

Main results:

* `Cedar.DNF.interp_dnf` / `interp_dnfOfExpr` — the DNF interprets exactly
  like the input under every three-valued valuation on which the `canError`
  answers are correct;
* `Cedar.DNF.evaluate_dnf` / `evaluate_dnfOfExpr` — under
  `Cedar.Spec.evaluate`, the DNF and the input produce the same boolean value
  or both err, for every request and entity store on which every atom
  evaluates to a boolean or an error and the `canError` answers are correct
  (`evaluate_dnfOfExpr` needs only the former); soundness and completeness:
  the two sides agree exactly, up to the kind of error;
* `Cedar.DNF.dnf_cubes_exclusive` — at most one cube of the DNF is true,
  under any valuation. Together with the master invariant's no-err clauses
  (which make a true cube never coexist with an erring one), this is why the
  cubes' order does not matter.
For the Step 2 atom splitter modeled in `Cedar.DNF.Split`:

* `Cedar.DNF.evaluate_splitAtoms` — splitting the atoms preserves evaluation
  exactly (the same value, of any type, or the same error), for every
  expression, request and entity store, with no hypotheses: the hoisted `if`
  is guarded by `g == g` for the offending node's left siblings `g`, which
  reproduce their errors in the original order;
* `Cedar.DNF.splitAtoms_clean` — no atom of the output contains any
  `&&`/`||`/`!`/`if` node outside an opaque `iferror` call;
* `Cedar.DNF.evaluate_dnf_splitAtoms` — the pipeline: the DNF of the split
  expression evaluates like the original, under the Step 1 hypotheses for
  the split expression.

For the `iferror` operator (Step 4, part 1), in `Cedar.Thm.DNF.IfError`:

* `Cedar.DNF.outcome_ifError` — the three-valued table: `tt`/`ff` pass
  through, `err` becomes the fallback's outcome;
* `Cedar.DNF.outcome_ifError_false_ne_err` — `iferror(e, false)` never errs
  for boolean-or-error `e`;
* `Cedar.DNF.ifError_false_ok_true_iff` / `not_ifError_false_ok_true_iff` —
  `iferror(e, false)` is `true` exactly when `e` is, and its negation is
  `true` exactly when `e` is not `true` (hypothesis-free / for boolean-or-
  error `e`): the shape Step 4 moves deny terms with.
-/
