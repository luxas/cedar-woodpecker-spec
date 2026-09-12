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

import Cedar.Thm.SymCC.Evaluator.Outcomes
import Cedar.Thm.SymCC.Evaluator.Tree
import Cedar.Thm.SymCC.Evaluator.Soundness

/-!
This directory proves the symbolic evaluator model
(`Cedar.SymCC.Opt.symEvaluate`) sound: given an oracle whose `unsat? = true`
answers are correct, the outcome set of every node covers the concrete
outcome (S1), and the folded result evaluates like the input up to the error
kind (S2).
-/
