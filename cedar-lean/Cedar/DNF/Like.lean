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

public import Cedar.DNF

/-!
This file models `cedar-policy-symcc/src/dnf/like.rs` (the `cedar-spec/cedar/`
checkout, branch `rewrite-like`, Phase 4 Step 1): `x like p` with a pattern
`p` free of wildcards matches exactly one string, so it is rewritten to
`x == "<p>"`; every `like` left in the result has a wildcard, and is matched
by at least two strings. The theorems are in `Cedar.Thm.DNF.Like`.
-/

namespace Cedar.DNF

open Cedar.Spec

@[expose] public section

/-- Whether a pattern has a wildcard. -/
def hasStar (p : Pattern) : Bool :=
  p.any (· == .star)

/-- The characters of a pattern, wildcards dropped. -/
def patternChars (p : Pattern) : List Char :=
  p.filterMap fun
    | .justChar c => some c
    | .star => none

/-- For a wildcard-free pattern, the one string it matches. -/
def patternString (p : Pattern) : String :=
  String.ofList (patternChars p)

/-- Rewrites every `x like p` whose pattern has no wildcard into
`x == "<p>"`, bottom-up (Rust `rewrite_like`). -/
def rewriteLike : Expr → Expr
  | .lit p => .lit p
  | .var v => .var v
  | .ite x₁ x₂ x₃ => .ite (rewriteLike x₁) (rewriteLike x₂) (rewriteLike x₃)
  | .and x₁ x₂ => .and (rewriteLike x₁) (rewriteLike x₂)
  | .or x₁ x₂ => .or (rewriteLike x₁) (rewriteLike x₂)
  | .unaryApp (.like p) x =>
    if hasStar p then .unaryApp (.like p) (rewriteLike x)
    else .binaryApp .eq (rewriteLike x) (.lit (.string (patternString p)))
  | .unaryApp op x => .unaryApp op (rewriteLike x)
  | .binaryApp op x₁ x₂ => .binaryApp op (rewriteLike x₁) (rewriteLike x₂)
  | .getAttr x a => .getAttr (rewriteLike x) a
  | .hasAttr x a => .hasAttr (rewriteLike x) a
  | .set xs => .set (xs.map₁ (fun ⟨x, _⟩ => rewriteLike x))
  | .record axs => .record (axs.map₂ (fun ⟨(a, x), _⟩ => (a, rewriteLike x)))
  | .call xfn xs => .call xfn (xs.map₁ (fun ⟨x, _⟩ => rewriteLike x))

/-- The operands of the wildcard-free `like`s in `e` — the ones the rewrite
touches; the soundness hypothesis ranges over them: each must evaluate to a
string or an error. -/
def likeOperands : Expr → List Expr
  | .lit _ | .var _ => []
  | .ite x₁ x₂ x₃ => likeOperands x₁ ++ likeOperands x₂ ++ likeOperands x₃
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ => likeOperands x₁ ++ likeOperands x₂
  | .unaryApp (.like p) x => if hasStar p then likeOperands x else x :: likeOperands x
  | .unaryApp _ x | .getAttr x _ | .hasAttr x _ => likeOperands x
  | .set xs => xs.attach.flatMap (fun ⟨x, _⟩ => likeOperands x)
  | .record axs => axs.attach.flatMap (fun ⟨(_, x), _⟩ => likeOperands x)
  | .call _ xs => xs.attach.flatMap (fun ⟨x, _⟩ => likeOperands x)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem
       simp +arith at this
       omega))

/-- The patterns of the `like`s in `e`. -/
def likePatterns : Expr → List Pattern
  | .lit _ | .var _ => []
  | .ite x₁ x₂ x₃ => likePatterns x₁ ++ likePatterns x₂ ++ likePatterns x₃
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ => likePatterns x₁ ++ likePatterns x₂
  | .unaryApp (.like p) x => p :: likePatterns x
  | .unaryApp _ x | .getAttr x _ | .hasAttr x _ => likePatterns x
  | .set xs => xs.attach.flatMap (fun ⟨x, _⟩ => likePatterns x)
  | .record axs => axs.attach.flatMap (fun ⟨(_, x), _⟩ => likePatterns x)
  | .call _ xs => xs.attach.flatMap (fun ⟨x, _⟩ => likePatterns x)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem
       simp +arith at this
       omega))

/-- Whether every `like` in `e` has at least one wildcard (Rust
`likes_have_wildcards`). -/
def likesHaveWildcards : Expr → Bool
  | .lit _ | .var _ => true
  | .ite x₁ x₂ x₃ => likesHaveWildcards x₁ && likesHaveWildcards x₂ && likesHaveWildcards x₃
  | .and x₁ x₂ | .or x₁ x₂ | .binaryApp _ x₁ x₂ =>
    likesHaveWildcards x₁ && likesHaveWildcards x₂
  | .unaryApp (.like p) x => hasStar p && likesHaveWildcards x
  | .unaryApp _ x | .getAttr x _ | .hasAttr x _ => likesHaveWildcards x
  | .set xs => xs.attach.all (fun ⟨x, _⟩ => likesHaveWildcards x)
  | .record axs => axs.attach.all (fun ⟨(_, x), _⟩ => likesHaveWildcards x)
  | .call _ xs => xs.attach.all (fun ⟨x, _⟩ => likesHaveWildcards x)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | (simp +arith; done)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem
       simp +arith at this
       omega))

end

end Cedar.DNF
