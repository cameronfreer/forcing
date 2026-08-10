/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Syntax.MemLang
import Forcing.Name.Basic

/-!
# Evaluating membership-language terms into names

The bridge from the membership language (`Forcing/Syntax/MemLang.lean`) to typed names.

**Syntax-only** (normative import boundary from ADR 0003): nothing from `Semantics` — term
evaluation into names needs no `Structure` instance, because the impossible function cases
eliminate. Semantic realization arrives only with the truth-lemma layer.

## Main definitions

* `Forcing.evalTerm`: function-free term evaluation into names.
-/

universe u v

namespace Forcing

open FirstOrder

/-- Evaluate a function-free term into names. No `Structure` instance is needed: the function
cases are impossible. -/
def evalTerm {β : Type v} {P : Type u} (v : β → PName P) : memLang.Term β → PName P
  | .var x => v x
  | .func f _ => f.elim

@[simp] theorem evalTerm_var {β : Type v} {P : Type u} (v : β → PName P) (x : β) :
    evalTerm v (.var x) = v x :=
  rfl

/-- Values of function-free terms stay inside any family containing the assignment. -/
theorem evalTerm_mem {β : Type v} {P : Type u} {𝒩 : Set (PName P)} {v : β → PName P}
    (hv : ∀ x, v x ∈ 𝒩) : ∀ t : memLang.Term β, evalTerm v t ∈ 𝒩
  | .var x => hv x
  | .func f _ => f.elim

end Forcing
