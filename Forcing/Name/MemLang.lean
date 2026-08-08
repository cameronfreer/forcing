/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Syntax
import Forcing.Name.Basic

/-!
# The membership language

The function-free first-order language of membership, per ADR 0003: mathlib's
`FirstOrder.Language` with the graph-language pattern — relation symbols as an indexed
inductive type, so every downstream match is single-constructor and arity-forcing, with no
dependent transports.

**Syntax-only** (normative import boundary from the ADR): this module imports
`Mathlib.ModelTheory.Syntax` and nothing from `Semantics` — term evaluation into names
(`evalTerm`) needs no `Structure` instance, because the impossible function cases eliminate.
Semantic realization arrives only with the truth-lemma layer.

## Main definitions

* `Forcing.memRel`, `Forcing.memLang`: the membership language.
* `Forcing.memFormula`: the atomic membership formula.
* `Forcing.evalTerm`: function-free term evaluation into names.
-/

universe u v

namespace Forcing

open FirstOrder

/-- The relation symbols of the membership language: a single binary relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The function-free membership language, graph-pattern. -/
def memLang : FirstOrder.Language :=
  ⟨fun _ ↦ Empty, memRel⟩

/-- The membership relation applied to two terms — the only atomic formula shape of the
language, named once so downstream axioms and codings need not spell the relation out. -/
def memFormula {α : Type v} {n : ℕ} (t₁ t₂ : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  Language.Relations.boundedFormula₂ (L := memLang) memRel.mem t₁ t₂

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
