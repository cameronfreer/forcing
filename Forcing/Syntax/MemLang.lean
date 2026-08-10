/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Syntax

/-!
# The membership language

The function-free first-order language of membership, per ADR 0003: mathlib's
`FirstOrder.Language` with the graph-language pattern — relation symbols as an indexed
inductive type, so every downstream match is single-constructor and arity-forcing, with no
dependent transports.

**Syntax-only, and independent of any forcing notion**: this module knows nothing of
conditions, names, orders, or carriers, so both the name layer (which evaluates terms into
names) and the coding layer (which codes formulas as sets) build on it without either
depending on the other.

## Main definitions

* `Forcing.memRel`, `Forcing.memLang`: the membership language.
* `Forcing.memFormula`: the atomic membership formula.
-/

universe v

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

end Forcing
