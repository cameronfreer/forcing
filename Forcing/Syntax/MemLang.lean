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
* `Forcing.unorderedPairDef`, `Forcing.pairDef`: the pair relations, as builders over terms.
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

/-! ### Pair formulas

Builders over **terms**, not over fixed variable positions, so a consumer can splice them
anywhere without relabelling a fixed three-variable formula. Syntax only; their realization
laws live in the material semantics layer. -/

/-- Weakening of a term into one more bound variable. -/
def liftTerm {α : Type v} {n : ℕ} (t : memLang.Term (α ⊕ Fin n)) :
    memLang.Term (α ⊕ Fin (n + 1)) :=
  t.relabel (Sum.map id Fin.castSucc)

/-- `z` is the unordered pair `{x, y}`. -/
def unorderedPairDef {α : Type v} {n : ℕ} (x y z : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm z) ⇔
    ((&(Fin.last n) =' liftTerm x) ⊔ (&(Fin.last n) =' liftTerm y)))

/-- `z` is the Kuratowski pair `⟨x, y⟩`, i.e. `{{x}, {x, y}}`. The two intermediate sets are
quantified rather than named, so the builder needs no auxiliary variables from its caller. -/
def pairDef {α : Type v} {n : ℕ} (x y z : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (unorderedPairDef (liftTerm (liftTerm x)) (liftTerm (liftTerm x))
        (&(Fin.castSucc (Fin.last n))) ⊓
      (unorderedPairDef (liftTerm (liftTerm x)) (liftTerm (liftTerm y))
        (&(Fin.last (n + 1))) ⊓
      unorderedPairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
        (liftTerm (liftTerm z))))

end Forcing
