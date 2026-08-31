/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.NameCoding
import Forcing.Material.Semantics

/-!
# Internal recognition of a name family

The capability the formula compiler's universal case needs: an internal formula recognizing
**exactly** the codes of a chosen name presentation.

## Supplied, never derived

Spike #218 refuted derivability. `InternalNameCoding`'s two fields — representation and
faithfulness — describe *known* codes and say nothing that pins the **range** of `N.code`.
Concretely: restricting a presentation to a subname-closed proper subfamily yields another
legitimate presentation satisfying `InternalNameCoding` with a *different* range, so no formula
determined by those fields can recognize both.

So this is a **capability, supplied as a hypothesis**:

* not a field on `MaterialGround`;
* not a strengthening of `InternalNamePresentation`;
* a structure relative to a presentation, exactly as `InternalNameCoding` is a proposition
  relative to one.

## Why a set will not do

A material `nameSet` with `c ∈ nameSet ↔ ∃ i, c = N.code i` is precisely a master set of all
name codes, which `Forcing/Material/NameCoding.lean` explicitly refuses. A bounded piece does
not help either: `ForcesFormula.all` quantifies over the whole family.

## The law is exact

`realize_iff` is a biconditional: **soundness and no junk**, against the exact range of
`N.code`. Recognizing a superset of structurally valid forcing names would be useless — the
universal case's correctness proof must extract an `i : N.Code` to apply `N.decode`.

## Not instantiated here

Consistency of the interface is cheap; applicability to an intended family is not. Building a
usable recognizer is **#219**, and it blocks the material truth lemma. Nothing in this file or
its consumers proves one exists.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-- **Internal recognition of a name family.** A fixed unary formula, its parameter
assignment, and the exact law that it recognizes the range of `N.code`.

Unary and fixed rather than term-indexed: #218 verified that splicing into the compiler's
growing context needs only `BoundedFormula.relabel`, so no substitution API is required. -/
structure InternalNameRecognition {M : MaterialCarrier.{u}} {P : Type u}
    (N : InternalNamePresentation M P) where
  /-- The number of parameters the recognizing formula uses. -/
  arity : ℕ
  /-- The recognizing formula: one free bound variable, the candidate code. -/
  formula : memLang.BoundedFormula (Fin arity) 1
  /-- The parameters it is read at. -/
  params : Fin arity → ↥M
  /-- **Soundness and no junk**, against the exact range of `N.code`. -/
  realize_iff : ∀ c : ↥M,
    formula.Realize params ![c] ↔ ∃ i : N.Code, (c : ZFSet.{u}) = N.code i

namespace InternalNameRecognition

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P}
  (R : InternalNameRecognition N)

/-- Every code is recognized. -/
theorem realize_code (i : N.Code) :
    R.formula.Realize R.params ![⟨N.code i, N.code_mem i⟩] :=
  (R.realize_iff _).2 ⟨i, rfl⟩

/-- Nothing else is. -/
theorem exists_code_of_realize {c : ↥M} (h : R.formula.Realize R.params ![c]) :
    ∃ i : N.Code, (c : ZFSet.{u}) = N.code i :=
  (R.realize_iff c).1 h

end InternalNameRecognition

end Forcing
