/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Semantics
import Forcing.Name.MemLang
import Forcing.Material.Extension

/-!
# Membership semantics on material carriers

The audited carrier semantics of ADR 0003, exposed cleanly: the membership-language structure
on a material carrier (a **scoped** instance — available to everything that opens `Forcing`,
never leaking as a global default), the name-to-extension-value helper (`extVal`), and the
carrier-quantifier bridge (`forall_extensionCarrier_iff_names`) — quantification over the
extension carrier *is* quantification over the internal names, through
`mem_extensionCarrier_iff`.

This module is the `Semantics`-side counterpart of the Syntax-only `MemLang`: per the ADR's
normative import boundary, `Mathlib.ModelTheory.Semantics` enters here and nowhere below the
truth layer.

## Main definitions

* the scoped `memLang.Structure` instance on material carriers;
* `Forcing.InternalNamePresentation.extVal`: a name's value as a carrier element.

## Main results

* `Forcing.InternalNamePresentation.realize_term_extVal`: term realization is `extVal` of
  `evalTerm`.
* `Forcing.InternalNamePresentation.forall_extensionCarrier_iff_names`: the
  carrier-quantifier bridge.
-/

universe u v

namespace Forcing

open FirstOrder PName

/-- Membership semantics on a material carrier: the single relation is `ZFSet` membership of
the underlying elements. Scoped, so it never becomes a global default. -/
scoped instance (M : MaterialCarrier.{u}) : memLang.Structure M where
  funMap f _ := f.elim
  RelMap := fun r x ↦ match r with | .mem => (x 0 : ZFSet) ∈ (x 1 : ZFSet)

/-- The membership relation is interpreted as `ZFSet` membership of the underlying
elements. -/
@[simp] theorem relMap_mem {M : MaterialCarrier.{u}} {x : Fin 2 → M} :
    Language.Structure.RelMap (L := memLang) memRel.mem x ↔ (x 0 : ZFSet.{u}) ∈ (x 1 : ZFSet.{u}) :=
  Iff.rfl

namespace InternalNamePresentation

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P}
variable {S : Set P}

/-- A name of the family, as an element of the extension carrier. -/
def extVal (N : InternalNamePresentation M P) (S : Set P) (τ : PName P) (hτ : τ ∈ N.names) :
    N.extensionCarrier S :=
  ⟨zval S τ, N.mem_extensionCarrier_of_mem_of_zval_eq hτ rfl⟩

@[simp] theorem coe_extVal {τ : PName P} (hτ : τ ∈ N.names) :
    (N.extVal S τ hτ : ZFSet.{u}) = zval S τ :=
  rfl

/-- Realization of a function-free term along `extVal`-valued assignments is `extVal` of the
syntactic evaluation. -/
theorem realize_term_extVal {γ : Type v} {a : γ → PName P} (ha : ∀ g, a g ∈ N.names) :
    ∀ t : memLang.Term γ,
      (Language.Term.realize (M := N.extensionCarrier S)
        (fun g ↦ N.extVal S (a g) (ha g)) t) = N.extVal S (evalTerm a t) (evalTerm_mem ha t)
  | .var _ => rfl
  | .func f _ => f.elim

/-- **The carrier-quantifier bridge**: quantification over the extension carrier is
quantification over the internal names — every carrier element is the value of a decoded
name, and every name's value lands in the carrier. -/
theorem forall_extensionCarrier_iff_names (Φ : N.extensionCarrier S → Prop) :
    (∀ x, Φ x) ↔ ∀ τ, ∀ hτ : τ ∈ N.names, Φ (N.extVal S τ hτ) := by
  constructor
  · exact fun h τ hτ ↦ h _
  · rintro h ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := N.mem_extensionCarrier_iff.1 hx
    exact h (N.decode i) (N.decode_mem_names i)

end InternalNamePresentation

end Forcing
