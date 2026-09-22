/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes
import Forcing.Material.Extension

/-!
# The free axioms: Extensionality and Foundation on every material carrier

M7 item 6 (#241), step 1. Two axioms hold in **every** material carrier — a transitive
collection of ambient well-founded sets — with no ground theory, no genericity, no filter, and
no name family:

* **Extensionality**: two carrier elements with the same carrier members are equal. The carrier
  is transitive, so its members' members are carrier elements, and the internal quantifier
  ranges over *all* members; `ZFSet.ext` does the rest.
* **Foundation**: every inhabited carrier element has an `∈`-minimal member. Ambient membership
  is well-founded; transitivity places the minimal element in the carrier. This is
  `MaterialGround.realize_foundationSentence`'s argument, restated where it belongs — on the
  carrier, with no theory in sight.

The extension `M[G]` is a material carrier (`InternalNamePresentation.extensionCarrier`), so
both axioms hold there as a special case: the first two rows of item 6's ledger, priced at
nothing. Stated for an arbitrary condition set `S`, since neither needs genericity.

## Main definitions

* `Forcing.extensionalitySentence`: the named axiom.

## Main results

* `Forcing.MaterialCarrier.realize_extensionalitySentence`,
  `Forcing.MaterialCarrier.realize_foundationSentence`: the free axioms on every carrier.
* `Forcing.InternalNamePresentation.extension_models_extensionality`,
  `…extension_models_foundation`: the specializations to `M[G]`.
-/

universe u

namespace Forcing

open FirstOrder Language

/-- **The extensionality axiom**: sets with the same members are equal. -/
def extensionalitySentence : memLang.Sentence :=
  ∀' ∀' ((∀' (memFormula &2 &0 ⇔ memFormula &2 &1)) ⟹ (&0 =' &1))

namespace MaterialCarrier

variable (C : MaterialCarrier.{u})

/-- **Extensionality is free** on every material carrier: transitivity makes the internal
membership quantifier range over all members. -/
theorem realize_extensionalitySentence : ↥C ⊨ extensionalitySentence := by
  have key : ∀ x y : ↥C,
      (∀ z : ↥C, (z : ZFSet.{u}) ∈ (x : ZFSet.{u}) ↔ (z : ZFSet.{u}) ∈ (y : ZFSet.{u})) →
        x = y := by
    intro x y h
    refine Subtype.ext (ZFSet.ext fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩)
    · exact (h ⟨z, C.mem_trans hz x.2⟩).1 hz
    · exact (h ⟨z, C.mem_trans hz y.2⟩).2 hz
  simpa [extensionalitySentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc]
    using key

/-- **Foundation is free** on every material carrier. -/
theorem realize_foundationSentence : ↥C ⊨ foundationSentence := by
  have key : ∀ b : ↥C, (∃ w : ↥C, (w : ZFSet.{u}) ∈ (b : ZFSet.{u})) →
      ∃ y : ↥C, (y : ZFSet.{u}) ∈ (b : ZFSet.{u}) ∧
        ¬∃ z : ↥C, (z : ZFSet.{u}) ∈ (y : ZFSet.{u}) ∧ (z : ZFSet.{u}) ∈ (b : ZFSet.{u}) := by
    rintro b ⟨w, hw⟩
    obtain ⟨y, hyb, hyC, hmin⟩ := C.exists_minimal b.2 hw
    exact ⟨⟨y, hyC⟩, hyb, fun ⟨z, hzy, hzb⟩ ↦ hmin z hzy hzb⟩
  simpa [foundationSentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc]
    using key

end MaterialCarrier

namespace InternalNamePresentation

variable {M : MaterialCarrier.{u}} {P : Type u} (N : InternalNamePresentation M P) (S : Set P)

/-- **`M[G]` satisfies Extensionality**, for any condition set — no theory, no genericity. -/
theorem extension_models_extensionality : ↥(N.extensionCarrier S) ⊨ extensionalitySentence :=
  (N.extensionCarrier S).realize_extensionalitySentence

/-- **`M[G]` satisfies Foundation**, for any condition set — no theory, no genericity. -/
theorem extension_models_foundation : ↥(N.extensionCarrier S) ⊨ foundationSentence :=
  (N.extensionCarrier S).realize_foundationSentence

end InternalNamePresentation

end Forcing
