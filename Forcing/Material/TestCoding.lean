/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes
import Forcing.Material.Recursion

/-!
# Coding a test by one Separation instance

The two facts every test-coding module shares: a typed condition as a carrier element, and the
step from a Separation instance over the condition set to an `InternalSubset` whose membership is
read at typed conditions. Neutral between the atomic tests (`Forcing/Material/AtomicTests.lean`)
and the connective tests (`Forcing/Material/ConnectiveTests.lean`), so neither depends on the
other.

## Main results

* `Forcing.condElem`: a typed condition, as a carrier element.
* `Forcing.MaterialGround.exists_internalSubset_of_separation`: one Separation instance, one
  internal subset.
-/

universe u

namespace Forcing

open FirstOrder Language AtomicRecursion

section Cond

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]

/-- A typed condition, as a carrier element: `condCode`, with its membership. -/
def condElem (Pres : InternalForcingPresentation M P) (p : P) : ↥M :=
  ⟨condCode Pres p, M.mem_trans (Pres.code_mem p) Pres.conditionSet.2⟩

end Cond

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] {Pres : InternalForcingPresentation M.toMaterialCarrier P}

/-- A Separation instance over the condition set yields an internal subset, with membership
read at typed conditions. -/
theorem exists_internalSubset_of_separation {k : ℕ} {φ : memLang.BoundedFormula (Fin k) 1}
    (hφ : separationSentence φ ∈ T) (params : Fin k → ↥M.toMaterialCarrier) :
    ∃ d : Pres.InternalSubset, ∀ q : P,
      q ∈ d.externalize ↔ φ.Realize params ![condElem Pres q] := by
  obtain ⟨b, hb⟩ := M.exists_separation hφ params Pres.conditionSet
  refine ⟨⟨b, fun z hz ↦ ?_⟩, fun q ↦ ?_⟩
  · have hzM : z ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hz b.2
    exact ((hb ⟨z, hzM⟩).1 hz).1
  · rw [InternalForcingPresentation.InternalSubset.mem_externalize]
    exact (hb (condElem Pres q)).trans (and_iff_right (Pres.code_mem q))

end MaterialGround

end Forcing
