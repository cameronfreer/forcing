/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.RecursionExistence
import Forcing.Material.UnionIterationFamily

/-!
# The atomic construction certificate

Composing the two halves of 3b. `RecursionExistence` builds a coherent graph over *any
supplied* transitive domain; `UnionIterationFamily` supplies one for an arbitrary pair of name
codes. Together they give, for each pair, an internal graph whose two tagged slices *are* the
external atomic forcing relations.

## What this theorem is

A **construction certificate**, deliberately explicit about both `A` and `R`. It says which
domain was built and which graph lives over it, because everything downstream — the internal
formulas, and eventually the compiler — needs to name them.

It is *not yet* the packaged internal definitions promised by #157. Those come next, and take
`A` as a material parameter.

## The ledger

Everything the two halves charge, and nothing new:

* the seventeen recursion instances, plus the union-iteration instances;
* Infinity and `omegaSepSentence`, for internal `ω` — and **only** through
  `exists_transitiveDomain`. `exists_atomicCoherentOn` remains priced without Infinity, which
  is the separation ADR 0005 predicted;
* Empty Set, Pairing, Binary Union, General Union;
* **no Foundation, no Power Set**, and no Cartesian product.

Empty Set appears here (through `natCode_mem`, for the tag numerals) even though neither half
needed it on its own — worth stating, since the two halves' ledgers do not simply add.
-/

universe u

namespace Forcing

open FirstOrder Language AtomicRecursion

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **The atomic construction certificate.**

For any two name codes there is a transitive `A ∈ M` containing both and a graph `R ∈ M`
coherent over it, whose slices are the external atomic relations at those codes:

* the membership slice is `MemWitness`;
* the equality slice is `ForcesEq`;
* the *density* of the membership slice is `ForcesMem`.

`A` and `R` are exposed rather than hidden behind an existential over the conclusion, because
the internal formulas built next must name the domain. -/
theorem exists_atomicCertificate
    -- the recursion instances
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    -- the union-iteration instances
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmem : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    -- finite closure and general union
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T)
    {P : Type u} [Preorder P] {Pres : InternalForcingPresentation M.toMaterialCarrier P}
    {N : InternalNamePresentation M.toMaterialCarrier P}
    (hc : InternalNameCoding Pres N) (i j : N.Code) :
    ∃ A R : ↥M.toMaterialCarrier,
      (A : ZFSet.{u}).IsTransitive ∧
        N.code i ∈ (A : ZFSet.{u}) ∧ N.code j ∈ (A : ZFSet.{u}) ∧
        AtomicCoherentOn (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u})
          (A : ZFSet.{u}) (R : ZFSet.{u}) ∧
        (∀ p : P, entry memWitnessTag (condCode Pres p) (N.code i) (N.code j) ∈
            (R : ZFSet.{u}) ↔ MemWitness p (N.decode i) (N.decode j)) ∧
        (∀ p : P, entry eqTag (condCode Pres p) (N.code i) (N.code j) ∈ (R : ZFSet.{u}) ↔
          ForcesEq p (N.decode i) (N.decode j)) ∧
        (∀ q : P, DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u})
            (R : ZFSet.{u}) (condCode Pres q) (N.code i) (N.code j) ↔
          ForcesMem q (N.decode i) (N.decode j)) := by
  -- the ambient domain, the only place Infinity is charged
  obtain ⟨A, hAtrans, hiA, hjA⟩ :=
    M.exists_transitiveDomain hinf hosep higat hifil hex hmem hagree hp hu huni
      ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩
  -- the tag numerals, priced at finite closure
  refine ⟨A, ?_⟩
  obtain ⟨R, hR⟩ := M.exists_atomicCoherentOn hbnd hsep hgat hfil hdom hgra hbr hbl hpsep
    hrgat hrfil hfgat hffil huni he hp hu
    ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
    ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩
    Pres.conditionSet Pres.orderCode A hAtrans rfl rfl
  exact ⟨R, hAtrans, hiA, hjA, hR,
    fun p ↦ memWitness_entry_iff hAtrans hR hc hiA hjA p,
    fun p ↦ forcesEq_entry_iff hAtrans hR hc hiA hjA p,
    fun q ↦ denseMem_iff_forcesMem hAtrans hR hc hiA hjA q⟩

end MaterialGround

end Forcing
