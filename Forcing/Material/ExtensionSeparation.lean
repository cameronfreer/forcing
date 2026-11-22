/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.SeparationName
import Forcing.Material.ProductCover
import Forcing.Material.MaximalTruthLemma

/-!
# Separation in the extension

M7 item 6 (#241), Separation, second PR: the internal construction of the separation code and
the preservation theorem, one per formula `φ`:

```text
↥((maximal Pres).extensionCarrier (G : Set P)) ⊨ separationSentence φ
    (G : Order.PFilter P generic over Pres.derivedContext)
```

The first row of item 6 that needs genericity, and it enters only through
`truth_lemma_maximal`.

## The construction

1. **The bound.** Every branch `⟨⌜q⌝, code j⟩` of the separation code has `code j` as a right
   coordinate of a branch of `t = code i`, so it lies in `cs × ⋃⋃ t`
   (`components_mem_sUnion_sUnion`, with no validity, order, or membership assumption). The
   product cover (`Forcing/Material/ProductCover.lean`, shared with Union) is reused unchanged
   with `A := cs`, `R := ⋃⋃ t`.
2. **The separation code** (`exists_sepNameCode`): Separation by `sepNameSentence Rec φ` at the
   separation layout carves `B` from the cover, and `realize_sepNameFormula_iff` reads it, so
   `∀ m, m ∈ B ↔ IsSepBranch Pres free φ i m`. Coverage and exactness stay separate; empty
   index sets need no case split.
3. **Preservation** (`extension_models_separation`): through the carrier unfolding
   `MaterialCarrier.realize_separationSentence_iff`. The parameters `ps` and the set `a` are
   elements of the extension carrier, so each is the value of a maximal name; the choice of
   codes `free` and `i` makes the equalities with their `extVal` representatives explicit. Then
   validity (`isNameCode_of_isSepBranch`) represents `B` as `code b`, and valuation
   (`mem_zval_decode_of_isSepBranch`) is the required membership equivalence, with `htl`
   discharged by `truth_lemma_maximal` at `bound := ![j]`.

The singleton conversions `decode ∘ ![j] = ![decode j]` and
`(fun l ↦ extVal (decode (![j] l))) = ![extVal (decode j)]` are `funext` on `Fin 1`: no theory
charge and no sentence bridge.

## Ledger

Read off `exists_sepNameCode`: **two Collection instances** (`pairImageGatherSentence`,
`fiberCoverGatherSentence`, shared with Union), **one Separation instance**
(`sepNameSentence Rec φ`, one per `φ`), **Pairing**, **General Union**, and the compiled
formula's inputs: the two atomic equivalences, the tags, and the parameter assignment.
`extension_models_separation` adds `truth_lemma_maximal`'s full ledger for `φ` (which also
supplies those inputs: the atomic equivalences from `atomicDefinability`, the tags and the
assignment from Empty Set, Pairing, and Binary Union) and genericity. No Power Set, and no
Infinity beyond what `atomicDefinability` already charges.

## Main results

* `Forcing.MaterialGround.exists_sepNameCode`.
* `Forcing.MaterialGround.extension_models_separation`.
-/

universe u

namespace Forcing

open FirstOrder Language PName AtomicRecursion MaximalNames

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-! ### The separation code -/

/-- **The separation code exists in the ground**, characterized exactly: for `t = code i` and
parameter codes `free`, some `B ∈ M` has `m ∈ B ↔ IsSepBranch Pres free φ i m`. Separation by
the instance for `φ` from the product cover of `cs × ⋃⋃ t`. Ledger: two Collection instances,
one Separation instance, Pairing, General Union, and the compiled formula's inputs. -/
theorem exists_sepNameCode (hpg : pairImageGatherSentence ∈ T)
    (hfc : fiberCoverGatherSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {Rec : InternalNameRecognition (maximal Pres)} {k : ℕ} {φ : memLang.BoundedFormula (Fin k) 1}
    (hsepφ : sepNameSentence Rec φ ∈ T)
    (hEq : ∀ (r : P) (i j : (maximal Pres).Code),
      AtomicEqRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode (condCode Pres r)
          ((maximal Pres).code i) ((maximal Pres).code j) ↔
        ForcesEq r ((maximal Pres).decode i) ((maximal Pres).decode j))
    (hMem : ∀ (r : P) (i j : (maximal Pres).Code),
      AtomicMemRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode (condCode Pres r)
          ((maximal Pres).code i) ((maximal Pres).code j) ↔
        ForcesMem r ((maximal Pres).decode i) ((maximal Pres).decode j))
    (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M.toMaterialCarrier)
    (hq : (natCode eqTag : ZFSet.{u}) ∈ M.toMaterialCarrier)
    (free : Fin k → (maximal Pres).Code)
    (hA : (maximal Pres).assignmentCode (combinedCodes free ![]) ∈ M.toMaterialCarrier)
    (i : (maximal Pres).Code) :
    ∃ B ∈ M.toMaterialCarrier, ∀ m, m ∈ B ↔ IsSepBranch Pres free φ i m := by
  have htM := (maximal Pres).code_mem i
  have hR : ZFSet.sUnion (ZFSet.sUnion ((maximal Pres).code i)) ∈ M.toMaterialCarrier :=
    M.sUnion_mem huni (M.sUnion_mem huni htM)
  obtain ⟨Bd, hBdM, hBd⟩ := M.exists_productCover hpg hfc hp huni Pres.conditionSet.2 hR
  obtain ⟨B, hB⟩ := M.exists_separation hsepφ
    (sepVector Rec ⟨_, hm⟩ ⟨_, hq⟩ Pres.conditionSet Pres.orderCode ⟨_, hA⟩ ⟨_, htM⟩) ⟨Bd, hBdM⟩
  have hlaw := fun x ↦ realize_sepNameFormula_iff (Rec := Rec) (free := free)
    (fun hx hy ↦ M.pair_mem hp hx hy) hEq hMem hm hq φ i ⟨_, hA⟩ rfl x
  refine ⟨B, B.2, fun m ↦ ⟨fun hmB ↦ ?_, fun hsb ↦ ?_⟩⟩
  · have hmM := M.mem_trans hmB B.2
    exact (hlaw ⟨m, hmM⟩).1 ((hB ⟨m, hmM⟩).1 hmB).2
  · obtain ⟨q, j, rfl, ⟨p, hpj, -⟩, -⟩ := id hsb
    have hmBd := hBd _ (Pres.code_mem q) _ (components_mem_sUnion_sUnion hpj).2
    have hmM := M.mem_trans hmBd hBdM
    exact (hB ⟨_, hmM⟩).2 ⟨hmBd, (hlaw ⟨_, hmM⟩).2 hsb⟩

/-! ### Preservation -/

/-- **Separation holds in the extension along a generic filter**, one theorem per formula `φ`.
The separation code of each name is built in the ground, represented as a maximal name by
validity, and values to the separated set by the valuation law, whose truth-lemma input is
`truth_lemma_maximal`. Genericity enters only there. Ledger: `truth_lemma_maximal`'s for `φ`,
the two shared Collection instances of the product cover, and one Separation instance for `φ`. -/
theorem extension_models_separation
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T)
    (hmemTest : separationSentence memLocalizeTest ∈ T)
    (heqTest : separationSentence eqDecisionTest ∈ T)
    (hcgat : certificateGatherSentence ∈ T) (hcfil : certificateFilterSentence ∈ T)
    (hpg : pairImageGatherSentence ∈ T) (hfc : fiberCoverGatherSentence ∈ T)
    {k : ℕ} (φ : memLang.BoundedFormula (Fin k) 1)
    (hT : formulaTestSentences (M.maximalRecognition Pres hcgat hcfil hp huni) φ ⊆ T)
    (hsepφ : sepNameSentence (M.maximalRecognition Pres hcgat hcfil hp huni) φ ∈ T)
    {G : Order.PFilter P} (hG : GenericOver Pres.derivedContext G) :
    ↥((maximal Pres).extensionCarrier (G : Set P)) ⊨ separationSentence φ := by
  rw [MaterialCarrier.realize_separationSentence_iff]
  intro ps a
  -- representatives: the parameters and the separated set are values of maximal names
  have hrep : ∀ y : ↥((maximal Pres).extensionCarrier (G : Set P)),
      ∃ c, (y : ZFSet.{u}) = zval (G : Set P) ((maximal Pres).decode c) :=
    fun y ↦ (maximal Pres).mem_extensionCarrier_iff.1 y.2
  choose free hfree using fun l ↦ hrep (ps l)
  obtain ⟨i, hi⟩ := hrep a
  obtain rfl : ps = fun l ↦ (maximal Pres).extVal (G : Set P) ((maximal Pres).decode (free l))
      ((maximal Pres).decode_mem_names _) :=
    funext fun l ↦ Subtype.ext (hfree l)
  -- the separation code, built in the ground
  have hat := fun i j r ↦ M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat
    hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni (maximal_coding Pres)
    i j r
  obtain ⟨B, hBM, hB⟩ := M.exists_sepNameCode Pres hpg hfc hp huni hsepφ
    (fun r i j ↦ (hat i j r).2.1) (fun r i j ↦ (hat i j r).2.2) (M.natCode_mem he hp hu _)
    (M.natCode_mem he hp hu _) free (InternalNamePresentation.assignmentCode_mem he hp _) i
  -- validity represents it as a maximal name
  obtain ⟨b, hb⟩ := (mem_range_code_iff Pres).2 ⟨hBM, isNameCode_of_isSepBranch Pres hB⟩
  refine ⟨(maximal Pres).extVal (G : Set P) ((maximal Pres).decode b)
    ((maximal Pres).decode_mem_names _), fun x ↦ ?_⟩
  rw [InternalNamePresentation.coe_extVal, hi]
  -- valuation, with the truth lemma at `bound := ![j]`
  refine mem_zval_decode_of_isSepBranch (fun _ _ hab ha ↦ G.mem_of_le hab ha) G.directed
    (fun m ↦ by rw [hb]; exact hB m) (fun j ↦ ?_) x
  have h := M.truth_lemma_maximal Pres hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
    hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hmemTest heqTest hcgat hcfil
    φ hT free ![j] hG
  have e₁ : (fun l ↦ (maximal Pres).extVal (G : Set P) ((maximal Pres).decode (![j] l))
      ((maximal Pres).decode_mem_names _)) =
      ![(maximal Pres).extVal (G : Set P) ((maximal Pres).decode j)
        ((maximal Pres).decode_mem_names _)] := by
    funext l
    rw [Fin.fin_one_eq_zero l]
    rfl
  have e₂ : ((maximal Pres).decode ∘ ![j]) = ![(maximal Pres).decode j] := by
    funext l
    rw [Fin.fin_one_eq_zero l]
    rfl
  rw [e₁, e₂] at h
  exact h

end MaterialGround

end Forcing
