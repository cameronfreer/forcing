/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.CollectionName
import Forcing.Material.ProductCover
import Forcing.Material.MaximalTruthLemma

/-!
# Collection in the extension

M7 item 6 (#241), Collection, second PR: the internal construction of the collection code and
the preservation theorem, one per formula `φ`:

```text
↥((maximal Pres).extensionCarrier (G : Set P)) ⊨ collectionSentence φ
    (G : Order.PFilter P generic over Pres.derivedContext)
```

Genericity enters only through `truth_lemma_maximal`, which supplies the equivalence the witness
lemma uses in both directions.

## The construction (`exists_collCode`)

1. **The index set.** The product cover (`Forcing/Material/ProductCover.lean`, shared with Union
   and Separation) with `A := cs`, `R := ⋃⋃ t` for `t = code i`: coverage of `cs × ⋃⋃ t` only,
   no exact index set.
2. **The collected set.** Collection by `collWitnessGatherSentence Rec φ` over the cover. Its
   hypothesis is totality (`exists_isCollWitness`) through the typed relation law, at every
   internal index, including those that fail the guards.
3. **The collection code.** Separation of the collected set by the φ-independent
   `collPairFilterSentence Rec`, keeping exactly its packages `⟨⌜q⌝, code j⟩`.

## Preservation (`extension_models_collection`)

Through the carrier unfolding `MaterialCarrier.realize_collectionSentence_iff`. The parameters
and the set `a` are transported to `extVal`s of named representatives `free` and `i`. Validity
(`isNameCode_of_isCodePair`) represents the code as `code b`, and the witness lemma
(`exists_mem_zval_of_isCollWitness`) supplies, for each `x ∈ a` with a witness, one in the value
of `b`. Its `htl` is `truth_lemma_maximal` at `bound := ![j, j']`, through the two `Fin 2`
conversions.

## Ledger

Read off `exists_collCode`: **two Collection instances** of the product cover
(`pairImageGatherSentence`, `fiberCoverGatherSentence`, shared with Union and Separation),
**one Collection instance per `φ`** (`collWitnessGatherSentence Rec φ`), **one Separation
instance independent of `φ`** (`collPairFilterSentence Rec`), **Pairing**, **General Union**,
and the compiled formula's inputs: the two atomic equivalences, the tags, and the parameter
assignment. `extension_models_collection` adds `truth_lemma_maximal`'s full ledger for `φ`
(which also supplies those inputs) and genericity. No Power Set, no Replacement, and no
Infinity beyond what `atomicDefinability` already charges.

## Main results

* `Forcing.MaterialGround.exists_collCode`.
* `Forcing.MaterialGround.extension_models_collection`.
-/

universe u

namespace Forcing

open FirstOrder Language PName AtomicRecursion MaximalNames

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-! ### The collection code -/

/-- **The collection code exists in the ground.** For `t = code i` and parameter codes `free`:
an index set `I` covering `cs × ⋃⋃ t`, a set `Y` witnessing every index of `I`, and `B ∈ M`
whose members are exactly the packages of `Y`. The product cover, one Collection by the
witness relation for `φ`, and one φ-independent Separation. -/
theorem exists_collCode (hpg : pairImageGatherSentence ∈ T)
    (hfc : fiberCoverGatherSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {Rec : InternalNameRecognition (maximal Pres)} {k : ℕ} {φ : memLang.BoundedFormula (Fin k) 2}
    (hcol : collWitnessGatherSentence Rec φ ∈ T) (hfil : collPairFilterSentence Rec ∈ T)
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
    ∃ I Y : ZFSet.{u},
      (∀ s ∈ (Pres.conditionSet : ZFSet.{u}),
        ∀ ρ ∈ ZFSet.sUnion (ZFSet.sUnion ((maximal Pres).code i)), ZFSet.pair s ρ ∈ I) ∧
      (∀ idx ∈ I, ∃ y ∈ Y, IsCollWitness Pres free φ idx y) ∧
      ∃ B ∈ M.toMaterialCarrier, ∀ m, m ∈ B ↔ m ∈ Y ∧ IsCodePair Pres m := by
  have hpair : ∀ {x y : ZFSet.{u}}, x ∈ M.toMaterialCarrier → y ∈ M.toMaterialCarrier →
      ZFSet.pair x y ∈ M.toMaterialCarrier := fun hx hy ↦ M.pair_mem hp hx hy
  have hR : ZFSet.sUnion (ZFSet.sUnion ((maximal Pres).code i)) ∈ M.toMaterialCarrier :=
    M.sUnion_mem huni (M.sUnion_mem huni ((maximal Pres).code_mem i))
  -- the index set: coverage of `cs × ⋃⋃ t`
  obtain ⟨Bd, hBdM, hBd⟩ := M.exists_productCover hpg hfc hp huni Pres.conditionSet.2 hR
  -- the collected set: Collection, its hypothesis totality
  have hlaw := fun idx y ↦ realize_collWitnessFormula_iff (Rec := Rec) (free := free) hpair hEq
    hMem hm hq φ ⟨_, hA⟩ rfl idx y
  obtain ⟨Y, hY⟩ := M.exists_collection hcol
    (testVector Rec ⟨_, hm⟩ ⟨_, hq⟩ Pres.conditionSet Pres.orderCode ⟨_, hA⟩) ⟨Bd, hBdM⟩
    fun idx _ ↦ (exists_isCollWitness hpair free φ idx).imp fun y hy ↦ (hlaw idx y).2 hy
  -- the collection code: the φ-independent filter
  obtain ⟨B, hB⟩ := M.exists_separation hfil (collFilterVector Rec Pres.conditionSet) Y
  refine ⟨Bd, Y, hBd, fun idx hidx ↦ ?_, B, B.2, fun m ↦ ⟨fun hmB ↦ ?_, fun ⟨hmY, hmp⟩ ↦ ?_⟩⟩
  · obtain ⟨y, hyY, hy⟩ := hY ⟨idx, M.mem_trans hidx hBdM⟩ hidx
    exact ⟨y, hyY, (hlaw _ y).1 hy⟩
  · have hmM := M.mem_trans hmB B.2
    obtain ⟨hmY, hmf⟩ := (hB ⟨m, hmM⟩).1 hmB
    exact ⟨hmY, (realize_collPairFilterFormula_iff Rec ⟨m, hmM⟩).1 hmf⟩
  · have hmM := M.mem_trans hmY Y.2
    exact (hB ⟨m, hmM⟩).2 ⟨hmY, (realize_collPairFilterFormula_iff Rec ⟨m, hmM⟩).2 hmp⟩

/-! ### Preservation -/

/-- **Collection holds in the extension along a generic filter**, one theorem per formula `φ`.
The collection code of each name is built in the ground, represented as a maximal name by
validity, and its value contains a witness for every element of the given set that has one, by
the witness lemma, whose truth-lemma input is `truth_lemma_maximal`. Genericity enters only
there. Ledger: `truth_lemma_maximal`'s for `φ`, the two shared Collection instances of the
product cover, one Collection instance for `φ`, and one φ-independent Separation instance. -/
theorem extension_models_collection
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
    {k : ℕ} (φ : memLang.BoundedFormula (Fin k) 2)
    (hT : formulaTestSentences (M.maximalRecognition Pres hcgat hcfil hp huni) φ ⊆ T)
    (hcol : collWitnessGatherSentence (M.maximalRecognition Pres hcgat hcfil hp huni) φ ∈ T)
    (hcpf : collPairFilterSentence (M.maximalRecognition Pres hcgat hcfil hp huni) ∈ T)
    {G : Order.PFilter P} (hG : GenericOver Pres.derivedContext G) :
    ↥((maximal Pres).extensionCarrier (G : Set P)) ⊨ collectionSentence φ := by
  rw [MaterialCarrier.realize_collectionSentence_iff]
  intro ps a hwit
  -- representatives: the parameters and the set are values of maximal names
  have hrep : ∀ y : ↥((maximal Pres).extensionCarrier (G : Set P)),
      ∃ c, (y : ZFSet.{u}) = zval (G : Set P) ((maximal Pres).decode c) :=
    fun y ↦ (maximal Pres).mem_extensionCarrier_iff.1 y.2
  choose free hfree using fun l ↦ hrep (ps l)
  obtain ⟨i, hi⟩ := hrep a
  obtain rfl : ps = fun l ↦ (maximal Pres).extVal (G : Set P) ((maximal Pres).decode (free l))
      ((maximal Pres).decode_mem_names _) :=
    funext fun l ↦ Subtype.ext (hfree l)
  -- the collection code, built in the ground
  have hat := fun i j r ↦ M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat
    hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni (maximal_coding Pres)
    i j r
  obtain ⟨I, Y, hI, hY, B, hBM, hB⟩ := M.exists_collCode Pres hpg hfc hp huni hcol hcpf
    (fun r i j ↦ (hat i j r).2.1) (fun r i j ↦ (hat i j r).2.2) (M.natCode_mem he hp hu _)
    (M.natCode_mem he hp hu _) free (InternalNamePresentation.assignmentCode_mem he hp _) i
  -- validity represents it as a maximal name
  obtain ⟨b, hb⟩ := (mem_range_code_iff Pres).2 ⟨hBM, isNameCode_of_isCodePair hB⟩
  refine ⟨(maximal Pres).extVal (G : Set P) ((maximal Pres).decode b)
    ((maximal Pres).decode_mem_names _), fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hwit x hx
  -- the witness lemma, with the truth lemma at `bound := ![j, j']`
  refine (exists_mem_zval_of_isCollWitness (b := b) hI hY (fun m ↦ by rw [hb]; exact hB m)
    (fun j j' ↦ ?_) x (hi ▸ hx) y hy).imp fun y' ⟨hy'b, hy'φ⟩ ↦
      ⟨by rw [InternalNamePresentation.coe_extVal]; exact hy'b, hy'φ⟩
  have h := M.truth_lemma_maximal Pres hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
    hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hmemTest heqTest hcgat hcfil
    φ hT free ![j, j'] hG
  have e₁ : (fun l ↦ (maximal Pres).extVal (G : Set P) ((maximal Pres).decode (![j, j'] l))
      ((maximal Pres).decode_mem_names _)) =
      ![(maximal Pres).extVal (G : Set P) ((maximal Pres).decode j)
          ((maximal Pres).decode_mem_names _),
        (maximal Pres).extVal (G : Set P) ((maximal Pres).decode j')
          ((maximal Pres).decode_mem_names _)] := by
    funext l
    match l with
    | 0 => rfl
    | 1 => rfl
  have e₂ : ((maximal Pres).decode ∘ ![j, j']) =
      ![(maximal Pres).decode j, (maximal Pres).decode j'] := by
    funext l
    match l with
    | 0 => rfl
    | 1 => rfl
  rw [e₁, e₂] at h
  exact h

end MaterialGround

end Forcing
