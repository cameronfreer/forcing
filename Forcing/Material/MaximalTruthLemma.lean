/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.MaterialTruthLemma
import Forcing.Material.MaximalRecognition

/-!
# The material truth lemma for the maximal name family

M7 item 5. `MaterialGround.truth_lemma_of_genericOver` is parametric in an
`InternalNameRecognition`; this module instantiates it at the maximal presentation
(`MaximalNames.maximal`), its coding laws (`maximal_coding`), and its concrete recognizer
(`maximalRecognition`). **The supplied-recognizer gap is closed**: no hypothesis of the theorem
below is a recognizer, a coding law, a visibility obligation, or a test code.

## What the statement retains

Every theory instance stays explicit — `atomicDefinability`'s ledger, the two atomic test
instances, the recognizer's four sentences (the certificate's Collection and Separation instances,
Pairing, General Union), and `formulaTestSentences` **specialized to the constructed recognizer**,
so the universal-case Separation instances are now concrete sentences rather than sentences of a
parameter — together with genericity over the presentation's derived visibility context.

## Main results

* `Forcing.MaterialGround.truth_lemma_maximal`: the material truth lemma for the maximal family.
-/

universe u

namespace Forcing

open FirstOrder Language Order AtomicRecursion MaximalNames

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-- **The material truth lemma for the maximal name family.** Realization in the extension
carrier is forcing along a generic filter, for every name the maximal family contains. The
recognizer is `maximalRecognition`, the coding laws are `maximal_coding`; neither is a
hypothesis. -/
theorem truth_lemma_maximal
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
    {k n : ℕ} (φ : memLang.BoundedFormula (Fin k) n)
    (hT : formulaTestSentences (M.maximalRecognition Pres hcgat hcfil hp huni) φ ⊆ T)
    (free : Fin k → (maximal Pres).Code) (bound : Fin n → (maximal Pres).Code)
    {G : PFilter P} (hG : GenericOver Pres.derivedContext G) :
    φ.Realize
        (fun b ↦ (maximal Pres).extVal (G : Set P) ((maximal Pres).decode (free b))
          ((maximal Pres).decode_mem_names _))
        (fun i ↦ (maximal Pres).extVal (G : Set P) ((maximal Pres).decode (bound i))
          ((maximal Pres).decode_mem_names _)) ↔
      ∃ p ∈ G, ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) p φ
        ((maximal Pres).decode ∘ bound) :=
  M.truth_lemma_of_genericOver hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat hffil
    hinf hosep higat hifil hex hmemi hagree he hp hu huni hmemTest heqTest (maximal_coding Pres) φ
    hT bound hG

end MaterialGround

end Forcing
