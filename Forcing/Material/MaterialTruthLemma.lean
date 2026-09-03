/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicTests
import Forcing.Material.ConnectiveTests
import Forcing.Material.DerivedVisibility
import Forcing.Material.TruthLemma

/-!
# The material truth lemma

M7 item 4c, and the specialization it enables. The three visibility hypotheses of
`truth_lemma_of_genericOver` are discharged from the derived visibility context of the
presentation: each test set is the externalization of an internal subset (4a, 4b), and the
derived context's visible sets are exactly those externalizations.

```text
hvmem  ←  exists_memLocalizeCode        (one Separation instance)
hveq   ←  exists_eqDecisionCode         (one Separation instance)
hvT    ←  exists_code_of_mem_formulaTests   (formulaTestSentences Rec φ)
```

## What the final theorem mentions, and what it does not

`MaterialGround.truth_lemma_of_genericOver` mentions **no** hand-supplied visibility obligation
and **no** test code: genericity over `Pres.derivedContext` is the only observer-side hypothesis.
It remains visibly parametric in two things: the recognizer `Rec` (no concrete instance exists
yet, #219) and the theory, whose instances are explicit — `atomicDefinability`'s ledger, the
two atomic test instances, and `formulaTestSentences Rec φ ⊆ T`.

Dense-openness stays external (`isDenseOpen_of_mem_formulaTests` and its atomic companions are
consumed inside `truth_lemma_of_genericOver`, never here), and no capability bundle is added to
`MaterialGround`.

## Main results

* `Forcing.MaterialGround.visible_memLocalize`, `…visible_eqDecision`,
  `…visible_formulaTests`: the three budgets, materially.
* `Forcing.MaterialGround.truth_lemma_of_genericOver`: the material truth lemma.
-/

universe u

namespace Forcing

open FirstOrder Language Order AtomicRecursion InternalForcingPresentation

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] {Pres : InternalForcingPresentation M.toMaterialCarrier P}
variable {N : InternalNamePresentation M.toMaterialCarrier P} {Rec : InternalNameRecognition N}
variable {k : ℕ} {free : Fin k → N.Code}

/-- **The localized membership budget**, from the derived context. -/
theorem visible_memLocalize
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
    (htest : separationSentence memLocalizeTest ∈ T)
    (hc : InternalNameCoding Pres N) :
    ∀ τ ∈ N.names, ∀ σ ∈ N.names, ∀ p : P,
      Pres.derivedContext.Visible (localizeBelow (memWitness τ σ) p) := by
  rintro τ ⟨i, rfl⟩ σ ⟨j, rfl⟩ p
  exact M.exists_memLocalizeCode hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat
    hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni htest hc p i j

/-- **The equality decision budget**, from the derived context. -/
theorem visible_eqDecision
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
    (htest : separationSentence eqDecisionTest ∈ T)
    (hc : InternalNameCoding Pres N) :
    ∀ τ ∈ N.names, ∀ σ ∈ N.names, Pres.derivedContext.Visible (eqDecision τ σ) := by
  rintro τ ⟨i, rfl⟩ σ ⟨j, rfl⟩
  exact M.exists_eqDecisionCode hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat
    hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni htest hc i j

/-- **The formula-test budget**, from the derived context, given exactly the Separation
instances in `formulaTestSentences`. -/
theorem visible_formulaTests
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
    (huni : unionSentence ∈ T) (hc : InternalNameCoding Pres N)
    {n : ℕ} (φ : memLang.BoundedFormula (Fin k) n) (hT : formulaTestSentences Rec φ ⊆ T)
    (bound : Fin n → N.Code) :
    ∀ D ∈ formulaTests N.names (N.decode ∘ free) φ (N.decode ∘ bound),
      Pres.derivedContext.Visible D :=
  fun D hD ↦ M.exists_code_of_mem_formulaTests hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat
    hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc φ hT bound D hD

/-- **The material truth lemma.** Over a filter generic for the presentation's derived
visibility context, realization in the extension carrier is forcing along the filter — with
every visibility budget discharged from internal codes, and no test code or visibility
obligation in the statement.

Parametric in the recognizer `Rec` and explicit in every theory instance: `atomicDefinability`'s
ledger, the two atomic test instances, and the formula-indexed `formulaTestSentences Rec φ`. -/
theorem truth_lemma_of_genericOver
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
    (hc : InternalNameCoding Pres N)
    {n : ℕ} (φ : memLang.BoundedFormula (Fin k) n) (hT : formulaTestSentences Rec φ ⊆ T)
    (bound : Fin n → N.Code) {G : PFilter P} (hG : GenericOver Pres.derivedContext G) :
    φ.Realize (fun b ↦ N.extVal (G : Set P) (N.decode (free b)) (N.decode_mem_names _))
        (fun i ↦ N.extVal (G : Set P) (N.decode (bound i)) (N.decode_mem_names _)) ↔
      ∃ p ∈ G, ForcesFormula N.names (N.decode ∘ free) p φ (N.decode ∘ bound) :=
  InternalNamePresentation.truth_lemma_of_genericOver hG (fun b ↦ N.decode_mem_names (free b))
    (fun τ hτ σ hσ p _ _ ↦ M.visible_memLocalize hbnd hsep hgat hfil hdom hgra hbr hbl hpsep
      hrgat hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hmemTest hc
      τ hτ σ hσ p)
    (M.visible_eqDecision hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat hffil
      hinf hosep higat hifil hex hmemi hagree he hp hu huni heqTest hc)
    φ (N.decode ∘ bound) (fun i ↦ N.decode_mem_names (bound i))
    (M.visible_formulaTests hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat hffil
      hinf hosep higat hifil hex hmemi hagree he hp hu huni hc φ hT bound)

end MaterialGround

end Forcing
