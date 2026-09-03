/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicDefinability

/-!
# The atomic definitions, as their consumers read them

The semantic content of the three uniform seven-parameter atomic definitions, named as `Prop`s
on sets, together with the readers identifying each uniform formula's realization with them.

Two consumers, one shape: the formula compiler's correctness induction
(`Forcing/Material/CompilerCorrectness.lean`) and the atomic test codes
(`Forcing/Material/AtomicTests.lean`) both consume the atomic definitions **as black boxes** — an
equivalence between a realized formula and an external atomic relation — and neither reopens the
domain, the relation, or coherence. This module is that black box's interface.

## Main definitions

* `Forcing.AtomicMemWitnessRealized`, `Forcing.AtomicEqRealized`, `Forcing.AtomicMemRealized`.

## Main results

* `Forcing.MaterialGround.atomicRealized_iff`: **the interface** — the three typed
  equivalences against `MemWitness`, `ForcesEq`, `ForcesMem`, on `atomicDefinability`'s ledger.
  Both consumers take exactly this.
* `Forcing.realize_memWitnessUniform_iff`, `…forcesEqUniform_iff`, `…forcesMemUniform_iff`: each
  uniform formula at its parameter vector is the corresponding predicate.
-/

universe u

namespace Forcing

open FirstOrder Language AtomicRecursion

section Atomic

variable (M : MaterialCarrier.{u})

/-- The semantic content of `memWitnessDef` at given codes: some transitive carrier element
contains both names' codes, and some coherent relation on it records the membership witness. -/
def AtomicMemWitnessRealized (condSet orderCode p x y : ZFSet.{u}) : Prop :=
  ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧ x ∈ ((A : ↥M) : ZFSet.{u}) ∧
    y ∈ ((A : ↥M) : ZFSet.{u}) ∧
    ∃ R : ↥M, AtomicCoherentOn condSet orderCode ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
      entry memWitnessTag p x y ∈ ((R : ↥M) : ZFSet.{u})

/-- The semantic content of `forcesEqDef` at given codes: likewise, recording the forced
equality. -/
def AtomicEqRealized (condSet orderCode p x y : ZFSet.{u}) : Prop :=
  ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧ x ∈ ((A : ↥M) : ZFSet.{u}) ∧
    y ∈ ((A : ↥M) : ZFSet.{u}) ∧
    ∃ R : ↥M, AtomicCoherentOn condSet orderCode ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
      entry eqTag p x y ∈ ((R : ↥M) : ZFSet.{u})

/-- The semantic content of `forcesMemDef` at given codes: likewise, with density of the
membership slice below `p`. -/
def AtomicMemRealized (condSet orderCode p x y : ZFSet.{u}) : Prop :=
  ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧ x ∈ ((A : ↥M) : ZFSet.{u}) ∧
    y ∈ ((A : ↥M) : ZFSet.{u}) ∧
    ∃ R : ↥M, AtomicCoherentOn condSet orderCode ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
      DenseMem condSet orderCode ((R : ↥M) : ZFSet.{u}) p x y

end Atomic

section Uniform

variable {M : MaterialCarrier.{u}}

/-- The uniform membership-witness formula, read at its parameter vector, is
`AtomicMemWitnessRealized`. -/
theorem realize_memWitnessUniform_iff {condSet orderCode p x y : ↥M}
    (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M) (hq : (natCode eqTag : ZFSet.{u}) ∈ M) :
    memWitnessUniform.Realize (uniformParams ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩
        condSet orderCode p x y) default ↔
      AtomicMemWitnessRealized M condSet orderCode p x y := by
  rw [memWitnessUniform, realize_memWitnessDef (by simp [uniformParams]) (by simp [uniformParams])]
  simp only [uniformParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
  rfl

/-- The uniform forced-equality formula, read at its parameter vector, is `AtomicEqRealized`. -/
theorem realize_forcesEqUniform_iff {condSet orderCode p x y : ↥M}
    (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M) (hq : (natCode eqTag : ZFSet.{u}) ∈ M) :
    forcesEqUniform.Realize (uniformParams ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩
        condSet orderCode p x y) default ↔
      AtomicEqRealized M condSet orderCode p x y := by
  rw [forcesEqUniform, realize_forcesEqDef (by simp [uniformParams]) (by simp [uniformParams])]
  simp only [uniformParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
  rfl

/-- The uniform forced-membership formula, read at its parameter vector, is
`AtomicMemRealized`. -/
theorem realize_forcesMemUniform_iff {condSet orderCode p x y : ↥M}
    (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M) (hq : (natCode eqTag : ZFSet.{u}) ∈ M) :
    forcesMemUniform.Realize (uniformParams ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩
        condSet orderCode p x y) default ↔
      AtomicMemRealized M condSet orderCode p x y := by
  rw [forcesMemUniform, realize_forcesMemDef (by simp [uniformParams]) (by simp [uniformParams])]
  simp only [uniformParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
  rfl

end Uniform

/-! ### The typed equivalences, materially

What `atomicDefinability` says once its uniform formulas are read through the predicates
above: the shape every consumer takes as a hypothesis. -/

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **The three typed atomic equivalences**, on `atomicDefinability`'s ledger. -/
theorem atomicRealized_iff
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
    {P : Type u} [Preorder P] {Pres : InternalForcingPresentation M.toMaterialCarrier P}
    {N : InternalNamePresentation M.toMaterialCarrier P}
    (hc : InternalNameCoding Pres N) (i j : N.Code) (r : P) :
    (AtomicMemWitnessRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode
        (condCode Pres r) (N.code i) (N.code j) ↔ MemWitness r (N.decode i) (N.decode j)) ∧
    (AtomicEqRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode
        (condCode Pres r) (N.code i) (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j)) ∧
    (AtomicMemRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode
        (condCode Pres r) (N.code i) (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j)) := by
  obtain ⟨h₁, h₂, h₃⟩ := M.atomicDefinability hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat
    hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r
  rw [realize_memWitnessUniform_iff] at h₁
  rw [realize_forcesEqUniform_iff] at h₂
  rw [realize_forcesMemUniform_iff] at h₃
  exact ⟨h₁, h₂, h₃⟩

end MaterialGround

end Forcing
