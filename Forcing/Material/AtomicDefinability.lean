/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicFormula
import Forcing.Material.RecursionExistence
import Forcing.Material.UnionIterationFamily

/-!
# Atomic definability

Composing the two halves of 3b. `RecursionExistence` builds a coherent graph over *any
supplied* transitive domain; `UnionIterationFamily` supplies one for an arbitrary pair of name
codes. Together they give, for each pair, an internal graph whose two tagged slices *are* the
external atomic forcing relations.

## What this theorem is

Three layers, and the distinctions between them are the point.

* `exists_atomicCertificate` — a **construction certificate**, explicit about both `A` and
  `R`. Not a definability theorem.
* `exists_atomicDefinitionDomain` — definability **relative to a domain**. The formulas hide
  the graph but take `A` as a parameter, so it is uniform in the condition and *not* in the
  name codes: the domain varies with the pair.
* `atomicDefinability` — **the uniform endpoint**. The domain is hidden too, so three fixed
  seven-parameter formulas work at every pair. This is 3b's endpoint and ADR 0005's stated
  target.

The middle layer is retained because the certificate's `A` is genuinely useful to anything
that wants to name the domain; the top layer is what the formula compiler consumes.

## The ledger

Everything the two halves charge, and nothing new:

* the seventeen recursion instances, plus the union-iteration instances;
* Infinity and `omegaSepSentence`, for internal `ω` — and **only** through
  `exists_transitiveDomain`. `exists_atomicCoherentOn` remains priced without Infinity, which
  is the separation ADR 0005 predicted;
* Pairing, Binary Union, General Union;
* **Empty Set**, which appears here and *only* here;
* **no Foundation, no Power Set**, and no Cartesian product.

**On Empty Set.** Neither half charges it. `exists_transitiveDomain` takes `∅` from `ω`;
`exists_atomicCoherentOn` takes its tags as parameters, and `entry_mem` takes each tag's
numeral as a hypothesis rather than building it. Composition is the first point at which
someone must actually construct the two numerals, which is `natCode_mem` — so Empty Set
genuinely emerges at composition rather than being inherited.

That is a real fact about the construction, not a bookkeeping accident, and it only became
true after the parameterized recursion was weakened to take tag numerals as hypotheses.
-/

universe u

namespace Forcing

open FirstOrder Language AtomicRecursion

/-! ### The three atomic instances

The formulas at their eight parameters — the two tags, the condition set, the order code, the
domain, the condition, and the two name codes. Naming them pins the bound-variable count at
zero — these are closed in the bound-variable context, with eight parameters. (They are
`BoundedFormula (Fin 8) 0`, not `memLang.Sentence`: the parameters are free.) -/

/-- The parameter vector the atomic instances are read at. -/
def atomicParams {M : MaterialCarrier.{u}} (tagMem tagEq condSet orderCode A p x y : ↥M) :
    Fin 8 → ↥M := ![tagMem, tagEq, condSet, orderCode, A, p, x, y]

/-- Internal membership-witness, at its eight parameters. -/
def memWitnessInstance : memLang.BoundedFormula (Fin 8) 0 :=
  memWitnessDefOn (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6)) (var (Sum.inl 7))

/-- Internal forced equality, at its eight parameters. -/
def forcesEqInstance : memLang.BoundedFormula (Fin 8) 0 :=
  forcesEqDefOn (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6)) (var (Sum.inl 7))

/-- Internal forced membership, at its eight parameters. -/
def forcesMemInstance : memLang.BoundedFormula (Fin 8) 0 :=
  forcesMemDefOn (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6)) (var (Sum.inl 7))

/-! ### The uniform instances

**Seven** parameters — the domain is gone, hidden inside the formula. These are the atomic
definitions proper; the eight-parameter ones above are the relative versions they are built
from. -/

/-- The parameter vector the uniform instances are read at. -/
def uniformParams {M : MaterialCarrier.{u}} (tagMem tagEq condSet orderCode p x y : ↥M) :
    Fin 7 → ↥M := ![tagMem, tagEq, condSet, orderCode, p, x, y]

/-- Uniform internal membership-witness. -/
def memWitnessUniform : memLang.BoundedFormula (Fin 7) 0 :=
  memWitnessDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6))

/-- Uniform internal forced equality. -/
def forcesEqUniform : memLang.BoundedFormula (Fin 7) 0 :=
  forcesEqDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6))

/-- Uniform internal forced membership. -/
def forcesMemUniform : memLang.BoundedFormula (Fin 7) 0 :=
  forcesMemDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6))

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **The atomic construction certificate.**

For any two name codes there is a transitive `A ∈ M` containing both and a graph `R ∈ M`
coherent over it, whose slices are the external atomic relations at those codes:

* the membership slice is `MemWitness`;
* the equality slice is `ForcesEq`;
* the *density* of the membership slice is `ForcesMem`.

`A` and `R` are exposed rather than hidden behind an existential over the conclusion. That is
what makes this a certificate: `exists_atomicDefinitionDomain` and `atomicDefinability` are
built from it, and the first of them still hands the domain back. -/
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
    hrgat hrfil hfgat hffil huni hp hu
    ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
    ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩
    Pres.conditionSet Pres.orderCode A hAtrans rfl rfl
  exact ⟨R, hAtrans, hiA, hjA, hR,
    fun p ↦ memWitness_entry_iff hAtrans hR hc hiA hjA p,
    fun p ↦ forcesEq_entry_iff hAtrans hR hc hiA hjA p,
    fun q ↦ denseMem_iff_forcesMem hAtrans hR hc hiA hjA q⟩

/-- **Atomic definability relative to a domain.**

For any two name codes there is a transitive `A ∈ M` containing both, over which the three
internal instances define the external atomic forcing relations.

`A` is a **material parameter**; the graph is **existentially hidden** inside each formula.

**Soundness** (formula → external) works for *whichever* coherent graph the formula supplies,
since conditional correctness applies to every graph coherent over `A`. **Completeness**
(external → formula) offers the certificate's graph. Neither direction consults uniqueness, so
no graph framework leaks into the formula interface.

**Not** 3b's endpoint: the domain is returned externally, so this is uniform in the condition
but not in the name codes. `atomicDefinability` below hides the domain and is uniform in
all of them. -/
theorem exists_atomicDefinitionDomain
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
    (hc : InternalNameCoding Pres N) (i j : N.Code) :
    ∃ A : ↥M.toMaterialCarrier,
      (A : ZFSet.{u}).IsTransitive ∧
        N.code i ∈ (A : ZFSet.{u}) ∧ N.code j ∈ (A : ZFSet.{u}) ∧
        ∀ p : P,
          (memWitnessInstance.Realize
              (atomicParams ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
                ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩
                Pres.conditionSet Pres.orderCode A
                ⟨condCode Pres p, M.toMaterialCarrier.mem_trans (Pres.code_mem p)
                  Pres.conditionSet.2⟩
                ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩) default ↔
            MemWitness p (N.decode i) (N.decode j)) ∧
          (forcesEqInstance.Realize
              (atomicParams ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
                ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩
                Pres.conditionSet Pres.orderCode A
                ⟨condCode Pres p, M.toMaterialCarrier.mem_trans (Pres.code_mem p)
                  Pres.conditionSet.2⟩
                ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩) default ↔
            ForcesEq p (N.decode i) (N.decode j)) ∧
          (forcesMemInstance.Realize
              (atomicParams ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
                ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩
                Pres.conditionSet Pres.orderCode A
                ⟨condCode Pres p, M.toMaterialCarrier.mem_trans (Pres.code_mem p)
                  Pres.conditionSet.2⟩
                ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩) default ↔
            ForcesMem p (N.decode i) (N.decode j)) := by
  obtain ⟨A, R, hAtrans, hiA, hjA, hR, hmw, heq, hfm⟩ :=
    M.exists_atomicCertificate hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat
      hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j
  refine ⟨A, hAtrans, hiA, hjA, fun p ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [memWitnessInstance, realize_memWitnessDefOn (by simp [atomicParams])
      (by simp [atomicParams])]
    simp only [atomicParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    exact ⟨fun ⟨R', hR', he'⟩ ↦ (memWitness_entry_iff hAtrans hR' hc hiA hjA p).1 he',
      fun h ↦ ⟨R, hR, (hmw p).2 h⟩⟩
  · rw [forcesEqInstance, realize_forcesEqDefOn (by simp [atomicParams])
      (by simp [atomicParams])]
    simp only [atomicParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    exact ⟨fun ⟨R', hR', he'⟩ ↦ (forcesEq_entry_iff hAtrans hR' hc hiA hjA p).1 he',
      fun h ↦ ⟨R, hR, (heq p).2 h⟩⟩
  · rw [forcesMemInstance, realize_forcesMemDefOn (by simp [atomicParams])
      (by simp [atomicParams])]
    simp only [atomicParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    exact ⟨fun ⟨R', hR', hd'⟩ ↦ (denseMem_iff_forcesMem hAtrans hR' hc hiA hjA p).1 hd',
      fun h ↦ ⟨R, hR, (hfm p).2 h⟩⟩

/-- **Atomic definability, uniform.**

Three **fixed** internal formulas, uniform in the condition *and* the name codes:

```text
memWitnessUniform  ↔  MemWitness p τ σ
forcesEqUniform    ↔  ForcesEq   p τ σ
forcesMemUniform   ↔  ForcesMem  p τ σ
```

Nothing is returned externally. The domain is existentially quantified *inside* each formula,
alongside its transitivity and the codes' membership, so the same seven-parameter formula
works at every pair. That is what ADR 0005 asked of 3b, and what the formula compiler needs:
an assignment ranges over all names, and there is deliberately no single material set
containing every name code.

**This is 3b's endpoint.** -/
theorem atomicDefinability
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
    (hc : InternalNameCoding Pres N) (i j : N.Code) (p : P) :
    (memWitnessUniform.Realize
        (uniformParams ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
          ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩ Pres.conditionSet Pres.orderCode
          ⟨condCode Pres p, M.toMaterialCarrier.mem_trans (Pres.code_mem p)
            Pres.conditionSet.2⟩
          ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩) default ↔
      MemWitness p (N.decode i) (N.decode j)) ∧
    (forcesEqUniform.Realize
        (uniformParams ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
          ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩ Pres.conditionSet Pres.orderCode
          ⟨condCode Pres p, M.toMaterialCarrier.mem_trans (Pres.code_mem p)
            Pres.conditionSet.2⟩
          ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩) default ↔
      ForcesEq p (N.decode i) (N.decode j)) ∧
    (forcesMemUniform.Realize
        (uniformParams ⟨natCode memWitnessTag, M.natCode_mem he hp hu memWitnessTag⟩
          ⟨natCode eqTag, M.natCode_mem he hp hu eqTag⟩ Pres.conditionSet Pres.orderCode
          ⟨condCode Pres p, M.toMaterialCarrier.mem_trans (Pres.code_mem p)
            Pres.conditionSet.2⟩
          ⟨N.code i, N.code_mem i⟩ ⟨N.code j, N.code_mem j⟩) default ↔
      ForcesMem p (N.decode i) (N.decode j)) := by
  obtain ⟨A, R, hAtrans, hiA, hjA, hR, hmw, heq, hfm⟩ :=
    M.exists_atomicCertificate hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil hfgat
      hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j
  refine ⟨?_, ?_, ?_⟩
  · rw [memWitnessUniform, realize_memWitnessDef (by simp [uniformParams])
      (by simp [uniformParams])]
    simp only [uniformParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    exact ⟨fun ⟨A', hA', hiA', hjA', R', hR', he'⟩ ↦
        (memWitness_entry_iff hA' hR' hc hiA' hjA' p).1 he',
      fun h ↦ ⟨A, hAtrans, hiA, hjA, R, hR, (hmw p).2 h⟩⟩
  · rw [forcesEqUniform, realize_forcesEqDef (by simp [uniformParams])
      (by simp [uniformParams])]
    simp only [uniformParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    exact ⟨fun ⟨A', hA', hiA', hjA', R', hR', he'⟩ ↦
        (forcesEq_entry_iff hA' hR' hc hiA' hjA' p).1 he',
      fun h ↦ ⟨A, hAtrans, hiA, hjA, R, hR, (heq p).2 h⟩⟩
  · rw [forcesMemUniform, realize_forcesMemDef (by simp [uniformParams])
      (by simp [uniformParams])]
    simp only [uniformParams, Term.realize_var, Sum.elim_inl, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons]
    exact ⟨fun ⟨A', hA', hiA', hjA', R', hR', hd'⟩ ↦
        (denseMem_iff_forcesMem hA' hR' hc hiA' hjA' p).1 hd',
      fun h ↦ ⟨A, hAtrans, hiA, hjA, R, hR, (hfm p).2 h⟩⟩

end MaterialGround

end Forcing
