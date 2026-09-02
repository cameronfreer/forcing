/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicRealized
import Forcing.Material.CompilerBridge

/-!
# Compiler correctness

The compiled formula realizes exactly when the coded condition forces the source formula under the
decoded assignment. One structural induction, two directional projections, one material corollary.

## One induction, not two

The two directions are **mutually recursive**, through `.imp`. `ForcesFormula` is contravariant
there: `∀ q ≤ p, ForcesFormula q φ → ForcesFormula q ψ`. So proving external → compiled for
`φ.imp ψ` needs, from a *compiled* antecedent, an *external* one — the other direction at `φ`.
Proving compiled → external needs them in the opposite order. Neither direction has a standalone
induction; `forcesDef_correct` proves the conjunction, crossing projections at `.imp` explicitly.

## What the induction is parameterized by

* **The atomic equivalences**, `AtomicEqRealized` and `AtomicMemRealized` against `ForcesEq` and
  `ForcesMem`. These are the semantic content of the uniform seven-parameter definitions, consumed
  as black boxes: nothing here reopens the domain, the relation, or coherence. `atomicDefinability`
  supplies them in the material corollary.
* **Pair closure** of the carrier, used at exactly one site: compiled → external at `.all`, to
  build the extended assignment code the compiled universal hypothesis is instantiated at. The
  next assignment is a single `pair` of two elements already in hand, so Pairing is the whole
  price — Empty Set is *not* charged, because the induction never constructs a root assignment.
  Pairing is nonetheless a hypothesis of both projections: the mutual recursion carries it across.
* The fixed-parameter invariant `CompilerParams.Realizes`, the condition equation, and the
  assignment equation. The last two vary down the recursion and are re-established at each binder.

## Main results

* `Forcing.forcesDef_correct`: the simultaneous induction.
* `Forcing.realize_forcesDef_of_forcesFormula`, `Forcing.forcesFormula_of_realize_forcesDef`: the
  two projections.
* `Forcing.realize_forcesDef_iff_forcesFormula`: the biconditional.
* `Forcing.MaterialGround.realize_forcesDef_iff_forcesFormula`: the material corollary, with the
  atomic equivalences discharged by `atomicDefinability` and pair closure by `pairingSentence`.
-/

universe u v

namespace Forcing

open FirstOrder Language AtomicRecursion

/-! ### The induction -/

section Correctness

variable {α : Type v} {k : ℕ} {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}
variable {Rec : InternalNameRecognition N} {v : α → M} {free : Fin k → N.Code}

/-- **Compiler correctness, simultaneously in both directions.**

For every source formula, ambient context, parameter block realizing the presentation's fixed
codes, condition term realizing `condCode Pres r`, and assignment term realizing the combined
code of `free` and `bound`: the compiled formula realizes iff `r` forces the source formula
under the decoded assignment, in the family `N.names`.

The conjunction rather than an `Iff` is deliberate: the `.imp` case uses the antecedent's
induction hypothesis in one direction and the consequent's in the other, and the two projections
below are its two components. -/
theorem forcesDef_correct
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
    (hEq : ∀ (r : P) (i j : N.Code),
      AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j))
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j)) :
    ∀ {sn : ℕ} (φ : memLang.BoundedFormula (Fin k) sn) {m : ℕ}
      (Γ : CompilerParams α Rec.arity m) (pt aTm : memLang.Term (α ⊕ Fin m)) (xs : Fin m → M)
      (r : P) (bound : Fin sn → N.Code),
      Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs →
      ((Term.realize (Sum.elim v xs) pt : ↥M) : ZFSet.{u}) = condCode Pres r →
      ((Term.realize (Sum.elim v xs) aTm : ↥M) : ZFSet.{u}) =
        N.assignmentCode (combinedCodes free bound) →
      (ForcesFormula N.names (N.decode ∘ free) r φ (N.decode ∘ bound) →
        (forcesDef Rec.formula φ Γ pt aTm).Realize v xs) ∧
      ((forcesDef Rec.formula φ Γ pt aTm).Realize v xs →
        ForcesFormula N.names (N.decode ∘ free) r φ (N.decode ∘ bound)) := by
  intro sn φ
  induction φ with
  | falsum =>
    intro m Γ pt aTm xs r bound _ _ _
    exact ⟨fun h ↦ h.elim, fun h ↦ h⟩
  | equal t₁ t₂ =>
    intro m Γ pt aTm xs r bound hΓ hp ha
    rw [realize_forcesDef_equal_bridge ha hΓ, forcesFormula_equal,
      ← decode_combinedCodes_srcIndex free bound t₁, ← decode_combinedCodes_srcIndex free bound t₂,
      ← hEq, hp]
    constructor
    · intro h
      exact ⟨⟨_, N.code_mem _⟩, ⟨_, N.code_mem _⟩, rfl, rfl, h⟩
    · rintro ⟨x, y, hx, hy, h⟩
      rw [← hx, ← hy]
      exact h
  | rel R ts =>
    cases R
    intro m Γ pt aTm xs r bound hΓ hp ha
    rw [realize_forcesDef_rel_bridge ha hΓ, forcesFormula_rel,
      ← decode_combinedCodes_srcIndex free bound (ts 0),
      ← decode_combinedCodes_srcIndex free bound (ts 1), ← hMem, hp]
    constructor
    · intro h
      exact ⟨⟨_, N.code_mem _⟩, ⟨_, N.code_mem _⟩, rfl, rfl, h⟩
    · rintro ⟨x, y, hx, hy, h⟩
      rw [← hx, ← hy]
      exact h
  | imp φ ψ ihφ ihψ =>
    intro m Γ pt aTm xs r bound hΓ hp ha
    rw [realize_forcesDef_imp_bridge hΓ, forcesFormula_imp]
    have hlift : ∀ q : ↥M,
        ((Term.realize (Sum.elim v (Fin.snoc xs q)) (liftTerm aTm) : ↥M) : ZFSet.{u}) =
          N.assignmentCode (combinedCodes free bound) := by
      intro q; rw [realize_liftTerm]; exact ha
    have hq : ∀ q : ↥M, ((Term.realize (Sum.elim v (Fin.snoc xs q))
        (&(Fin.last m) : memLang.Term (α ⊕ Fin (m + 1))) : ↥M) : ZFSet.{u}) = (q : ZFSet.{u}) := by
      intro q; simp
    constructor
    · -- external → compiled: decode the internal strengthening, cross projections
      intro hext q hmem horder hφ
      rw [hp] at horder
      obtain ⟨q', hq', hle⟩ := exists_typed_of_imp_guard Pres hmem horder
      have hpq : ((Term.realize (Sum.elim v (Fin.snoc xs q))
          (&(Fin.last m) : memLang.Term (α ⊕ Fin (m + 1))) : ↥M) : ZFSet.{u}) =
            condCode Pres q' := by rw [hq]; exact hq'
      exact (ihψ Γ.lift _ _ _ q' bound (hΓ.lift q) hpq (hlift q)).1
        (hext q' hle ((ihφ Γ.lift _ _ _ q' bound (hΓ.lift q) hpq (hlift q)).2 hφ))
    · -- compiled → external: encode the typed strengthening, cross projections
      intro hcomp q' hle hφ
      obtain ⟨hmem, horder⟩ := imp_guard_of_typed Pres hle
      let q : ↥M := ⟨condCode Pres q', M.mem_trans (Pres.code_mem q') Pres.conditionSet.2⟩
      have hpq : ((Term.realize (Sum.elim v (Fin.snoc xs q))
          (&(Fin.last m) : memLang.Term (α ⊕ Fin (m + 1))) : ↥M) : ZFSet.{u}) =
            condCode Pres q' := hq q
      exact (ihψ Γ.lift _ _ _ q' bound (hΓ.lift q) hpq (hlift q)).2
        (hcomp q hmem (by rw [hp]; exact horder)
          ((ihφ Γ.lift _ _ _ q' bound (hΓ.lift q) hpq (hlift q)).1 hφ))
  | all φ ih =>
    intro m Γ pt aTm xs r bound hΓ hp ha
    rw [realize_forcesDef_all_bridge ha hΓ, forcesFormula_all]
    have hplift : ∀ c a' : ↥M,
        ((Term.realize (Sum.elim v (Fin.snoc (Fin.snoc xs c) a'))
          (liftTerm (liftTerm pt)) : ↥M) : ZFSet.{u}) = condCode Pres r := by
      intro c a'; rw [realize_liftTerm, realize_liftTerm]; exact hp
    have hsnoc : ∀ i : N.Code, N.decode ∘ Fin.snoc bound i =
        Fin.snoc (N.decode ∘ bound) (N.decode i) := fun i ↦ Fin.comp_snoc N.decode bound i
    constructor
    · -- external → compiled: the extension is handed to us
      intro hext i c a' hc ha'
      refine (ih Γ.lift.lift _ _ _ r (Fin.snoc bound i) ((hΓ.lift c).lift a') (hplift c a')
        (by simpa using ha')).1 ?_
      rw [hsnoc]
      exact hext (N.decode i) (N.decode_mem_names i)
    · -- compiled → external: build the extension by one pair — the Pairing site
      intro hcomp τ hτ
      obtain ⟨i, rfl⟩ := hτ
      have haM : N.assignmentCode (combinedCodes free bound) ∈ M :=
        ha ▸ (Term.realize (Sum.elim v xs) aTm : ↥M).2
      let c : ↥M := ⟨N.code i, N.code_mem i⟩
      let a' : ↥M := ⟨ZFSet.pair (N.code i) (N.assignmentCode (combinedCodes free bound)),
        hpair (N.code_mem i) haM⟩
      have ha' : ((a' : ↥M) : ZFSet.{u}) =
          N.assignmentCode (combinedCodes free (Fin.snoc bound i)) := by
        rw [combinedCodes_snoc, InternalNamePresentation.assignmentCode_snoc]
      rw [← hsnoc]
      exact (ih Γ.lift.lift _ _ _ r (Fin.snoc bound i) ((hΓ.lift c).lift a') (hplift c a')
        (by simpa using ha')).2 (hcomp i c a' rfl ha')

/-! ### The projections -/

variable {sn m : ℕ} {φ : memLang.BoundedFormula (Fin k) sn} {Γ : CompilerParams α Rec.arity m}
variable {pt aTm : memLang.Term (α ⊕ Fin m)} {xs : Fin m → M} {r : P} {bound : Fin sn → N.Code}

/-- **External forcing → compiled realization.** Pair closure is a hypothesis here too: this
direction reaches the other through every implication. -/
theorem realize_forcesDef_of_forcesFormula
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
    (hEq : ∀ (r : P) (i j : N.Code),
      AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j))
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hp : ((Term.realize (Sum.elim v xs) pt : ↥M) : ZFSet.{u}) = condCode Pres r)
    (ha : ((Term.realize (Sum.elim v xs) aTm : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound))
    (h : ForcesFormula N.names (N.decode ∘ free) r φ (N.decode ∘ bound)) :
    (forcesDef Rec.formula φ Γ pt aTm).Realize v xs :=
  (forcesDef_correct hpair hEq hMem φ Γ pt aTm xs r bound hΓ hp ha).1 h

/-- **Compiled realization → external forcing.** -/
theorem forcesFormula_of_realize_forcesDef
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
    (hEq : ∀ (r : P) (i j : N.Code),
      AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j))
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hp : ((Term.realize (Sum.elim v xs) pt : ↥M) : ZFSet.{u}) = condCode Pres r)
    (ha : ((Term.realize (Sum.elim v xs) aTm : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound))
    (h : (forcesDef Rec.formula φ Γ pt aTm).Realize v xs) :
    ForcesFormula N.names (N.decode ∘ free) r φ (N.decode ∘ bound) :=
  (forcesDef_correct hpair hEq hMem φ Γ pt aTm xs r bound hΓ hp ha).2 h

/-- **The biconditional.** -/
theorem realize_forcesDef_iff_forcesFormula
    (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
    (hEq : ∀ (r : P) (i j : N.Code),
      AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j))
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hp : ((Term.realize (Sum.elim v xs) pt : ↥M) : ZFSet.{u}) = condCode Pres r)
    (ha : ((Term.realize (Sum.elim v xs) aTm : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound)) :
    (forcesDef Rec.formula φ Γ pt aTm).Realize v xs ↔
      ForcesFormula N.names (N.decode ∘ free) r φ (N.decode ∘ bound) :=
  ⟨forcesFormula_of_realize_forcesDef hpair hEq hMem hΓ hp ha,
    realize_forcesDef_of_forcesFormula hpair hEq hMem hΓ hp ha⟩

end Correctness

/-! ### The material corollary -/

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **Compiler correctness, materially.** The atomic equivalences come from
`atomicDefinability`, pair closure from `pairingSentence ∈ T`; the ledger is exactly
`atomicDefinability`'s. -/
theorem realize_forcesDef_iff_forcesFormula
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
    (hc : InternalNameCoding Pres N) {Rec : InternalNameRecognition N}
    {α : Type v} {k sn m : ℕ} {v : α → M.toMaterialCarrier} {free : Fin k → N.Code}
    {φ : memLang.BoundedFormula (Fin k) sn} {Γ : CompilerParams α Rec.arity m}
    {pt aTm : memLang.Term (α ⊕ Fin m)} {xs : Fin m → M.toMaterialCarrier} {r : P}
    {bound : Fin sn → N.Code}
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hpt : ((Term.realize (Sum.elim v xs) pt : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      condCode Pres r)
    (ha : ((Term.realize (Sum.elim v xs) aTm : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound)) :
    (forcesDef Rec.formula φ Γ pt aTm).Realize v xs ↔
      ForcesFormula N.names (N.decode ∘ free) r φ (N.decode ∘ bound) := by
  exact Forcing.realize_forcesDef_iff_forcesFormula (fun hx hy ↦ M.pair_mem hp hx hy)
    (fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).2.1)
    (fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).2.2)
    hΓ hpt ha

end MaterialGround

end Forcing
