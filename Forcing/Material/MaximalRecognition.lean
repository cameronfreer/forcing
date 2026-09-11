/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.MaximalNames
import Forcing.Material.NameCertificateCompleteness
import Forcing.Material.NameRecognition

/-!
# The concrete recognizer for the maximal name family

ADR 0006, tranche 2, closing step: an `InternalNameRecognition` for `MaximalNames.maximal`, the
first one that exists rather than being assumed. The recognizing formula is the certificate

```text
∃ D, x ∈ D ∧ nameDomainDef condSet D
```

a fixed unary formula with the condition set as its **sole parameter**. It is per-candidate — the
witness `D` is an existentially quantified set, never a master set of all name codes — so the
guardrail of `Forcing/Material/NameCoding.lean` is respected.

## Exactness, from three theorems

`realize_iff` is soundness and no junk against the exact range of `code`:

* *soundness*: a certificate yields `IsNameCode`, by `isNameCode_of_mem_nameDomain` (axiom-free);
* *completeness*: `IsNameCode` in the ground yields a certificate in the ground, by
  `exists_nameDomain_of_isNameCode` — this is where the theory is charged;
* *exactness*: `mem_range_code_iff` identifies the hereditarily valid carrier elements with the
  range of the maximal presentation's `code`.

## Ledger

Exactly that of certificate completeness: `certificateGatherSentence` (Collection),
`certificateFilterSentence` (Separation), Pairing, General Union. Priced where paid — on the
recognizer's construction, not on any consumer's statement beyond these four hypotheses.

## Main definitions

* `Forcing.certificateFormula`: the recognizing formula.
* `Forcing.MaterialGround.maximalRecognition`: the recognizer.

## Main results

* `Forcing.MaterialGround.realize_certificateFormula`: the formula's exact law.
-/

universe u

namespace Forcing

open FirstOrder Language

/-- **The certificate formula**: parameter `condSet`; `∃ D, x ∈ D ∧ nameDomain condSet D`. -/
def certificateFormula : memLang.BoundedFormula (Fin 1) 1 :=
  ∃' (memFormula (liftTerm (&(0 : Fin 1))) (&(Fin.last 1)) ⊓
    nameDomainDef (liftTerm (var (Sum.inl 0))) (&(Fin.last 1)))

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- The certificate formula holds exactly when some member of the ground is a name domain
containing the candidate. -/
theorem realize_certificateFormula (cs c : ↥M.toMaterialCarrier) :
    certificateFormula.Realize ![cs] ![c] ↔
      ∃ D ∈ M, (c : ZFSet.{u}) ∈ D ∧ IsNameDomain (cs : ZFSet.{u}) D := by
  have hw : ∀ D : ↥M.toMaterialCarrier,
      (nameDomainDef (liftTerm (var (Sum.inl 0))) (&(Fin.last 1))).Realize ![cs]
        (Fin.snoc ![c] D) ↔ IsNameDomain (cs : ZFSet.{u}) (D : ZFSet.{u}) := by
    intro D
    rw [realize_nameDomainDef]
    simp [liftTerm]
  simp only [certificateFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  exact ⟨fun ⟨D, hcD, hD⟩ ↦ ⟨(D : ZFSet.{u}), D.2, hcD, (hw D).1 hD⟩,
    fun ⟨D, hDM, hcD, hD⟩ ↦ ⟨⟨D, hDM⟩, hcD, (hw _).2 hD⟩⟩

variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-- **The recognizer for the maximal name family.** Arity one, parameter the condition set,
formula the certificate. Exact by soundness, completeness, and maximality. -/
def maximalRecognition (hgat : certificateGatherSentence ∈ T)
    (hfil : certificateFilterSentence ∈ T) (hp : pairingSentence ∈ T)
    (huni : unionSentence ∈ T) : InternalNameRecognition (MaximalNames.maximal Pres) where
  arity := 1
  formula := certificateFormula
  params := ![Pres.conditionSet]
  realize_iff c := by
    rw [M.realize_certificateFormula]
    constructor
    · rintro ⟨D, -, hcD, hD⟩
      obtain ⟨i, hi⟩ := (MaximalNames.mem_range_code_iff Pres).2
        ⟨c.2, isNameCode_of_mem_nameDomain hD _ hcD⟩
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, hi⟩
      obtain ⟨-, hc⟩ := (MaximalNames.mem_range_code_iff Pres).1 ⟨i, hi.symm⟩
      exact M.exists_nameDomain_of_isNameCode hgat hfil hp huni Pres.conditionSet.2 hc c.2

end MaterialGround

end Forcing
