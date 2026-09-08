/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.MaximalNames
import Forcing.Material.Semantics

/-!
# The name certificate: internal vocabulary and assembly

ADR 0006, tranche 2, first step. The recognizer for the maximal name family is the certificate

```text
∃ D, x ∈ D ∧ IsNameDomain condSet D
```

and this module internalizes its vocabulary — the domain condition and the branch-witness
relation — as term-parameterized formulas with **exact** realization laws, then proves the
semantic assembly step that certificate completeness will run on.

## The formulas mention only membership and pairing

`IsNameCode` never enters a formula. It belongs to the external correctness argument: soundness
is `isNameCode_of_mem_nameDomain`, and completeness will be an external induction on `IsNameCode`
whose recursive witnesses are gathered by the named schemes. Every quantifier bridge below is
carrier transitivity — no construction axiom, no theory hypothesis.

## Assembly: any closed domain certifies

`IsNameDomain cs D` accepts **any** domain closed under branch second components, not the least
descendant closure, and closed domains are preserved by union. So a certificate for `x` can be
assembled from certificates for the subnames of its branches: `{x} ∪ ⋃₀ F`, where `F` covers every
branch of `x` and consists of closed domains. `F` need not contain *every* certificate of a branch
— certificates are not unique, and Collection will supply only coverage — so the assembly asks
exactly for coverage and closure, nothing more. This is what makes completeness a direct
induction on `IsNameCode` rather than an ω-iteration of the descendant step.

## Main definitions

* `Forcing.branchInDef`, `Forcing.nameDomainDef`, `Forcing.branchCertificateDef`: the formulas.
* `Forcing.BranchCertificate`: the branch-witness relation, on sets.

## Main results

* `Forcing.realize_branchInDef`, `Forcing.realize_nameDomainDef`,
  `Forcing.realize_branchCertificateDef`: the exact realization laws.
* `Forcing.isNameDomain_assemble`: the semantic assembly step, axiom-free.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-! ### The formulas -/

section Syntax

variable {α : Type v} {n : ℕ}

/-- `∃ c e, y = ⟨c, e⟩ ∧ c ∈ cs ∧ e ∈ D`: `y` is a branch whose condition lies in `cs` and whose
subname lies in `D`. -/
def branchInDef (cs D y : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) (liftTerm (liftTerm y)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm cs)) ⊓
      memFormula (&(Fin.last (n + 1))) (liftTerm (liftTerm D))))

/-- **The domain condition**: `∀ z ∈ D, ∀ y ∈ z, branchIn cs D y` — every member of `D` is
locally branch-shaped with subnames back in `D`. -/
def nameDomainDef (cs D : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm D) ⟹
    ∀' (memFormula (&(Fin.last (n + 1))) (&(Fin.castSucc (Fin.last n))) ⟹
      branchInDef (liftTerm (liftTerm cs)) (liftTerm (liftTerm D)) (&(Fin.last (n + 1)))))

/-- **The branch-witness relation**: `D` is a closed domain containing the subname of the branch
`b`. The relation Collection will be applied to, indexed by the branches of a code. -/
def branchCertificateDef (cs b D : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  branchInDef cs D b ⊓ nameDomainDef cs D

end Syntax

/-! ### The relation, on sets -/

/-- `BranchCertificate cs b D`: `b = ⟨c, e⟩` with `c ∈ cs`, `e ∈ D`, and `D` a name domain. -/
def BranchCertificate (cs b D : ZFSet.{u}) : Prop :=
  ∃ c e, b = ZFSet.pair c e ∧ c ∈ cs ∧ e ∈ D ∧ IsNameDomain cs D

theorem branchCertificate_iff {cs b D : ZFSet.{u}} :
    BranchCertificate cs b D ↔
      (∃ c e, b = ZFSet.pair c e ∧ c ∈ cs ∧ e ∈ D) ∧ IsNameDomain cs D := by
  constructor
  · rintro ⟨c, e, hb, hc, he, hD⟩
    exact ⟨⟨c, e, hb, hc, he⟩, hD⟩
  · rintro ⟨⟨c, e, hb, hc, he⟩, hD⟩
    exact ⟨c, e, hb, hc, he, hD⟩

/-! ### Realization laws -/

section Realization

variable {α : Type v} {n : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin n → M}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

/-- The branch law. The backward direction needs the two components in the carrier, and they
are members of members of the realized branch. -/
theorem realize_branchInDef {cs D y : memLang.Term (α ⊕ Fin n)} :
    (branchInDef cs D y).Realize v xs ↔
      ∃ c e, ⟪y⟫ = ZFSet.pair c e ∧ c ∈ ⟪cs⟫ ∧ e ∈ ⟪D⟫ := by
  simp only [branchInDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, realize_pairDef,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero,
    Matrix.cons_val_one, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]
  constructor
  · rintro ⟨c, e, hy, hc, he⟩
    exact ⟨c, e, hy, hc, he⟩
  · rintro ⟨c, e, hy, hc, he⟩
    have hyM : ⟪y⟫ ∈ M := (Term.realize (Sum.elim v xs) y : ↥M).2
    obtain ⟨hcM, heM⟩ := M.pair_components_mem (hy ▸ hyM)
    exact ⟨⟨c, hcM⟩, ⟨e, heM⟩, hy, hc, he⟩

/-- **The domain law**: exact against `IsNameDomain`. Every quantifier bridge is transitivity. -/
theorem realize_nameDomainDef {cs D : memLang.Term (α ⊕ Fin n)} :
    (nameDomainDef cs D).Realize v xs ↔ IsNameDomain ⟪cs⟫ ⟪D⟫ := by
  have hw : ∀ z y : ↥M,
      (branchInDef (liftTerm (liftTerm cs)) (liftTerm (liftTerm D))
        (&(Fin.last (n + 1)))).Realize v (Fin.snoc (Fin.snoc xs z) y) ↔
      ∃ c e, (y : ZFSet.{u}) = ZFSet.pair c e ∧ c ∈ ⟪cs⟫ ∧ e ∈ ⟪D⟫ := by
    intro z y
    rw [realize_branchInDef]
    simp [realize_liftTerm]
  have hDM : ⟪D⟫ ∈ M := (Term.realize (Sum.elim v xs) D : ↥M).2
  simp only [nameDomainDef, BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    realize_liftTerm, IsNameDomain]
  constructor
  · intro h z hz y hy
    exact (hw _ _).1 (h ⟨z, M.mem_trans hz hDM⟩ hz ⟨y, M.mem_trans hy (M.mem_trans hz hDM)⟩ hy)
  · intro h z hz y hy
    exact (hw z y).2 (h (z : ZFSet.{u}) hz (y : ZFSet.{u}) hy)

/-- **The branch-certificate law**: exact against `BranchCertificate`. -/
theorem realize_branchCertificateDef {cs b D : memLang.Term (α ⊕ Fin n)} :
    (branchCertificateDef cs b D).Realize v xs ↔ BranchCertificate ⟪cs⟫ ⟪b⟫ ⟪D⟫ := by
  rw [branchCertificateDef, BoundedFormula.realize_inf, realize_branchInDef,
    realize_nameDomainDef, branchCertificate_iff]

end Realization

/-! ### Assembly -/

/-- **The assembly step.** If `F` consists of name domains and covers every branch of `x` — each
branch has a certificate in `F` — then `{x} ∪ ⋃₀ F` is a name domain containing `x`. Coverage
and closure only: `F` is not assumed to contain every certificate. Axiom-free. -/
theorem isNameDomain_assemble {cs x F : ZFSet.{u}} (hF : ∀ D ∈ F, IsNameDomain cs D)
    (hcov : ∀ b ∈ x, ∃ D ∈ F, BranchCertificate cs b D) :
    x ∈ ({x} : ZFSet.{u}) ∪ ZFSet.sUnion F ∧
      IsNameDomain cs (({x} : ZFSet.{u}) ∪ ZFSet.sUnion F) := by
  refine ⟨ZFSet.mem_union.2 (Or.inl (ZFSet.mem_singleton.2 rfl)), fun z hz y hy ↦ ?_⟩
  rcases ZFSet.mem_union.1 hz with hz | hz
  · rw [ZFSet.mem_singleton] at hz
    subst hz
    obtain ⟨D, hDF, c, e, hb, hc, he, -⟩ := hcov y hy
    exact ⟨c, e, hb, hc, ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sUnion.2 ⟨D, hDF, he⟩))⟩
  · obtain ⟨D, hDF, hzD⟩ := ZFSet.mem_sUnion.1 hz
    obtain ⟨c, e, hb, hc, he⟩ := hF D hDF z hzD y hy
    exact ⟨c, e, hb, hc, ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sUnion.2 ⟨D, hDF, he⟩))⟩

end Forcing
