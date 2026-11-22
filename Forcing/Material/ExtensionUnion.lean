/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.UnionName
import Forcing.Material.ProductCover

/-!
# General Union in the extension

M7 item 6 (#241), general Union, second PR: the internal construction of the union code and
the preservation theorem

```text
↥((maximal Pres).extensionCarrier (G : Set P)) ⊨ unionSentence      (G : Order.PFilter P)
```

The preservation theorem is stated for a filter; its proof uses only upward closure and
downward directedness, through the valuation law (`UnionName.lean`), and filter nonemptiness is
unused. No genericity, no `OrderTop`, no truth lemma.

## The construction

1. **Product cover** (`exists_productCover`, in `Forcing/Material/ProductCover.lean`, shared
   with Separation): for internal sets `A` and `R`, a ground set containing `⟨s, ρ⟩` for every
   `s ∈ A` and `ρ ∈ R`. Coverage only: no name validity, order, or filter. Two Collection
   instances, Pairing, General Union; neither Collection output is filtered.
2. **The union code** (`exists_unionCode`): with `A := cs` and `R := ⋃⁵ t` (General Union five
   times), Separation by `unionFilterSentence` gives `U`, and `IsUnionBranch.exists_mem_bound`
   shows the cover contains every union branch, so `∀ m, m ∈ U ↔ IsUnionBranch cs ord t m`.
3. **Preservation** (`extension_models_union`): validity and valuation from `UnionName.lean`,
   through that exact characterization, and the carrier converse.

**Empty index sets need no case split.** When `A` or `R` is empty, the Collection obligations
are vacuous and the steps run unchanged. No internal empty set is assumed; Empty Set is not
charged.

## Ledger

Read off `exists_unionCode`: **two Collection instances** (`pairImageGatherSentence`,
`fiberCoverGatherSentence`), **one Separation instance** (`unionFilterSentence`), **Pairing**,
and **General Union**. No Infinity, Empty Set, Binary Union, or Power Set. The inner instance is
the check-name construction's pair-image gather, shared through
`Forcing/Material/PairImageGather.lean`; this module imports no check-graph machinery.

## Main results

* `Forcing.MaterialGround.exists_unionCode`.
* `Forcing.MaterialCarrier.realize_unionSentence_of`: the carrier converse.
* `Forcing.MaterialGround.extension_models_union`.
-/

universe u

namespace Forcing

open FirstOrder Language PName

/-! ### The carrier converse -/

/-- A carrier closed under `⋃₀` satisfies General Union. -/
theorem MaterialCarrier.realize_unionSentence_of (C : MaterialCarrier.{u})
    (h : ∀ x ∈ C, ZFSet.sUnion x ∈ C) : ↥C ⊨ unionSentence := by
  simp only [unionSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, realize_sUnionDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc]
  intro x
  exact ⟨⟨_, h x x.2⟩, rfl⟩

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-! ### The instances, at concrete parameters -/

theorem realize_unionFilterFormula (cs ord t m : ↥M.toMaterialCarrier) :
    unionFilterFormula.Realize ![cs, ord, t] ![m] ↔
      IsUnionBranch (cs : ZFSet.{u}) (ord : ZFSet.{u}) (t : ZFSet.{u}) (m : ZFSet.{u}) := by
  rw [unionFilterFormula, realize_unionBranchDef]
  simp

/-! ### The union code -/

/-- **The union code exists in the ground**, characterized exactly: for internal `cs`, `ord`,
`t`, some `U ∈ M` has `m ∈ U ↔ IsUnionBranch cs ord t m`. Separation from the product cover of
`cs × ⋃⁵ t`, which contains every union branch by `IsUnionBranch.exists_mem_bound`. Ledger: two
Collection instances, one Separation instance, Pairing, General Union. -/
theorem exists_unionCode (hpg : pairImageGatherSentence ∈ T)
    (hfc : fiberCoverGatherSentence ∈ T) (hsep : unionFilterSentence ∈ T)
    (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T) {cs ord t : ZFSet.{u}}
    (hcs : cs ∈ M) (hord : ord ∈ M) (ht : t ∈ M) :
    ∃ U ∈ M, ∀ m, m ∈ U ↔ IsUnionBranch cs ord t m := by
  have hR : ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion t)))) ∈ M :=
    M.sUnion_mem huni (M.sUnion_mem huni (M.sUnion_mem huni (M.sUnion_mem huni
      (M.sUnion_mem huni ht))))
  obtain ⟨Bd, hBdM, hBd⟩ := M.exists_productCover hpg hfc hp huni hcs hR
  obtain ⟨U, hU⟩ := M.exists_separation (φ := unionFilterFormula) hsep
    ![⟨cs, hcs⟩, ⟨ord, hord⟩, ⟨t, ht⟩] ⟨Bd, hBdM⟩
  refine ⟨U, U.2, fun m ↦ ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩⟩
  · have hmM := M.mem_trans hm U.2
    exact (M.realize_unionFilterFormula _ _ _ ⟨m, hmM⟩).1 ((hU ⟨m, hmM⟩).1 hm).2
  · obtain ⟨s, hs, ρ, hρ, rfl⟩ := hm.exists_mem_bound
    have hmBd := hBd s hs ρ hρ
    have hmM := M.mem_trans hmBd hBdM
    exact (hU ⟨_, hmM⟩).2 ⟨hmBd, (M.realize_unionFilterFormula _ _ _ ⟨_, hmM⟩).2 hm⟩

/-! ### Preservation -/

variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

open MaximalNames

/-- **General Union holds in the extension along a filter.** The union code of each name is
built in the ground and values to the union of its value. The proof uses only upward closure
and downward directedness of `G`; filter nonemptiness is unused. No genericity, no `OrderTop`, no
truth lemma. Ledger: two Collection
instances (`pairImageGatherSentence`, `fiberCoverGatherSentence`), one Separation instance
(`unionFilterSentence`), Pairing, General Union. -/
theorem extension_models_union (hpg : pairImageGatherSentence ∈ T)
    (hfc : fiberCoverGatherSentence ∈ T) (hsep : unionFilterSentence ∈ T)
    (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T) (G : Order.PFilter P) :
    ↥((maximal Pres).extensionCarrier (G : Set P)) ⊨ unionSentence := by
  refine MaterialCarrier.realize_unionSentence_of _ fun x hx ↦ ?_
  obtain ⟨i, rfl⟩ := (maximal Pres).mem_extensionCarrier_iff.1 hx
  obtain ⟨-, hi⟩ := (mem_range_code_iff Pres).1 ⟨i, rfl⟩
  obtain ⟨U, hUM, hU⟩ := M.exists_unionCode hpg hfc hsep hp huni Pres.conditionSet.2
    Pres.orderCode.2 ((maximal Pres).code_mem i)
  obtain ⟨k, hk⟩ := (mem_range_code_iff Pres).2 ⟨hUM, isNameCode_of_isUnionBranch hi hU⟩
  refine (maximal Pres).mem_extensionCarrier_iff.2 ⟨k, ?_⟩
  refine (zval_decode_of_isUnionBranch Pres (fun _ _ hab ha ↦ G.mem_of_le hab ha) G.directed
    (i := i) (k := k) fun m ↦ ?_).symm
  rw [hk]
  exact hU m

end MaterialGround

end Forcing
