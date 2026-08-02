/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.ZFC.Basic
import Forcing.Name.Basic

/-!
# Valuation of names against a set of conditions

The valuation of a name keeps the branches whose conditions lie in a given set, recursively.
The set is an **arbitrary** `Set P` — no order, no filter laws, and no genericity: any
collection of conditions values every name. A `PFilter` coerces to `Set P` at call sites;
genericity earns its keep at the truth lemma.

The intensional/extensional boundary is placed exactly here: `val` lands in `PSet`, the
intensional side of mathlib's set theory, and the public laws are stated for `zval`, its
composite with the quotient into `ZFSet`.

**Valuation is not monotone in the condition set.** Growing the set admits more branches
*recursively*, which can change an existing element rather than merely add one:
`exists_not_zval_subset_zval` certifies the failure with an explicit two-level name whose
values along `S ⊆ S'` are `{∅}` and `{{∅}}`.

## Main definitions

* `Forcing.PName.val`: valuation into `PSet`.
* `Forcing.PName.zval`: the extensional valuation into `ZFSet`.

## Main results

* `Forcing.PName.mem_zval_iff`: the principal law — extensional membership in a valuation.
* `Forcing.PName.exists_not_zval_subset_zval`: valuation is not monotone in the condition set.
-/

universe u

namespace Forcing.PName

variable {P : Type u}

/-- Valuation against an arbitrary set of conditions: keep the admitted branches, recursively.
Uses only membership in `S` — no order, no filter laws, and no genericity. -/
def val (S : Set P) : PName P → PSet.{u}
  | .mk _ e c => PSet.mk {i // c i ∈ S} fun i ↦ (e i.1).val S

@[simp] theorem val_mk (S : Set P) (ι : Type u) (e : ι → PName P) (c : ι → P) :
    (mk ι e c).val S = PSet.mk {i // c i ∈ S} fun i ↦ (e i.1).val S :=
  rfl

/-- The extensional valuation: the composite of `val` with the quotient into `ZFSet`. The
public laws are stated here. -/
def zval (S : Set P) (τ : PName P) : ZFSet.{u} :=
  ZFSet.mk (τ.val S)

/-- **The principal law**: a set belongs to the valuation of `τ` exactly when it is the
valuation of a branch of `τ` whose condition is admitted. -/
theorem mem_zval_iff {S : Set P} {τ : PName P} {y : ZFSet.{u}} :
    y ∈ zval S τ ↔ ∃ i : τ.Idx, τ.conds i ∈ S ∧ y = zval S (τ.elems i) := by
  obtain ⟨ι, e, c⟩ := τ
  induction y using Quotient.inductionOn with
  | h z =>
    constructor
    · intro h
      obtain ⟨⟨i, hi⟩, hz⟩ := h
      exact ⟨i, hi, ZFSet.sound hz⟩
    · rintro ⟨i, hi, hy⟩
      exact ⟨⟨i, hi⟩, ZFSet.exact hy⟩

/-- The empty name values to the empty set along every condition set. -/
@[simp] theorem zval_empty (S : Set P) : zval S (∅ : PName P) = ∅ := by
  refine (ZFSet.eq_empty _).2 fun y hy ↦ ?_
  obtain ⟨i, -, -⟩ := mem_zval_iff.1 hy
  exact PEmpty.elim i

/-! ### Non-monotonicity, certified

Valuation is **not** `⊆`-monotone in the condition set. The witness is a two-level name over
`Bool`: the outer branch is admitted by both sets, the inner branch only by the larger one, so
the smaller set values the name to `{∅}` and the larger to `{{∅}}` — and `∅ ∈ {∅}` while
`∅ ∉ {{∅}}`.
-/

/-- **Valuation is not monotone in the condition set**: growing the set can change an existing
element rather than merely add one. -/
theorem exists_not_zval_subset_zval :
    ∃ (τ : PName Bool) (S S' : Set Bool), S ⊆ S' ∧ ¬zval S τ ⊆ zval S' τ := by
  refine ⟨mk PUnit (fun _ ↦ mk PUnit (fun _ ↦ ∅) fun _ ↦ true) fun _ ↦ false,
    {false}, Set.univ, Set.subset_univ _, fun h ↦ ?_⟩
  have hin : zval ({false} : Set Bool)
      (mk PUnit (fun _ ↦ (∅ : PName Bool)) fun _ ↦ true) = ∅ := by
    refine (ZFSet.eq_empty _).2 fun y hy ↦ ?_
    obtain ⟨i, hi, -⟩ := mem_zval_iff.1 hy
    simp at hi
  have hmem : (∅ : ZFSet) ∈ zval ({false} : Set Bool)
      (mk PUnit (fun _ ↦ mk PUnit (fun _ ↦ (∅ : PName Bool)) fun _ ↦ true) fun _ ↦ false) :=
    mem_zval_iff.2 ⟨PUnit.unit, rfl, hin.symm⟩
  obtain ⟨i, -, h0⟩ := mem_zval_iff.1 (h hmem)
  simp only [elems_mk] at h0
  have hne : (∅ : ZFSet) ∈ zval (Set.univ : Set Bool)
      (mk PUnit (fun _ ↦ (∅ : PName Bool)) fun _ ↦ true) :=
    mem_zval_iff.2 ⟨PUnit.unit, trivial, (zval_empty _).symm⟩
  rw [← h0] at hne
  exact ZFSet.notMem_empty _ hne

end Forcing.PName
