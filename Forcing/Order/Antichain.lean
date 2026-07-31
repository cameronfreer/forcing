/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Zorn
import Forcing.Order.Filter

/-!
# Forcing antichains

Forcing antichains are pairwise-incompatible sets of conditions. Both the antichain and the
maximal-antichain predicates are direct aliases of mathlib's relation-parametric machinery: at
this pin `IsAntichain r s := s.Pairwise rᶜ` and `IsMaxAntichain` is inclusion-maximality among
antichains, so `IsAntichain Compatible A` says precisely that distinct members of `A` are
incompatible. The substantive content of this file is the predensity characterization of
maximality and the Zorn-style existence results.

## Main definitions

* `Forcing.IsForcingAntichain A`: alias of `IsAntichain Compatible A`.
* `Forcing.IsMaximalAntichain A`: alias of `IsMaxAntichain Compatible A`.

## Main results

* `Forcing.isMaximalAntichain_iff`: a set is a maximal antichain iff it is an antichain and
  predense.
* `Forcing.IsForcingAntichain.exists_isMaximalAntichain`: every antichain extends to a maximal
  one (Zorn).
* `Forcing.IsDense.exists_isMaximalAntichain_subset`: every dense set contains a maximal
  antichain.
* `Forcing.IsPredense.isDense_lowerClosure`: the downward closure of a predense set — in
  particular of a maximal antichain — is dense. Combined with `Forcing.meets_lowerClosure`,
  a filter meets a maximal antichain iff it meets the associated dense set.
-/

namespace Forcing

variable {P : Type*} [Preorder P] {A D : Set P} {p q : P}

/-- A *forcing antichain* is a set of pairwise-incompatible conditions: mathlib's `IsAntichain`
at the `Compatible` relation. -/
abbrev IsForcingAntichain (A : Set P) : Prop :=
  IsAntichain Compatible A

/-- A *maximal antichain* is an antichain not properly contained in any other antichain:
mathlib's `IsMaxAntichain` at the `Compatible` relation. -/
abbrev IsMaximalAntichain (A : Set P) : Prop :=
  IsMaxAntichain Compatible A

theorem isForcingAntichain_iff_pairwise_incompatible :
    IsForcingAntichain A ↔ A.Pairwise Incompatible :=
  .rfl

/-- Adjoining a condition incompatible with every member of an antichain yields an antichain.
(Named without dot notation: `IsForcingAntichain` is an abbrev, so `hA.insert` would resolve to
mathlib's `IsAntichain.insert`, which takes both one-sided hypotheses.) -/
theorem isForcingAntichain_insert (hA : IsForcingAntichain A)
    (h : ∀ a ∈ A, Incompatible p a) : IsForcingAntichain (insert p A) := by
  intro a ha b hb hab
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact h b hb
  · rcases hb with rfl | hb
    · exact fun hc ↦ h a ha hc.symm
    · exact hA ha hb hab

/-- The predensity characterization of maximality: a set is a maximal antichain iff it is an
antichain and predense. -/
theorem isMaximalAntichain_iff : IsMaximalAntichain A ↔ IsForcingAntichain A ∧ IsPredense A := by
  constructor
  · rintro ⟨hA, hmax⟩
    refine ⟨hA, fun p ↦ ?_⟩
    by_contra hp
    push Not at hp
    have hpA : p ∉ A := fun hpA ↦ hp p hpA (.refl p)
    have heq := hmax (isForcingAntichain_insert hA hp) (Set.subset_insert p A)
    exact hpA (heq.symm ▸ Set.mem_insert p A)
  · rintro ⟨hA, hpre⟩
    refine ⟨hA, fun t ht hAt ↦ hAt.antisymm fun b hb ↦ ?_⟩
    obtain ⟨a, haA, hba⟩ := hpre b
    by_cases hab : b = a
    · exact hab ▸ haA
    · exact absurd hba (ht hb (hAt haA) hab)

/-- Every antichain extends to a maximal antichain (Zorn). -/
theorem IsForcingAntichain.exists_isMaximalAntichain (hA : IsForcingAntichain A) :
    ∃ B, A ⊆ B ∧ IsMaximalAntichain B := by
  have H : ∀ c ⊆ {C : Set P | IsForcingAntichain C}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {C : Set P | IsForcingAntichain C}, ∀ s ∈ c, s ⊆ ub := by
    rintro c hcS hchain -
    refine ⟨⋃₀ c, ?_, fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    rintro a ⟨s, hs, has⟩ b ⟨t, ht, hbt⟩ hab
    rcases hchain.total hs ht with hst | hts
    · exact hcS ht (hst has) hbt hab
    · exact hcS hs has (hts hbt) hab
  obtain ⟨B, hAB, hBmax⟩ := zorn_subset_nonempty _ H A hA
  exact ⟨B, hAB, hBmax.1, fun t ht hBt ↦ hBt.antisymm (hBmax.2 ht hBt)⟩

/-- Every dense set contains a maximal antichain: refine the dense set by an antichain maximal
among the antichains inside it, then use density to upgrade to global maximality. -/
theorem IsDense.exists_isMaximalAntichain_subset (hD : IsDense D) :
    ∃ A ⊆ D, IsMaximalAntichain A := by
  have H : ∀ c ⊆ {C : Set P | IsForcingAntichain C ∧ C ⊆ D}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {C : Set P | IsForcingAntichain C ∧ C ⊆ D}, ∀ s ∈ c, s ⊆ ub := by
    rintro c hcS hchain -
    refine ⟨⋃₀ c, ⟨?_, Set.sUnion_subset fun s hs ↦ (hcS hs).2⟩,
      fun s hs ↦ Set.subset_sUnion_of_mem hs⟩
    rintro a ⟨s, hs, has⟩ b ⟨t, ht, hbt⟩ hab
    rcases hchain.total hs ht with hst | hts
    · exact (hcS ht).1 (hst has) hbt hab
    · exact (hcS hs).1 has (hts hbt) hab
  obtain ⟨A, -, hAmax⟩ := zorn_subset_nonempty _ H ∅
    ⟨Set.pairwise_empty _, Set.empty_subset D⟩
  refine ⟨A, hAmax.1.2, isMaximalAntichain_iff.2 ⟨hAmax.1.1, fun p ↦ ?_⟩⟩
  obtain ⟨q, hqD, hqp⟩ := hD p
  by_cases hq : ∃ a ∈ A, Compatible q a
  · obtain ⟨a, haA, r, hrq, hra⟩ := hq
    exact ⟨a, haA, r, hrq.trans hqp, hra⟩
  · push Not at hq
    have hqA : q ∉ A := fun h ↦ hq q h (.refl q)
    have hgrow : insert q A ⊆ A := hAmax.2
      ⟨isForcingAntichain_insert hAmax.1.1 hq, Set.insert_subset hqD hAmax.1.2⟩
      (Set.subset_insert q A)
    exact absurd (hgrow (Set.mem_insert q A)) hqA

/-- The downward closure of a predense set is dense. -/
theorem IsPredense.isDense_lowerClosure (h : IsPredense A) :
    IsDense (↑(lowerClosure A) : Set P) := by
  intro p
  obtain ⟨q, hqA, r, hrp, hrq⟩ := h p
  exact ⟨r, mem_lowerClosure.2 ⟨q, hqA, hrq⟩, hrp⟩

/-- The downward closure of a maximal antichain is dense. Together with
`Forcing.meets_lowerClosure`, a filter meets a maximal antichain iff it meets this dense set. -/
theorem IsMaximalAntichain.isDense_lowerClosure (h : IsMaximalAntichain A) :
    IsDense (↑(lowerClosure A) : Set P) :=
  (isMaximalAntichain_iff.1 h).2.isDense_lowerClosure

/-!
### Sanity examples

In a linear order any two conditions are compatible, so antichains are subsingletons and any
predense singleton is a maximal antichain.
-/

example {p q : ℤ} (h : Incompatible p q) : False :=
  h ⟨min p q, min_le_left p q, min_le_right p q⟩

example : IsMaximalAntichain ({0} : Set ℕ) :=
  isMaximalAntichain_iff.2 ⟨Set.subsingleton_singleton.isAntichain _,
    fun n ↦ ⟨0, rfl, 0, Nat.zero_le n, le_rfl⟩⟩

end Forcing
