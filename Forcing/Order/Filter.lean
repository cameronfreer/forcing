/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.PFilter
import Forcing.Order.Basic

/-!
# Forcing filters and family-relative genericity

Mathlib's `Order.PFilter` is exactly the forcing-filter notion under the smaller-is-stronger
convention: nonempty, closed under weakening (`Order.PFilter.mem_of_le`), and any two members have
a common strengthening inside the filter (`Order.PFilter.directed`). This file adds the forcing
vocabulary on top: what it means for a filter to *meet* a set of conditions, and for a filter to
be *generic for* a supplied family of sets.

Genericity here is family-relative and purely order-theoretic. Genericity over a ground model
(`GenericOver`) is deliberately not defined in the kernel; it arrives with the model layer.

## Main definitions

* `Forcing.Meets G D`: the filter `G` intersects the set of conditions `D`.
* `Forcing.GenericFor 𝒟 G`: `G` meets every member of the family `𝒟`.

## Main results

* `Forcing.exists_mem_le_le`: any two members of a filter have a common strengthening in the
  filter; hence `Forcing.compatible_of_mem` — members of a filter are pairwise compatible.
* `Forcing.meets_lowerClosure`: a filter meets a set iff it meets its downward closure.
* `Forcing.Meets.exists_mem_le`: a filter meeting a downward-closed set contains a member of it
  strengthening any given member of the filter (the localization lemma).
* `Forcing.genericFor_principal_bot`: with a weakest condition `⊥`, the principal filter at `⊥`
  is generic for every family of dense sets — genericity is only interesting above atomless-like
  behavior, which is why the kernel never assumes `OrderBot`.
-/

namespace Forcing

open Order

variable {P : Type*} [Preorder P] {G : PFilter P} {D D' : Set P} {𝒟 𝒟' : Set (Set P)} {p q : P}

/-- A filter *meets* a set of conditions if they intersect. -/
def Meets (G : PFilter P) (D : Set P) : Prop :=
  ((G : Set P) ∩ D).Nonempty

/-- A filter is *generic for* a family of sets of conditions if it meets every member of the
family. -/
def GenericFor (𝒟 : Set (Set P)) (G : PFilter P) : Prop :=
  ∀ D ∈ 𝒟, Meets G D

theorem meets_iff_exists : Meets G D ↔ ∃ p ∈ G, p ∈ D :=
  .rfl

theorem Meets.exists_mem (h : Meets G D) : ∃ p ∈ G, p ∈ D :=
  h

/-- Any two members of a filter have a common strengthening inside the filter. -/
theorem exists_mem_le_le (hp : p ∈ G) (hq : q ∈ G) : ∃ r ∈ G, r ≤ p ∧ r ≤ q := by
  obtain ⟨r, hrG, hrp, hrq⟩ := G.directed p hp q hq
  exact ⟨r, hrG, hrp, hrq⟩

/-- Members of a filter are pairwise compatible. -/
theorem compatible_of_mem (hp : p ∈ G) (hq : q ∈ G) : Compatible p q :=
  let ⟨r, _, hrp, hrq⟩ := exists_mem_le_le hp hq
  ⟨r, hrp, hrq⟩

theorem Meets.mono (h : Meets G D) (hDD' : D ⊆ D') : Meets G D' :=
  let ⟨p, hpG, hpD⟩ := h
  ⟨p, hpG, hDD' hpD⟩

theorem Meets.mono_filter {G' : PFilter P} (h : Meets G D) (hGG' : G ≤ G') : Meets G' D :=
  let ⟨p, hpG, hpD⟩ := h
  ⟨p, hGG' hpG, hpD⟩

/-- Genericity is antitone in the family: generic for a family, generic for any subfamily. -/
theorem GenericFor.anti (h : GenericFor 𝒟 G) (h𝒟 : 𝒟' ⊆ 𝒟) : GenericFor 𝒟' G :=
  fun D hD ↦ h D (h𝒟 hD)

/-- A filter meets a set iff it meets its downward closure. -/
theorem meets_lowerClosure : Meets G (↑(lowerClosure D) : Set P) ↔ Meets G D := by
  constructor
  · rintro ⟨g, hgG, hgLC⟩
    obtain ⟨d, hdD, hgd⟩ := mem_lowerClosure.1 hgLC
    exact ⟨d, PFilter.mem_of_le hgd hgG, hdD⟩
  · exact fun h ↦ h.mono subset_lowerClosure

/-- Localization: a filter meeting a downward-closed set contains a member of that set
strengthening any given member of the filter. -/
theorem Meets.exists_mem_le (h : Meets G D) (hD : IsLowerSet D) (hp : p ∈ G) :
    ∃ q ∈ G, q ∈ D ∧ q ≤ p := by
  obtain ⟨g, hgG, hgD⟩ := h
  obtain ⟨r, hrG, hrg, hrp⟩ := exists_mem_le_le hgG hp
  exact ⟨r, hrG, hD hrg hgD, hrp⟩

@[simp] theorem meets_principal {x : P} : Meets (PFilter.principal x) D ↔ ∃ q ∈ D, x ≤ q := by
  constructor
  · rintro ⟨q, hqx, hqD⟩
    exact ⟨q, hqD, PFilter.mem_principal.1 hqx⟩
  · rintro ⟨q, hqD, hxq⟩
    exact ⟨q, PFilter.mem_principal.2 hxq, hqD⟩

/-- With a weakest condition, the principal filter at `⊥` is generic for every family of dense
sets: nontrivial genericity requires leaving pointed trivialities behind. -/
theorem genericFor_principal_bot [OrderBot P] (h : ∀ D ∈ 𝒟, IsDense D) :
    GenericFor 𝒟 (PFilter.principal (⊥ : P)) := by
  intro D hD
  obtain ⟨q, hqD, -⟩ := h D hD ⊥
  exact meets_principal.2 ⟨q, hqD, bot_le⟩

/-!
### Sanity examples

`ℤ` has no weakest condition, and the strictly negative integers are dense; the principal filter
at `0` fails to meet them, so principal filters are not generic in general. Contrast with
`genericFor_principal_bot`.
-/

example : IsDense (Set.Iio (0 : ℤ)) := fun n ↦
  ⟨min n 0 - 1, by simp only [Set.mem_Iio]; omega, by omega⟩

example : ¬Meets (PFilter.principal (0 : ℤ)) (Set.Iio 0) := by
  rintro ⟨q, hq0, hqIio⟩
  have : (0 : ℤ) ≤ q := PFilter.mem_principal.1 hq0
  exact absurd hqIio (by simpa using this)

example (hp : p ∈ G) (hq : q ∈ G) : Compatible p q := compatible_of_mem hp hq

end Forcing
