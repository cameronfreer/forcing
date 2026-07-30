/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Set.Countable
import Forcing.Order.Dual
import Forcing.Order.Filter

/-!
# The Rasiowa–Sikorski lemma in forcing orientation

Through any condition there is a filter meeting every member of a countable family of dense sets.
The construction is mathlib's `Order.idealOfCofinals`, reached through the forcing-oriented
wrapper `Forcing.pfilterOfDense`; both the statements and the proofs here are free of
`OrderDual`, `Order.Cofinal`, and `Order.Ideal`.

Mathlib's construction is indexed by `[Encodable ι]`; the public statements take the weaker
`[Countable ι]` (respectively `Set.Countable`) and bridge noncomputably inside the proof.

## Main results

* `Forcing.exists_pfilter_genericFor`: the indexed-family form.
* `Forcing.exists_pfilter_genericFor'`: the set-of-sets form, concluding `GenericFor`.
-/

namespace Forcing

open Order

variable {P : Type*} [Preorder P]

/-- **The Rasiowa–Sikorski lemma**, indexed-family form: through any condition `p` there is a
filter containing `p` and meeting every member of a countable family of dense sets. -/
theorem exists_pfilter_genericFor (p : P) {ι : Type*} [Countable ι] (𝒟 : ι → Set P)
    (h : ∀ i, IsDense (𝒟 i)) : ∃ G : PFilter P, p ∈ G ∧ ∀ i, Meets G (𝒟 i) := by
  obtain ⟨enc⟩ := nonempty_encodable ι
  letI := enc
  exact ⟨pfilterOfDense p h, self_mem_pfilterOfDense h,
    fun i ↦ meets_iff_exists.2 (exists_mem_pfilterOfDense h i)⟩

/-- **The Rasiowa–Sikorski lemma**, set-of-sets form: through any condition `p` there is a filter
containing `p` and generic for a countable family of dense sets. -/
theorem exists_pfilter_genericFor' (p : P) {𝒟 : Set (Set P)} (h𝒟 : 𝒟.Countable)
    (h : ∀ D ∈ 𝒟, IsDense D) : ∃ G : PFilter P, p ∈ G ∧ GenericFor 𝒟 G := by
  haveI := h𝒟.to_subtype
  obtain ⟨G, hpG, hG⟩ := exists_pfilter_genericFor p (fun D : 𝒟 ↦ (D : Set P)) fun D ↦ h D D.2
  exact ⟨G, hpG, fun D hD ↦ hG ⟨D, hD⟩⟩

/-!
### Sanity example

In `ℤ` (no strongest condition), a filter through `0` meeting every `Set.Iic (-n)`: genericity
produces filters reaching arbitrarily strong conditions.
-/

example : ∃ G : PFilter ℤ, (0 : ℤ) ∈ G ∧ ∀ n : ℕ, Meets G (Set.Iic (-(n : ℤ))) :=
  exists_pfilter_genericFor 0 _ fun n m ↦
    ⟨min (-(n : ℤ)) m, Set.mem_Iic.2 (min_le_left _ _), min_le_right _ _⟩

end Forcing
