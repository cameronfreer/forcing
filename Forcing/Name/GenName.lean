/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.Check

/-!
# The generic's name over an explicit condition code

The generic filter can name itself once conditions are coded as sets. The coding is an
explicit, bundled parameter (`ConditionCode`) — not a typeclass, because different material
grounds will code conditions differently and nothing at this layer fixes a canonical one. This
is *external material coding*: internal presentation, with membership and absoluteness facts
relative to a material ground, is a later layer.

The exact prices, continuing the factoring of `Forcing/Name/Check.lean`:

* `ConditionCode` needs no order;
* `genName` needs only `[Top P]`;
* its valuation **faithfully codes any condition set containing `⊤`**
  (`mem_zval_genName_iff`, `eq_of_zval_genName_eq`);
* forcing filters obtain that condition from `[Preorder P] [OrderTop P]` via
  `Order.PFilter.top_mem`, so the filter statements are corollaries.

Wording discipline: the valuation of the generic's name is a *faithful material code* of the
filter — a set from which the filter is recoverable — never the Lean object itself.

## Main definitions

* `Forcing.ConditionCode`: an injective coding of conditions as sets.
* `Forcing.PName.genName`: the generic's name.

## Main results

* `Forcing.PName.mem_zval_genName_iff`: the membership description of the code.
* `Forcing.PName.eq_of_zval_genName_eq`: recovery — equal codes, equal condition sets.
* `Forcing.PName.eq_of_zval_genName_eq_pfilter`: distinct filters have distinct codes.
-/

universe u

namespace Forcing

/-- An explicit coding of conditions as sets: a representation together with injectivity of its
extensional image. A bundled parameter, not a typeclass — different material grounds code
conditions differently, and nothing at this layer fixes a canonical coding. Needs no order. -/
structure ConditionCode (P : Type u) where
  /-- The set coding a condition. -/
  repr : P → PSet.{u}
  /-- Distinct conditions have extensionally distinct codes. -/
  injective_mk : Function.Injective fun p ↦ ZFSet.mk (repr p)

namespace PName

variable {P : Type u} {κ : ConditionCode P}

/-- The generic's name: one branch per condition, each tagged with itself and carrying the
condition's code, checked. Needs only `[Top P]`. -/
def genName [Top P] (κ : ConditionCode P) : PName P :=
  .mk P (fun p ↦ check (κ.repr p)) id

/-- **The membership description**: along any condition set containing `⊤`, the generic's name
values to the set of codes of members — a faithful material code of the condition set. -/
theorem mem_zval_genName_iff [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) {y : ZFSet.{u}} :
    y ∈ zval S (genName κ) ↔ ∃ p ∈ S, y = ZFSet.mk (κ.repr p) :=
  mem_zval_iff.trans
    ⟨fun ⟨p, hp, hy⟩ ↦ ⟨p, hp, hy.trans (zval_check hS _)⟩,
      fun ⟨p, hp, hy⟩ ↦ ⟨p, hp, hy.trans (zval_check hS _).symm⟩⟩

/-- **Recovery**: condition sets containing `⊤` with equal codes are equal — the code is
faithful. Unconditional once a `ConditionCode` is supplied: the injectivity lives inside the
bundle. -/
theorem eq_of_zval_genName_eq [Top P] {S T : Set P} (hS : (⊤ : P) ∈ S) (hT : (⊤ : P) ∈ T)
    (h : zval S (genName κ) = zval T (genName κ)) : S = T := by
  have key : ∀ {S T : Set P}, (⊤ : P) ∈ S → (⊤ : P) ∈ T →
      zval S (genName κ) = zval T (genName κ) → S ⊆ T := by
    intro S T hS hT h p hp
    have hmem : ZFSet.mk (κ.repr p) ∈ zval T (genName κ) := by
      rw [← h]
      exact (mem_zval_genName_iff hS).2 ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hqe⟩ := (mem_zval_genName_iff hT).1 hmem
    rwa [κ.injective_mk hqe]
  exact Set.Subset.antisymm (key hS hT h) (key hT hS h.symm)

/-- The filter corollary of the membership description, via `Order.PFilter.top_mem`. -/
theorem mem_zval_genName_iff_pfilter [Preorder P] [OrderTop P] (G : Order.PFilter P)
    {y : ZFSet.{u}} :
    y ∈ zval (G : Set P) (genName κ) ↔ ∃ p ∈ G, y = ZFSet.mk (κ.repr p) :=
  mem_zval_genName_iff G.top_mem

/-- **Distinct filters have distinct codes**: the filter corollary of recovery. The valuation
of the generic's name is a faithful material code of the filter. -/
theorem eq_of_zval_genName_eq_pfilter [Preorder P] [OrderTop P] {G G' : Order.PFilter P}
    (h : zval (G : Set P) (genName κ) = zval (G' : Set P) (genName κ)) : G = G' := by
  ext q
  exact Set.ext_iff.1 (eq_of_zval_genName_eq G.top_mem G'.top_mem h) q

end PName

end Forcing
