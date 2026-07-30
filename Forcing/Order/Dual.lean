/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.PFilter
import Forcing.Order.Basic

/-!
# The `OrderDual` bridge

Mathlib's cofinality and ideal machinery (`Order.Cofinal`, `Order.idealOfCofinals`) is
upward-oriented, while this library states everything in forcing orientation (smaller is
stronger). This module is the **only** place the two meet: it packages forcing-dense sets as
`Order.Cofinal` structures on `Pᵒᵈ` and repackages ideals on `Pᵒᵈ` as forcing filters on `P`,
with definitional membership lemmas. Downstream files must never manipulate `OrderDual` directly;
if a new dualization is needed, it belongs here.

In particular, this module wraps `Order.idealOfCofinals` in forcing orientation
(`Forcing.pfilterOfDense`) with base-membership and meeting-witness lemmas, so that the
Rasiowa–Sikorski file downstream is entirely dual-free — in statements *and* proofs.

## Main definitions

* `Forcing.IsDense.toCofinalDual`: a forcing-dense set as a `Cofinal Pᵒᵈ`.
* `Forcing.pfilterOfDualIdeal`: an ideal on `Pᵒᵈ` as a forcing filter on `P`.
* `Forcing.pfilterOfDense`: the forcing filter through `p` meeting a countable family of dense
  sets, built from `Order.idealOfCofinals` on the dual.
-/

namespace Forcing

open OrderDual

variable {P : Type*} [Preorder P] {D : Set P}

theorem isDense_iff_isCofinal_dual : IsDense D ↔ IsCofinal (ofDual ⁻¹' D : Set Pᵒᵈ) :=
  .rfl

/-- Package a forcing-dense set as a mathlib `Cofinal` structure on `Pᵒᵈ`, the form consumed by
`Order.idealOfCofinals`. -/
def IsDense.toCofinalDual (hD : IsDense D) : Order.Cofinal Pᵒᵈ where
  carrier := ofDual ⁻¹' D
  isCofinal := isDense_iff_isCofinal_dual.1 hD

@[simp] theorem IsDense.mem_toCofinalDual (hD : IsDense D) {q : Pᵒᵈ} :
    q ∈ hD.toCofinalDual ↔ ofDual q ∈ D :=
  .rfl

/-- Repackage an ideal on `Pᵒᵈ` as a forcing filter on `P`. -/
def pfilterOfDualIdeal (I : Order.Ideal Pᵒᵈ) : Order.PFilter P :=
  ⟨I⟩

@[simp] theorem mem_pfilterOfDualIdeal {I : Order.Ideal Pᵒᵈ} {x : P} :
    x ∈ pfilterOfDualIdeal I ↔ toDual x ∈ I :=
  .rfl

@[simp] theorem coe_pfilterOfDualIdeal (I : Order.Ideal Pᵒᵈ) :
    (pfilterOfDualIdeal I : Set P) = toDual ⁻¹' (I : Set Pᵒᵈ) :=
  rfl

@[simp] theorem dual_pfilterOfDualIdeal (I : Order.Ideal Pᵒᵈ) : (pfilterOfDualIdeal I).dual = I :=
  rfl

@[simp] theorem pfilterOfDualIdeal_dual (G : Order.PFilter P) : pfilterOfDualIdeal G.dual = G :=
  rfl

section PfilterOfDense

variable {ι : Type*} [Encodable ι] {𝒟 : ι → Set P} {p : P}

/-- The forcing filter through `p` meeting each member of a countable family of dense sets:
`Order.idealOfCofinals` on the dual, in forcing packaging. Downstream Rasiowa–Sikorski
statements and proofs use this wrapper and its lemmas, never `OrderDual` directly. -/
def pfilterOfDense (p : P) (h : ∀ i, IsDense (𝒟 i)) : Order.PFilter P :=
  pfilterOfDualIdeal (Order.idealOfCofinals (toDual p) fun i ↦ (h i).toCofinalDual)

/-- Base membership: `pfilterOfDense` contains the prescribed condition. -/
theorem self_mem_pfilterOfDense (h : ∀ i, IsDense (𝒟 i)) : p ∈ pfilterOfDense p h :=
  Order.mem_idealOfCofinals (toDual p) fun i ↦ (h i).toCofinalDual

/-- Meeting witness: `pfilterOfDense` intersects each dense set of the family. -/
theorem exists_mem_pfilterOfDense (h : ∀ i, IsDense (𝒟 i)) (i : ι) :
    ∃ q ∈ pfilterOfDense p h, q ∈ 𝒟 i := by
  obtain ⟨x, hxD, hxI⟩ := Order.cofinal_meets_idealOfCofinals (toDual p)
    (fun i ↦ (h i).toCofinalDual) i
  exact ⟨ofDual x, hxI, hxD⟩

end PfilterOfDense

/-!
### Round-trip sanity examples

The conversions are definitional: forcing statements are recovered exactly after dualization.
-/

example (hD : IsDense D) : (hD.toCofinalDual.carrier : Set Pᵒᵈ) = ofDual ⁻¹' D := rfl

example (I : Order.Ideal Pᵒᵈ) (x : P) (hx : toDual x ∈ I) : x ∈ pfilterOfDualIdeal I := hx

example (hD : IsDense D) (q : Pᵒᵈ) (hq : q ∈ hD.toCofinalDual) : ofDual q ∈ D := hq

end Forcing
