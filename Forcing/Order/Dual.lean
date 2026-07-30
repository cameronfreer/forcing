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

The Rasiowa–Sikorski wrapper (`Order.idealOfCofinals` in forcing orientation) consumes exactly
these conversions.

## Main definitions

* `Forcing.IsDense.toCofinalDual`: a forcing-dense set as a `Cofinal Pᵒᵈ`.
* `Forcing.pfilterOfDualIdeal`: an ideal on `Pᵒᵈ` as a forcing filter on `P`.
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

/-!
### Round-trip sanity examples

The conversions are definitional: forcing statements are recovered exactly after dualization.
-/

example (hD : IsDense D) : (hD.toCofinalDual.carrier : Set Pᵒᵈ) = ofDual ⁻¹' D := rfl

example (I : Order.Ideal Pᵒᵈ) (x : P) (hx : toDual x ∈ I) : x ∈ pfilterOfDualIdeal I := hx

example (hD : IsDense D) (q : Pᵒᵈ) (hq : q ∈ hD.toCofinalDual) : ofDual q ∈ D := hq

end Forcing
