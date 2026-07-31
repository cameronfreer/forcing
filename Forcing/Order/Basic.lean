/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.UpperLower.Closure

/-!
# Basic forcing vocabulary

Compatibility of conditions and the density notions used throughout the forcing library, on an
arbitrary preorder.

**Orientation convention: smaller means stronger.** For conditions `p q : P`, `q ≤ p` means `q` is
a stronger condition than `p` (it carries more information). All public statements in this library
use this orientation; density notions are direct aliases of mathlib's coinitiality vocabulary,
which already points the right way.

## Main definitions

* `Forcing.Compatible p q`: the conditions `p` and `q` have a common strengthening.
* `Forcing.Incompatible p q`: they do not.
* `Forcing.IsDense D`: every condition has a strengthening in `D` (alias of `IsCoinitial D`).
* `Forcing.IsDenseBelow D p`: every strengthening of `p` has a further strengthening in `D`
  (alias of `IsCoinitialFor (Set.Iic p) D`).
* `Forcing.IsPredense D`: every condition is compatible with some member of `D`.
* `Forcing.IsDenseOpen D`: `D` is dense and closed under strengthening.

## Main results

* `Forcing.IsDense.isPredense`: dense sets are predense.
* `Forcing.isDense_iff_forall_isDenseBelow`: density is density below every condition.
* `Forcing.IsDenseBelow.mono_condition`, `Forcing.IsDenseBelow.trans`: density below a condition
  is stable under strengthening and transitive.
* `Forcing.IsDense.isDenseOpen_lowerClosure`: the downward closure of a dense set is dense open.
-/

namespace Forcing

variable {P : Type*} [Preorder P] {p q : P} {D E : Set P}

/-- Two conditions are *compatible* if they have a common strengthening. -/
def Compatible (p q : P) : Prop :=
  ∃ r, r ≤ p ∧ r ≤ q

/-- Two conditions are *incompatible* if they have no common strengthening. -/
def Incompatible (p q : P) : Prop :=
  ¬Compatible p q

instance : Std.Refl (Compatible : P → P → Prop) :=
  ⟨fun p ↦ ⟨p, le_rfl, le_rfl⟩⟩

instance : Std.Symm (Compatible : P → P → Prop) :=
  ⟨fun _ _ ⟨r, hp, hq⟩ ↦ ⟨r, hq, hp⟩⟩

@[simp] theorem Compatible.refl (p : P) : Compatible p p :=
  Std.Refl.refl p

theorem Compatible.symm (h : Compatible p q) : Compatible q p :=
  Std.Symm.symm p q h

theorem compatible_comm : Compatible p q ↔ Compatible q p :=
  ⟨.symm, .symm⟩

theorem Compatible.of_le (h : q ≤ p) : Compatible q p :=
  ⟨q, le_rfl, h⟩

theorem Incompatible.symm (h : Incompatible p q) : Incompatible q p :=
  fun hc ↦ h hc.symm

theorem incompatible_comm : Incompatible p q ↔ Incompatible q p :=
  ⟨.symm, .symm⟩

theorem Incompatible.ne (h : Incompatible p q) : p ≠ q := by
  rintro rfl
  exact h (.refl p)

@[simp] theorem not_incompatible_self (p : P) : ¬Incompatible p p :=
  fun h ↦ h (.refl p)

/-- A set of conditions is *dense* if every condition has a strengthening in it. This is
mathlib's `IsCoinitial`, already in forcing orientation. -/
abbrev IsDense (D : Set P) : Prop :=
  IsCoinitial D

/-- A set of conditions is *dense below `p`* if every strengthening of `p` has a further
strengthening in it. This is mathlib's `IsCoinitialFor` from the cone below `p`. -/
abbrev IsDenseBelow (D : Set P) (p : P) : Prop :=
  IsCoinitialFor (Set.Iic p) D

/-- A set of conditions is *predense* if every condition is compatible with one of its
members. -/
def IsPredense (D : Set P) : Prop :=
  ∀ p, ∃ q ∈ D, Compatible p q

/-- A set of conditions is *dense open* if it is dense and closed under strengthening. -/
def IsDenseOpen (D : Set P) : Prop :=
  IsDense D ∧ IsLowerSet D

theorem isDense_iff_isCoinitial : IsDense D ↔ IsCoinitial D :=
  .rfl

theorem isDenseBelow_iff_isCoinitialFor : IsDenseBelow D p ↔ IsCoinitialFor (Set.Iic p) D :=
  .rfl

theorem IsDense.isPredense (h : IsDense D) : IsPredense D := by
  intro p
  obtain ⟨q, hqD, hqp⟩ := h p
  exact ⟨q, hqD, q, hqp, le_rfl⟩

theorem IsDenseOpen.isDense (h : IsDenseOpen D) : IsDense D :=
  h.1

theorem IsDenseOpen.isLowerSet (h : IsDenseOpen D) : IsLowerSet D :=
  h.2

theorem IsDense.isDenseBelow (h : IsDense D) (p : P) : IsDenseBelow D p :=
  fun q _ ↦ h q

theorem isDense_iff_forall_isDenseBelow : IsDense D ↔ ∀ p, IsDenseBelow D p :=
  ⟨fun h p ↦ h.isDenseBelow p, fun h p ↦ h p (Set.mem_Iic.2 le_rfl)⟩

theorem isDenseBelow_Iic (p : P) : IsDenseBelow (Set.Iic p) p :=
  fun q hq ↦ ⟨q, hq, le_rfl⟩

/-- Pullback stability: density below a condition persists to every strengthening of it. Note
that this is a genuinely local statement — `isDense_iff_forall_isDenseBelow` relates global to
local density but is not this theorem. -/
theorem IsDenseBelow.mono_condition (hD : IsDenseBelow D p) (hqp : q ≤ p) : IsDenseBelow D q :=
  fun _ hr ↦ hD (Set.mem_Iic.2 ((Set.mem_Iic.1 hr).trans hqp))

/-- Transitivity: if `D` is dense below `p` and `E` is dense below every member of `D`, then `E`
is dense below `p`. Together with `IsDenseBelow.mono_condition` this is the coverage calculation
in forcing-order form; no sieve or Grothendieck-topology machinery is involved. -/
theorem IsDenseBelow.trans (hD : IsDenseBelow D p) (hE : ∀ q ∈ D, IsDenseBelow E q) :
    IsDenseBelow E p := by
  intro q hq
  obtain ⟨r, hrD, hrq⟩ := hD hq
  obtain ⟨s, hsE, hsr⟩ := hE r hrD (Set.mem_Iic.2 le_rfl)
  exact ⟨s, hsE, hsr.trans hrq⟩

/-- The downward closure of a dense set is dense open. -/
theorem IsDense.isDenseOpen_lowerClosure (h : IsDense D) :
    IsDenseOpen (↑(lowerClosure D) : Set P) := by
  refine ⟨fun p ↦ ?_, (lowerClosure D).lower⟩
  obtain ⟨q, hqD, hqp⟩ := h p
  exact ⟨q, subset_lowerClosure hqD, hqp⟩

/-!
### Sanity examples

Small checks that the orientation and the distinctions between the density notions behave as
intended. In `ℕ` with the usual order, `0` strengthens everything, so `{0}` is dense; `{1}` is
predense (any two naturals are compatible via `0`) but not dense (nothing in it strengthens `0`).
-/

example : IsDense (Set.univ : Set P) := fun p ↦ ⟨p, trivial, le_rfl⟩

example : IsDense ({0} : Set ℕ) := fun n ↦ ⟨0, rfl, Nat.zero_le n⟩

example (p : P) : IsDenseBelow (Set.Iic p) p := isDenseBelow_Iic p

example (hD : IsDense D) (hqp : q ≤ p) : IsDenseBelow D q :=
  (hD.isDenseBelow p).mono_condition hqp

example (h : Compatible p q) : Compatible q p := h.symm

example : IsPredense ({1} : Set ℕ) := fun n ↦ ⟨1, rfl, 0, Nat.zero_le n, Nat.zero_le 1⟩

example : ¬IsDense ({1} : Set ℕ) := by
  intro h
  obtain ⟨q, hq, hq0⟩ := h 0
  simp only [Set.mem_singleton_iff] at hq
  omega

example : IsDenseOpen (Set.Iic 5 : Set ℕ) :=
  ⟨fun n ↦ ⟨0, Nat.zero_le 5, Nat.zero_le n⟩, fun _ _ h hb ↦ h.trans hb⟩

end Forcing
