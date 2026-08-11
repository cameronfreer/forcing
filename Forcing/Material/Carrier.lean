/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Data.SetLike.Basic

/-!
# The material carrier

A `MaterialCarrier` is a transitive `ZFSet` with a thin membership interface — deliberately
**not** a ground model. No satisfaction, no countability, no closure properties, no visibility,
no name family: a transitive set (including `∅`) is never called a ground, and the name
`MaterialGround` is reserved for the later model-bearing interface.

The public boundary is membership, through `SetLike`: membership `x ∈ M`, the coercion to
`Set ZFSet`, the element subtype, and membership-level extensionality (`MaterialCarrier.ext`).
The `carrier` projection is for proofs; `mem_carrier` is the one simp bridge, and there is
deliberately no second coercion `MaterialCarrier → ZFSet` and no subset order on carriers.

Everything downstream in the material layer — the internal forcing presentation, the internal
name family, the material extension — is *relative to* a carrier. Visibility and internal
names are later **derived** from one material presentation; nothing of that kind is stored
here.

## Main definitions

* `Forcing.MaterialCarrier`: a transitive `ZFSet`, with `SetLike` membership.

## Main results

* `Forcing.MaterialCarrier.ext`: membership-level extensionality.
* `Forcing.MaterialCarrier.mem_trans`: an element of an element is an element.
* `Forcing.MaterialCarrier.exists_minimal`: Foundation, unconditionally — carriers are
  transitive collections of ambient well-founded sets.
-/

universe u

namespace Forcing

/-- A transitive material set with a membership interface. Deliberately not a ground model —
no satisfaction, no countability, no closure, no visibility; the name `MaterialGround` is
reserved for the later model-bearing interface. -/
structure MaterialCarrier : Type (u + 1) where
  /-- The underlying transitive set. Use public membership `x ∈ M`, not this projection;
  `mem_carrier` is the bridge. -/
  carrier : ZFSet.{u}
  /-- The carrier is transitive. -/
  isTransitive : carrier.IsTransitive

namespace MaterialCarrier

variable {M N : MaterialCarrier.{u}} {x y z : ZFSet.{u}}

/-- Membership is the public interface: `SetLike` supplies `x ∈ M`, the coercion to
`Set ZFSet`, and the element subtype. Injectivity is proved directly from equality of the
underlying carriers — the public `ext` below is its consequence, not its source. -/
instance : SetLike MaterialCarrier.{u} ZFSet.{u} where
  coe M := {x | x ∈ M.carrier}
  coe_injective := by
    rintro ⟨s, _⟩ ⟨t, _⟩ h
    congr 1
    exact ZFSet.ext fun z ↦ Set.ext_iff.1 h z

/-- The one bridge between the raw projection and public membership. -/
@[simp] theorem mem_carrier : x ∈ M.carrier ↔ x ∈ M :=
  Iff.rfl

/-- Membership-level extensionality: carriers with the same members are equal. -/
@[ext] theorem ext (h : ∀ x, x ∈ M ↔ x ∈ N) : M = N :=
  SetLike.ext h

/-- Transitivity in public membership notation: an element of an element is an element. -/
theorem mem_trans (hxy : x ∈ y) (hyM : y ∈ M) : x ∈ M :=
  M.isTransitive.mem_trans hxy hyM

/-- **Foundation is free for material carriers.** A carrier is a transitive collection of
ambient `ZFSet`s, and ambient membership is well-founded, so every inhabited member has an
`∈`-minimal element — with transitivity placing that element, and everything relevant below
it, back in the carrier. Dependency mining: the recursion layer must **not** be charged
Foundation over transitive `ZFSet` carriers. -/
theorem exists_minimal (M : MaterialCarrier.{u}) {a x : ZFSet.{u}} (ha : a ∈ M)
    (hx : x ∈ a) :
    ∃ y, y ∈ a ∧ y ∈ M ∧ ∀ z, z ∈ y → z ∉ a := by
  obtain ⟨y, hya, hmin⟩ := ZFSet.mem_wf.has_min {w : ZFSet.{u} | w ∈ a} ⟨x, hx⟩
  exact ⟨y, hya, M.mem_trans hya ha, fun z hzy hza ↦ hmin z hza hzy⟩

/-!
### Sanity examples

The degenerate carrier exists — as an example, deliberately not a public definition: it
certifies minimality of the interface without advertising an empty "ground". Its membership is
empty in public notation, and `mem_trans` composes in public notation alone.
-/

example : MaterialCarrier.{u} :=
  ⟨∅, ZFSet.isTransitive_empty⟩

example (h : x ∈ (⟨∅, ZFSet.isTransitive_empty⟩ : MaterialCarrier.{u})) : False :=
  ZFSet.notMem_empty x h

example (hx : x ∈ y) (hy : y ∈ z) (hz : z ∈ M) : x ∈ M :=
  M.mem_trans hx (M.mem_trans hy hz)

end MaterialCarrier

end Forcing
