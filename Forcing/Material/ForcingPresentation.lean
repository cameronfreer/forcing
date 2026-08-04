/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Carrier
import Forcing.Name.GenName

/-!
# The internal forcing presentation

A no-junk coded copy of the forcing notion inside a material carrier. A `ConditionCode` alone
codes conditions externally and says nothing about the codes or the order being
ground-visible; an `InternalForcingPresentation` supplies exactly that: an internal condition
set in the carrier containing every code (`code_mem`) and **nothing else**
(`code_surjective` — no phantom conditions for internal quantification to range over), and an
internal order code whose membership law pins both the Kuratowski representation and the
smaller-is-stronger orientation on the nose (`order_iff`).

The structure stores mathematical obligations, not an arbitrary inverse function: the no-junk
equivalence with `{x : ZFSet // x ∈ conditionSet}` is *derived* (`conditionEquiv`, via
`Equiv.ofBijective`), with injectivity from the bundled `ConditionCode.injective_mk` and
surjectivity exactly the no-phantom-conditions field — so the correspondence is tied to the
supplied code by construction and cannot certify a second, unrelated coding. Membership of
individual condition codes in the carrier is likewise derived from transitivity
(`code_mem_carrier`), not assumed.

Internal subsets are handled by the external condition `d ∈ M ∧ d ⊆ conditionSet` at use
sites, with externalization **defined, not stored** (`externalizeSubset`, membership
`Iff.rfl`). Constructing the resulting visibility context from the range of externalization
is deliberately left to the Cohen material adapter — this file is independent of the observer
layer and imports nothing from `Forcing/Model/`.

No additional order-code no-junk field: the exact `order_iff` over coded conditions is what
restricted internal quantification consumes; more is added only if an absoluteness theorem
needs it.

## Main definitions

* `Forcing.InternalForcingPresentation`: the no-junk internal presentation.
* `Forcing.InternalForcingPresentation.conditionEquiv`: the derived no-junk equivalence.
* `Forcing.InternalForcingPresentation.externalizeSubset`: externalization of an internal
  subset, derived not stored.

## Main results

* `Forcing.InternalForcingPresentation.code_mem_carrier`: individual codes lie in the
  carrier, by transitivity.
* `Forcing.InternalForcingPresentation.mem_externalizeSubset`: the externalization membership
  law, definitionally.
-/

universe u

namespace Forcing

/-- A no-junk coded copy of the forcing notion `P` inside the material carrier `M`: a
condition code, an internal condition set containing every code and nothing else, and an
internal order code with the exact orientation-pinned membership law. The no-junk equivalence
is derived, not stored. -/
structure InternalForcingPresentation (M : MaterialCarrier.{u}) (P : Type u) [Preorder P] where
  /-- The underlying external coding of conditions. -/
  conditionCode : ConditionCode P
  /-- The internal condition set: an element of the carrier. -/
  conditionSet : M
  /-- Every condition's code belongs to the internal condition set. -/
  code_mem : ∀ p, ZFSet.mk (conditionCode.repr p) ∈ (conditionSet : ZFSet.{u})
  /-- No junk: every element of the internal condition set codes an external condition, so
  internal quantification ranges over no phantom conditions. -/
  code_surjective : ∀ x ∈ (conditionSet : ZFSet.{u}), ∃ p, x = ZFSet.mk (conditionCode.repr p)
  /-- The internal order code: an element of the carrier. -/
  orderCode : M
  /-- The exact order law, pinning both the Kuratowski-pair representation and the
  smaller-is-stronger orientation. -/
  order_iff : ∀ p q : P,
    ZFSet.pair (ZFSet.mk (conditionCode.repr q)) (ZFSet.mk (conditionCode.repr p)) ∈
      (orderCode : ZFSet.{u}) ↔ q ≤ p

namespace InternalForcingPresentation

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- Individual condition codes belong to the carrier: derived from transitivity, not
assumed. -/
theorem code_mem_carrier (p : P) : ZFSet.mk (Pres.conditionCode.repr p) ∈ M :=
  M.mem_trans (Pres.code_mem p) Pres.conditionSet.property

/-- **The no-junk equivalence**, derived: external conditions correspond exactly to the
elements of the internal condition set. Injectivity is the bundled
`ConditionCode.injective_mk`; surjectivity is precisely the no-phantom-conditions field — so
the equivalence is tied to the supplied code by construction. -/
noncomputable def conditionEquiv : P ≃ {x : ZFSet.{u} // x ∈ (Pres.conditionSet : ZFSet.{u})} :=
  Equiv.ofBijective (fun p ↦ ⟨ZFSet.mk (Pres.conditionCode.repr p), Pres.code_mem p⟩)
    ⟨fun _ _ h ↦ Pres.conditionCode.injective_mk (congrArg Subtype.val h),
      fun x ↦ (Pres.code_surjective x.1 x.2).imp fun _ hp ↦ Subtype.ext hp.symm⟩

/-- The equivalence is the coding, on the nose. -/
@[simp] theorem conditionEquiv_apply (p : P) :
    (Pres.conditionEquiv p : ZFSet.{u}) = ZFSet.mk (Pres.conditionCode.repr p) :=
  rfl

/-- Externalization of an internal subset of the condition set: derived, not stored. Use
sites supply the external condition `d ∈ M ∧ d ⊆ conditionSet`; the visibility context
arising as the range of this map is the business of the Cohen material adapter, not of this
file. -/
def externalizeSubset (d : ZFSet.{u}) : Set P :=
  {p | ZFSet.mk (Pres.conditionCode.repr p) ∈ d}

/-- The externalization membership law, definitionally. -/
@[simp] theorem mem_externalizeSubset {d : ZFSet.{u}} {p : P} :
    p ∈ Pres.externalizeSubset d ↔ ZFSet.mk (Pres.conditionCode.repr p) ∈ d :=
  Iff.rfl

/-- An **internal subset**: an element of the carrier all of whose members lie in the
internal condition set. The generic input to externalization — internal test codes, derived
visibility, and countability arguments all consume it. -/
def InternalSubset :=
  {d : M // (d : ZFSet.{u}).toSet ⊆ (Pres.conditionSet : ZFSet.{u}).toSet}

variable {Pres}

/-- Externalization of an internal subset: the derived map, specialized. -/
def InternalSubset.externalize (d : Pres.InternalSubset) : Set P :=
  Pres.externalizeSubset (d.1 : ZFSet.{u})

@[simp] theorem InternalSubset.mem_externalize {d : Pres.InternalSubset} {p : P} :
    p ∈ d.externalize ↔ ZFSet.mk (Pres.conditionCode.repr p) ∈ (d.1 : ZFSet.{u}) :=
  Iff.rfl

/-!
### Sanity examples

The order law transports through the equivalence with no residue; externalizing the whole
internal condition set recovers every external condition (no-junk in action); and the order
code's law is exactly the typed order on coded conditions.
-/

example {p q : P} :
    ZFSet.pair (Pres.conditionEquiv q : ZFSet.{u}) (Pres.conditionEquiv p : ZFSet.{u}) ∈
      (Pres.orderCode : ZFSet.{u}) ↔ q ≤ p :=
  Pres.order_iff p q

example : Pres.externalizeSubset (Pres.conditionSet : ZFSet.{u}) = Set.univ :=
  Set.eq_univ_of_forall Pres.code_mem

end InternalForcingPresentation

end Forcing
