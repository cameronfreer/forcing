/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.ForcingPresentation
import Forcing.Name.ValuationImage

/-!
# The ground's internal name family

The internal name family with its **smallness evidence kept**: `valuationImage` is an
extensional `Set ZFSet` and remains the external API, while the material construction of the
extension needs an explicit small enumeration — so the enumeration is the structure, and the
family of names is its derived range. Discarding the indexing and later trying to recover
smallness is exactly the design this file exists to prevent.

Two layers, so the core inherits no top element merely because the current external
implementations of `check` and `genName` use one:

* **`InternalNamePresentation`** — the enumeration (`Code`, `code`, `decode`) plus
  **syntactic** subname closure. No order, no top. The `code` side records *internality*
  (each internal name-object is an element of the carrier); the coherence between the
  internal code and the decoded external name is an absoluteness obligation of a later
  layer, deliberately not yet a field.
* **`HasCanonicalNames`** — a separate `Prop`-bundle asserting **semantic representatives**
  of check names (for carrier elements) and of the generic name — for the presentation's own
  `ConditionCode`, tying the demand to the internal presentation rather than to an arbitrary
  second coding. Prices are the established ones: `[Top P]` with `⊤ ∈ S` hypotheses, and
  `OrderTop` entering only through the filter corollaries.

Semantic representation is the boundary throughout: membership demands are stated up to
valuation (`∃ τ ∈ names, ∀ S, ⊤ ∈ S → zval S τ = x`), **never** as literal membership of
`checkZF x` or `genName κ` — representation-insensitivity where it matters, while subname
closure remains syntactic on decoded names.

## Main definitions

* `Forcing.InternalNamePresentation`: the small enumeration with syntactic subname closure.
* `Forcing.InternalNamePresentation.names`: the derived name family.
* `Forcing.InternalNamePresentation.HasCanonicalNames`: semantic representatives of the
  checked carrier and of the generic name.

## Main results

* `Forcing.InternalNamePresentation.elems_mem_names`: the family is closed under subnames.
* `Forcing.InternalNamePresentation.HasCanonicalNames.mem_valuationImage_of_mem`,
  `Forcing.InternalNamePresentation.HasCanonicalNames.zval_genName_mem_valuationImage`:
  the checked-ground and generic-name membership facts of the external layer, with their
  explicit `∈ N` hypotheses discharged semantically.
-/

universe u

namespace Forcing

/-- The ground's internal name family, as a small enumeration: internal name-objects in the
carrier (`code`, `code_mem`), their decoded external names (`decode`), and **syntactic**
subname closure. No order, no top. The family itself is the derived `names`; the enumeration
is kept so the material extension can be built as a genuine `ZFSet` without recovering
smallness after the fact. -/
structure InternalNamePresentation (M : MaterialCarrier.{u}) (P : Type u) where
  /-- The index type of the enumeration. -/
  Code : Type u
  /-- The internal name-object of a code: the material side. -/
  code : Code → ZFSet.{u}
  /-- Internality: each internal name-object is an element of the carrier. -/
  code_mem : ∀ i, code i ∈ M
  /-- The decoded external name of a code. -/
  decode : Code → PName P
  /-- Syntactic subname closure: every immediate subname of a decoded name is decoded. -/
  subname_closed : ∀ (i : Code) (j : (decode i).Idx), ∃ k, decode k = (decode i).elems j

namespace InternalNamePresentation

open PName

variable {M : MaterialCarrier.{u}} {P : Type u}
variable (N : InternalNamePresentation M P)

/-- The internal name family: the range of the enumeration. -/
def names : Set (PName P) :=
  Set.range N.decode

theorem decode_mem_names (i : N.Code) : N.decode i ∈ N.names :=
  ⟨i, rfl⟩

/-- The family is closed under immediate subnames — the set-level form of the syntactic
closure field, and the shape the material extension's transitivity proof consumes. -/
theorem elems_mem_names {τ : PName P} (hτ : τ ∈ N.names) (j : τ.Idx) :
    τ.elems j ∈ N.names := by
  obtain ⟨i, rfl⟩ := hτ
  exact N.subname_closed i j

section Canonical

variable [Preorder P] [Top P] {S : Set P}

/-- **Canonical-name availability**: the family contains semantic representatives of the
check name of every carrier element, and of the generic name for the presentation's own
condition code. Semantic, not literal: nothing here mentions `checkZF` or `genName`
membership, only agreement of valuations along every condition set containing `⊤`. A separate
bundle so the core enumeration inherits no top. -/
structure HasCanonicalNames (Pres : InternalForcingPresentation M P)
    (N : InternalNamePresentation M P) : Prop where
  /-- Every carrier element has a semantic check-name representative in the family. -/
  check_represented : ∀ x : ZFSet.{u}, x ∈ M →
    ∃ τ ∈ N.names, ∀ S : Set P, (⊤ : P) ∈ S → zval S τ = x
  /-- The generic name for the presentation's condition code has a semantic representative in
  the family. -/
  genName_represented :
    ∃ τ ∈ N.names, ∀ S : Set P, (⊤ : P) ∈ S →
      zval S τ = zval S (genName Pres.conditionCode)

namespace HasCanonicalNames

variable {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}

/-- **The checked-ground membership, proved**: every carrier element lands in the valuation
image of the internal family, along any condition set containing `⊤`. The external layer's
explicit `checkZF x ∈ N` hypothesis is discharged by the semantic representative. -/
theorem mem_valuationImage_of_mem (h : HasCanonicalNames Pres N) {x : ZFSet.{u}}
    (hx : x ∈ M) (hS : (⊤ : P) ∈ S) :
    x ∈ valuationImage N.names S := by
  obtain ⟨τ, hτ, hval⟩ := h.check_represented x hx
  exact mem_valuationImage_of_mem_of_zval_eq hτ (hval S hS)

/-- **The generic-name membership, proved**: the generic's code lands in the valuation image
of the internal family, along any condition set containing `⊤`. The external layer's explicit
`genName κ ∈ N` hypothesis is discharged by the semantic representative. -/
theorem zval_genName_mem_valuationImage (h : HasCanonicalNames Pres N)
    (hS : (⊤ : P) ∈ S) :
    zval S (genName Pres.conditionCode) ∈ valuationImage N.names S := by
  obtain ⟨τ, hτ, hval⟩ := h.genName_represented
  exact mem_valuationImage_of_mem_of_zval_eq hτ (hval S hS)

end HasCanonicalNames

end Canonical

/-- The filter corollary of the checked-ground membership: the order and the filter laws
supply `⊤ ∈ G` via `Order.PFilter.top_mem`, and `OrderTop` supplies the `Top` that the
canonical bundle prices at `[Top P]`. -/
theorem HasCanonicalNames.mem_valuationImage_of_mem_pfilter [Preorder P] [OrderTop P]
    {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}
    (h : HasCanonicalNames Pres N) {x : ZFSet.{u}} (hx : x ∈ M) (G : Order.PFilter P) :
    x ∈ valuationImage N.names (G : Set P) :=
  h.mem_valuationImage_of_mem hx G.top_mem

end InternalNamePresentation

end Forcing
