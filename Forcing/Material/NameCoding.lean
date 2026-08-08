/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Names

/-!
# Internal name coding and subname absoluteness

The names layer of the internal-coding work: relating the material codes of an
`InternalNamePresentation` to the external typed names they decode to. The content is a
single **representation law** — a name's code is the coded set of its `⟨condition, subname⟩`
branches — together with **faithfulness**: the code determines the name. Absoluteness of the
immediate-subname relation is then *derived* (`subname_absolute`), not assumed.

Discipline, per the coding design:

* the condition coding is **reused** from `InternalForcingPresentation` — there is no second
  condition coding here, and no second synchronized presentation;
* the syntax stays **intensional**: the laws relate codes to names by representation, never
  by literal equality with a particular external `PName` tree;
* there is **no master set of all name codes**. Names form an internal definable class; each
  code lies in the carrier (`pair_mem_carrier` derives that for branches, from transitivity),
  but no `nameCodeSet ∈ M` is demanded;
* nothing is stored on `MaterialGround`: this is a proposition *relative to* a presentation.

**Axiom price: none.** This layer is a hypothesis bundle, not a construction — the theory
ledger opens when a construction needs it, and each such theorem will cite
`MaterialGround.realize_of_mem` against the sentence it consumes.

## Main definitions

* `Forcing.InternalNameCoding`: the representation and faithfulness laws.

## Main results

* `Forcing.InternalNameCoding.subname_absolute`: the immediate-subname relation is absolute.
* `Forcing.InternalNameCoding.pair_mem_carrier`: coded branches lie in the carrier.
-/

universe u

namespace Forcing

open PName

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]

/-- **The names-layer coding laws**, relative to a condition presentation and a name
presentation: each name code is the coded set of its `⟨condition, subname⟩` branches, and the
code determines the name. A `Prop` — a demand on the presentations, not data, and not a
capability stored on a ground. -/
structure InternalNameCoding (Pres : InternalForcingPresentation M P)
    (N : InternalNamePresentation M P) : Prop where
  /-- **Representation**: the members of a name's code are exactly the coded branches — the
  condition code paired with the code of the corresponding subname. -/
  branch_mem_code_iff : ∀ (i : N.Code) (y : ZFSet.{u}),
    y ∈ N.code i ↔ ∃ (k : (N.decode i).Idx) (j : N.Code),
      N.decode j = (N.decode i).elems k ∧
        y = ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr ((N.decode i).conds k))) (N.code j)
  /-- **Faithfulness**: the material code determines the external name. Intensional syntax is
  preserved — nothing here forces a particular tree, only that codes do not conflate names. -/
  decode_eq_of_code_eq : ∀ i j : N.Code, N.code i = N.code j → N.decode i = N.decode j

namespace InternalNameCoding

variable {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}

omit [Preorder P] in
/-- Coded branches lie in the carrier — by transitivity from the name code, with no axiom
consumed. -/
theorem pair_mem_carrier {i : N.Code} {y : ZFSet.{u}} (hy : y ∈ N.code i) : y ∈ M :=
  M.mem_trans hy (N.code_mem i)

/-- **Subname absoluteness**: a code is a coded branch of another exactly when its name is an
immediate subname of the other's name. Derived from representation plus faithfulness — the
whole point of stating the laws in that form. -/
theorem subname_absolute (h : InternalNameCoding Pres N) {i j : N.Code} :
    (∃ p : P, ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr p)) (N.code j) ∈ N.code i) ↔
      Subname (N.decode j) (N.decode i) := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨k, j', hj', hy⟩ := (h.branch_mem_code_iff i _).1 hp
    obtain ⟨-, hcode⟩ := ZFSet.pair_inj.1 hy
    exact ⟨k, hj'.symm.trans (h.decode_eq_of_code_eq j' j hcode.symm)⟩
  · rintro ⟨k, hk⟩
    refine ⟨(N.decode i).conds k, (h.branch_mem_code_iff i _).2 ⟨k, j, hk.symm, rfl⟩⟩

/-- The condition side of a coded branch, in the carrier. -/
theorem conditionCode_mem_carrier (h : InternalNameCoding Pres N) {i : N.Code}
    {k : (N.decode i).Idx} {j : N.Code} (hj : N.decode j = (N.decode i).elems k) :
    ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr ((N.decode i).conds k))) (N.code j) ∈ M :=
  pair_mem_carrier ((h.branch_mem_code_iff i _).2 ⟨k, j, hj, rfl⟩)

/-!
### Sanity examples

Subname absoluteness composes with the presentation's own subname closure: every immediate
subname of a decoded name is itself decoded, and its code is a coded branch.
-/

example {i : N.Code} (k : (N.decode i).Idx) :
    ∃ j : N.Code, Subname (N.decode j) (N.decode i) := by
  obtain ⟨j, hj⟩ := N.subname_closed i k
  exact ⟨j, ⟨k, hj.symm⟩⟩

end InternalNameCoding

end Forcing
