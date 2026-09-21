/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.MaximalNames
import Forcing.Material.Axioms

/-!
# Richness pressure tests for the maximal name family

ADR 0006, tranche 3. Two constructions are shown to be **represented** in the maximal family —
in the range of `code`, with `decode` behaving as the construction says:

* **the empty name**: `∅` is vacuously a name code; it lies in the ground at the price of Empty
  Set; its decoding has no branches;
* **a branch constructor**: adjoining a branch `⟨condCode q, e⟩` to a valid code keeps it valid;
  the singleton case lies in the ground at the price of Pairing alone, the general `insert` at
  Pairing and Binary Union; and the decoded singleton has a branch decoding `e` at condition `q`.

These are pressure tests on the *definition*: they show the family is not trivially small and
that decoding reads the branches the constructor wrote. Check names, the generic name, and the
Cohen-real name are **not** here — their membership in the family is M7 item 7's composition
work on the Cohen material presentation's own codes.

The validity lemmas and the decoding facts live with the presentation
(`Forcing/Material/MaximalNames.lean`), since they reason through its index representation; this
module is a consumer and mentions no `Shrink`.

## Main results

* `Forcing.MaterialGround.empty_mem_range_code`, `…singleton_pair_mem_range_code`,
  `…insert_pair_mem_range_code`: representation in the ground, each priced where paid.
-/

universe u

namespace Forcing

/-! ### Representation in the ground -/

namespace MaterialGround

open MaximalNames

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-- **The empty name is represented**, at the price of Empty Set. -/
theorem empty_mem_range_code (he : emptySetSentence ∈ T) :
    (∅ : ZFSet.{u}) ∈ Set.range (maximal Pres).code :=
  (mem_range_code_iff Pres).2 ⟨M.empty_mem he, isNameCode_empty _⟩

/-- **The single-branch name is represented**, at the price of Pairing alone. -/
theorem singleton_pair_mem_range_code (hp : pairingSentence ∈ T) (q : P) {e : ZFSet.{u}}
    (he : e ∈ Set.range (maximal Pres).code) :
    ({ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) e} : ZFSet.{u}) ∈
      Set.range (maximal Pres).code := by
  obtain ⟨heM, hev⟩ := (mem_range_code_iff Pres).1 he
  exact (mem_range_code_iff Pres).2
    ⟨M.singleton_mem hp (M.pair_mem hp (Pres.code_mem_carrier q) heM),
      isNameCode_singleton_pair (Pres.code_mem q) hev⟩

/-- **Branch adjunction is represented**, at the price of Pairing and Binary Union. -/
theorem insert_pair_mem_range_code (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (q : P) {e x : ZFSet.{u}} (he : e ∈ Set.range (maximal Pres).code)
    (hx : x ∈ Set.range (maximal Pres).code) :
    insert (ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) e) x ∈
      Set.range (maximal Pres).code := by
  obtain ⟨heM, hev⟩ := (mem_range_code_iff Pres).1 he
  obtain ⟨hxM, hxv⟩ := (mem_range_code_iff Pres).1 hx
  exact (mem_range_code_iff Pres).2
    ⟨M.insert_mem hp hu (M.pair_mem hp (Pres.code_mem_carrier q) heM) hxM,
      isNameCode_insert_pair (Pres.code_mem q) hev hxv⟩

end MaterialGround

end Forcing
