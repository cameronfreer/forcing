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

## Main results

* `Forcing.isNameCode_empty`, `Forcing.isNameCode_insert_pair`,
  `Forcing.isNameCode_singleton_pair`: validity, on sets. Axiom-free.
* `Forcing.MaximalNames.isEmpty_idx_decode_empty`, `Forcing.MaximalNames.decode_singleton_pair`:
  what the decodings are.
* `Forcing.MaterialGround.empty_mem_range_code`, `…singleton_pair_mem_range_code`,
  `…insert_pair_mem_range_code`: representation in the ground, each priced where paid.
-/

universe u

namespace Forcing

/-! ### Validity, on sets -/

section Sets

variable {cs c e x : ZFSet.{u}}

/-- The empty set is a name code, vacuously. -/
theorem isNameCode_empty (cs : ZFSet.{u}) : IsNameCode cs ∅ :=
  IsNameCode.mk ∅ (fun y hy ↦ absurd hy (ZFSet.notMem_empty y))
    (fun y hy ↦ absurd hy (ZFSet.notMem_empty y))

/-- **The branch constructor**: adjoining a branch with a valid condition and a valid subname
keeps a code valid. -/
theorem isNameCode_insert_pair (hc : c ∈ cs) (he : IsNameCode cs e) (hx : IsNameCode cs x) :
    IsNameCode cs (insert (ZFSet.pair c e) x) := by
  refine IsNameCode.mk _ (fun y hy ↦ ?_) (fun y hy c' e' hy' ↦ ?_)
  · rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ⟨c, e, rfl, hc⟩
    · exact hx.branch y hy
  · rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 hy'
      exact he
    · exact hx.sub y hy c' e' hy'

/-- The single-branch name code. -/
theorem isNameCode_singleton_pair (hc : c ∈ cs) (he : IsNameCode cs e) :
    IsNameCode cs {ZFSet.pair c e} :=
  isNameCode_insert_pair hc he (isNameCode_empty cs)

end Sets

/-! ### What the decodings are -/

namespace MaximalNames

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- Decoding is determined by the code alone. -/
theorem decode_congr {x x' : ZFSet.{u}} (h : IsNameCode (Pres.conditionSet : ZFSet.{u}) x)
    (h' : IsNameCode (Pres.conditionSet : ZFSet.{u}) x') (hxx : x = x') :
    decode Pres x h = decode Pres x' h' := by
  subst hxx
  rfl

/-- **The empty name decodes to a name with no branches.** -/
theorem isEmpty_idx_decode_empty :
    IsEmpty (decode Pres ∅ (isNameCode_empty _)).Idx := by
  rw [decode_eq]
  exact ⟨fun i ↦ ZFSet.notMem_empty _ ((equivShrink (∅ : ZFSet.{u})).symm i).2⟩

/-- **The singleton name decodes to a name with a branch reading `e` at `q`.** -/
theorem decode_singleton_pair (q : P) {e : ZFSet.{u}}
    (he : IsNameCode (Pres.conditionSet : ZFSet.{u}) e) :
    ∃ k : (decode Pres _ (isNameCode_singleton_pair (Pres.code_mem q) he)).Idx,
      (decode Pres _ (isNameCode_singleton_pair (Pres.code_mem q) he)).elems k =
          decode Pres e he ∧
        (decode Pres _ (isNameCode_singleton_pair (Pres.code_mem q) he)).conds k = q := by
  set h := isNameCode_singleton_pair (Pres.code_mem q) he
  have hy : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) e ∈
      ({ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) e} : ZFSet.{u}) :=
    ZFSet.mem_singleton.2 rfl
  obtain ⟨hcond, hsub⟩ := ZFSet.pair_inj.1 (branch_eq h hy)
  rw [decode_eq]
  refine ⟨equivShrink _ ⟨_, hy⟩, ?_, ?_⟩
  · simp only [PName.elems_mk, Equiv.symm_apply_apply]
    exact decode_congr Pres _ _ hsub.symm
  · simp only [PName.conds_mk, Equiv.symm_apply_apply]
    apply Pres.conditionCode.injective_mk
    change ZFSet.mk (Pres.conditionCode.repr (condOf Pres _)) = ZFSet.mk (Pres.conditionCode.repr q)
    rw [← condCode_condOf, ← hcond]

end MaximalNames

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
