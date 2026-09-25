/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.MaximalNames
import Forcing.Material.Extension
import Forcing.Material.Axioms

/-!
# Finite closure in the extension: Empty Set, Pairing, Binary Union

M7 item 6 (#241), sequencing step 2. Three axioms hold in the extension along an arbitrary
condition set `S`, each through an **explicit name** and each priced at **its own** ground
sentence:

| axiom | the name's code | charged | condition |
|---|---|---|---|
| Empty Set | `∅` | `emptySetSentence` | none |
| Pairing | `{⟨⌜q⌝, code i⟩, ⟨⌜q⌝, code j⟩}` | `pairingSentence` | `q ∈ S` |
| Binary Union | `code i ∪ code j` | `binaryUnionSentence` | none |

No filter, genericity, `OrderTop`, or truth lemma. **Independent of the check-name
construction and of Infinity**: this module does not import them, so no scheme instance and no
Infinity can reach these ledgers.

## Three layers

* **Carrier converses** (`MaterialCarrier.realize_emptySetSentence_of_empty_mem`, …): a carrier
  closed under the operation satisfies the sentence. No transitivity is needed in this
  direction; the realization laws of `emptyDef` and `unorderedPairDef` already carry it.
* **Valuation laws** (`MaximalNames.zval_decode_of_code_eq_empty`, `…_pair`, `…_union`),
  axiom-free: what the explicit codes value to, read through `mem_zval_decode_iff`.
* **The extension theorems**: the code is in the ground (the one charged sentence) and valid
  (`isNameCode_empty`, `isNameCode_insert_pair`, `isNameCode_union`), hence in the maximal
  family by `mem_range_code_iff`.

## Main results

* `Forcing.MaterialGround.extension_models_emptySet`,
  `Forcing.MaterialGround.extension_models_pairing`,
  `Forcing.MaterialGround.extension_models_binaryUnion`.
-/

universe u

namespace Forcing

open FirstOrder Language PName

/-! ### Carrier converses -/

namespace MaterialCarrier

variable (C : MaterialCarrier.{u})

/-- A carrier containing `∅` satisfies Empty Set. -/
theorem realize_emptySetSentence_of_empty_mem (h : (∅ : ZFSet.{u}) ∈ C) :
    ↥C ⊨ emptySetSentence := by
  simp only [emptySetSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex,
    realize_emptyDef]
  exact ⟨⟨∅, h⟩, rfl⟩

/-- A carrier closed under unordered pairs satisfies Pairing. -/
theorem realize_pairingSentence_of (h : ∀ x ∈ C, ∀ y ∈ C, ({x, y} : ZFSet.{u}) ∈ C) :
    ↥C ⊨ pairingSentence := by
  simp only [pairingSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, realize_unorderedPairDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc]
  intro x y
  exact ⟨⟨_, h x x.2 y y.2⟩, rfl⟩

/-- A carrier closed under binary unions satisfies Binary Union. -/
theorem realize_binaryUnionSentence_of (h : ∀ x ∈ C, ∀ y ∈ C, x ∪ y ∈ C) :
    ↥C ⊨ binaryUnionSentence := by
  have key : ∀ a b : ↥C, ∃ c : ↥C, ∀ z : ↥C, ((z : ZFSet.{u}) ∈ (c : ZFSet.{u}) ↔
      (z : ZFSet.{u}) ∈ (a : ZFSet.{u}) ∨ (z : ZFSet.{u}) ∈ (b : ZFSet.{u})) :=
    fun a b ↦ ⟨⟨_, h a a.2 b b.2⟩, fun _ ↦ ZFSet.mem_union⟩
  simpa [binaryUnionSentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc]
    using key

end MaterialCarrier

/-! ### What the explicit codes value to -/

namespace MaximalNames

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- A maximal name coded by `∅` values to `∅` along every `S`. -/
theorem zval_decode_of_code_eq_empty {S : Set P} {k : (maximal Pres).Code}
    (hk : (maximal Pres).code k = ∅) : zval S ((maximal Pres).decode k) = ∅ := by
  refine (ZFSet.eq_empty _).2 fun y hy ↦ ?_
  obtain ⟨p, -, j, hpj, -⟩ := (mem_zval_decode_iff Pres k).1 hy
  rw [hk] at hpj
  exact ZFSet.notMem_empty _ hpj

/-- A maximal name coded by `{⟨⌜q⌝, code i⟩, ⟨⌜q⌝, code j⟩}` values to the pair of the values
of `i` and `j` along every `S` containing `q`. -/
theorem zval_decode_of_code_eq_pair {q : P} {S : Set P} (hq : q ∈ S)
    {i j k : (maximal Pres).Code}
    (hk : (maximal Pres).code k =
      {ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) ((maximal Pres).code i),
        ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) ((maximal Pres).code j)}) :
    zval S ((maximal Pres).decode k) =
      {zval S ((maximal Pres).decode i), zval S ((maximal Pres).decode j)} := by
  have hcod := maximal_coding Pres
  refine ZFSet.ext fun y ↦ ?_
  rw [mem_zval_decode_iff, ZFSet.mem_pair, hk]
  constructor
  · rintro ⟨p, -, l, hpl, rfl⟩
    rcases ZFSet.mem_pair.1 hpl with h | h
    · exact Or.inl (by rw [hcod.decode_eq_of_code_eq l i (ZFSet.pair_inj.1 h).2])
    · exact Or.inr (by rw [hcod.decode_eq_of_code_eq l j (ZFSet.pair_inj.1 h).2])
  · rintro (rfl | rfl)
    · exact ⟨q, hq, i, ZFSet.mem_pair.2 (Or.inl rfl), rfl⟩
    · exact ⟨q, hq, j, ZFSet.mem_pair.2 (Or.inr rfl), rfl⟩

/-- A maximal name coded by `code i ∪ code j` values to the union of the values of `i` and `j`
along every `S`. -/
theorem zval_decode_of_code_eq_union {S : Set P} {i j k : (maximal Pres).Code}
    (hk : (maximal Pres).code k = (maximal Pres).code i ∪ (maximal Pres).code j) :
    zval S ((maximal Pres).decode k) =
      zval S ((maximal Pres).decode i) ∪ zval S ((maximal Pres).decode j) := by
  refine ZFSet.ext fun y ↦ ?_
  rw [ZFSet.mem_union, mem_zval_decode_iff, mem_zval_decode_iff, mem_zval_decode_iff, hk]
  constructor
  · rintro ⟨p, hp, l, hl, rfl⟩
    rcases ZFSet.mem_union.1 hl with hl | hl
    · exact Or.inl ⟨p, hp, l, hl, rfl⟩
    · exact Or.inr ⟨p, hp, l, hl, rfl⟩
  · rintro (⟨p, hp, l, hl, rfl⟩ | ⟨p, hp, l, hl, rfl⟩)
    · exact ⟨p, hp, l, ZFSet.mem_union.2 (Or.inl hl), rfl⟩
    · exact ⟨p, hp, l, ZFSet.mem_union.2 (Or.inr hl), rfl⟩

end MaximalNames

/-! ### The extension theorems -/

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

open MaximalNames

/-- **Empty Set holds in the extension** along every `S`, through the name coded by `∅`.
Ledger: `emptySetSentence`. -/
theorem extension_models_emptySet (he : emptySetSentence ∈ T) (S : Set P) :
    ↥((maximal Pres).extensionCarrier S) ⊨ emptySetSentence := by
  obtain ⟨k, hk⟩ := (mem_range_code_iff Pres).2 ⟨M.empty_mem he, isNameCode_empty _⟩
  exact MaterialCarrier.realize_emptySetSentence_of_empty_mem _
    ((maximal Pres).mem_extensionCarrier_iff.2 ⟨k, (zval_decode_of_code_eq_empty Pres hk).symm⟩)

/-- **Pairing holds in the extension** along every `S` containing a supplied condition `q`,
through the two-branch name at `q`. Ledger: `pairingSentence` alone. -/
theorem extension_models_pairing (hp : pairingSentence ∈ T) {q : P} {S : Set P} (hq : q ∈ S) :
    ↥((maximal Pres).extensionCarrier S) ⊨ pairingSentence := by
  refine MaterialCarrier.realize_pairingSentence_of _ fun x hx y hy ↦ ?_
  obtain ⟨i, rfl⟩ := (maximal Pres).mem_extensionCarrier_iff.1 hx
  obtain ⟨j, rfl⟩ := (maximal Pres).mem_extensionCarrier_iff.1 hy
  have hc : ZFSet.mk (Pres.conditionCode.repr q) ∈ M :=
    M.mem_trans (Pres.code_mem q) Pres.conditionSet.2
  obtain ⟨-, hi⟩ := (mem_range_code_iff Pres).1 ⟨i, rfl⟩
  obtain ⟨-, hj⟩ := (mem_range_code_iff Pres).1 ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := (mem_range_code_iff Pres).2
    ⟨M.insert_pair_mem hp (M.pair_mem hp hc ((maximal Pres).code_mem i))
        (M.pair_mem hp hc ((maximal Pres).code_mem j)),
      isNameCode_insert_pair (Pres.code_mem q) hi (isNameCode_singleton_pair (Pres.code_mem q) hj)⟩
  exact (maximal Pres).mem_extensionCarrier_iff.2
    ⟨k, (zval_decode_of_code_eq_pair Pres hq hk).symm⟩

/-- **Binary Union holds in the extension** along every `S`, through the union of the codes.
Ledger: `binaryUnionSentence`. -/
theorem extension_models_binaryUnion (hu : binaryUnionSentence ∈ T) (S : Set P) :
    ↥((maximal Pres).extensionCarrier S) ⊨ binaryUnionSentence := by
  refine MaterialCarrier.realize_binaryUnionSentence_of _ fun x hx y hy ↦ ?_
  obtain ⟨i, rfl⟩ := (maximal Pres).mem_extensionCarrier_iff.1 hx
  obtain ⟨j, rfl⟩ := (maximal Pres).mem_extensionCarrier_iff.1 hy
  obtain ⟨-, hi⟩ := (mem_range_code_iff Pres).1 ⟨i, rfl⟩
  obtain ⟨-, hj⟩ := (mem_range_code_iff Pres).1 ⟨j, rfl⟩
  obtain ⟨k, hk⟩ := (mem_range_code_iff Pres).2
    ⟨M.union_mem hu ((maximal Pres).code_mem i) ((maximal Pres).code_mem j),
      isNameCode_union hi hj⟩
  exact (maximal Pres).mem_extensionCarrier_iff.2
    ⟨k, (zval_decode_of_code_eq_union Pres hk).symm⟩

end MaterialGround

end Forcing
