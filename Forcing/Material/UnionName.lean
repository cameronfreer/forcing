/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes
import Forcing.Material.MaximalNames

/-!
# The union name: semantic laws and exact formula laws

M7 item 6 (#241), general Union, first of two PRs. For a name code `t`, the **union code** is
the set of `⟨s, ρ⟩` such that some branch `⟨p, σ⟩` of `t` and some branch `⟨r, ρ⟩` of `σ`
have `s` as a common strengthening:

```text
IsUnionBranch cs ord t m :=
  ∃ s ρ, m = ⟨s, ρ⟩ ∧ s ∈ cs ∧
    ∃ p σ, ⟨p, σ⟩ ∈ t ∧ p ∈ cs ∧ ⟨s, p⟩ ∈ ord ∧
      ∃ r, ⟨r, ρ⟩ ∈ σ ∧ r ∈ cs ∧ ⟨s, r⟩ ∈ ord
```

The orientation is `order_iff`'s: `⟨⌜s⌝, ⌜p⌝⟩ ∈ ord ↔ s ≤ p`. **Every internally quantified
condition carries its `cs` guard** (#223); the guards on `p` and `r` are redundant for valid `t`
but keep the formula's meaning independent of validity.

## Contract

Validity and valuation are stated against a **supplied exact characterization**
`∀ m, m ∈ U ↔ IsUnionBranch cs ord t m`, so they do not depend on how the internal bound is
built (`Forcing/Material/ExtensionUnion.lean`):

* `isNameCode_of_isUnionBranch`: `U` is a valid code when `t` is;
* `MaximalNames.zval_decode_of_isUnionBranch`: `U` values to `⋃₀` of `t`'s value along every
  `S` that is **upward closed** and **downward directed**. Upward closure takes an admitted
  common strengthening back to both branch conditions; directedness supplies one from two
  admitted conditions. A `PFilter` supplies both; nonemptiness, genericity, and the truth lemma
  are not needed. Unlike Empty Set, Pairing, and Binary Union, this does **not** hold along an
  arbitrary `S`.

## The bound

`mem_sUnion_five_of_pair_mem`: the structural chain
`ρ ∈ {r, ρ} ∈ ⟨r, ρ⟩ ∈ σ ∈ {p, σ} ∈ ⟨p, σ⟩ ∈ t` puts every right coordinate in `⋃⁵ t`, with no
validity, order, or material membership. So a union code lies inside `cs × ⋃⁵ t`
(`IsUnionBranch.exists_mem_bound`), which `ExtensionUnion.lean` covers by nested Collection:
`FiberCovers R s y := ∀ ρ ∈ R, ⟨s, ρ⟩ ∈ y` is the outer relation. It promises coverage only,
never that `y` contains only those pairs; exactness comes from the final Separation.

## The formulas

Term-parameterized, membership and pairing only, each with an exact realization law carrying no
name-validity and no theory hypothesis. Every quantifier bridge is carrier transitivity or a
pair-component step. Instances: `unionFilterFormula : BoundedFormula (Fin 3) 1` (Separation;
parameters `cs`, `ord`, `t`) and `fiberCoverGatherFormula : BoundedFormula (Fin 1) 2`
(Collection; parameter `R`, index `s`, witness `y`).

## Main results

* `Forcing.IsUnionBranch`, `Forcing.FiberCovers`; `Forcing.mem_sUnion_five_of_pair_mem`,
  `Forcing.IsUnionBranch.exists_mem_bound`.
* `Forcing.isNameCode_of_isUnionBranch`, `Forcing.MaximalNames.zval_decode_of_isUnionBranch`.
* `Forcing.realize_unionBranchDef`, `Forcing.realize_fiberCoversDef`.
-/

universe u v

namespace Forcing

open FirstOrder Language PName

/-! ### The union name, on sets -/

/-- **A branch of the union code** of `t`: `⟨s, ρ⟩` where `s` strengthens the conditions of a
branch `⟨p, σ⟩` of `t` and a branch `⟨r, ρ⟩` of `σ`. All three conditions are guarded by `cs`. -/
def IsUnionBranch (cs ord t m : ZFSet.{u}) : Prop :=
  ∃ s ρ, m = ZFSet.pair s ρ ∧ s ∈ cs ∧
    ∃ p σ, ZFSet.pair p σ ∈ t ∧ p ∈ cs ∧ ZFSet.pair s p ∈ ord ∧
      ∃ r, ZFSet.pair r ρ ∈ σ ∧ r ∈ cs ∧ ZFSet.pair s r ∈ ord

/-- **Fiber coverage**: `y` contains `⟨s, ρ⟩` for every `ρ ∈ R`. Coverage only; `y` may contain
anything else. The outer Collection relation of the bound construction. -/
def FiberCovers (R s y : ZFSet.{u}) : Prop :=
  ∀ ρ ∈ R, ZFSet.pair s ρ ∈ y

/-- **The depth of the bound**: a branch of a branch of `t` has its right coordinate in `⋃⁵ t`,
along `ρ ∈ {r, ρ} ∈ ⟨r, ρ⟩ ∈ σ ∈ {p, σ} ∈ ⟨p, σ⟩ ∈ t`. Structural: no validity, order, or
material membership. -/
theorem mem_sUnion_five_of_pair_mem {t p σ r ρ : ZFSet.{u}} (hpσ : ZFSet.pair p σ ∈ t)
    (hrρ : ZFSet.pair r ρ ∈ σ) :
    ρ ∈ ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion t)))) := by
  have hσ := (components_mem_sUnion_sUnion hpσ).2
  have h3 : ZFSet.pair r ρ ∈ ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion t)) :=
    ZFSet.mem_sUnion.2 ⟨σ, hσ, hrρ⟩
  have h4 : ({r, ρ} : ZFSet.{u}) ∈ ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion t))) :=
    ZFSet.mem_sUnion.2 ⟨_, h3, ZFSet.mem_pair.2 (Or.inr rfl)⟩
  exact ZFSet.mem_sUnion.2 ⟨_, h4, ZFSet.mem_pair.2 (Or.inr rfl)⟩

/-- A union branch lies in `cs × ⋃⁵ t`: the coverage target of the bound construction. -/
theorem IsUnionBranch.exists_mem_bound {cs ord t m : ZFSet.{u}} (h : IsUnionBranch cs ord t m) :
    ∃ s ∈ cs, ∃ ρ ∈ ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion t)))),
      m = ZFSet.pair s ρ := by
  obtain ⟨s, ρ, rfl, hs, p, σ, hpσ, -, -, r, hrρ, -, -⟩ := h
  exact ⟨s, hs, ρ, mem_sUnion_five_of_pair_mem hpσ hrρ, rfl⟩

/-- **Validity**: a set characterized exactly by `IsUnionBranch` over a valid code is a valid
code. Each member's right coordinate is a subname of a subname. -/
theorem isNameCode_of_isUnionBranch {cs ord t U : ZFSet.{u}} (ht : IsNameCode cs t)
    (hU : ∀ m, m ∈ U ↔ IsUnionBranch cs ord t m) : IsNameCode cs U := by
  refine IsNameCode.mk _ (fun m hm ↦ ?_) (fun m hm c e hm' ↦ ?_)
  · obtain ⟨s, ρ, rfl, hs, -⟩ := (hU m).1 hm
    exact ⟨s, ρ, rfl, hs⟩
  · obtain ⟨s, ρ, rfl, -, p, σ, hpσ, -, -, r, hrρ, -, -⟩ := (hU m).1 hm
    obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 hm'
    exact (ht.sub _ hpσ p σ rfl).sub _ hrρ r ρ rfl

/-! ### Valuation -/

namespace MaximalNames

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- **Valuation of the union name**: a maximal name whose code is exactly the union code of
`code i` values to `⋃₀` of the value of `i`, along every upward-closed, downward-directed `S`.
Upward closure gives `⊆`, directedness `⊇`. Axiom-free; no genericity, no nonemptiness. -/
theorem zval_decode_of_isUnionBranch {S : Set P} (hup : IsUpperSet S)
    (hdir : DirectedOn (· ≥ ·) S) {i k : (maximal Pres).Code}
    (hk : ∀ m, m ∈ (maximal Pres).code k ↔
      IsUnionBranch (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u})
        ((maximal Pres).code i) m) :
    zval S ((maximal Pres).decode k) = ZFSet.sUnion (zval S ((maximal Pres).decode i)) := by
  obtain ⟨htM, ht⟩ := (mem_range_code_iff Pres).1 ⟨i, rfl⟩
  refine ZFSet.ext fun y ↦ ?_
  rw [mem_zval_decode_iff, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨s, hs, j, hsj, rfl⟩
    obtain ⟨s', ρ, hpair, -, p', σ, hpσ, hp', hsp, r', hrρ, hr', hsr⟩ := (hk _).1 hsj
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 hpair
    obtain ⟨p, rfl⟩ := Pres.code_surjective p' hp'
    obtain ⟨r, rfl⟩ := Pres.code_surjective r' hr'
    have hσ := (MaterialCarrier.pair_components_mem_of_mem htM hpσ).2
    obtain ⟨j₁, rfl⟩ := (mem_range_code_iff Pres).2 ⟨hσ, ht.sub _ hpσ _ _ rfl⟩
    refine ⟨_, (mem_zval_decode_iff Pres i).2
      ⟨p, hup ((Pres.order_iff p s).1 hsp) hs, j₁, hpσ, rfl⟩, ?_⟩
    exact (mem_zval_decode_iff Pres j₁).2 ⟨r, hup ((Pres.order_iff r s).1 hsr) hs, j, hrρ, rfl⟩
  · rintro ⟨z, hz, hyz⟩
    obtain ⟨p, hp, j₁, hpj₁, rfl⟩ := (mem_zval_decode_iff Pres i).1 hz
    obtain ⟨r, hr, j₂, hrj₂, rfl⟩ := (mem_zval_decode_iff Pres j₁).1 hyz
    obtain ⟨s, hs, hsp, hsr⟩ := hdir p hp r hr
    exact ⟨s, hs, j₂, (hk _).2 ⟨_, _, rfl, Pres.code_mem s, _, _, hpj₁, Pres.code_mem p,
      (Pres.order_iff p s).2 hsp, _, hrj₂, Pres.code_mem r, (Pres.order_iff r s).2 hsr⟩, rfl⟩

end MaximalNames

/-! ### The formulas -/

section Syntax

variable {α : Type v} {n : ℕ}

/-- `∃ r, ⟨r, ρ⟩ ∈ σ ∧ r ∈ cs ∧ ⟨s, r⟩ ∈ ord`. -/
def unionInnerDef (cs ord s ρ σ : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (pairMemDef (&(Fin.last n)) (liftTerm ρ) (liftTerm σ) ⊓
    (memFormula (&(Fin.last n)) (liftTerm cs) ⊓
      pairMemDef (liftTerm s) (&(Fin.last n)) (liftTerm ord)))

/-- `∃ p σ, ⟨p, σ⟩ ∈ t ∧ p ∈ cs ∧ ⟨s, p⟩ ∈ ord ∧ ∃ r, ⟨r, ρ⟩ ∈ σ ∧ r ∈ cs ∧ ⟨s, r⟩ ∈ ord`. -/
def unionMiddleDef (cs ord t s ρ : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' ∃' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm t)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm cs)) ⊓
      (pairMemDef (liftTerm (liftTerm s)) (&(Fin.castSucc (Fin.last n)))
          (liftTerm (liftTerm ord)) ⊓
        unionInnerDef (liftTerm (liftTerm cs)) (liftTerm (liftTerm ord)) (liftTerm (liftTerm s))
          (liftTerm (liftTerm ρ)) (&(Fin.last (n + 1))))))

/-- **The guarded union-branch formula**: `∃ s ρ, m = ⟨s, ρ⟩ ∧ s ∈ cs ∧ middle`. -/
def unionBranchDef (cs ord t m : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) (liftTerm (liftTerm m)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm cs)) ⊓
      unionMiddleDef (liftTerm (liftTerm cs)) (liftTerm (liftTerm ord)) (liftTerm (liftTerm t))
        (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))))

/-- **Fiber coverage**: `∀ ρ ∈ R, ⟨s, ρ⟩ ∈ y`. -/
def fiberCoversDef (R s y : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm R) ⟹
    pairMemDef (liftTerm s) (&(Fin.last n)) (liftTerm y))

/-- **The union filter** (Separation; parameters `cs`, `ord`, `t`). -/
def unionFilterFormula : memLang.BoundedFormula (Fin 3) 1 :=
  unionBranchDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (&0)

/-- **The outer fiber gather** (Collection; parameter `R`; index `s`, witness `y`). -/
def fiberCoverGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  fiberCoversDef (var (Sum.inl 0)) (&0) (&1)

def unionFilterSentence : memLang.Sentence := separationSentence unionFilterFormula
def fiberCoverGatherSentence : memLang.Sentence := collectionSentence fiberCoverGatherFormula

theorem unionFilterSentence_mem_scheme : unionFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme unionFilterFormula
theorem fiberCoverGatherSentence_mem_scheme : fiberCoverGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme fiberCoverGatherFormula

end Syntax

/-! ### Realization laws -/

section Realization

variable {α : Type v} {n : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin n → M}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

theorem realize_unionInnerDef {cs ord s ρ σ : memLang.Term (α ⊕ Fin n)} :
    (unionInnerDef cs ord s ρ σ).Realize v xs ↔
      ∃ r, ZFSet.pair r ⟪ρ⟫ ∈ ⟪σ⟫ ∧ r ∈ ⟪cs⟫ ∧ ZFSet.pair ⟪s⟫ r ∈ ⟪ord⟫ := by
  have hσM : ⟪σ⟫ ∈ M := (Term.realize (Sum.elim v xs) σ : ↥M).2
  simp only [unionInnerDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    realize_liftTerm]
  exact ⟨fun ⟨r, h⟩ ↦ ⟨r, h⟩,
    fun ⟨r, h⟩ ↦ ⟨⟨r, (M.pair_components_mem_of_mem hσM h.1).1⟩, h⟩⟩

theorem realize_unionMiddleDef {cs ord t s ρ : memLang.Term (α ⊕ Fin n)} :
    (unionMiddleDef cs ord t s ρ).Realize v xs ↔
      ∃ p σ, ZFSet.pair p σ ∈ ⟪t⟫ ∧ p ∈ ⟪cs⟫ ∧ ZFSet.pair ⟪s⟫ p ∈ ⟪ord⟫ ∧
        ∃ r, ZFSet.pair r ⟪ρ⟫ ∈ σ ∧ r ∈ ⟪cs⟫ ∧ ZFSet.pair ⟪s⟫ r ∈ ⟪ord⟫ := by
  have htM : ⟪t⟫ ∈ M := (Term.realize (Sum.elim v xs) t : ↥M).2
  simp only [unionMiddleDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, realize_unionInnerDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm]
  constructor
  · rintro ⟨p, σ, h⟩
    exact ⟨p, σ, h⟩
  · rintro ⟨p, σ, h⟩
    obtain ⟨hpM, hσM⟩ := M.pair_components_mem_of_mem htM h.1
    exact ⟨⟨p, hpM⟩, ⟨σ, hσM⟩, h⟩

/-- **The union-branch law**: exact against `IsUnionBranch`, with no validity or theory
hypothesis. -/
theorem realize_unionBranchDef {cs ord t m : memLang.Term (α ⊕ Fin n)} :
    (unionBranchDef cs ord t m).Realize v xs ↔ IsUnionBranch ⟪cs⟫ ⟪ord⟫ ⟪t⟫ ⟪m⟫ := by
  have hmM : ⟪m⟫ ∈ M := (Term.realize (Sum.elim v xs) m : ↥M).2
  simp only [unionBranchDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairDef, realize_unionMiddleDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm, IsUnionBranch]
  constructor
  · rintro ⟨s, ρ, h⟩
    exact ⟨s, ρ, h⟩
  · rintro ⟨s, ρ, h⟩
    obtain ⟨hsM, hρM⟩ := M.pair_components_mem (h.1 ▸ hmM)
    exact ⟨⟨s, hsM⟩, ⟨ρ, hρM⟩, h⟩

/-- **The fiber-coverage law**: exact against `FiberCovers`. -/
theorem realize_fiberCoversDef {R s y : memLang.Term (α ⊕ Fin n)} :
    (fiberCoversDef R s y).Realize v xs ↔ FiberCovers ⟪R⟫ ⟪s⟫ ⟪y⟫ := by
  have hRM : ⟪R⟫ ∈ M := (Term.realize (Sum.elim v xs) R : ↥M).2
  simp only [fiberCoversDef, BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    realize_liftTerm, FiberCovers]
  exact ⟨fun h ρ hρ ↦ h ⟨ρ, M.mem_trans hρ hRM⟩ hρ, fun h ρ hρ ↦ h ρ hρ⟩

end Realization

end Forcing
