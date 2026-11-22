/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.PairImageGather

/-!
# The product cover

For internal sets `A` and `R`, a ground set containing `⟨s, ρ⟩` for every `s ∈ A` and `ρ ∈ R`
(`exists_productCover`). About arbitrary internal sets and coverage only: no name validity,
order, or filter. Two consumers bound their names by it: general Union
(`Forcing/Material/ExtensionUnion.lean`, over `cs × ⋃⁵ t`) and Separation
(`Forcing/Material/ExtensionSeparation.lean`, over `cs × ⋃⋃ t`). Moved unchanged from
`UnionName.lean` and `ExtensionUnion.lean`.

The inner Collection instance (`pairImageGatherSentence`, parameter `s`, Pairing witnesses)
gives a set covering the fiber `{s} × R`. The outer relation is
`FiberCovers R s y := ∀ ρ ∈ R, ⟨s, ρ⟩ ∈ y`; it promises coverage only, never that `y` contains
only those pairs. The outer Collection instance (`fiberCoverGatherSentence`, parameter `R`)
collects one covering set per `s`, and General Union flattens. Neither Collection output is
filtered, and empty index sets need no case split.

**Ledger:** two Collection instances (`pairImageGatherSentence`, `fiberCoverGatherSentence`),
Pairing, General Union.

## Main definitions

* `Forcing.FiberCovers`, `Forcing.fiberCoversDef`, `Forcing.fiberCoverGatherFormula`,
  `Forcing.fiberCoverGatherSentence`.

## Main results

* `Forcing.realize_fiberCoversDef`, `Forcing.MaterialGround.realize_fiberCoverGatherFormula`.
* `Forcing.MaterialGround.exists_productCover`.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-- **Fiber coverage**: `y` contains `⟨s, ρ⟩` for every `ρ ∈ R`. Coverage only; `y` may contain
anything else. The outer Collection relation of the bound construction. -/
def FiberCovers (R s y : ZFSet.{u}) : Prop :=
  ∀ ρ ∈ R, ZFSet.pair s ρ ∈ y

section Syntax

variable {α : Type v} {n : ℕ}

/-- **Fiber coverage**: `∀ ρ ∈ R, ⟨s, ρ⟩ ∈ y`. -/
def fiberCoversDef (R s y : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm R) ⟹
    pairMemDef (liftTerm s) (&(Fin.last n)) (liftTerm y))

/-- **The outer fiber gather** (Collection; parameter `R`; index `s`, witness `y`). -/
def fiberCoverGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  fiberCoversDef (var (Sum.inl 0)) (&0) (&1)

def fiberCoverGatherSentence : memLang.Sentence := collectionSentence fiberCoverGatherFormula

theorem fiberCoverGatherSentence_mem_scheme : fiberCoverGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme fiberCoverGatherFormula

end Syntax

section Realization

variable {α : Type v} {n : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin n → M}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

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

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

theorem realize_fiberCoverGatherFormula (R s y : ↥M.toMaterialCarrier) :
    fiberCoverGatherFormula.Realize ![R] ![s, y] ↔
      FiberCovers (R : ZFSet.{u}) (s : ZFSet.{u}) (y : ZFSet.{u}) := by
  rw [fiberCoverGatherFormula, realize_fiberCoversDef]
  simp

/-! ### The product cover -/

/-- **The product cover**: for internal `A` and `R`, some ground set contains `⟨s, ρ⟩` for every
`s ∈ A`, `ρ ∈ R`. Coverage only — the set may contain anything else. Arbitrary internal sets:
no name validity, order, or filter. Ledger: two Collection instances, Pairing, General Union. -/
theorem exists_productCover (hpg : pairImageGatherSentence ∈ T)
    (hfc : fiberCoverGatherSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {A R : ZFSet.{u}} (hA : A ∈ M) (hR : R ∈ M) :
    ∃ Bd ∈ M, ∀ s ∈ A, ∀ ρ ∈ R, ZFSet.pair s ρ ∈ Bd := by
  -- inner: for each `s ∈ M`, a ground set covering the fiber `{s} × R`
  have hfiber : ∀ s : ↥M.toMaterialCarrier, ∃ y : ↥M.toMaterialCarrier,
      FiberCovers R (s : ZFSet.{u}) (y : ZFSet.{u}) := by
    intro s
    obtain ⟨y, hy⟩ := M.exists_collection (φ := pairImageGatherFormula) hpg ![s] ⟨R, hR⟩
      (fun ρ _ ↦ ⟨⟨_, M.pair_mem hp s.2 ρ.2⟩,
        (M.realize_pairImageGatherFormula s ρ ⟨_, M.pair_mem hp s.2 ρ.2⟩).2 rfl⟩)
    refine ⟨y, fun ρ hρ ↦ ?_⟩
    obtain ⟨⟨p, hpM⟩, hpy, hp'⟩ := hy ⟨ρ, M.mem_trans hρ hR⟩ hρ
    rw [M.realize_pairImageGatherFormula] at hp'
    change p = ZFSet.pair (s : ZFSet.{u}) ρ at hp'
    subst hp'
    exact hpy
  -- outer: one covering set per `s ∈ A`
  obtain ⟨C, hC⟩ := M.exists_collection (φ := fiberCoverGatherFormula) hfc ![⟨R, hR⟩] ⟨A, hA⟩
    (fun s _ ↦ by
      obtain ⟨y, hy⟩ := hfiber s
      exact ⟨y, (M.realize_fiberCoverGatherFormula ⟨R, hR⟩ s y).2 hy⟩)
  -- flatten
  refine ⟨ZFSet.sUnion (C : ZFSet.{u}), M.sUnion_mem huni C.2, fun s hs ρ hρ ↦ ?_⟩
  obtain ⟨y, hyC, hy⟩ := hC ⟨s, M.mem_trans hs hA⟩ hs
  rw [M.realize_fiberCoverGatherFormula] at hy
  exact ZFSet.mem_sUnion.2 ⟨y, hyC, hy ρ hρ⟩

end MaterialGround

end Forcing
