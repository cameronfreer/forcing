/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Order.Basic

/-!
# The abstract visibility context

Genericity over a ground model quantifies over the tests *visible to the model*. This file
introduces the minimal interface that makes such quantification possible: a `VisibilityContext` is
nothing but the family of sets of conditions the ground model can see.

The context is deliberately spartan:

* **No countability.** Countability of the visible family is always an external hypothesis of an
  existence statement (Rasiowa–Sikorski), never a field of the context.
* **No carrier-specific data.** Designated designated reals arrive with the Cohen layer, not here.
* **No model of anything.** Visibility is an interface to be implemented by a later material
  ground model; nothing here is a claim about sets, transitivity, or ZFC.

Visibility and dense-openness are independent predicates — see the sanity examples — and
`visibleDenseOpen` is their intersection. Genericity over the context is `GenericFor` of that
family; it is deliberately not defined in this file.

## Main definitions

* `Forcing.VisibilityContext P`: the visibility interface.
* `Forcing.VisibilityContext.Visible`: `M` can see the set of conditions `D`.
* `Forcing.VisibilityContext.visibleDenseOpen`: the visible dense-open tests.

## Main results

* `Forcing.VisibilityContext.visibleDenseOpen_mono`: a context that sees more has more tests.
* `Forcing.VisibilityContext.full`, `Forcing.VisibilityContext.empty`: the extreme contexts, and the
  sanity examples separating `Visible` from `IsDenseOpen` in both directions.
-/

namespace Forcing

variable {P : Type*} [Preorder P]

/-- An abstract visibility context over the forcing notion `P`: the family of sets of
conditions the ground model can see. Deliberately minimal — no countability (that is always an
external hypothesis of an existence statement), no carrier-specific data, and no claim to model
anything. -/
@[ext] structure VisibilityContext (P : Type*) [Preorder P] where
  /-- The sets of conditions the ground model can see. -/
  visible : Set (Set P)

namespace VisibilityContext

variable {M M' : VisibilityContext P} {D : Set P}

/-- `M` can see the set of conditions `D`. Independent of `IsDenseOpen D` — see the sanity
examples below. -/
def Visible (M : VisibilityContext P) (D : Set P) : Prop :=
  D ∈ M.visible

theorem visible_def : M.Visible D ↔ D ∈ M.visible :=
  .rfl

/-- The visible dense-open family: the tests that count for genericity over `M`. -/
def visibleDenseOpen (M : VisibilityContext P) : Set (Set P) :=
  {D ∈ M.visible | IsDenseOpen D}

@[simp] theorem mem_visibleDenseOpen :
    D ∈ M.visibleDenseOpen ↔ M.Visible D ∧ IsDenseOpen D :=
  Iff.rfl

/-- Seeing more means owing more: the visible dense-open family is monotone in visibility. -/
theorem visibleDenseOpen_mono (h : M.visible ⊆ M'.visible) :
    M.visibleDenseOpen ⊆ M'.visibleDenseOpen :=
  fun _ hD ↦ ⟨h hD.1, hD.2⟩

/-- The full context: sees every set of conditions. Genericity over it will be genericity for
every dense open set. -/
def full (P : Type*) [Preorder P] : VisibilityContext P :=
  ⟨Set.univ⟩

@[simp] theorem visible_full : (full P).Visible D :=
  Set.mem_univ D

@[simp] theorem visibleDenseOpen_full : (full P).visibleDenseOpen = {D | IsDenseOpen D} :=
  Set.sep_univ

/-- The empty context: sees nothing. Genericity over it will be trivial. -/
def empty (P : Type*) [Preorder P] : VisibilityContext P :=
  ⟨∅⟩

@[simp] theorem not_visible_empty : ¬(empty P).Visible D :=
  Set.notMem_empty D

@[simp] theorem visibleDenseOpen_empty : (empty P).visibleDenseOpen = ∅ :=
  Set.sep_empty _

/-!
### Sanity examples

`Visible` and `IsDenseOpen` are independent. The full context sees the empty set, which is not
dense once `P` is nonempty (over the empty preorder every set is vacuously dense, so the
hypothesis is required); and the empty context fails to see `Set.univ`, which is dense open over
any preorder.
-/

example [Nonempty P] : (full P).Visible (∅ : Set P) ∧ ¬IsDense (∅ : Set P) :=
  ⟨visible_full, fun h ↦ by
    obtain ⟨q, hq, -⟩ := h (Classical.arbitrary P)
    exact hq⟩

example : IsDenseOpen (Set.univ : Set P) ∧ ¬(empty P).Visible (Set.univ : Set P) :=
  ⟨⟨fun p ↦ ⟨p, Set.mem_univ p, le_rfl⟩, isLowerSet_univ⟩, not_visible_empty⟩

example (h : M.visible ⊆ M'.visible) (hD : D ∈ M.visibleDenseOpen) :
    D ∈ M'.visibleDenseOpen :=
  visibleDenseOpen_mono h hD

end VisibilityContext

end Forcing
