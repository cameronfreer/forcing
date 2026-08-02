/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Order.Basic

/-!
# Typed intensional `P`-names

A `PName P` is a set of names, each tagged with the condition that admits it: an inductive tree
mirroring mathlib's `PSet`, with a condition on every branch. This is the raw material of the
generic-extension layer — a name is a set-in-waiting, its branches conditioned on the filter to
come.

Deliberately **intensional** (architecture constraint 6): there is no quotient, no `Setoid`,
and no extensional equality anywhere at this layer. Extensional identifications happen only at
the `ZFSet` end of the valuation (#56).

Equally deliberately, there is no `[Preorder P]` anywhere in this file: the tree structure does
not consult the order, and even valuation uses only membership of conditions in a set. The
order enters the story with genericity, not with names.

## Main definitions

* `Forcing.PName P`: the name type.
* `Forcing.PName.Idx`, `Forcing.PName.elems`, `Forcing.PName.conds`: the branch projections,
  with their `mk` reduction lemmas and the eta rule.
-/

universe u

namespace Forcing

/-- A typed, intensional `P`-name: a set of names, each tagged with the condition that admits
it. Mirrors mathlib's `PSet`, with a condition on every branch. Deliberately **no quotient**:
names are trees, and extensional identifications happen only at the `ZFSet` end of the
valuation. -/
inductive PName (P : Type u) : Type (u + 1) where
  | mk (ι : Type u) (elems : ι → PName P) (conds : ι → P)

namespace PName

variable {P : Type u}

/-- The index type of a name's branches. -/
def Idx : PName P → Type u
  | .mk ι _ _ => ι

/-- The name carried by a branch. -/
def elems : (τ : PName P) → τ.Idx → PName P
  | .mk _ e _ => e

/-- The condition tagging a branch. -/
def conds : (τ : PName P) → τ.Idx → P
  | .mk _ _ c => c

@[simp] theorem Idx_mk (ι : Type u) (e : ι → PName P) (c : ι → P) : (mk ι e c).Idx = ι :=
  rfl

@[simp] theorem elems_mk (ι : Type u) (e : ι → PName P) (c : ι → P) : (mk ι e c).elems = e :=
  rfl

@[simp] theorem conds_mk (ι : Type u) (e : ι → PName P) (c : ι → P) : (mk ι e c).conds = c :=
  rfl

/-- Every name is the `mk` of its projections — the eta rule, for destructing an abstract
name. -/
@[simp] theorem eta : ∀ τ : PName P, mk τ.Idx τ.elems τ.conds = τ
  | .mk _ _ _ => rfl

/-- The empty name: no branches. It will value to the empty set along every condition set. -/
instance : EmptyCollection (PName P) :=
  ⟨mk PEmpty (fun e ↦ e.elim) fun e ↦ e.elim⟩

instance : Inhabited (PName P) :=
  ⟨∅⟩

@[simp] theorem Idx_empty : (∅ : PName P).Idx = PEmpty :=
  rfl

/-!
### Sanity examples

Structural recursion over names needs no well-founded plumbing: the projections above are
structural matches, and concrete names build and destruct directly.
-/

example : PName Bool :=
  mk Bool (fun _ ↦ ∅) id

example : (mk Bool (fun _ ↦ (∅ : PName Bool)) id).conds true = true :=
  rfl

example (τ : PName P) (i : τ.Idx) : PName P :=
  τ.elems i

end PName

end Forcing
