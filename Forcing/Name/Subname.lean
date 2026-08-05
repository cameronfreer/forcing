/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.Basic

/-!
# The subname relation, well-founded

The structural descent of names: `Subname σ τ` when `σ` is an immediate subname of `τ`. Its
well-foundedness is the recursion principle the atomic forcing kernel runs on — **not** a
numerical or ordinal rank: the actual problem downstream is well-founded recursion on a pair
of names where either coordinate may descend, and the structural relation feeds
`Sym2.GameAdd` directly. A `PName.rank` would be introduced only if the structural approach
genuinely failed; it has not.

## Main definitions

* `Forcing.PName.Subname`: the immediate-subname relation.

## Main results

* `Forcing.PName.subname_wellFounded`: the relation is well-founded.
-/

universe u

namespace Forcing.PName

variable {P : Type u}

/-- `σ` is an immediate subname of `τ`. -/
def Subname (σ τ : PName P) : Prop :=
  ∃ i : τ.Idx, τ.elems i = σ

theorem subname_elems (τ : PName P) (i : τ.Idx) : Subname (τ.elems i) τ :=
  ⟨i, rfl⟩

/-- The subname relation is well-founded: names are well-founded trees. -/
theorem subname_wellFounded : WellFounded (Subname (P := P)) := by
  refine ⟨fun τ ↦ ?_⟩
  induction τ with
  | mk ι e c ih =>
    exact Acc.intro _ fun σ ⟨i, hi⟩ ↦ hi ▸ ih i

end Forcing.PName
