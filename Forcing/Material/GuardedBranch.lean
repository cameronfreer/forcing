/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Semantics

/-!
# The guarded branch below a condition

One formula builder with two consumers:

```text
unionInnerDef cs ord s ρ σ := ∃ r, ⟨r, ρ⟩ ∈ σ ∧ r ∈ cs ∧ ⟨s, r⟩ ∈ ord
```

`σ` has a branch at `ρ` whose condition `r` is guarded by `cs` and weakens `s` in `order_iff`'s
orientation. The union name (`Forcing/Material/UnionName.lean`) uses it as the inner branch of a
branch; the separation name (`Forcing/Material/SeparationName.lean`) uses it as the source branch
of the separated set. It lives here, apart from both, so neither imports the other. Moved
unchanged from `UnionName.lean`.

## Main definitions

* `Forcing.unionInnerDef`.

## Main results

* `Forcing.realize_unionInnerDef`: exact, with no validity or theory hypothesis.
-/

universe u v

namespace Forcing

open FirstOrder Language

section Syntax

variable {α : Type v} {n : ℕ}

/-- `∃ r, ⟨r, ρ⟩ ∈ σ ∧ r ∈ cs ∧ ⟨s, r⟩ ∈ ord`. -/
def unionInnerDef (cs ord s ρ σ : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (pairMemDef (&(Fin.last n)) (liftTerm ρ) (liftTerm σ) ⊓
    (memFormula (&(Fin.last n)) (liftTerm cs) ⊓
      pairMemDef (liftTerm s) (&(Fin.last n)) (liftTerm ord)))

end Syntax

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

end Realization

end Forcing
