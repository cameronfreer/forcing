/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AssignmentCoding
import Forcing.Material.Semantics

/-!
# Assignment lookup

Reading an entry out of a coded assignment, as a formula.

## A fixed finite block, not a recursion

The compiler runs **per formula**, so the arity and every index are numerals by the time
lookup is emitted. Reading the `i`-th entry is therefore a fixed finite block of existentials,
built by external recursion on the peel count. No internal recursion, no scheme, and no
syntactic substitution — `assignmentCode_snoc` is the whole interface.

## The orientation guard

`assignmentCode` is a **reversed** snoc-list:

```text
assignmentCode (Fin.snoc a i) = ZFSet.pair (N.code i) (assignmentCode a)
```

so the *last* entry is outermost and entry `i` of an arity-`ℓ` assignment is reached by peeling
`ℓ - 1 - i` times. Off-by-one here is invisible — it would surface only as a wrong name in the
universal case.

**The guard is not yet in place.** Only the peel-zero law is proved here. The law pinning
`lookupDef (ℓ - 1 - i)` against `assignmentCode a` and `a i` — which is what makes the index
arithmetic checkable rather than asserted — lands with the compiler that consumes it, since
its statement should be the one the compiler actually needs.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-- `target` is reached from `code` by peeling `peel` second components and taking the first.

The head at each peel is existentially bound and discarded: only the tail matters until the
last step. -/
def lookupDef {α : Type v} {m : ℕ} : ℕ → memLang.Term (α ⊕ Fin m) →
    memLang.Term (α ⊕ Fin m) → memLang.BoundedFormula α m
  | 0, code, target => ∃' (pairDef (liftTerm target) (&(Fin.last m)) (liftTerm code))
  | peel + 1, code, target =>
      ∃' ((∃' (pairDef (&(Fin.last (m + 1))) (&(Fin.castSucc (Fin.last m)))
              (liftTerm (liftTerm code)))) ⊓
        lookupDef peel (&(Fin.last m)) (liftTerm target))

section Realization

variable {α : Type v} {m : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin m → M}

/-- **The lookup law at peel zero**: the target is the first component. -/
theorem realize_lookupDef_zero {code target : memLang.Term (α ⊕ Fin m)} :
    (lookupDef 0 code target).Realize v xs ↔
      ∃ rest, ((Term.realize (Sum.elim v xs) code : ↥M) : ZFSet.{u}) =
        ZFSet.pair ((Term.realize (Sum.elim v xs) target : ↥M) : ZFSet.{u}) rest := by
  have hcM : ((Term.realize (Sum.elim v xs) code : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) code : ↥M).2
  simp only [lookupDef, BoundedFormula.realize_ex, realize_pairDef, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Fin.snoc_last, realize_liftTerm]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨(r : ZFSet.{u}), hr⟩, fun ⟨r, hr⟩ ↦ ?_⟩
  exact ⟨⟨r, MaterialCarrier.right_mem_of_pair_mem (hr ▸ hcM)⟩, hr⟩

end Realization

end Forcing
