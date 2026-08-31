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

`realize_lookupDef_assignmentCode` is that guard: it pins `lookupDef (ℓ - 1 - i)`, read at a
term realizing to `assignmentCode a`, to exactly `N.code (a i)`. Both directions, every peel,
every index. An off-by-one would make it unprovable rather than merely wrong downstream.

## Main results

* `Forcing.LookupAt`: peeling, semantically.
* `Forcing.realize_lookupDef`: the formula realizes exactly that, at every peel.
* `Forcing.realize_lookupDef_assignmentCode`: the orientation guard, against `assignmentCode`.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-- **Lookup, semantically**: `target` is reached from `code` by peeling `peel` second
components and taking the first. Named separately so the induction certifying the index
arithmetic runs on sets, not on formulas at shifting bound-variable depths. -/
def LookupAt : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, code, target => ∃ rest, code = ZFSet.pair target rest
  | peel + 1, code, target =>
      ∃ rest, (∃ hd, code = ZFSet.pair hd rest) ∧ LookupAt peel rest target

/-- Lookup is functional: pairs determine their components. -/
theorem LookupAt.unique : ∀ {peel : ℕ} {code t t' : ZFSet.{u}},
    LookupAt peel code t → LookupAt peel code t' → t = t'
  | 0, _, _, _, ⟨_, h⟩, ⟨_, h'⟩ => (ZFSet.pair_inj.1 (h.symm.trans h')).1
  | _ + 1, _, _, _, ⟨r, ⟨_, hr⟩, ht⟩, ⟨r', ⟨_, hr'⟩, ht'⟩ => by
      obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 (hr.symm.trans hr')
      exact LookupAt.unique ht ht'

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

/-- **The lookup law**: the formula realizes exactly the semantic lookup, at every peel. -/
theorem realize_lookupDef : ∀ {m : ℕ} {xs : Fin m → M} (peel : ℕ)
    (code target : memLang.Term (α ⊕ Fin m)),
    (lookupDef peel code target).Realize v xs ↔
      LookupAt peel ((Term.realize (Sum.elim v xs) code : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) target : ↥M) : ZFSet.{u})
  | m, xs, 0, code, target => by
      have hcM : ((Term.realize (Sum.elim v xs) code : ↥M) : ZFSet.{u}) ∈ M :=
        (Term.realize (Sum.elim v xs) code : ↥M).2
      simp only [lookupDef, LookupAt, BoundedFormula.realize_ex, realize_pairDef,
        Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, realize_liftTerm]
      refine ⟨fun ⟨r, hr⟩ ↦ ⟨(r : ZFSet.{u}), hr⟩, fun ⟨r, hr⟩ ↦ ?_⟩
      exact ⟨⟨r, MaterialCarrier.right_mem_of_pair_mem (hr ▸ hcM)⟩, hr⟩
  | m, xs, peel + 1, code, target => by
      have hcM : ((Term.realize (Sum.elim v xs) code : ↥M) : ZFSet.{u}) ∈ M :=
        (Term.realize (Sum.elim v xs) code : ↥M).2
      have hstep : ∀ r : ↥M,
          (lookupDef peel (&(Fin.last m)) (liftTerm target)).Realize v (Fin.snoc xs r) ↔
            LookupAt peel ((r : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) target : ↥M) : ZFSet.{u}) := by
        intro r
        rw [realize_lookupDef peel]
        simp [realize_liftTerm]
      simp only [lookupDef, LookupAt, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
        realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
        Fin.snoc_castSucc, realize_liftTerm]
      constructor
      · rintro ⟨r, ⟨hd, hpair⟩, htail⟩
        exact ⟨(r : ZFSet.{u}), ⟨(hd : ZFSet.{u}), hpair⟩, (hstep r).1 htail⟩
      · rintro ⟨r, ⟨hd, hpair⟩, htail⟩
        have hrM : r ∈ M := MaterialCarrier.right_mem_of_pair_mem (hpair ▸ hcM)
        have hdM : hd ∈ M := MaterialCarrier.left_mem_of_pair_mem (hpair ▸ hcM)
        exact ⟨⟨r, hrM⟩, ⟨⟨hd, hdM⟩, hpair⟩, (hstep ⟨r, hrM⟩).2 htail⟩

end Realization

section Assignment

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P}

/-- **The orientation fact**: entry `i` of an arity-`ℓ` assignment sits under `ℓ - 1 - i`
peels. The reversed-snoc convention is what makes this the right arithmetic. -/
theorem lookupAt_assignmentCode : ∀ {ℓ : ℕ} (a : Fin ℓ → N.Code) (i : Fin ℓ),
    LookupAt (ℓ - 1 - (i : ℕ)) (N.assignmentCode a) (N.code (a i))
  | 0, _, i => i.elim0
  | n + 1, a, i => by
      have hunfold : N.assignmentCode a =
          ZFSet.pair (N.code (a (Fin.last n))) (N.assignmentCode (Fin.init a)) := by
        rw [InternalNamePresentation.assignmentCode]
      refine Fin.lastCases ?_ ?_ i
      · simp [LookupAt, hunfold]
      · intro j
        have harith : n + 1 - 1 - (j.castSucc : ℕ) = (n - 1 - (j : ℕ)) + 1 := by
          have := j.isLt; simp only [Fin.val_castSucc]; omega
        have hinit : (Fin.init a) j = a j.castSucc := rfl
        rw [harith, hunfold]
        exact ⟨N.assignmentCode (Fin.init a), ⟨_, rfl⟩, hinit ▸ lookupAt_assignmentCode _ j⟩

variable {α : Type v} {m : ℕ} {v : α → M} {xs : Fin m → M}

/-- **The orientation guard.** Read at a term realizing to `N.assignmentCode a`, the lookup
formula at peel `ℓ - 1 - i` holds of exactly `N.code (a i)` — soundness and no junk. -/
theorem realize_lookupDef_assignmentCode {ℓ : ℕ} (a : Fin ℓ → N.Code) (i : Fin ℓ)
    (code target : memLang.Term (α ⊕ Fin m))
    (hcode : ((Term.realize (Sum.elim v xs) code : ↥M) : ZFSet.{u}) = N.assignmentCode a) :
    (lookupDef (ℓ - 1 - (i : ℕ)) code target).Realize v xs ↔
      ((Term.realize (Sum.elim v xs) target : ↥M) : ZFSet.{u}) = N.code (a i) := by
  rw [realize_lookupDef, hcode]
  refine ⟨fun h ↦ LookupAt.unique h (lookupAt_assignmentCode a i), fun h ↦ ?_⟩
  exact h ▸ lookupAt_assignmentCode a i

end Assignment

end Forcing
