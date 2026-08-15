/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Recursion
import Forcing.Material.Semantics

/-!
# The recursion formulas: entries

The formula layer of the atomic recursion, built bottom-up with a realization theorem at each
step. This module owns the **entry** formulas; they are specific to the tagged graph
representation, so unlike the pair builders they stay inside `AtomicRecursion` rather than
enlarging the shared syntax API.

Realization comes in two stages. The **arbitrary-tag** law keeps the syntax reusable — it
says only that the fifth term names the nested pair. The **specialization at a numeral tag**
connects it to the existing graph API, turning the formula into a statement about
`AtomicRecursion.entry`.

No material constants and no subtype-valued tag definitions are introduced here: the
realization theorems accept whatever tag value the carrier already holds, and the existence
proof later supplies numerals through `natCode_mem`, paying the finite-closure cost there.
Everything here is **universe-polymorphic**, matching the material presentations: the
recursion is certified for `MaterialGround.{u}` and `P : Type u`, not only at universe zero.
This is same-universe generality, so no `Cardinal.lift`-style residue appears (the
cross-universe lifting declined in ADR 0002 is a different question).

**This layer imports no axiom sentences**, and its realization laws consume none: every
intermediate set a backward direction needs is a member of a member, so repeated transitivity
supplies it.

## Main definitions

* `Forcing.AtomicRecursion.entryDef`, `Forcing.AtomicRecursion.entryMemDef`.

## Main results

* `Forcing.AtomicRecursion.realize_entryDef`: the arbitrary-tag law.
* `Forcing.AtomicRecursion.realize_entryDef_natCode`,
  `Forcing.AtomicRecursion.realize_entryMemDef_natCode`: the graph-API specializations.
-/

universe u v

namespace Forcing

namespace AtomicRecursion

open FirstOrder Language

variable {α : Type v} {n : ℕ}

/-- `e` names the tagged entry `⟨tag, ⟨p, ⟨x, y⟩⟩⟩`. The two intermediate pairs are
quantified inside the builder. -/
def entryDef (tag p x y e : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (liftTerm (liftTerm x)) (liftTerm (liftTerm y))
        (&(Fin.castSucc (Fin.last n))) ⊓
      (pairDef (liftTerm (liftTerm p)) (&(Fin.castSucc (Fin.last n)))
        (&(Fin.last (n + 1))) ⊓
      pairDef (liftTerm (liftTerm tag)) (&(Fin.last (n + 1))) (liftTerm (liftTerm e))))

/-- The tagged entry belongs to `R`. The lifting under the existential is confined here, so
the clause builders never repeat it. -/
def entryMemDef (tag p x y R : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (entryDef (liftTerm tag) (liftTerm p) (liftTerm x) (liftTerm y) (&(Fin.last n)) ⊓
    memFormula (&(Fin.last n)) (liftTerm R))

/-- A pair belongs to `S`. Private: branch and order membership use it repeatedly, but it
need not enlarge the shared syntax API yet. -/
private def pairMemDef (x y S : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (pairDef (liftTerm x) (liftTerm y) (&(Fin.last n)) ⊓ memFormula (&(Fin.last n)) (liftTerm S))

/-- **The density clause**, as a formula: every strengthening of `q` inside the condition set
has a further strengthening carrying a tagged entry. The tag is an arbitrary term; realization
specializes it. -/
def denseMemDef (condSet orderCode tag R q x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm condSet) ⟹
    (pairMemDef (&(Fin.last n)) (liftTerm q) (liftTerm orderCode) ⟹
      ∃' (memFormula (&(Fin.last (n + 1))) (liftTerm (liftTerm condSet)) ⊓
        (pairMemDef (&(Fin.last (n + 1))) (&(Fin.castSucc (Fin.last n)))
            (liftTerm (liftTerm orderCode)) ⊓
          entryMemDef (liftTerm (liftTerm tag)) (&(Fin.last (n + 1)))
            (liftTerm (liftTerm x)) (liftTerm (liftTerm y)) (liftTerm (liftTerm R))))))

section Realization

variable {M : MaterialCarrier.{u}} {tag p x y e R S : memLang.Term (α ⊕ Fin n)}
variable {v : α → M} {xs : Fin n → M}

/-- The right component of a Kuratowski pair in the carrier is in the carrier — repeated
transitivity, no axiom. -/
private theorem right_mem_of_pair_mem {a b : ZFSet.{u}} (h : ZFSet.pair a b ∈ M) : b ∈ M :=
  M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
    (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) h)

/-- **The arbitrary-tag entry law**: the formula says exactly that `e` names the nested
pair. -/
theorem realize_entryDef :
    (entryDef tag p x y e).Realize v xs ↔
      ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
        ZFSet.pair ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u})
          (ZFSet.pair ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            (ZFSet.pair ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}))) := by
  simp only [entryDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, realize_pairDef,
    realize_liftTerm, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc]
  constructor
  · rintro ⟨w₂, w₁, h₂, h₁, he⟩
    rw [he, h₁, h₂]
  · intro he
    have heM : ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) ∈ M :=
      (Term.realize (Sum.elim v xs) e : ↥M).2
    rw [he] at heM
    have h₁M := right_mem_of_pair_mem heM
    have h₂M := right_mem_of_pair_mem h₁M
    exact ⟨⟨_, h₂M⟩, ⟨_, h₁M⟩, rfl, rfl, he⟩

/-- Pair membership: the formula says the pair lies in `S`. Backward direction axiom-free —
the pair is a member of a member. -/
private theorem realize_pairMemDef :
    (pairMemDef x y S).Realize v xs ↔
      ZFSet.pair ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈
        ((Term.realize (Sum.elim v xs) S : ↥M) : ZFSet.{u}) := by
  simp only [pairMemDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairDef, realize_liftTerm]
  constructor
  · rintro ⟨w, hw, hmem⟩
    rw [← hw]
    exact hmem
  · intro hmem
    have hSM : ((Term.realize (Sum.elim v xs) S : ↥M) : ZFSet.{u}) ∈ M :=
      (Term.realize (Sum.elim v xs) S : ↥M).2
    exact ⟨⟨_, M.mem_trans hmem hSM⟩, rfl, hmem⟩

/-- **Specialization at a numeral tag**: the formula becomes a statement about the graph
API's `entry`. -/
theorem realize_entryDef_natCode {t : ℕ}
    (htag : ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u}) = natCode t) :
    (entryDef tag p x y e).Realize v xs ↔
      ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
        entry t ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  rw [realize_entryDef, htag, entry]

/-- **Entry membership, at a numeral tag**: the formula says the coded entry lies in `R`. The
backward direction is axiom-free — the entry is a member of a member. -/
theorem realize_entryMemDef_natCode {t : ℕ}
    (htag : ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u}) = natCode t) :
    (entryMemDef tag p x y R).Realize v xs ↔
      entry t ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈
      ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
  simp only [entryMemDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨w, hw, hmem⟩
    rw [realize_entryDef_natCode (by simpa [realize_liftTerm] using htag)] at hw
    simp only [realize_liftTerm] at hw
    rw [← hw]
    simpa [realize_liftTerm] using hmem
  · intro hmem
    have hRM : ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) ∈ M :=
      (Term.realize (Sum.elim v xs) R : ↥M).2
    refine ⟨⟨_, M.mem_trans hmem hRM⟩, ?_, ?_⟩
    · rw [realize_entryDef_natCode (by simpa [realize_liftTerm] using htag)]
      simp [realize_liftTerm]
    · simpa [realize_liftTerm] using hmem

/-- **The density-clause law**, and its orientation test: the formula realizes to exactly the
semantic `DenseMem`, with `r` strengthening `q` in the hypothesis and `s` strengthening `r` in
the conclusion. Carrier transitivity bridges the quantifiers — the formula ranges over carrier
elements, the predicate over sets — and **no transitivity hypothesis and no theory axiom are
consumed**. -/
theorem realize_denseMemDef {condSet orderCode q : memLang.Term (α ⊕ Fin n)}
    (htag : ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u}) = natCode memWitnessTag) :
    (denseMemDef condSet orderCode tag R q x y).Realize v xs ↔
      DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) q : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  have hcM : ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) condSet : ↥M).2
  have hent : ∀ r s : ↥M,
      (entryMemDef (liftTerm (liftTerm tag)) (&(Fin.last (n + 1)))
          (liftTerm (liftTerm x)) (liftTerm (liftTerm y))
          (liftTerm (liftTerm R))).Realize v (Fin.snoc (Fin.snoc xs r) s) ↔
        entry memWitnessTag ((s : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
    intro r s
    rw [realize_entryMemDef_natCode (by simpa [realize_liftTerm] using htag)]
    simp [realize_liftTerm]
  simp only [denseMemDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_pairMemDef, realize_liftTerm]
  constructor
  · intro h r hr hrq
    obtain ⟨s, hs, hsr, he⟩ := h ⟨r, M.mem_trans hr hcM⟩ hr hrq
    exact ⟨(s : ZFSet.{u}), hs, hsr, (hent _ s).1 he⟩
  · intro h r hr hrq
    obtain ⟨s, hs, hsr, he⟩ := h (r : ZFSet.{u}) hr hrq
    exact ⟨⟨s, M.mem_trans hs hcM⟩, hs, hsr, (hent _ ⟨s, M.mem_trans hs hcM⟩).2 he⟩

/-- **Tag placement pressure test**: no encoded entry satisfies both tagged relations with
identical remaining components — so tag placement, not merely pair nesting, matches
`entry_memWitness_ne_eq`. -/
example
    (h₁ : ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
      entry memWitnessTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}))
    (h₂ : ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
      entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})) : False :=
  entry_memWitness_ne_eq (h₁.symm.trans h₂)

end Realization

end AtomicRecursion

end Forcing
