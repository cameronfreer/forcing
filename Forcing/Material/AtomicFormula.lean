/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.RecursionFormula

/-!
# The atomic definitions

The internal formulas 3b promises, in two layers.

**Relative to a supplied domain** — `memWitnessDefOn`, `forcesEqDefOn`, `forcesMemDefOn` — each
taking `A` as a material parameter and existentially hiding the graph.

**Uniform** — `memWitnessDef`, `forcesEqDef`, `forcesMemDef` — hiding the domain too, so the
public formulas have **seven** parameters and a theorem stated with them is uniform in the
condition *and* the name codes. That is ADR 0005's stated target, and it is what the formula
compiler needs: an assignment ranges over all names, and there is deliberately no single
material set containing every name code.

## Why the graph is hidden

Soundness holds for *whichever* coherent graph the formula supplies, because conditional
correctness applies to every graph coherent over the domain; completeness has a graph to offer
because the construction certificate produces one. Neither direction needs graph uniqueness, so
no reusable graph framework leaks into the formula interface.

Every realization law here is **axiom-free apart from the two tag equations**.
-/

universe u v

namespace Forcing

open FirstOrder Language

namespace AtomicRecursion

variable {α : Type v} {n : ℕ}

/-! ### The atomic definitions over a supplied domain

The three internal formulas 3b promises. Each takes the domain `A` as a **material
parameter** and **existentially hides** the graph.

Hiding `R` is what keeps the API honest. Soundness holds for *whichever* coherent graph the
formula happens to supply, because conditional correctness applies to every one of them; and
completeness has a graph to offer because the construction certificate produces one. Neither
direction needs graph uniqueness, so no reusable graph framework leaks into the formula
interface. -/

/-- **Internal membership-witness**, over the domain `A`. -/
def memWitnessDefOn (tagMem tagEq condSet orderCode A p x y :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (atomicCoherentOnDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
      (liftTerm orderCode) (liftTerm A) (&(Fin.last n)) ⊓
    entryMemDef (liftTerm tagMem) (liftTerm p) (liftTerm x) (liftTerm y) (&(Fin.last n)))

/-- **Internal forced equality**, over the domain `A`. -/
def forcesEqDefOn (tagMem tagEq condSet orderCode A p x y :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (atomicCoherentOnDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
      (liftTerm orderCode) (liftTerm A) (&(Fin.last n)) ⊓
    entryMemDef (liftTerm tagEq) (liftTerm p) (liftTerm x) (liftTerm y) (&(Fin.last n)))

/-- **Internal forced membership**, over the domain `A`: the *density* of the membership
slice, which is where forced membership lives. -/
def forcesMemDefOn (tagMem tagEq condSet orderCode A p x y :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (atomicCoherentOnDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
      (liftTerm orderCode) (liftTerm A) (&(Fin.last n)) ⊓
    denseMemDef (liftTerm condSet) (liftTerm orderCode) (liftTerm tagMem) (&(Fin.last n))
      (liftTerm p) (liftTerm x) (liftTerm y))

/-! ### The uniform atomic definitions

The `…DefOn` formulas above are relative to a supplied domain, so a theorem stated with them is
uniform in the condition but **not** in the name codes: the domain varies with the pair.

These wrappers close that gap by hiding the domain too, asserting its transitivity and the
codes' membership as conjuncts. The public formulas then have **seven** parameters — two tags,
condition set, order code, condition, and the two codes — and the resulting theorem is uniform
in all of them. That is what ADR 0005 asked for, and what the formula compiler needs: an
assignment ranges over all names, and there is deliberately no single material set containing
every name code. -/

/-- **Internal membership-witness**, uniform: the domain is hidden. -/
def memWitnessDef (tagMem tagEq condSet orderCode p x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' (transitiveDef (&(Fin.last n)) ⊓
    (memFormula (liftTerm x) (&(Fin.last n)) ⊓
      (memFormula (liftTerm y) (&(Fin.last n)) ⊓
        memWitnessDefOn (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (&(Fin.last n)) (liftTerm p) (liftTerm x) (liftTerm y))))

/-- **Internal forced equality**, uniform. -/
def forcesEqDef (tagMem tagEq condSet orderCode p x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' (transitiveDef (&(Fin.last n)) ⊓
    (memFormula (liftTerm x) (&(Fin.last n)) ⊓
      (memFormula (liftTerm y) (&(Fin.last n)) ⊓
        forcesEqDefOn (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (&(Fin.last n)) (liftTerm p) (liftTerm x) (liftTerm y))))

/-- **Internal forced membership**, uniform. -/
def forcesMemDef (tagMem tagEq condSet orderCode p x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' (transitiveDef (&(Fin.last n)) ⊓
    (memFormula (liftTerm x) (&(Fin.last n)) ⊓
      (memFormula (liftTerm y) (&(Fin.last n)) ⊓
        forcesMemDefOn (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (&(Fin.last n)) (liftTerm p) (liftTerm x) (liftTerm y))))


section Realization

variable {M : MaterialCarrier.{u}} {x y : memLang.Term (α ⊕ Fin n)}
variable {v : α → M} {xs : Fin n → M}

open MaterialCarrier

/-! ### Realization of the atomic definitions

All three are **axiom-free apart from the two tag equations**. The existential over graphs is
carrier-valued, which is the honest reading: the formula asserts a coherent graph *inside the
ground*. -/

/-- **The internal membership-witness law.** -/
theorem realize_memWitnessDefOn
    {tagMem tagEq condSet orderCode A p : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (memWitnessDefOn tagMem tagEq condSet orderCode A p x y).Realize v xs ↔
      ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
        entry memWitnessTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
  have hco : ∀ R : ↥M,
      (atomicCoherentOnDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (liftTerm A) (&(Fin.last n))).Realize v (Fin.snoc xs R) ↔
        AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) := by
    intro R
    rw [realize_atomicCoherentOnDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  have hent : ∀ R : ↥M,
      (entryMemDef (liftTerm tagMem) (liftTerm p) (liftTerm x) (liftTerm y)
          (&(Fin.last n))).Realize v (Fin.snoc xs R) ↔
        entry memWitnessTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
    intro R
    rw [realize_entryMemDef_natCode (by simpa [realize_liftTerm] using hm)]
    simp [realize_liftTerm]
  simp only [memWitnessDefOn, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  exact ⟨fun ⟨R, hc, he⟩ ↦ ⟨R, (hco R).1 hc, (hent R).1 he⟩,
    fun ⟨R, hc, he⟩ ↦ ⟨R, (hco R).2 hc, (hent R).2 he⟩⟩

/-- **The internal forced-equality law.** -/
theorem realize_forcesEqDefOn
    {tagMem tagEq condSet orderCode A p : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesEqDefOn tagMem tagEq condSet orderCode A p x y).Realize v xs ↔
      ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
        entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
  have hco : ∀ R : ↥M,
      (atomicCoherentOnDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (liftTerm A) (&(Fin.last n))).Realize v (Fin.snoc xs R) ↔
        AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) := by
    intro R
    rw [realize_atomicCoherentOnDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  have hent : ∀ R : ↥M,
      (entryMemDef (liftTerm tagEq) (liftTerm p) (liftTerm x) (liftTerm y)
          (&(Fin.last n))).Realize v (Fin.snoc xs R) ↔
        entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
    intro R
    rw [realize_entryMemDef_natCode (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [forcesEqDefOn, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  exact ⟨fun ⟨R, hc, he⟩ ↦ ⟨R, (hco R).1 hc, (hent R).1 he⟩,
    fun ⟨R, hc, he⟩ ↦ ⟨R, (hco R).2 hc, (hent R).2 he⟩⟩

/-- **The internal forced-membership law.** -/
theorem realize_forcesMemDefOn
    {tagMem tagEq condSet orderCode A p : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesMemDefOn tagMem tagEq condSet orderCode A p x y).Realize v xs ↔
      ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
        DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  have hco : ∀ R : ↥M,
      (atomicCoherentOnDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (liftTerm A) (&(Fin.last n))).Realize v (Fin.snoc xs R) ↔
        AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) := by
    intro R
    rw [realize_atomicCoherentOnDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  have hden : ∀ R : ↥M,
      (denseMemDef (liftTerm condSet) (liftTerm orderCode) (liftTerm tagMem) (&(Fin.last n))
          (liftTerm p) (liftTerm x) (liftTerm y)).Realize v (Fin.snoc xs R) ↔
        DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
    intro R
    rw [realize_denseMemDef (by simpa [realize_liftTerm] using hm)]
    simp [realize_liftTerm]
  simp only [forcesMemDefOn, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  exact ⟨fun ⟨R, hc, hd⟩ ↦ ⟨R, (hco R).1 hc, (hden R).1 hd⟩,
    fun ⟨R, hc, hd⟩ ↦ ⟨R, (hco R).2 hc, (hden R).2 hd⟩⟩

/-! ### Realization of the uniform definitions

Also axiom-free apart from the tag equations. Each says: some transitive carrier element
contains both codes and carries a coherent graph with the required entry. -/

/-- **The uniform membership-witness law.** -/
theorem realize_memWitnessDef
    {tagMem tagEq condSet orderCode p : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (memWitnessDef tagMem tagEq condSet orderCode p x y).Realize v xs ↔
      ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
        ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
          entry memWitnessTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈
            ((R : ↥M) : ZFSet.{u}) := by
  have hinner : ∀ A : ↥M,
      (memWitnessDefOn (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
          (&(Fin.last n)) (liftTerm p) (liftTerm x) (liftTerm y)).Realize v
        (Fin.snoc xs A) ↔
        ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
          entry memWitnessTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
    intro A
    rw [realize_memWitnessDefOn (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [memWitnessDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm, realize_transitiveDef]
  exact ⟨fun ⟨A, ht, hxA, hyA, hQ⟩ ↦ ⟨A, ht, hxA, hyA, (hinner A).1 hQ⟩,
    fun ⟨A, ht, hxA, hyA, hQ⟩ ↦ ⟨A, ht, hxA, hyA, (hinner A).2 hQ⟩⟩

/-- **The uniform forced-equality law.** -/
theorem realize_forcesEqDef
    {tagMem tagEq condSet orderCode p : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesEqDef tagMem tagEq condSet orderCode p x y).Realize v xs ↔
      ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
        ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
          entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈
            ((R : ↥M) : ZFSet.{u}) := by
  have hinner : ∀ A : ↥M,
      (forcesEqDefOn (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
          (&(Fin.last n)) (liftTerm p) (liftTerm x) (liftTerm y)).Realize v
        (Fin.snoc xs A) ↔
        ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
          entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
    intro A
    rw [realize_forcesEqDefOn (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [forcesEqDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm, realize_transitiveDef]
  exact ⟨fun ⟨A, ht, hxA, hyA, hQ⟩ ↦ ⟨A, ht, hxA, hyA, (hinner A).1 hQ⟩,
    fun ⟨A, ht, hxA, hyA, hQ⟩ ↦ ⟨A, ht, hxA, hyA, (hinner A).2 hQ⟩⟩

/-- **The uniform forced-membership law.** -/
theorem realize_forcesMemDef
    {tagMem tagEq condSet orderCode p : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesMemDef tagMem tagEq condSet orderCode p x y).Realize v xs ↔
      ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
        ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
          DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  have hinner : ∀ A : ↥M,
      (forcesMemDefOn (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
          (&(Fin.last n)) (liftTerm p) (liftTerm x) (liftTerm y)).Realize v
        (Fin.snoc xs A) ↔
        ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
          DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
    intro A
    rw [realize_forcesMemDefOn (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [forcesMemDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm, realize_transitiveDef]
  exact ⟨fun ⟨A, ht, hxA, hyA, hQ⟩ ↦ ⟨A, ht, hxA, hyA, (hinner A).1 hQ⟩,
    fun ⟨A, ht, hxA, hyA, hQ⟩ ↦ ⟨A, ht, hxA, hyA, (hinner A).2 hQ⟩⟩


end Realization

end AtomicRecursion

end Forcing
