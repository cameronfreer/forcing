/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicRealized
import Forcing.Name.AtomicAdequacy
import Forcing.Order.Localize

/-!
# The atomic test codes

M7 item 4a: the two atomic visibility tests of `truth_lemma_of_genericOver`, as internal
formulas over the presentation's fixed codes, each with its externalization law and its
Separation-instance code.

```text
localizeBelow (memWitness τ σ) p   ↦  memLocalizeDef  …  ↦  memLocalizeTest
eqDecision τ σ                     ↦  eqDecisionDef   …  ↦  eqDecisionTest
```

## Recognizer-independent, not name-coding-independent

The name codes are fixed parameters, so nothing here needs an `InternalNameRecognition`. But the
equality obstructions inspect **coded branches** of a name, and that is
`InternalNameCoding.branch_mem_code_iff`: a named input, consumed at exactly the site that reads a
branch out of `N.code i`.

## The guardrail: every internal condition quantifier carries `q ∈ condSet`

`orderCode` has **no global no-junk law** — `order_iff` speaks only of pairs of already-typed
codes — so an internal quantifier over conditions guarded by an order-code fact alone would impose
an obligation at a carrier element that is not a condition, and the externalization would be
false in a presentation carrying such a pair (#223). Every quantified condition below therefore
carries condition-set membership alongside its order-code fact:

* the witness in `lowerClosure` (`belowWitnessDef`);
* the common strengthening in `Compatible` (`compatibleDef`);
* the branch condition and the inner strengthening in `eqObstruction` (`branchObstructionDef`,
  `noMemBelowDef`).

Each externalization theorem is that guard's pressure test: it is provable only because the
guard is there, and it also pins the orientation of every order-code pair.

## Two layers

The externalization laws are stated over a `MaterialCarrier`, parameterized by the atomic
equivalences of `Forcing/Material/AtomicRealized.lean`, consumed as black boxes. The material
theorems then supply those from `atomicRealized_iff` and the code itself from a single Separation
instance per test. The dense-open facts (`isDenseOpen_localizeBelow`, `isDenseOpen_eqDecision`)
stay external consequences; they never enter the construction.

## Main results

* `Forcing.memLocalizeDef`, `Forcing.eqDecisionDef`: the two test formulas, term-parameterized.
* `Forcing.externalize_memLocalize`, `Forcing.externalize_eqDecision`: the externalization laws.
* `Forcing.MaterialGround.exists_memLocalizeCode`, `…exists_eqDecisionCode`: an `InternalSubset`
  externalizing to each test, on `atomicDefinability`'s ledger plus one Separation instance.
-/

universe u v

namespace Forcing

open FirstOrder Language AtomicRecursion

/-! ### The formulas -/

section Syntax

variable {α : Type v} {n : ℕ}

/-- `∃ r ∈ condSet, ⟨q, r⟩ ∈ orderCode ∧ MemWitness r x y`: `q` lies below a membership
witness. The `lowerClosure` half of `localizeBelow`, with its witness guarded. -/
def belowWitnessDef (tagMem tagEq condSet orderCode q x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' (memFormula (&(Fin.last n)) (liftTerm condSet) ⊓
    (pairMemDef (liftTerm q) (&(Fin.last n)) (liftTerm orderCode) ⊓
      memWitnessDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
        (&(Fin.last n)) (liftTerm x) (liftTerm y)))

/-- `∃ r ∈ condSet, ⟨r, q⟩ ∈ orderCode ∧ ⟨r, p⟩ ∈ orderCode`: `q` and `p` are compatible, with
the common strengthening guarded. -/
def compatibleDef (condSet orderCode q p : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' (memFormula (&(Fin.last n)) (liftTerm condSet) ⊓
    (pairMemDef (&(Fin.last n)) (liftTerm q) (liftTerm orderCode) ⊓
      pairMemDef (&(Fin.last n)) (liftTerm p) (liftTerm orderCode)))

/-- **The localized membership test**: `q ∈ localizeBelow (memWitness x y) p` — below a
witness, or incompatible with `p`. -/
def memLocalizeDef (tagMem tagEq condSet orderCode p x y q : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  belowWitnessDef tagMem tagEq condSet orderCode q x y ⊔ ∼(compatibleDef condSet orderCode q p)

/-- `∀ s ∈ condSet, ⟨s, r⟩ ∈ orderCode → ¬ ForcesMem s e y`: no strengthening of `r` forces
`e ∈ y`, with the strengthening guarded. -/
def noMemBelowDef (tagMem tagEq condSet orderCode r e y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm condSet) ⟹
    (pairMemDef (&(Fin.last n)) (liftTerm r) (liftTerm orderCode) ⟹
      ∼(forcesMemDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
        (&(Fin.last n)) (liftTerm e) (liftTerm y))))

/-- `∃ c e, b = ⟨c, e⟩ ∧ c ∈ condSet ∧ ⟨r, c⟩ ∈ orderCode ∧ noMemBelow r e y`: the branch `b`
is activated by `r` and its subname is blocked from `y` below `r`. The branch condition is
guarded even though the pair law will pin it, so the guardrail is applied without exception. -/
def branchObstructionDef (tagMem tagEq condSet orderCode r b y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
        (liftTerm (liftTerm b)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm condSet)) ⊓
      (pairMemDef (liftTerm (liftTerm r)) (&(Fin.castSucc (Fin.last n)))
          (liftTerm (liftTerm orderCode)) ⊓
        noMemBelowDef (liftTerm (liftTerm tagMem)) (liftTerm (liftTerm tagEq))
          (liftTerm (liftTerm condSet)) (liftTerm (liftTerm orderCode))
          (liftTerm (liftTerm r)) (&(Fin.last (n + 1))) (liftTerm (liftTerm y)))))

/-- `r ∈ eqObstruction x y`: some branch of `x` is activated by `r` and blocked from `y`. -/
def eqObstructionDef (tagMem tagEq condSet orderCode r x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' (memFormula (&(Fin.last n)) (liftTerm x) ⊓
    branchObstructionDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
      (liftTerm orderCode) (liftTerm r) (&(Fin.last n)) (liftTerm y))

/-- **The equality decision test**: `r ∈ eqDecision x y` — forced equality, or an obstruction
on either side. -/
def eqDecisionDef (tagMem tagEq condSet orderCode r x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  forcesEqDef tagMem tagEq condSet orderCode r x y ⊔
    (eqObstructionDef tagMem tagEq condSet orderCode r x y ⊔
      eqObstructionDef tagMem tagEq condSet orderCode r y x)

end Syntax

/-! ### Realization, on sets -/

section Realization

variable {α : Type v} {n : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin n → M}
variable {tagMem tagEq condSet orderCode : memLang.Term (α ⊕ Fin n)}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

theorem realize_belowWitnessDef {q x y : memLang.Term (α ⊕ Fin n)}
    (hm : ⟪tagMem⟫ = natCode memWitnessTag) (hq : ⟪tagEq⟫ = natCode eqTag) :
    (belowWitnessDef tagMem tagEq condSet orderCode q x y).Realize v xs ↔
      ∃ r : ↥M, (r : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪q⟫ (r : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
        AtomicMemWitnessRealized M ⟪condSet⟫ ⟪orderCode⟫ (r : ZFSet.{u}) ⟪x⟫ ⟪y⟫ := by
  have hw : ∀ r : ↥M,
      (memWitnessDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
        (&(Fin.last n)) (liftTerm x) (liftTerm y)).Realize v (Fin.snoc xs r) ↔
      AtomicMemWitnessRealized M ⟪condSet⟫ ⟪orderCode⟫ (r : ZFSet.{u}) ⟪x⟫ ⟪y⟫ := by
    intro r
    rw [realize_memWitnessDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm, AtomicMemWitnessRealized]
  simp only [belowWitnessDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, realize_liftTerm]
  exact exists_congr fun r ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ hw r

theorem realize_compatibleDef {q p : memLang.Term (α ⊕ Fin n)} :
    (compatibleDef condSet orderCode q p).Realize v xs ↔
      ∃ r : ↥M, (r : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair (r : ZFSet.{u}) ⟪q⟫ ∈ ⟪orderCode⟫ ∧
        ZFSet.pair (r : ZFSet.{u}) ⟪p⟫ ∈ ⟪orderCode⟫ := by
  simp only [compatibleDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, realize_liftTerm]

theorem realize_memLocalizeDef {p x y q : memLang.Term (α ⊕ Fin n)}
    (hm : ⟪tagMem⟫ = natCode memWitnessTag) (hq : ⟪tagEq⟫ = natCode eqTag) :
    (memLocalizeDef tagMem tagEq condSet orderCode p x y q).Realize v xs ↔
      (∃ r : ↥M, (r : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪q⟫ (r : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
        AtomicMemWitnessRealized M ⟪condSet⟫ ⟪orderCode⟫ (r : ZFSet.{u}) ⟪x⟫ ⟪y⟫) ∨
      ¬ ∃ r : ↥M, (r : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair (r : ZFSet.{u}) ⟪q⟫ ∈ ⟪orderCode⟫ ∧
        ZFSet.pair (r : ZFSet.{u}) ⟪p⟫ ∈ ⟪orderCode⟫ := by
  rw [memLocalizeDef, BoundedFormula.realize_sup, BoundedFormula.realize_not,
    realize_belowWitnessDef hm hq, realize_compatibleDef]

theorem realize_noMemBelowDef {r e y : memLang.Term (α ⊕ Fin n)}
    (hm : ⟪tagMem⟫ = natCode memWitnessTag) (hq : ⟪tagEq⟫ = natCode eqTag) :
    (noMemBelowDef tagMem tagEq condSet orderCode r e y).Realize v xs ↔
      ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ → ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
        ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) ⟪e⟫ ⟪y⟫ := by
  have hw : ∀ s : ↥M,
      (forcesMemDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
        (&(Fin.last n)) (liftTerm e) (liftTerm y)).Realize v (Fin.snoc xs s) ↔
      AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) ⟪e⟫ ⟪y⟫ := by
    intro s
    rw [realize_forcesMemDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm, AtomicMemRealized]
  simp only [noMemBelowDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, memFormula, BoundedFormula.realize_rel₂, relMap_mem,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    realize_liftTerm]
  exact forall_congr' fun s ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ not_congr (hw s)

theorem realize_branchObstructionDef {r b y : memLang.Term (α ⊕ Fin n)}
    (hm : ⟪tagMem⟫ = natCode memWitnessTag) (hq : ⟪tagEq⟫ = natCode eqTag) :
    (branchObstructionDef tagMem tagEq condSet orderCode r b y).Realize v xs ↔
      ∃ c e : ↥M, ⟪b⟫ = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
        (c : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪r⟫ (c : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
        ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ → ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
          ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) (e : ZFSet.{u}) ⟪y⟫ := by
  have hw : ∀ c e : ↥M,
      (noMemBelowDef (liftTerm (liftTerm tagMem)) (liftTerm (liftTerm tagEq))
        (liftTerm (liftTerm condSet)) (liftTerm (liftTerm orderCode)) (liftTerm (liftTerm r))
        (&(Fin.last (n + 1))) (liftTerm (liftTerm y))).Realize v (Fin.snoc (Fin.snoc xs c) e) ↔
      ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ → ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
        ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) (e : ZFSet.{u}) ⟪y⟫ := by
    intro c e
    rw [realize_noMemBelowDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [branchObstructionDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pairDef, memFormula, BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_pairMemDef,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    realize_liftTerm]
  exact exists_congr fun c ↦ exists_congr fun e ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ hw c e

theorem realize_eqObstructionDef {r x y : memLang.Term (α ⊕ Fin n)}
    (hm : ⟪tagMem⟫ = natCode memWitnessTag) (hq : ⟪tagEq⟫ = natCode eqTag) :
    (eqObstructionDef tagMem tagEq condSet orderCode r x y).Realize v xs ↔
      ∃ b : ↥M, (b : ZFSet.{u}) ∈ ⟪x⟫ ∧
      ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
        (c : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪r⟫ (c : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
        ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ → ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
          ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) (e : ZFSet.{u}) ⟪y⟫ := by
  have hw : ∀ b : ↥M,
      (branchObstructionDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
        (liftTerm orderCode) (liftTerm r) (&(Fin.last n)) (liftTerm y)).Realize v
          (Fin.snoc xs b) ↔
      ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
        (c : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪r⟫ (c : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
        ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ → ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
          ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) (e : ZFSet.{u}) ⟪y⟫ := by
    intro b
    rw [realize_branchObstructionDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [eqObstructionDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, realize_liftTerm]
  exact exists_congr fun b ↦ and_congr_right fun _ ↦ hw b

theorem realize_eqDecisionDef {r x y : memLang.Term (α ⊕ Fin n)}
    (hm : ⟪tagMem⟫ = natCode memWitnessTag) (hq : ⟪tagEq⟫ = natCode eqTag) :
    (eqDecisionDef tagMem tagEq condSet orderCode r x y).Realize v xs ↔
      AtomicEqRealized M ⟪condSet⟫ ⟪orderCode⟫ ⟪r⟫ ⟪x⟫ ⟪y⟫ ∨
      ((∃ b : ↥M, (b : ZFSet.{u}) ∈ ⟪x⟫ ∧
        ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
          (c : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪r⟫ (c : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
          ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ →
            ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
            ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) (e : ZFSet.{u}) ⟪y⟫) ∨
      (∃ b : ↥M, (b : ZFSet.{u}) ∈ ⟪y⟫ ∧
        ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
          (c : ZFSet.{u}) ∈ ⟪condSet⟫ ∧ ZFSet.pair ⟪r⟫ (c : ZFSet.{u}) ∈ ⟪orderCode⟫ ∧
          ∀ s : ↥M, (s : ZFSet.{u}) ∈ ⟪condSet⟫ →
            ZFSet.pair (s : ZFSet.{u}) ⟪r⟫ ∈ ⟪orderCode⟫ →
            ¬ AtomicMemRealized M ⟪condSet⟫ ⟪orderCode⟫ (s : ZFSet.{u}) (e : ZFSet.{u}) ⟪x⟫)) := by
  rw [eqDecisionDef, BoundedFormula.realize_sup, BoundedFormula.realize_sup,
    realize_forcesEqDef hm hq, realize_eqObstructionDef hm hq, realize_eqObstructionDef hm hq]
  rfl

end Realization

/-! ### Externalization, typed

Each theorem below is the guardrail's pressure test: an internal quantifier over conditions is
decoded by `code_surjective`, which consumes exactly the condition-set conjunct, and its
order-code fact then transports through `order_iff` at the orientation the external set fixes. -/

section Externalize

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}

/-- A typed condition, as a carrier element: `condCode`, with its membership. -/
def condElem (Pres : InternalForcingPresentation M P) (p : P) : ↥M :=
  ⟨condCode Pres p, M.mem_trans (Pres.code_mem p) Pres.conditionSet.2⟩

/-- **Below a witness.** The guarded internal witness decodes to a typed member of
`memWitness`, above `q`. -/
theorem belowWitness_iff
    (hMW : ∀ (r : P) (i j : N.Code),
      AtomicMemWitnessRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ MemWitness r (N.decode i) (N.decode j))
    (q : P) (i j : N.Code) :
    (∃ r : ↥M, (r : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
        ZFSet.pair (condCode Pres q) (r : ZFSet.{u}) ∈ (Pres.orderCode : ZFSet.{u}) ∧
        AtomicMemWitnessRealized M Pres.conditionSet Pres.orderCode (r : ZFSet.{u}) (N.code i)
          (N.code j)) ↔
      q ∈ (↑(lowerClosure (memWitness (N.decode i) (N.decode j))) : Set P) := by
  constructor
  · rintro ⟨r, hr, hqr, hw⟩
    obtain ⟨r', hr'⟩ := Pres.code_surjective r hr
    rw [hr'] at hqr hw
    exact ⟨r', (hMW r' i j).1 hw, (Pres.order_iff r' q).1 hqr⟩
  · rintro ⟨r', hr', hqr⟩
    exact ⟨condElem Pres r', Pres.code_mem r', (Pres.order_iff r' q).2 hqr, (hMW r' i j).2 hr'⟩

/-- **Compatibility.** The guarded common strengthening decodes to a typed one. -/
theorem compatible_iff (q p : P) :
    (∃ r : ↥M, (r : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
        ZFSet.pair (r : ZFSet.{u}) (condCode Pres q) ∈ (Pres.orderCode : ZFSet.{u}) ∧
        ZFSet.pair (r : ZFSet.{u}) (condCode Pres p) ∈ (Pres.orderCode : ZFSet.{u})) ↔
      Compatible q p := by
  constructor
  · rintro ⟨r, hr, hrq, hrp⟩
    obtain ⟨r', hr'⟩ := Pres.code_surjective r hr
    rw [hr'] at hrq hrp
    exact ⟨r', (Pres.order_iff q r').1 hrq, (Pres.order_iff p r').1 hrp⟩
  · rintro ⟨r', hrq, hrp⟩
    exact ⟨condElem Pres r', Pres.code_mem r', (Pres.order_iff q r').2 hrq,
      (Pres.order_iff p r').2 hrp⟩

/-- **The localized membership test externalizes.** -/
theorem externalize_memLocalize
    (hMW : ∀ (r : P) (i j : N.Code),
      AtomicMemWitnessRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ MemWitness r (N.decode i) (N.decode j))
    (p q : P) (i j : N.Code) :
    ((∃ r : ↥M, (r : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
        ZFSet.pair (condCode Pres q) (r : ZFSet.{u}) ∈ (Pres.orderCode : ZFSet.{u}) ∧
        AtomicMemWitnessRealized M Pres.conditionSet Pres.orderCode (r : ZFSet.{u}) (N.code i)
          (N.code j)) ∨
      ¬ ∃ r : ↥M, (r : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
        ZFSet.pair (r : ZFSet.{u}) (condCode Pres q) ∈ (Pres.orderCode : ZFSet.{u}) ∧
        ZFSet.pair (r : ZFSet.{u}) (condCode Pres p) ∈ (Pres.orderCode : ZFSet.{u})) ↔
      q ∈ localizeBelow (memWitness (N.decode i) (N.decode j)) p := by
  rw [belowWitness_iff hMW q i j, compatible_iff q p]
  rfl

/-- **No membership below.** The guarded strengthening decodes to a typed one. -/
theorem noMemBelow_iff
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (r : P) (e j : N.Code) :
    (∀ s : ↥M, (s : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) →
        ZFSet.pair (s : ZFSet.{u}) (condCode Pres r) ∈ (Pres.orderCode : ZFSet.{u}) →
        ¬ AtomicMemRealized M Pres.conditionSet Pres.orderCode (s : ZFSet.{u}) (N.code e)
          (N.code j)) ↔
      ∀ s : P, s ≤ r → ¬ ForcesMem s (N.decode e) (N.decode j) := by
  constructor
  · intro h s hsr hf
    exact h (condElem Pres s) (Pres.code_mem s) ((Pres.order_iff r s).2 hsr) ((hMem s e j).2 hf)
  · intro h s hs hsr hf
    obtain ⟨s', hs'⟩ := Pres.code_surjective s hs
    rw [hs'] at hsr hf
    exact h s' ((Pres.order_iff r s').1 hsr) ((hMem s' e j).1 hf)

/-- **The equality obstruction externalizes.** This is where `branch_mem_code_iff` is consumed:
a member of `N.code i` is a coded branch, so the internal pair decomposes into the branch's
typed condition and its subname's code. -/
theorem eqObstruction_iff (hc : InternalNameCoding Pres N)
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (r : P) (i j : N.Code) :
    (∃ b : ↥M, (b : ZFSet.{u}) ∈ N.code i ∧
      ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
        (c : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
        ZFSet.pair (condCode Pres r) (c : ZFSet.{u}) ∈ (Pres.orderCode : ZFSet.{u}) ∧
        ∀ s : ↥M, (s : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) →
          ZFSet.pair (s : ZFSet.{u}) (condCode Pres r) ∈ (Pres.orderCode : ZFSet.{u}) →
          ¬ AtomicMemRealized M Pres.conditionSet Pres.orderCode (s : ZFSet.{u}) (e : ZFSet.{u})
            (N.code j)) ↔
      r ∈ eqObstruction (N.decode i) (N.decode j) := by
  constructor
  · rintro ⟨b, hb, c, e, hbce, -, hrc, hno⟩
    obtain ⟨k, j', hj', hb'⟩ := (hc.branch_mem_code_iff i b).1 hb
    rw [hbce] at hb'
    obtain ⟨hc', he'⟩ := ZFSet.pair_inj.1 hb'
    refine ⟨k, (Pres.order_iff _ r).1 (hc' ▸ hrc), ?_⟩
    have := (noMemBelow_iff hMem r j' j).1 (by simpa [he'] using hno)
    simpa [hj'] using this
  · rintro ⟨k, hrk, hno⟩
    obtain ⟨j', hj'⟩ := N.subname_closed i k
    have hb : ZFSet.pair (condCode Pres ((N.decode i).conds k)) (N.code j') ∈ N.code i :=
      (hc.branch_mem_code_iff i _).2 ⟨k, j', hj', rfl⟩
    refine ⟨⟨_, InternalNameCoding.pair_mem_carrier hb⟩, hb, condElem Pres _,
      ⟨N.code j', N.code_mem j'⟩, rfl, Pres.code_mem _, (Pres.order_iff _ r).2 hrk, ?_⟩
    exact (noMemBelow_iff hMem r j' j).2 (by simpa [hj'] using hno)

/-- **The equality decision test externalizes.** -/
theorem externalize_eqDecision (hc : InternalNameCoding Pres N)
    (hEq : ∀ (r : P) (i j : N.Code),
      AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j))
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (r : P) (i j : N.Code) :
    (AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
        (N.code j) ∨
      ((∃ b : ↥M, (b : ZFSet.{u}) ∈ N.code i ∧
        ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
          (c : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
          ZFSet.pair (condCode Pres r) (c : ZFSet.{u}) ∈ (Pres.orderCode : ZFSet.{u}) ∧
          ∀ s : ↥M, (s : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) →
            ZFSet.pair (s : ZFSet.{u}) (condCode Pres r) ∈ (Pres.orderCode : ZFSet.{u}) →
            ¬ AtomicMemRealized M Pres.conditionSet Pres.orderCode (s : ZFSet.{u})
              (e : ZFSet.{u}) (N.code j)) ∨
      (∃ b : ↥M, (b : ZFSet.{u}) ∈ N.code j ∧
        ∃ c e : ↥M, (b : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (e : ZFSet.{u}) ∧
          (c : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) ∧
          ZFSet.pair (condCode Pres r) (c : ZFSet.{u}) ∈ (Pres.orderCode : ZFSet.{u}) ∧
          ∀ s : ↥M, (s : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) →
            ZFSet.pair (s : ZFSet.{u}) (condCode Pres r) ∈ (Pres.orderCode : ZFSet.{u}) →
            ¬ AtomicMemRealized M Pres.conditionSet Pres.orderCode (s : ZFSet.{u})
              (e : ZFSet.{u}) (N.code i)))) ↔
      r ∈ eqDecision (N.decode i) (N.decode j) := by
  rw [hEq, eqObstruction_iff hc hMem r i j, eqObstruction_iff hc hMem r j i, eqDecision,
    Set.mem_union, Set.mem_union, or_assoc]
  rfl

end Externalize

/-! ### The Separation instances

One fixed formula per test, with the tested condition as the single bound variable and the
presentation's codes as parameters. Each externalization theorem above is now read at those
parameters, and one Separation instance produces the code. -/

section Tests

/-- The localized membership test, as a Separation instance: parameters
`tagMem, tagEq, condSet, orderCode, p, x, y`; the bound variable is the tested condition. -/
def memLocalizeTest : memLang.BoundedFormula (Fin 7) 1 :=
  memLocalizeDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6)) &0

/-- The equality decision test, as a Separation instance: parameters
`tagMem, tagEq, condSet, orderCode, x, y`; the bound variable is the tested condition. -/
def eqDecisionTest : memLang.BoundedFormula (Fin 6) 1 :=
  eqDecisionDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3)) &0
    (var (Sum.inl 4)) (var (Sum.inl 5))

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}

/-- **The localized membership test, read at a typed condition.** -/
theorem realize_memLocalizeTest
    (hMW : ∀ (r : P) (i j : N.Code),
      AtomicMemWitnessRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ MemWitness r (N.decode i) (N.decode j))
    (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M) (hq : (natCode eqTag : ZFSet.{u}) ∈ M)
    (p q : P) (i j : N.Code) :
    memLocalizeTest.Realize
        ![⟨natCode memWitnessTag, hm⟩, ⟨natCode eqTag, hq⟩, Pres.conditionSet, Pres.orderCode,
          condElem Pres p, ⟨N.code i, N.code_mem i⟩, ⟨N.code j, N.code_mem j⟩]
        ![condElem Pres q] ↔
      q ∈ localizeBelow (memWitness (N.decode i) (N.decode j)) p := by
  rw [memLocalizeTest, realize_memLocalizeDef (by simp) (by simp)]
  simp only [Term.realize_var, Sum.elim_inl, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, Fin.isValue]
  exact externalize_memLocalize hMW p q i j

/-- **The equality decision test, read at a typed condition.** -/
theorem realize_eqDecisionTest (hc : InternalNameCoding Pres N)
    (hEq : ∀ (r : P) (i j : N.Code),
      AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j))
    (hMem : ∀ (r : P) (i j : N.Code),
      AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i)
          (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j))
    (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M) (hq : (natCode eqTag : ZFSet.{u}) ∈ M)
    (r : P) (i j : N.Code) :
    eqDecisionTest.Realize
        ![⟨natCode memWitnessTag, hm⟩, ⟨natCode eqTag, hq⟩, Pres.conditionSet, Pres.orderCode,
          ⟨N.code i, N.code_mem i⟩, ⟨N.code j, N.code_mem j⟩]
        ![condElem Pres r] ↔
      r ∈ eqDecision (N.decode i) (N.decode j) := by
  rw [eqDecisionTest, realize_eqDecisionDef (by simp) (by simp)]
  simp only [Term.realize_var, Sum.elim_inl, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.tail_cons, Matrix.head_cons, Fin.isValue]
  exact externalize_eqDecision hc hEq hMem r i j

end Tests

/-! ### The codes, materially -/

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] {Pres : InternalForcingPresentation M.toMaterialCarrier P}

/-- A Separation instance over the condition set yields an internal subset, with membership
read at typed conditions. -/
theorem exists_internalSubset_of_separation {k : ℕ} {φ : memLang.BoundedFormula (Fin k) 1}
    (hφ : separationSentence φ ∈ T) (params : Fin k → ↥M.toMaterialCarrier) :
    ∃ d : Pres.InternalSubset, ∀ q : P,
      q ∈ d.externalize ↔ φ.Realize params ![condElem Pres q] := by
  obtain ⟨b, hb⟩ := M.exists_separation hφ params Pres.conditionSet
  refine ⟨⟨b, fun z hz ↦ ?_⟩, fun q ↦ ?_⟩
  · have hzM : z ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hz b.2
    exact ((hb ⟨z, hzM⟩).1 hz).1
  · rw [InternalForcingPresentation.InternalSubset.mem_externalize]
    exact (hb (condElem Pres q)).trans (and_iff_right (Pres.code_mem q))

variable {N : InternalNamePresentation M.toMaterialCarrier P}

/-- **The localized membership test is coded**, on `atomicDefinability`'s ledger plus one
Separation instance. -/
theorem exists_memLocalizeCode
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T)
    (htest : separationSentence memLocalizeTest ∈ T)
    (hc : InternalNameCoding Pres N) (p : P) (i j : N.Code) :
    ∃ d : Pres.InternalSubset,
      d.externalize = localizeBelow (memWitness (N.decode i) (N.decode j)) p := by
  obtain ⟨d, hd⟩ := M.exists_internalSubset_of_separation (Pres := Pres) htest
    ![⟨natCode memWitnessTag, M.natCode_mem he hp hu _⟩, ⟨natCode eqTag, M.natCode_mem he hp hu _⟩,
      Pres.conditionSet, Pres.orderCode, condElem Pres p, ⟨N.code i, N.code_mem i⟩,
      ⟨N.code j, N.code_mem j⟩]
  refine ⟨d, Set.ext fun q ↦ (hd q).trans ?_⟩
  exact realize_memLocalizeTest
    (fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).1) _ _ p q i j

/-- **The equality decision test is coded**, likewise. -/
theorem exists_eqDecisionCode
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T)
    (htest : separationSentence eqDecisionTest ∈ T)
    (hc : InternalNameCoding Pres N) (i j : N.Code) :
    ∃ d : Pres.InternalSubset, d.externalize = eqDecision (N.decode i) (N.decode j) := by
  obtain ⟨d, hd⟩ := M.exists_internalSubset_of_separation (Pres := Pres) htest
    ![⟨natCode memWitnessTag, M.natCode_mem he hp hu _⟩, ⟨natCode eqTag, M.natCode_mem he hp hu _⟩,
      Pres.conditionSet, Pres.orderCode, ⟨N.code i, N.code_mem i⟩, ⟨N.code j, N.code_mem j⟩]
  refine ⟨d, Set.ext fun r ↦ (hd r).trans ?_⟩
  exact realize_eqDecisionTest hc
    (fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).2.1)
    (fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).2.2) _ _ r i j

end MaterialGround

end Forcing
