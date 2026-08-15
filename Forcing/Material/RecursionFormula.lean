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
* `Forcing.AtomicRecursion.realize_stageValueDef`: the stage law, the last realization
  theorem before the schemes are named.
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

/-- **The membership-witness clause**, as a formula: some branch of `y` is activated by `q`
and its subname is forced equal to `x`. **Tag wiring**: this clause queries the *equality*
slice, so its tag term is specialized to `eqTag`. -/
def memClauseDef (condSet orderCode tag R q x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
        (liftTerm (liftTerm y)) ⊓
      (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm condSet)) ⊓
      (pairMemDef (liftTerm (liftTerm q)) (&(Fin.castSucc (Fin.last n)))
          (liftTerm (liftTerm orderCode)) ⊓
        entryMemDef (liftTerm (liftTerm tag)) (liftTerm (liftTerm q))
          (liftTerm (liftTerm x)) (&(Fin.last (n + 1))) (liftTerm (liftTerm R)))))

/-- One side of the equality clause: every valid branch of `source`, at every common
strengthening, is densely a member of `target`. Private, and factored so that the second side
of `eqClauseDef` is obtained **solely** by swapping `source` and `target` — never by
rewriting argument order inside the body, which is what would make a partial swap possible.
Both order comparisons read downward: `q ≤ p` and `q ≤ c`. -/
private def eqSideDef (condSet orderCode tag R p source target : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' ∀' ∀' (memFormula (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
        (liftTerm (liftTerm (liftTerm condSet))) ⟹
    (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.castSucc (Fin.last (n + 1))))
        (liftTerm (liftTerm (liftTerm source))) ⟹
    (memFormula (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm condSet))) ⟹
    (pairMemDef (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm p)))
        (liftTerm (liftTerm (liftTerm orderCode))) ⟹
    (pairMemDef (&(Fin.last (n + 2))) (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
        (liftTerm (liftTerm (liftTerm orderCode))) ⟹
      denseMemDef (liftTerm (liftTerm (liftTerm condSet)))
        (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm tag)))
        (liftTerm (liftTerm (liftTerm R))) (&(Fin.last (n + 2)))
        (&(Fin.castSucc (Fin.last (n + 1)))) (liftTerm (liftTerm (liftTerm target))))))))

/-- **The forced-equality clause**, as a formula: the two inclusions. The second is the first
with `source` and `target` exchanged, nothing more. **Tag wiring**: it queries `denseMemDef`,
hence the `memWitnessTag` slice. -/
def eqClauseDef (condSet orderCode tag R p x y : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  eqSideDef condSet orderCode tag R p x y ⊓ eqSideDef condSet orderCode tag R p y x

/-- **Coherence**, as a formula: at every valid condition code and every pair of domain
elements, each tagged slice is exactly its clause. Both tag terms are exposed independently,
and the **four-way routing** is the content — `tagMem` on the left of the membership equation
with `memClauseDef` (which queries the equality slice, hence `tagEq`) on its right; `tagEq` on
the left of the equality equation with `eqClauseDef` (which queries density, hence `tagMem`)
on its right. Tag *inequality* is deliberately not stated inside the formula: the realization
hypotheses identify the two terms with distinct injective numerals, which already guarantees
the distinction. -/
def atomicCoherentOnDef (tagMem tagEq condSet orderCode A R : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  (∀' ∀' ∀' (memFormula (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
        (liftTerm (liftTerm (liftTerm condSet))) ⟹
    (memFormula (&(Fin.castSucc (Fin.last (n + 1)))) (liftTerm (liftTerm (liftTerm A))) ⟹
    (memFormula (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm A))) ⟹
      (entryMemDef (liftTerm (liftTerm (liftTerm tagMem)))
          (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.castSucc (Fin.last (n + 1))))
          (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm R))) ⇔
        memClauseDef (liftTerm (liftTerm (liftTerm condSet)))
          (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm tagEq)))
          (liftTerm (liftTerm (liftTerm R))) (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
          (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2))))))))
  ⊓ (∀' ∀' ∀' (memFormula (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
        (liftTerm (liftTerm (liftTerm condSet))) ⟹
    (memFormula (&(Fin.castSucc (Fin.last (n + 1)))) (liftTerm (liftTerm (liftTerm A))) ⟹
    (memFormula (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm A))) ⟹
      (entryMemDef (liftTerm (liftTerm (liftTerm tagEq)))
          (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.castSucc (Fin.last (n + 1))))
          (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm R))) ⇔
        eqClauseDef (liftTerm (liftTerm (liftTerm condSet)))
          (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm tagMem)))
          (liftTerm (liftTerm (liftTerm R))) (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
          (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2))))))))

/-- **A stage entry**, as a formula: `e` is one of the tagged entries at `(x, y)` whose clause
succeeds against `history`. Both tag terms are exposed, and the **routing repeats the
coherence pattern**: `tagMem` names the membership entry while its clause queries the equality
slice (`tagEq`), and `tagEq` names the equality entry while its clause queries density
(`tagMem`).

The formula states no validity condition on `x` and `y` beyond what the clauses themselves
impose: the branch quantifiers admit only members whose first coordinate is a condition code,
so the guards filter for **branch shape**, member by member. They do not test whether `x` and
`y` are name codes, and an arbitrary set may well contain branch-shaped members that pass —
what is guaranteed is that anything not branch-shaped contributes no entry. That is enough to
make the stage relation total on arbitrary arguments, which is what Collection will need. -/
def stageEntryDef (tagMem tagEq condSet orderCode history x y e :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  (∃' (memFormula (&(Fin.last n)) (liftTerm condSet) ⊓
      (entryDef (liftTerm tagMem) (&(Fin.last n)) (liftTerm x) (liftTerm y) (liftTerm e) ⊓
        memClauseDef (liftTerm condSet) (liftTerm orderCode) (liftTerm tagEq)
          (liftTerm history) (&(Fin.last n)) (liftTerm x) (liftTerm y))))
    ⊔ (∃' (memFormula (&(Fin.last n)) (liftTerm condSet) ⊓
      (entryDef (liftTerm tagEq) (&(Fin.last n)) (liftTerm x) (liftTerm y) (liftTerm e) ⊓
        eqClauseDef (liftTerm condSet) (liftTerm orderCode) (liftTerm tagMem)
          (liftTerm history) (&(Fin.last n)) (liftTerm x) (liftTerm y))))

/-- **The stage relation**, as a formula: the members of `value` are exactly the stage entries
at `(x, y)`. The factoring is structural, not incidental — the very same `stageEntryDef` is
what the Separation instance carves from a bound. -/
def stageValueDef (tagMem tagEq condSet orderCode history x y value :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm value) ⇔
    stageEntryDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
      (liftTerm history) (liftTerm x) (liftTerm y) (&(Fin.last n)))

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

/-- **The membership-clause law**, and its orientation test: the formula realizes to exactly
the semantic `MemClause`, with `q` strengthening the branch's condition. The reverse
direction shows the dependency boundary plainly — the branch condition code is in the carrier
because it belongs to the condition set, the subname code because the coded branch belongs to
`y`, and the encoded equality entry because it belongs to `R`. All three are **intrinsic
transitivity** consequences, so no axiom sentence enters. -/
theorem realize_memClauseDef {condSet orderCode q : memLang.Term (α ⊕ Fin n)}
    (htag : ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (memClauseDef condSet orderCode tag R q x y).Realize v xs ↔
      MemClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) q : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  have hcM : ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) condSet : ↥M).2
  have hyM : ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) y : ↥M).2
  have hent : ∀ c z : ↥M,
      (entryMemDef (liftTerm (liftTerm tag)) (liftTerm (liftTerm q))
          (liftTerm (liftTerm x)) (&(Fin.last (n + 1)))
          (liftTerm (liftTerm R))).Realize v (Fin.snoc (Fin.snoc xs c) z) ↔
        entry eqTag ((Term.realize (Sum.elim v xs) q : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) ((z : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
    intro c z
    rw [realize_entryMemDef_natCode (by simpa [realize_liftTerm] using htag)]
    simp [realize_liftTerm]
  simp only [memClauseDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_pairMemDef, realize_liftTerm]
  constructor
  · rintro ⟨c, z, hb, hc, hord, he⟩
    exact ⟨(c : ZFSet.{u}), (z : ZFSet.{u}), hb, hc, hord, (hent c z).1 he⟩
  · rintro ⟨c, z, hb, hc, hord, he⟩
    have hcM' : c ∈ M := M.mem_trans hc hcM
    have hzM : z ∈ M := right_mem_of_pair_mem (M.mem_trans hb hyM)
    exact ⟨⟨c, hcM'⟩, ⟨z, hzM⟩, hb, hc, hord, (hent ⟨c, hcM'⟩ ⟨z, hzM⟩).2 he⟩

/-- Realization of one side. The reverse direction performs the same carrier conversions as
`memClauseDef` — `c` from the condition set, `z` from the branch pair in `source`, `q` from
the condition set — with the inner density theorem instantiated explicitly at the lifted tag
equation. Private, like the side itself. -/
private theorem realize_eqSideDef {condSet orderCode p source target : memLang.Term (α ⊕ Fin n)}
    (htag : ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u}) = natCode memWitnessTag) :
    (eqSideDef condSet orderCode tag R p source target).Realize v xs ↔
      ∀ c z, ZFSet.pair c z ∈ ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) →
        c ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) →
        ∀ q ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
          ZFSet.pair q ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u}) ∈
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) →
          ZFSet.pair q c ∈ ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) →
          DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) q z
            ((Term.realize (Sum.elim v xs) target : ↥M) : ZFSet.{u}) := by
  have hcM : ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) condSet : ↥M).2
  have hsM : ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) source : ↥M).2
  have hden : ∀ c z q : ↥M,
      (denseMemDef (liftTerm (liftTerm (liftTerm condSet)))
          (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm tag)))
          (liftTerm (liftTerm (liftTerm R))) (&(Fin.last (n + 2)))
          (&(Fin.castSucc (Fin.last (n + 1))))
          (liftTerm (liftTerm (liftTerm target)))).Realize v
        (Fin.snoc (Fin.snoc (Fin.snoc xs c) z) q) ↔
        DenseMem ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u})
          ((q : ↥M) : ZFSet.{u}) ((z : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) target : ↥M) : ZFSet.{u}) := by
    intro c z q
    rw [realize_denseMemDef (by simpa [realize_liftTerm] using htag)]
    simp [realize_liftTerm]
  simp only [eqSideDef, BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_pairMemDef, realize_liftTerm]
  constructor
  · intro h c z hb hc q hq hqp hqc
    exact (hden ⟨c, M.mem_trans hc hcM⟩ ⟨z, right_mem_of_pair_mem (M.mem_trans hb hsM)⟩
      ⟨q, M.mem_trans hq hcM⟩).1
      (h ⟨c, M.mem_trans hc hcM⟩ ⟨z, right_mem_of_pair_mem (M.mem_trans hb hsM)⟩
        ⟨q, M.mem_trans hq hcM⟩ hc hb hq hqp hqc)
  · intro h c z q hc hb hq hqp hqc
    exact (hden c z q).2 (h _ _ hb hc _ hq hqp hqc)

/-- **The equality-clause law**: the formula realizes to exactly the semantic `EqClause`, both
inclusions. This is the orientation check for the pair of sides — a partial swap would fail
here — and for both downward comparisons inside each side. -/
theorem realize_eqClauseDef {condSet orderCode p : memLang.Term (α ⊕ Fin n)}
    (htag : ((Term.realize (Sum.elim v xs) tag : ↥M) : ZFSet.{u}) = natCode memWitnessTag) :
    (eqClauseDef condSet orderCode tag R p x y).Realize v xs ↔
      EqClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  rw [eqClauseDef, BoundedFormula.realize_inf, realize_eqSideDef htag, realize_eqSideDef htag]
  exact Iff.rfl

/-- **The coherence law** — the decisive check that both tags and both sides survived every
binder lift in their intended positions. Its only hypotheses are the two tag-value equations:
**no domain transitivity, no `A ∈ M`, and no theory membership**. Transitivity is used while
realizing nested encoded witnesses, but it is the carrier structure's *intrinsic*
transitivity, not a ground-theory charge. -/
theorem realize_atomicCoherentOnDef
    {tagMem tagEq condSet orderCode A R : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (he : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (atomicCoherentOnDef tagMem tagEq condSet orderCode A R).Realize v xs ↔
      AtomicCoherentOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
  have hcM : ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) condSet : ↥M).2
  have hAM : ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) A : ↥M).2
  have hentM : ∀ p x y : ↥M,
      (entryMemDef (liftTerm (liftTerm (liftTerm tagMem)))
          (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.castSucc (Fin.last (n + 1))))
          (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm R)))).Realize v
        (Fin.snoc (Fin.snoc (Fin.snoc xs p) x) y) ↔
        entry memWitnessTag ((p : ↥M) : ZFSet.{u}) ((x : ↥M) : ZFSet.{u})
            ((y : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
    intro p x y
    rw [realize_entryMemDef_natCode (by simpa [realize_liftTerm] using hm)]
    simp [realize_liftTerm]
  have hentE : ∀ p x y : ↥M,
      (entryMemDef (liftTerm (liftTerm (liftTerm tagEq)))
          (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.castSucc (Fin.last (n + 1))))
          (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm R)))).Realize v
        (Fin.snoc (Fin.snoc (Fin.snoc xs p) x) y) ↔
        entry eqTag ((p : ↥M) : ZFSet.{u}) ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
    intro p x y
    rw [realize_entryMemDef_natCode (by simpa [realize_liftTerm] using he)]
    simp [realize_liftTerm]
  have hmemC : ∀ p x y : ↥M,
      (memClauseDef (liftTerm (liftTerm (liftTerm condSet)))
          (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm tagEq)))
          (liftTerm (liftTerm (liftTerm R))) (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
          (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))).Realize v
        (Fin.snoc (Fin.snoc (Fin.snoc xs p) x) y) ↔
        MemClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) ((p : ↥M) : ZFSet.{u})
          ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) := by
    intro p x y
    rw [realize_memClauseDef (by simpa [realize_liftTerm] using he)]
    simp [realize_liftTerm]
  have heqC : ∀ p x y : ↥M,
      (eqClauseDef (liftTerm (liftTerm (liftTerm condSet)))
          (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm tagMem)))
          (liftTerm (liftTerm (liftTerm R))) (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
          (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))).Realize v
        (Fin.snoc (Fin.snoc (Fin.snoc xs p) x) y) ↔
        EqClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) ((p : ↥M) : ZFSet.{u})
          ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) := by
    intro p x y
    rw [realize_eqClauseDef (by simpa [realize_liftTerm] using hm)]
    simp [realize_liftTerm]
  simp only [atomicCoherentOnDef, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p hp x hx y hy ↦ ?_, fun p hp x hx y hy ↦ ?_⟩
    · have hpM := M.mem_trans hp hcM
      have hxM := M.mem_trans hx hAM
      have hyM := M.mem_trans hy hAM
      exact ((hentM ⟨p, hpM⟩ ⟨x, hxM⟩ ⟨y, hyM⟩).symm.trans
        ((h₁ ⟨p, hpM⟩ ⟨x, hxM⟩ ⟨y, hyM⟩ hp hx hy).trans
          (hmemC ⟨p, hpM⟩ ⟨x, hxM⟩ ⟨y, hyM⟩)))
    · have hpM := M.mem_trans hp hcM
      have hxM := M.mem_trans hx hAM
      have hyM := M.mem_trans hy hAM
      exact ((hentE ⟨p, hpM⟩ ⟨x, hxM⟩ ⟨y, hyM⟩).symm.trans
        ((h₂ ⟨p, hpM⟩ ⟨x, hxM⟩ ⟨y, hyM⟩ hp hx hy).trans
          (heqC ⟨p, hpM⟩ ⟨x, hxM⟩ ⟨y, hyM⟩)))
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun p x y hp hx hy ↦ ?_, fun p x y hp hx hy ↦ ?_⟩
    · exact (hentM p x y).trans ((h₁ _ hp _ hx _ hy).trans (hmemC p x y).symm)
    · exact (hentE p x y).trans ((h₂ _ hp _ hx _ hy).trans (heqC p x y).symm)

/-- **The stage-entry law**: the formula says exactly that `e` is one of the two tagged
entries at `(x, y)` whose clause succeeds. Its only hypotheses are the two tag equations —
the entry is *named*, not asserted to lie anywhere, so nothing is charged here. -/
theorem realize_stageEntryDef
    {tagMem tagEq condSet orderCode history e : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (he : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (stageEntryDef tagMem tagEq condSet orderCode history x y e).Realize v xs ↔
      (∃ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
          ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
            entry memWitnessTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∧
          MemClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u}) p
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})) ∨
        (∃ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
          ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
            entry eqTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∧
          EqClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u}) p
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})) := by
  have hcM : ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) condSet : ↥M).2
  have hentD : ∀ p : ↥M,
      (entryDef (liftTerm tagMem) (&(Fin.last n)) (liftTerm x) (liftTerm y)
          (liftTerm e)).Realize v (Fin.snoc xs p) ↔
        ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
          entry memWitnessTag ((p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
    intro p
    rw [realize_entryDef_natCode (by simpa [realize_liftTerm] using hm)]
    simp [realize_liftTerm]
  have hentE : ∀ p : ↥M,
      (entryDef (liftTerm tagEq) (&(Fin.last n)) (liftTerm x) (liftTerm y)
          (liftTerm e)).Realize v (Fin.snoc xs p) ↔
        ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) =
          entry eqTag ((p : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
    intro p
    rw [realize_entryDef_natCode (by simpa [realize_liftTerm] using he)]
    simp [realize_liftTerm]
  have hmemC : ∀ p : ↥M,
      (memClauseDef (liftTerm condSet) (liftTerm orderCode) (liftTerm tagEq)
          (liftTerm history) (&(Fin.last n)) (liftTerm x) (liftTerm y)).Realize v
        (Fin.snoc xs p) ↔
        MemClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u}) ((p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
    intro p
    rw [realize_memClauseDef (by simpa [realize_liftTerm] using he)]
    simp [realize_liftTerm]
  have heqC : ∀ p : ↥M,
      (eqClauseDef (liftTerm condSet) (liftTerm orderCode) (liftTerm tagMem)
          (liftTerm history) (&(Fin.last n)) (liftTerm x) (liftTerm y)).Realize v
        (Fin.snoc xs p) ↔
        EqClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u}) ((p : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
    intro p
    rw [realize_eqClauseDef (by simpa [realize_liftTerm] using hm)]
    simp [realize_liftTerm]
  simp only [stageEntryDef, BoundedFormula.realize_sup, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, memFormula, BoundedFormula.realize_rel₂, relMap_mem,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm]
  constructor
  · rintro (⟨p, hp, hd, hc⟩ | ⟨p, hp, hd, hc⟩)
    · exact Or.inl ⟨(p : ZFSet.{u}), hp, (hentD p).1 hd, (hmemC p).1 hc⟩
    · exact Or.inr ⟨(p : ZFSet.{u}), hp, (hentE p).1 hd, (heqC p).1 hc⟩
  · rintro (⟨p, hp, hd, hc⟩ | ⟨p, hp, hd, hc⟩)
    · exact Or.inl ⟨⟨p, M.mem_trans hp hcM⟩, hp, (hentD ⟨p, _⟩).2 hd, (hmemC ⟨p, _⟩).2 hc⟩
    · exact Or.inr ⟨⟨p, M.mem_trans hp hcM⟩, hp, (hentE ⟨p, _⟩).2 hd, (heqC ⟨p, _⟩).2 hc⟩

/-- **The stage law**: the formula realizes to exactly the semantic `StageValue`.

Beyond the two tag equations, the only hypothesis is that the candidate entries lie in the
carrier — needed because the predicate quantifies over all sets while the formula quantifies
over carrier elements, so the backward direction must place a named entry in range.
**No scheme is consumed here.**

That hypothesis has two routes, and the cheaper one is not the obvious one.
`MaterialGround.entry_mem` builds the entries outright, at the finite-closure axioms already
on the ledger. But a consumer holding a *bound* in the carrier gets it for free: the entries
are members of the bound, hence carrier elements by transitivity, with nothing charged. That
is how `MaterialGround.exists_stageValue_of_bound` discharges it. -/
theorem realize_stageValueDef
    {tagMem tagEq condSet orderCode history value : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (he : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag)
    (hentM : ∀ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
      entry memWitnessTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ M ∧
        entry eqTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∈ M) :
    (stageValueDef tagMem tagEq condSet orderCode history x y value).Realize v xs ↔
      StageValue ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) value : ↥M) : ZFSet.{u}) := by
  have hvM : ((Term.realize (Sum.elim v xs) value : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) value : ↥M).2
  have hbody : ∀ e : ↥M,
      (stageEntryDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (liftTerm history) (liftTerm x) (liftTerm y)
          (&(Fin.last n))).Realize v (Fin.snoc xs e) ↔
        (∃ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
            ((e : ↥M) : ZFSet.{u}) =
              entry memWitnessTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
                ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∧
            MemClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u}) p
              ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})) ∨
          (∃ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
            ((e : ↥M) : ZFSet.{u}) =
              entry eqTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
                ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ∧
            EqClause ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u}) p
              ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})) := by
    intro e
    rw [realize_stageEntryDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using he)]
    simp [realize_liftTerm]
  simp only [stageValueDef, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  constructor
  · intro h e
    constructor
    · intro hev
      exact (hbody ⟨e, M.mem_trans hev hvM⟩).1 ((h ⟨e, M.mem_trans hev hvM⟩).1 hev)
    · rintro (⟨p, hp, rfl, hc⟩ | ⟨p, hp, rfl, hc⟩)
      · exact (h ⟨_, (hentM p hp).1⟩).2 ((hbody ⟨_, (hentM p hp).1⟩).2
          (Or.inl ⟨p, hp, rfl, hc⟩))
      · exact (h ⟨_, (hentM p hp).2⟩).2 ((hbody ⟨_, (hentM p hp).2⟩).2
          (Or.inr ⟨p, hp, rfl, hc⟩))
  · intro h e
    exact ((h (e : ZFSet.{u})).trans (hbody e).symm)

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
