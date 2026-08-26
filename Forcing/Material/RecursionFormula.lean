/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Recursion
import Forcing.Material.Semantics

/-!
# The recursion formulas: entries and clauses

The formula layer of the atomic recursion, built bottom-up with a realization theorem at each
step. This module owns the **entry and clause** formulas — entries, the three coherence
clauses, stages, rows, graphs, and the recursion's own predicates. They are specific to the
tagged graph representation, so unlike the pair builders they stay inside `AtomicRecursion`
rather than enlarging the shared syntax API.

The **atomic definitions** built on top of these live in
`Forcing/Material/AtomicFormula.lean`.

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
* `Forcing.AtomicRecursion.realize_atomicCoherentOnDef`, and the stage/row/graph and
  descent-closed laws: the clause-level realization theorems the atomic definitions consume.
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

/-- **A row entry**, as a formula: `e` is a stage entry at `(x, y)` for some `y` in the
domain `A`. -/
def rowEntryDef (tagMem tagEq condSet orderCode history A x e :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (memFormula (&(Fin.last n)) (liftTerm A) ⊓
    stageEntryDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
      (liftTerm history) (liftTerm x) (&(Fin.last n)) (liftTerm e))

/-- **The row relation**, as a formula: the members of `row` are exactly the row entries at
`x`. Same shape as `stageValueDef` one level up — the factoring is what lets the Collection
instance at the graph level quantify over rows. -/
def rowValueDef (tagMem tagEq condSet orderCode history A x row :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm row) ⇔
    rowEntryDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
      (liftTerm history) (liftTerm A) (liftTerm x) (&(Fin.last n)))

/-- **The fixed-point predicate**, as a formula: the members of `R` are exactly the stage
entries its own clauses admit at states of `D`. The history slot of `stageEntryDef` is filled
with `R` itself — that is the whole point, and it is why this formula, unlike the aggregation
ones, has no separate history parameter. -/
def correctOnDef (tagMem tagEq condSet orderCode D R : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm R) ⇔
    ∃' ∃' (pairMemDef (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))
        (liftTerm (liftTerm (liftTerm D))) ⊓
      stageEntryDef (liftTerm (liftTerm (liftTerm tagMem)))
        (liftTerm (liftTerm (liftTerm tagEq))) (liftTerm (liftTerm (liftTerm condSet)))
        (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm R)))
        (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))
        (&(Fin.castSucc (Fin.castSucc (Fin.last n))))))

/-- One predecessor shape, right-oriented: every valid branch `z` of `source` yields the state
`(fixed, z)` in `D`. Private, and split by orientation so that the three shapes of
`DescentClosed` are obtained by *choosing arguments*, never by rewriting coordinate order
inside a body — the discipline the equality clause already uses. -/
private def predRightDef (condSet D source fixed : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm source)) ⟹
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm condSet)) ⟹
      pairMemDef (liftTerm (liftTerm fixed)) (&(Fin.last (n + 1))) (liftTerm (liftTerm D))))

/-- The left-oriented shape: the branch supplies the *first* coordinate. -/
private def predLeftDef (condSet D source fixed : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm source)) ⟹
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm condSet)) ⟹
      pairMemDef (&(Fin.last (n + 1))) (liftTerm (liftTerm fixed)) (liftTerm (liftTerm D))))

/-- **Descent-closure**, as a formula: every member of `D` decodes to a state over `A`, and
all three direct predecessor shapes stay in `D`. Transitivity of `A` is **not** stated — the
semantic predicate does not require it, and neither does this. -/
def descentClosedDef (condSet A D : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  (∀' (memFormula (&(Fin.last n)) (liftTerm D) ⟹
    ∃' ∃' (memFormula (&(Fin.castSucc (Fin.last (n + 1))))
          (liftTerm (liftTerm (liftTerm A))) ⊓
        (memFormula (&(Fin.last (n + 2))) (liftTerm (liftTerm (liftTerm A))) ⊓
          pairDef (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))
            (&(Fin.castSucc (Fin.castSucc (Fin.last n))))))))
  ⊓ (∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
        (liftTerm (liftTerm D)) ⟹
      (predRightDef (liftTerm (liftTerm condSet)) (liftTerm (liftTerm D))
          (&(Fin.last (n + 1))) (&(Fin.castSucc (Fin.last n))) ⊓
        (predLeftDef (liftTerm (liftTerm condSet)) (liftTerm (liftTerm D))
            (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) ⊓
          predLeftDef (liftTerm (liftTerm condSet)) (liftTerm (liftTerm D))
            (&(Fin.last (n + 1))) (&(Fin.castSucc (Fin.last n)))))))

/-- **The approximation conditions**, as one formula: descent-closure of the domain and
correctness of the graph on it. This is the predicate the package filter certifies, and it
factors exactly — the descent-closure side is pure bookkeeping, and the whole
finite-construction obligation sits on the correctness side. -/
def approximationDef (tagMem tagEq condSet orderCode A D R : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  descentClosedDef condSet A D ⊓ correctOnDef tagMem tagEq condSet orderCode D R

/-- **The package predicate**, as a formula: `a` codes a pair whose components satisfy the
approximation conditions, with the domain covering `s`. -/
def packageAtDef (tagMem tagEq condSet orderCode A s a : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm a)) ⊓
    (approximationDef (liftTerm (liftTerm tagMem)) (liftTerm (liftTerm tagEq))
        (liftTerm (liftTerm condSet)) (liftTerm (liftTerm orderCode))
        (liftTerm (liftTerm A)) (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) ⊓
      memFormula (liftTerm (liftTerm s)) (&(Fin.castSucc (Fin.last n)))))

/-- The domain-selection formula: `d` occurs as a first coordinate in `F`. -/
def domainFamilyDef (F d : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (pairMemDef (liftTerm d) (&(Fin.last n)) (liftTerm F))

/-- The graph-selection formula: `r` occurs as a second coordinate in `F`. -/
def graphFamilyDef (F r : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (pairMemDef (&(Fin.last n)) (liftTerm r) (liftTerm F))

/-- One predecessor *witness* shape, right-oriented: `s` is `⟨fixed, z⟩` for a valid branch
`z` of `source`. Private, and split by orientation for the same reason as the closure
shapes — the three cases differ only by argument choice. -/
private def predWitnessRightDef (condSet source fixed s : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm source)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm condSet)) ⊓
      pairDef (liftTerm (liftTerm fixed)) (&(Fin.last (n + 1))) (liftTerm (liftTerm s))))

/-- The left-oriented witness shape: the branch supplies the first coordinate. -/
private def predWitnessLeftDef (condSet source fixed s : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm source)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) (liftTerm (liftTerm condSet)) ⊓
      pairDef (&(Fin.last (n + 1))) (liftTerm (liftTerm fixed)) (liftTerm (liftTerm s))))

/-- **The predecessor relation**, as a formula: `s` is one of the three states the clauses at
`(x, y)` consult. This is what the `Pred` Separation instance carves with. -/
def predSpecDef (condSet x y s : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  predWitnessRightDef condSet y x s ⊔
    (predWitnessLeftDef condSet x y s ⊔ predWitnessLeftDef condSet y x s)

/-- The right-oriented **bound** formula, for Collection: whenever `w` decodes as a branch
`⟨c, z⟩`, the witness is `⟨fixed, z⟩`. Unconditional on `w` — a `w` that is not a coded pair
imposes nothing, which is what makes the witness relation total on its whole index set. Note
that no condition-set guard appears: a bound needs only to *contain* the witnesses, and the
guard is applied later by the `predSpecDef` separation. -/
def predBoundRightDef (fixed w s : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' ∀' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm w)) ⟹
    pairDef (liftTerm (liftTerm fixed)) (&(Fin.last (n + 1))) (liftTerm (liftTerm s)))

/-- The left-oriented bound formula. -/
def predBoundLeftDef (fixed w s : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' ∀' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm w)) ⟹
    pairDef (&(Fin.last (n + 1))) (liftTerm (liftTerm fixed)) (liftTerm (liftTerm s)))

/-- `a` is a package covering the state `⟨x, y⟩`. The state is built by an existential rather
than a term, since the language is function-free. -/
def statePackageAtDef (tagMem tagEq condSet orderCode A x y a :
    memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (pairDef (liftTerm x) (liftTerm y) (&(Fin.last n)) ⊓
    packageAtDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
      (liftTerm A) (&(Fin.last n)) (liftTerm a))

/-- The universal row-coverage condition: every `y` in the domain gives a state `⟨x, y⟩` in
`D`. A named condition rather than an inline conjunct, since it is what the final filter
certifies and what global coverage is read off. -/
def rowCoverageDef (A x D : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm A) ⟹
    pairMemDef (liftTerm x) (&(Fin.last n)) (liftTerm D))

/-- **The row-package predicate**, as a formula: `a` codes an approximation whose domain
covers every state `⟨x, y⟩` with `y ∈ A`. Both conjuncts are load-bearing — the approximation
conditions and the *universal row coverage* — since dropping the second would leave the final
aggregation with no route to global coverage. -/
def rowPackageAtDef (tagMem tagEq condSet orderCode A x a : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm a)) ⊓
    (approximationDef (liftTerm (liftTerm tagMem)) (liftTerm (liftTerm tagEq))
        (liftTerm (liftTerm condSet)) (liftTerm (liftTerm orderCode))
        (liftTerm (liftTerm A)) (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) ⊓
      rowCoverageDef (liftTerm (liftTerm A)) (liftTerm (liftTerm x))
        (&(Fin.castSucc (Fin.last n)))))

section Realization

variable {M : MaterialCarrier.{u}} {tag p x y e R S : memLang.Term (α ⊕ Fin n)}
variable {v : α → M} {xs : Fin n → M}

open MaterialCarrier

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
      StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) := by
  rw [StageEntry]
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
        StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) ((e : ↥M) : ZFSet.{u}) := by
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

/-- **The row-entry law**. Like the stage-entry law it charges nothing: the entry is named,
not asserted to lie anywhere. -/
theorem realize_rowEntryDef
    {tagMem tagEq condSet orderCode history A : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (rowEntryDef tagMem tagEq condSet orderCode history A x e).Realize v xs ↔
      ∃ y ∈ ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}),
        StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) y
          ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) := by
  have hAM : ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) A : ↥M).2
  have hse : ∀ w : ↥M,
      (stageEntryDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (liftTerm history) (liftTerm x) (&(Fin.last n))
          (liftTerm e)).Realize v (Fin.snoc xs w) ↔
        StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) ((w : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) e : ↥M) : ZFSet.{u}) := by
    intro w
    rw [realize_stageEntryDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [rowEntryDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  constructor
  · rintro ⟨w, hw, hs⟩
    exact ⟨(w : ZFSet.{u}), hw, (hse w).1 hs⟩
  · rintro ⟨w, hw, hs⟩
    exact ⟨⟨w, M.mem_trans hw hAM⟩, hw, (hse ⟨w, _⟩).2 hs⟩

/-- **The row law**: the formula realizes to exactly the semantic `RowValue`. As with the
stage law, the extra hypothesis places the candidate entries in the carrier; here it is
needed across the whole domain, and finite closure supplies it. -/
theorem realize_rowValueDef
    {tagMem tagEq condSet orderCode history A row : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag)
    (hentM : ∀ y ∈ ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}),
      ∀ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
        entry memWitnessTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) y ∈ M ∧
          entry eqTag p ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) y ∈ M) :
    (rowValueDef tagMem tagEq condSet orderCode history A x row).Realize v xs ↔
      RowValue ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) row : ↥M) : ZFSet.{u}) := by
  have hrM : ((Term.realize (Sum.elim v xs) row : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) row : ↥M).2
  have hbody : ∀ w : ↥M,
      (rowEntryDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet) (liftTerm orderCode)
          (liftTerm history) (liftTerm A) (liftTerm x) (&(Fin.last n))).Realize v
        (Fin.snoc xs w) ↔
        ∃ y ∈ ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}),
          StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) y ((w : ↥M) : ZFSet.{u}) := by
    intro w
    rw [realize_rowEntryDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  -- Any row entry is a member of the carrier, by finite closure across the domain.
  have hinM : ∀ y ∈ ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}), ∀ c : ZFSet.{u},
      StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) history : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) y c → c ∈ M := by
    rintro y hy c (⟨p, hp, rfl, -⟩ | ⟨p, hp, rfl, -⟩)
    · exact (hentM y hy p hp).1
    · exact (hentM y hy p hp).2
  simp only [rowValueDef, BoundedFormula.realize_all, BoundedFormula.realize_iff, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  constructor
  · intro h c
    constructor
    · intro hc
      exact (hbody ⟨c, M.mem_trans hc hrM⟩).1 ((h ⟨c, M.mem_trans hc hrM⟩).1 hc)
    · rintro ⟨y, hy, hs⟩
      have hcM := hinM y hy c hs
      exact (h ⟨c, hcM⟩).2 ((hbody ⟨c, hcM⟩).2 ⟨y, hy, hs⟩)
  · intro h w
    exact ((h (w : ZFSet.{u})).trans (hbody w).symm)

/-- **The fixed-point law**: the formula realizes to exactly the semantic `CorrectOn`.

One hypothesis beyond the tags: the candidate entries must lie in the carrier, as for every
statement in this layer that quantifies over all sets while the formula quantifies over
carrier elements. That is the genuine finite-construction obligation, discharged by
`entry_mem`.

Nothing is assumed about `D`. That the coordinates of its states are carrier elements is
**structural** — `D` is a carrier element, so transitivity puts the coded state in the
carrier, and descending the Kuratowski pair gives both components. Taking it as a hypothesis
instead would falsely couple this law to `DescentClosed` and make the eventual conjunction
order-dependent. -/
theorem realize_correctOnDef
    {tagMem tagEq condSet orderCode D R : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag)
    (hentM : ∀ a b : ZFSet.{u},
      ZFSet.pair a b ∈ ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) →
      ∀ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
        entry memWitnessTag p a b ∈ M ∧ entry eqTag p a b ∈ M) :
    (correctOnDef tagMem tagEq condSet orderCode D R).Realize v xs ↔
      CorrectOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) := by
  have hRM : ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) R : ↥M).2
  have hDM : ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) D : ↥M).2
  -- Structural, not a hypothesis: a coded state in `D` has both coordinates in the carrier.
  have hstates : ∀ a b : ZFSet.{u},
      ZFSet.pair a b ∈ ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) →
      a ∈ M ∧ b ∈ M := fun a b hab ↦
    ⟨left_mem_of_pair_mem (M.mem_trans hab hDM), right_mem_of_pair_mem (M.mem_trans hab hDM)⟩
  have hbody : ∀ e a b : ↥M,
      (pairMemDef (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))
          (liftTerm (liftTerm (liftTerm D)))).Realize v (Fin.snoc (Fin.snoc (Fin.snoc xs e) a) b) ↔
        ZFSet.pair ((a : ↥M) : ZFSet.{u}) ((b : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) := by
    intro e a b
    rw [realize_pairMemDef]
    simp [realize_liftTerm]
  have hstage : ∀ e a b : ↥M,
      (stageEntryDef (liftTerm (liftTerm (liftTerm tagMem)))
          (liftTerm (liftTerm (liftTerm tagEq))) (liftTerm (liftTerm (liftTerm condSet)))
          (liftTerm (liftTerm (liftTerm orderCode))) (liftTerm (liftTerm (liftTerm R)))
          (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))
          (&(Fin.castSucc (Fin.castSucc (Fin.last n))))).Realize v
        (Fin.snoc (Fin.snoc (Fin.snoc xs e) a) b) ↔
        StageEntry ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u}) ((a : ↥M) : ZFSet.{u})
          ((b : ↥M) : ZFSet.{u}) ((e : ↥M) : ZFSet.{u}) := by
    intro e a b
    rw [realize_stageEntryDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [correctOnDef, BoundedFormula.realize_all, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  constructor
  · intro h e
    constructor
    · intro he
      obtain ⟨a, b, hab, hse⟩ := (h ⟨e, M.mem_trans he hRM⟩).1 he
      exact ⟨(a : ZFSet.{u}), (b : ZFSet.{u}), (hbody ⟨e, _⟩ a b).1 hab,
        (hstage ⟨e, _⟩ a b).1 hse⟩
    · rintro ⟨a, b, hab, hse⟩
      obtain ⟨haM, hbM⟩ := hstates a b hab
      have heM : e ∈ M := by
        rcases hse with ⟨p, hp, rfl, -⟩ | ⟨p, hp, rfl, -⟩
        · exact (hentM a b hab p hp).1
        · exact (hentM a b hab p hp).2
      refine (h ⟨e, heM⟩).2 ⟨⟨a, haM⟩, ⟨b, hbM⟩, (hbody ⟨e, heM⟩ ⟨a, haM⟩ ⟨b, hbM⟩).2 hab, ?_⟩
      exact (hstage ⟨e, heM⟩ ⟨a, haM⟩ ⟨b, hbM⟩).2 hse
  · intro h e
    constructor
    · intro he
      obtain ⟨a, b, hab, hse⟩ := (h (e : ZFSet.{u})).1 he
      obtain ⟨haM, hbM⟩ := hstates a b hab
      exact ⟨⟨a, haM⟩, ⟨b, hbM⟩, (hbody e ⟨a, haM⟩ ⟨b, hbM⟩).2 hab,
        (hstage e ⟨a, haM⟩ ⟨b, hbM⟩).2 hse⟩
    · rintro ⟨a, b, hab, hse⟩
      exact (h (e : ZFSet.{u})).2 ⟨(a : ZFSet.{u}), (b : ZFSet.{u}),
        (hbody e a b).1 hab, (hstage e a b).1 hse⟩

/-- Branch components of a carrier element are carrier elements — the structural bridge the
descent-closure quantifiers need. No axiom, no transitivity hypothesis. -/
private theorem branch_components_mem {S c z : ZFSet.{u}} (hS : S ∈ M)
    (h : ZFSet.pair c z ∈ S) : c ∈ M ∧ z ∈ M :=
  ⟨left_mem_of_pair_mem (M.mem_trans h hS), right_mem_of_pair_mem (M.mem_trans h hS)⟩

private theorem realize_predRightDef {condSet D source fixed : memLang.Term (α ⊕ Fin n)} :
    (predRightDef condSet D source fixed).Realize v xs ↔
      ∀ c z, ZFSet.pair c z ∈ ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) →
        c ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) →
        ZFSet.pair ((Term.realize (Sum.elim v xs) fixed : ↥M) : ZFSet.{u}) z ∈
          ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) := by
  have hsM : ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) source : ↥M).2
  simp only [predRightDef, BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairMemDef]
  exact ⟨fun h c z hb hc ↦ h ⟨c, (branch_components_mem hsM hb).1⟩
      ⟨z, (branch_components_mem hsM hb).2⟩ hb hc,
    fun h c z ↦ h (c : ZFSet.{u}) (z : ZFSet.{u})⟩

private theorem realize_predLeftDef {condSet D source fixed : memLang.Term (α ⊕ Fin n)} :
    (predLeftDef condSet D source fixed).Realize v xs ↔
      ∀ c z, ZFSet.pair c z ∈ ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) →
        c ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) →
        ZFSet.pair z ((Term.realize (Sum.elim v xs) fixed : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) := by
  have hsM : ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) source : ↥M).2
  simp only [predLeftDef, BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairMemDef]
  exact ⟨fun h c z hb hc ↦ h ⟨c, (branch_components_mem hsM hb).1⟩
      ⟨z, (branch_components_mem hsM hb).2⟩ hb hc,
    fun h c z ↦ h (c : ZFSet.{u}) (z : ZFSet.{u})⟩

/-- **The descent-closure law**: the formula realizes to exactly the semantic `DescentClosed`.

**No auxiliary hypotheses and no theory axioms.** Every quantifier bridge is structural: a
member of `D` is a carrier element by transitivity, a coded state in `D` has both coordinates
in the carrier by descending the Kuratowski pair, and a branch of a carrier element likewise.
Nothing is constructed, so nothing is charged — the finite-entry obligation lives entirely on
the `correctOnDef` side of the eventual conjunction. -/
theorem realize_descentClosedDef {condSet A D : memLang.Term (α ⊕ Fin n)} :
    (descentClosedDef condSet A D).Realize v xs ↔
      DescentClosed ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) := by
  have hDM : ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) D : ↥M).2
  have hAM : ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) A : ↥M).2
  rw [descentClosedDef, DescentClosed]
  simp only [BoundedFormula.realize_inf]
  refine and_congr ?_ ?_
  · -- every member of `D` decodes to a state over `A`
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp,
      BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
      BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
      Matrix.cons_val_one, realize_liftTerm, realize_pairDef]
    constructor
    · intro h s hs
      obtain ⟨a, b, haA, hbA, hp⟩ := h ⟨s, M.mem_trans hs hDM⟩ hs
      exact ⟨(a : ZFSet.{u}), haA, (b : ZFSet.{u}), hbA, hp⟩
    · intro h s hs
      obtain ⟨a, haA, b, hbA, hp⟩ := h (s : ZFSet.{u}) hs
      exact ⟨⟨a, M.mem_trans haA hAM⟩, ⟨b, M.mem_trans hbA hAM⟩, haA, hbA, hp⟩
  · -- all three predecessor shapes stay in `D`
    simp only [BoundedFormula.realize_all, BoundedFormula.realize_imp,
      BoundedFormula.realize_inf, realize_pairMemDef, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm,
      realize_predRightDef, realize_predLeftDef]
    exact ⟨fun h x y hxy ↦ h ⟨x, left_mem_of_pair_mem (M.mem_trans hxy hDM)⟩
        ⟨y, right_mem_of_pair_mem (M.mem_trans hxy hDM)⟩ hxy,
      fun h x y ↦ h (x : ZFSet.{u}) (y : ZFSet.{u})⟩

/-- **The approximation law**, and the point of the factoring: its hypotheses are exactly
those of `realize_correctOnDef`. The descent-closure conjunct contributes none — it needs no
auxiliary hypothesis and charges no theory axiom — so the two sides may be proved in either
order and the ledger reads off the correctness side alone. -/
theorem realize_approximationDef
    {tagMem tagEq condSet orderCode A D R : memLang.Term (α ⊕ Fin n)}
    (hm : ((Term.realize (Sum.elim v xs) tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) tagEq : ↥M) : ZFSet.{u}) = natCode eqTag)
    (hentM : ∀ a b : ZFSet.{u},
      ZFSet.pair a b ∈ ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) →
      ∀ p ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}),
        entry memWitnessTag p a b ∈ M ∧ entry eqTag p a b ∈ M) :
    (approximationDef tagMem tagEq condSet orderCode A D R).Realize v xs ↔
      (DescentClosed ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) ∧
        CorrectOn ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u})
          ((Term.realize (Sum.elim v xs) R : ↥M) : ZFSet.{u})) := by
  rw [approximationDef]
  simp only [BoundedFormula.realize_inf]
  exact and_congr realize_descentClosedDef (realize_correctOnDef hm hq hentM)

/-- The other component of a package in a carrier element is a carrier element — the bridge
the selection quantifiers need, structural and axiom-free. -/
private theorem component_mem {F a b : ZFSet.{u}} (hF : F ∈ M) (h : ZFSet.pair a b ∈ F) :
    a ∈ M ∧ b ∈ M :=
  ⟨left_mem_of_pair_mem (M.mem_trans h hF), right_mem_of_pair_mem (M.mem_trans h hF)⟩

/-- **The domain-selection law.** No hypotheses and no theory axioms. -/
theorem realize_domainFamilyDef {F d : memLang.Term (α ⊕ Fin n)} :
    (domainFamilyDef F d).Realize v xs ↔
      ∃ R, ZFSet.pair ((Term.realize (Sum.elim v xs) d : ↥M) : ZFSet.{u}) R ∈
        ((Term.realize (Sum.elim v xs) F : ↥M) : ZFSet.{u}) := by
  have hFM : ((Term.realize (Sum.elim v xs) F : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) F : ↥M).2
  simp only [domainFamilyDef, BoundedFormula.realize_ex, realize_pairMemDef, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Fin.snoc_last, realize_liftTerm]
  exact ⟨fun ⟨R, hR⟩ ↦ ⟨(R : ZFSet.{u}), hR⟩,
    fun ⟨R, hR⟩ ↦ ⟨⟨R, (component_mem hFM hR).2⟩, hR⟩⟩

/-- **The graph-selection law.** Likewise. -/
theorem realize_graphFamilyDef {F r : memLang.Term (α ⊕ Fin n)} :
    (graphFamilyDef F r).Realize v xs ↔
      ∃ D, ZFSet.pair D ((Term.realize (Sum.elim v xs) r : ↥M) : ZFSet.{u}) ∈
        ((Term.realize (Sum.elim v xs) F : ↥M) : ZFSet.{u}) := by
  have hFM : ((Term.realize (Sum.elim v xs) F : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) F : ↥M).2
  simp only [graphFamilyDef, BoundedFormula.realize_ex, realize_pairMemDef, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Fin.snoc_last, realize_liftTerm]
  exact ⟨fun ⟨D, hD⟩ ↦ ⟨(D : ZFSet.{u}), hD⟩,
    fun ⟨D, hD⟩ ↦ ⟨⟨D, (component_mem hFM hD).1⟩, hD⟩⟩

private theorem realize_predWitnessRightDef
    {condSet source fixed s : memLang.Term (α ⊕ Fin n)} :
    (predWitnessRightDef condSet source fixed s).Realize v xs ↔
      ∃ c z, ZFSet.pair c z ∈ ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∧
        c ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∧
        ((Term.realize (Sum.elim v xs) s : ↥M) : ZFSet.{u}) =
          ZFSet.pair ((Term.realize (Sum.elim v xs) fixed : ↥M) : ZFSet.{u}) z := by
  have hsM : ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) source : ↥M).2
  simp only [predWitnessRightDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairMemDef, realize_pairDef]
  exact ⟨fun ⟨c, z, hb, hc, hp⟩ ↦ ⟨(c : ZFSet.{u}), (z : ZFSet.{u}), hb, hc, hp⟩,
    fun ⟨c, z, hb, hc, hp⟩ ↦ ⟨⟨c, (branch_components_mem hsM hb).1⟩,
      ⟨z, (branch_components_mem hsM hb).2⟩, hb, hc, hp⟩⟩

private theorem realize_predWitnessLeftDef
    {condSet source fixed s : memLang.Term (α ⊕ Fin n)} :
    (predWitnessLeftDef condSet source fixed s).Realize v xs ↔
      ∃ c z, ZFSet.pair c z ∈ ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∧
        c ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) ∧
        ((Term.realize (Sum.elim v xs) s : ↥M) : ZFSet.{u}) =
          ZFSet.pair z ((Term.realize (Sum.elim v xs) fixed : ↥M) : ZFSet.{u}) := by
  have hsM : ((Term.realize (Sum.elim v xs) source : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) source : ↥M).2
  simp only [predWitnessLeftDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairMemDef, realize_pairDef]
  exact ⟨fun ⟨c, z, hb, hc, hp⟩ ↦ ⟨(c : ZFSet.{u}), (z : ZFSet.{u}), hb, hc, hp⟩,
    fun ⟨c, z, hb, hc, hp⟩ ↦ ⟨⟨c, (branch_components_mem hsM hb).1⟩,
      ⟨z, (branch_components_mem hsM hb).2⟩, hb, hc, hp⟩⟩

/-- **The predecessor law**: the formula realizes to exactly the semantic `PredSpec`. **No
auxiliary hypotheses and no theory axioms** — every bridge is the structural one for branch
components. -/
theorem realize_predSpecDef {condSet x y s : memLang.Term (α ⊕ Fin n)} :
    (predSpecDef condSet x y s).Realize v xs ↔
      PredSpec ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) s : ↥M) : ZFSet.{u}) := by
  rw [predSpecDef, PredSpec]
  simp only [BoundedFormula.realize_sup]
  exact or_congr realize_predWitnessRightDef
    (or_congr realize_predWitnessLeftDef realize_predWitnessLeftDef)

/-- **The right bound law.** No hypotheses and no theory axioms. -/
theorem realize_predBoundRightDef {fixed w s : memLang.Term (α ⊕ Fin n)} :
    (predBoundRightDef fixed w s).Realize v xs ↔
      ∀ c z, ((Term.realize (Sum.elim v xs) w : ↥M) : ZFSet.{u}) = ZFSet.pair c z →
        ((Term.realize (Sum.elim v xs) s : ↥M) : ZFSet.{u}) =
          ZFSet.pair ((Term.realize (Sum.elim v xs) fixed : ↥M) : ZFSet.{u}) z := by
  have hwM : ((Term.realize (Sum.elim v xs) w : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) w : ↥M).2
  simp only [predBoundRightDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    realize_liftTerm, realize_pairDef]
  refine ⟨fun h c z hcz ↦ ?_, fun h c z ↦ h (c : ZFSet.{u}) (z : ZFSet.{u})⟩
  have hpM : ZFSet.pair c z ∈ M := hcz ▸ hwM
  exact h ⟨c, left_mem_of_pair_mem hpM⟩ ⟨z, right_mem_of_pair_mem hpM⟩ hcz

/-- **The left bound law.** -/
theorem realize_predBoundLeftDef {fixed w s : memLang.Term (α ⊕ Fin n)} :
    (predBoundLeftDef fixed w s).Realize v xs ↔
      ∀ c z, ((Term.realize (Sum.elim v xs) w : ↥M) : ZFSet.{u}) = ZFSet.pair c z →
        ((Term.realize (Sum.elim v xs) s : ↥M) : ZFSet.{u}) =
          ZFSet.pair z ((Term.realize (Sum.elim v xs) fixed : ↥M) : ZFSet.{u}) := by
  have hwM : ((Term.realize (Sum.elim v xs) w : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) w : ↥M).2
  simp only [predBoundLeftDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    realize_liftTerm, realize_pairDef]
  refine ⟨fun h c z hcz ↦ ?_, fun h c z ↦ h (c : ZFSet.{u}) (z : ZFSet.{u})⟩
  have hpM : ZFSet.pair c z ∈ M := hcz ▸ hwM
  exact h ⟨c, left_mem_of_pair_mem hpM⟩ ⟨z, right_mem_of_pair_mem hpM⟩ hcz

/-- **The row-coverage law.** No hypotheses and no theory axioms. -/
theorem realize_rowCoverageDef {A D : memLang.Term (α ⊕ Fin n)} :
    (rowCoverageDef A x D).Realize v xs ↔
      ∀ y ∈ ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}),
        ZFSet.pair ((Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}) y ∈
          ((Term.realize (Sum.elim v xs) D : ↥M) : ZFSet.{u}) := by
  have hAM : ((Term.realize (Sum.elim v xs) A : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) A : ↥M).2
  simp only [rowCoverageDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm, realize_pairMemDef]
  exact ⟨fun h y hy ↦ h ⟨y, M.mem_trans hy hAM⟩ hy, fun h y ↦ h (y : ZFSet.{u})⟩

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
