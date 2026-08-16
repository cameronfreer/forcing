/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.GameAdd
import Mathlib.SetTheory.ZFC.Rank
import Forcing.Material.RecursionEntry
import Forcing.Material.ForcingPresentation
import Forcing.Material.NameCoding
import Forcing.Name.Atomic

/-!
# The atomic recursion: coherence clauses and descent machinery

The coded clauses of the atomic recursion, mirroring the external kernel exactly, together
with the rank machinery its inductions run on. Uniqueness, locality, existence, correctness,
and the first-order compilation of these clauses follow in subsequent steps.

**The clauses are ZFSet-level semantic predicates**, parameterized by the coded condition set
and order code as *plain sets*. Two dependency facts fall out of that shape and are worth
recording: the clauses need the coded forcing presentation and transitivity of the domain
`A`, but **neither `A ∈ M` nor any theory axiom**; and **`InternalNameCoding` is not needed
here at all** — raw coherence treats members shaped like coded branches directly, and the
name coding enters only with correctness against the typed relations.

Coherence is imposed **exactly** — membership in each tagged slice is an `↔` with its clause,
not mere closure under it — and only for valid condition codes and domain elements. Other
elements of a candidate graph stay unconstrained, so the uniqueness to come is
**observational**: agreement on the two tagged slices, never whole-set equality. For
malformed ambient sets the branch quantifiers range only over branches whose first coordinate
is a condition code, which makes the recursion total on arbitrary `x, y ∈ A` without a master
predicate of name codes.

Orientation is the one thing that could typecheck while being mathematically wrong: the
equality and density clauses nest three order comparisons, so each occurrence has a named
typed reading (`pair_mem_orderCode_iff` and the `orientation` theorems) fixing its direction
against the stored smaller-is-stronger convention.

The external kernel (`Forcing/Name/Atomic.lean`) descends along the *structurally visible*
immediate-subname relation. The material representation inserts several Kuratowski-pair
membership levels between a name code and the code of a subname, so the same descent is not
directly available. **Rank removes those encoding layers without making them part of the
recursion clause.**

Four constraints govern its use, and this module observes all of them:

* rank is **metatheoretic proof machinery only** — it never appears in an internal coherence
  formula and is never charged to a ground theory;
* the well-founded measure stays **local**, like the `Sym2` termination instance of the
  external kernel;
* rank is kept **out of the public uniqueness and locality statements** (which is why
  everything here is `private`);
* **no general rank-descent API is factored** until a second consumer appears.

The two descent facts are kept apart deliberately: the first is about *rank*, the second
about *closure of the recursion domain*, and conflating them would let rank descent stand in
for domain closure. Using ambient rank does **not** reintroduce Foundation as a ground-theory
cost: it proves externally that any two coherent candidate graphs agree, while Separation and
Collection remain the only costs of constructing such a graph inside the carrier.

## Descent-closed correctness

`CorrectOn D R` is the form the fixed-point recursion is built in: the clauses are evaluated
against `R` itself, and `R` has no members beyond the entries those clauses admit at states in
`D`. Controlling **support**, not merely the clauses, is what makes approximations safe to
union — see `correctOn_unique`. Domains are descent-closed *sets of states*, not squares,
because a square domain would force the transitive closure of a pair and so charge Infinity.

## Stages

`StageValue` names the value the construction assigns at one state, computed against an
already-collected history. It is introduced **before any scheme is consumed**, so the first
ledger charge can describe the construction rather than two arbitrary sentences. Its four
properties are functionality (`stageValue_unique`), totality from a bound
(`stageValue_exists_of_bound`, the Collection pressure test), and dependence on observable
predecessors only (`stageValue_congr`, and `stageValue_congr_of_coherent` via locality).
-/

universe u

namespace Forcing

namespace AtomicRecursion

/-! ### The two descent facts -/

/-- A branch code sits three Kuratowski levels above the subname code it carries, so the
subname code has strictly smaller rank. *Rank only* — nothing about the domain. -/
private theorem rank_lt_of_pair_mem {c z w : ZFSet.{u}} (h : ZFSet.pair c z ∈ w) :
    z.rank < w.rank := by
  have h₁ : z.rank < ({c, z} : ZFSet.{u}).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  have h₂ : ({c, z} : ZFSet.{u}).rank < (ZFSet.pair c z).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  exact (h₁.trans h₂).trans (ZFSet.rank_lt_of_mem h)

/-- In a transitive domain, the subname code carried by a branch of a member is itself a
member. *Domain closure only* — nothing about rank. -/
private theorem mem_of_pair_mem {A c z w : ZFSet.{u}} (hA : A.IsTransitive) (hw : w ∈ A)
    (h : ZFSet.pair c z ∈ w) : z ∈ A :=
  hA.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
    (hA.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) (hA.mem_trans h hw))

/-! ### The measure, and the three descent shapes

The unordered pair of ranks under `Sym2.GameAdd (· < ·)`, reproducing exactly the three
descent shapes of the external kernel: lower the right coordinate, lower the left, and
lower-after-swap. -/

private noncomputable def rankPair (x y : ZFSet.{u}) : Sym2 Ordinal.{u} :=
  s(x.rank, y.rank)

private theorem rankPair_wf : WellFounded (Sym2.GameAdd ((· < ·) : Ordinal → Ordinal → Prop)) :=
  (Ordinal.lt_wf).sym2_gameAdd

/-- Shape 1 — a membership witness descends to forced equality against a branch of the right
coordinate. -/
private theorem descent_right {c z x y : ZFSet.{u}} (h : ZFSet.pair c z ∈ y) :
    Sym2.GameAdd (· < ·) (rankPair x z) (rankPair x y) :=
  Sym2.GameAdd.snd (rank_lt_of_pair_mem h)

/-- Shape 2 — forced equality descends to a membership witness for a branch of the left
coordinate. -/
private theorem descent_left {c z x y : ZFSet.{u}} (h : ZFSet.pair c z ∈ x) :
    Sym2.GameAdd (· < ·) (rankPair z y) (rankPair x y) :=
  Sym2.GameAdd.fst (rank_lt_of_pair_mem h)

/-- Shape 3 — forced equality descends to a membership witness for a branch of the right
coordinate, with the arguments swapped. -/
private theorem descent_swap {c z x y : ZFSet.{u}} (h : ZFSet.pair c z ∈ y) :
    Sym2.GameAdd (· < ·) (rankPair z x) (rankPair x y) :=
  Sym2.GameAdd.fst_snd (rank_lt_of_pair_mem h)

/-! ### The coherence clauses -/

section Clauses

variable (condSet orderCode : ZFSet.{u})

/-- **Density of the membership-witness slice** below a condition: every strengthening has a
further strengthening carrying a witness. -/
def DenseMem (R q x y : ZFSet.{u}) : Prop :=
  ∀ r ∈ condSet, ZFSet.pair r q ∈ orderCode →
    ∃ s ∈ condSet, ZFSet.pair s r ∈ orderCode ∧ entry memWitnessTag s x y ∈ R

/-- **The membership-witness clause**: some branch of `y` is activated by `q` and its subname
is forced equal to `x`. -/
def MemClause (R q x y : ZFSet.{u}) : Prop :=
  ∃ c z, ZFSet.pair c z ∈ y ∧ c ∈ condSet ∧ ZFSet.pair q c ∈ orderCode ∧
    entry eqTag q x z ∈ R

/-- **The forced-equality clause**: the two inclusions, each saying that every branch
activated below `p` on one side is densely a member of the other. Branch quantifiers range
only over branches whose first coordinate is a condition code, so the clause is total on
arbitrary domain elements. -/
def EqClause (R p x y : ZFSet.{u}) : Prop :=
  (∀ c z, ZFSet.pair c z ∈ x → c ∈ condSet → ∀ q ∈ condSet,
      ZFSet.pair q p ∈ orderCode → ZFSet.pair q c ∈ orderCode →
      DenseMem condSet orderCode R q z y) ∧
    (∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet → ∀ q ∈ condSet,
      ZFSet.pair q p ∈ orderCode → ZFSet.pair q c ∈ orderCode →
      DenseMem condSet orderCode R q z x)

/-- **Coherence on a domain**: each tagged slice of the graph is *exactly* its clause, at
valid condition codes and domain elements. Elements outside those slices are unconstrained —
uniqueness will therefore be observational. -/
def AtomicCoherentOn (A R : ZFSet.{u}) : Prop :=
  (∀ q ∈ condSet, ∀ x ∈ A, ∀ y ∈ A,
      (entry memWitnessTag q x y ∈ R ↔ MemClause condSet orderCode R q x y)) ∧
    (∀ p ∈ condSet, ∀ x ∈ A, ∀ y ∈ A,
      (entry eqTag p x y ∈ R ↔ EqClause condSet orderCode R p x y))

end Clauses

/-! ### Domain preservation

The recursive arguments of every clause stay inside the domain — proved from transitivity
alone, with no rank and no theory axiom, so that rank descent never stands in for closure of
the recursion domain. -/

/-- The subname code carried by a branch of a domain element is itself in the domain. -/
theorem branch_mem_domain {A c z y : ZFSet.{u}} (hA : A.IsTransitive) (hy : y ∈ A)
    (h : ZFSet.pair c z ∈ y) : z ∈ A :=
  mem_of_pair_mem hA hy h

/-- The recursive argument of the membership-witness clause stays in the domain. -/
theorem memClause_domain {condSet orderCode A R q x y : ZFSet.{u}} (hA : A.IsTransitive)
    (hy : y ∈ A) (h : MemClause condSet orderCode R q x y) :
    ∃ c z, ZFSet.pair c z ∈ y ∧ z ∈ A ∧ ZFSet.pair q c ∈ orderCode ∧
      entry eqTag q x z ∈ R := by
  obtain ⟨c, z, hb, -, hord, he⟩ := h
  exact ⟨c, z, hb, branch_mem_domain hA hy hb, hord, he⟩

/-! ### Orientation

Each order comparison of the clauses gets a named typed reading. A reversal would still
typecheck against the raw `ZFSet` definitions, so these are the guard rails. -/

section Orientation

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
  (Pres : InternalForcingPresentation M P)

/-- The stored orientation: a coded pair lies in the order code exactly when the *first*
condition strengthens the second (smaller is stronger). -/
theorem pair_mem_orderCode_iff (a b : P) :
    ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr a)) (ZFSet.mk (Pres.conditionCode.repr b)) ∈
        (Pres.orderCode : ZFSet.{u}) ↔ a ≤ b :=
  Pres.order_iff b a

/-- Orientation of `MemClause`: its comparison says the witness condition **strengthens the
branch's** condition. -/
theorem memClause_orientation {R x y z : ZFSet.{u}} {q c : P}
    (hb : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr c)) z ∈ y)
    (hc : ZFSet.mk (Pres.conditionCode.repr c) ∈ (Pres.conditionSet : ZFSet.{u}))
    (hle : q ≤ c)
    (he : entry eqTag (ZFSet.mk (Pres.conditionCode.repr q)) x z ∈ R) :
    MemClause (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R
      (ZFSet.mk (Pres.conditionCode.repr q)) x y :=
  ⟨_, z, hb, hc, (pair_mem_orderCode_iff Pres q c).2 hle, he⟩

/-- Orientation of `DenseMem`: the hypothesis reads "`r` strengthens `q`" and the conclusion
"`s` strengthens `r`" — density *below*, not above. -/
theorem denseMem_orientation {R q x y : ZFSet.{u}} {r : P}
    (h : DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R q x y)
    (hr : ZFSet.mk (Pres.conditionCode.repr r) ∈ (Pres.conditionSet : ZFSet.{u}))
    (hrq : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr r)) q ∈ (Pres.orderCode : ZFSet.{u})) :
    ∃ s ∈ (Pres.conditionSet : ZFSet.{u}),
      ZFSet.pair s (ZFSet.mk (Pres.conditionCode.repr r)) ∈ (Pres.orderCode : ZFSet.{u}) ∧
        entry memWitnessTag s x y ∈ R :=
  h _ hr hrq

/-- Orientation of `EqClause`: its comparisons read "`q` strengthens `p`" and "`q`
strengthens the branch's condition" — both downward. -/
theorem eqClause_orientation {R p x y z : ZFSet.{u}} {c q : P}
    (h : EqClause (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R p x y)
    (hb : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr c)) z ∈ x)
    (hc : ZFSet.mk (Pres.conditionCode.repr c) ∈ (Pres.conditionSet : ZFSet.{u}))
    (hq : ZFSet.mk (Pres.conditionCode.repr q) ∈ (Pres.conditionSet : ZFSet.{u}))
    (hqp : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) p ∈
      (Pres.orderCode : ZFSet.{u}))
    (hqc : q ≤ c) :
    DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R
      (ZFSet.mk (Pres.conditionCode.repr q)) z y :=
  h.1 _ z hb hc _ hq hqp ((pair_mem_orderCode_iff Pres q c).2 hqc)

end Orientation

/-! ### Observational agreement, and locality

Coherence constrains only the two tagged slices, so the right notion of sameness is
**observational agreement at a state**, never equality of graphs. Locality is the primary
theorem — two graphs coherent over *different* domains agree at every state lying in both —
and same-domain uniqueness is its specialization.

The clause-congruence lemmas below know nothing about rank or domains, which leaves the
induction itself as pure dependency routing: rank supplies descent, domain preservation
supplies eligibility for the induction hypothesis. -/

section Locality

variable {condSet orderCode : ZFSet.{u}}

/-- Two candidate graphs **agree at a state**: their two tagged slices coincide there. -/
def AgreeAt (condSet R S x y : ZFSet.{u}) : Prop :=
  (∀ p ∈ condSet, entry memWitnessTag p x y ∈ R ↔ entry memWitnessTag p x y ∈ S) ∧
    (∀ p ∈ condSet, entry eqTag p x y ∈ R ↔ entry eqTag p x y ∈ S)

/-- Congruence for the density clause: agreement of the membership slice suffices. -/
private theorem denseMem_congr {R S q x y : ZFSet.{u}}
    (h : ∀ p ∈ condSet, entry memWitnessTag p x y ∈ R ↔ entry memWitnessTag p x y ∈ S) :
    DenseMem condSet orderCode R q x y ↔ DenseMem condSet orderCode S q x y := by
  constructor
  · intro hd r hr hrq
    obtain ⟨s, hs, hsr, he⟩ := hd r hr hrq
    exact ⟨s, hs, hsr, (h s hs).1 he⟩
  · intro hd r hr hrq
    obtain ⟨s, hs, hsr, he⟩ := hd r hr hrq
    exact ⟨s, hs, hsr, (h s hs).2 he⟩

/-- Congruence for the membership clause: agreement of the equality slice at every relevant
state suffices. -/
private theorem memClause_congr {R S q x y : ZFSet.{u}} (hq : q ∈ condSet)
    (h : ∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet →
      ∀ p ∈ condSet, (entry eqTag p x z ∈ R ↔ entry eqTag p x z ∈ S)) :
    MemClause condSet orderCode R q x y ↔ MemClause condSet orderCode S q x y := by
  constructor
  · rintro ⟨c, z, hb, hc, hord, he⟩
    exact ⟨c, z, hb, hc, hord, (h c z hb hc q hq).1 he⟩
  · rintro ⟨c, z, hb, hc, hord, he⟩
    exact ⟨c, z, hb, hc, hord, (h c z hb hc q hq).2 he⟩

/-- Congruence for the equality clause: the two families of density agreements suffice. -/
private theorem eqClause_congr {R S p x y : ZFSet.{u}}
    (h₁ : ∀ c z, ZFSet.pair c z ∈ x → c ∈ condSet → ∀ q,
      (DenseMem condSet orderCode R q z y ↔ DenseMem condSet orderCode S q z y))
    (h₂ : ∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet → ∀ q,
      (DenseMem condSet orderCode R q z x ↔ DenseMem condSet orderCode S q z x)) :
    EqClause condSet orderCode R p x y ↔ EqClause condSet orderCode S p x y := by
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨fun c z hb hc q hqm hqp hqc ↦ (h₁ c z hb hc q).1 (hx c z hb hc q hqm hqp hqc),
      fun c z hb hc q hqm hqp hqc ↦ (h₂ c z hb hc q).1 (hy c z hb hc q hqm hqp hqc)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨fun c z hb hc q hqm hqp hqc ↦ (h₁ c z hb hc q).2 (hx c z hb hc q hqm hqp hqc),
      fun c z hb hc q hqm hqp hqc ↦ (h₂ c z hb hc q).2 (hy c z hb hc q hqm hqp hqc)⟩

/-- **Locality**: graphs coherent over *different* domains agree at every state lying in
both. Consumes only exact coherence, transitivity, and ambient rank — no material
membership, no scheme, no name coding, and no forcing relation. -/
theorem agreeAt_of_coherent {A B R S : ZFSet.{u}} (hA : A.IsTransitive) (hB : B.IsTransitive)
    (hR : AtomicCoherentOn condSet orderCode A R)
    (hS : AtomicCoherentOn condSet orderCode B S) :
    ∀ x y, x ∈ A → y ∈ A → x ∈ B → y ∈ B → AgreeAt condSet R S x y := by
  have hwf : WellFounded fun u v : ZFSet.{u} × ZFSet.{u} ↦
      Sym2.GameAdd (· < ·) (rankPair u.1 u.2) (rankPair v.1 v.2) :=
    InvImage.wf _ rankPair_wf
  suffices H : ∀ u : ZFSet.{u} × ZFSet.{u}, u.1 ∈ A → u.2 ∈ A → u.1 ∈ B → u.2 ∈ B →
      AgreeAt condSet R S u.1 u.2 from fun x y hxA hyA hxB hyB ↦ H (x, y) hxA hyA hxB hyB
  intro u
  induction u using hwf.induction with
  | _ u ih =>
    obtain ⟨x, y⟩ := u
    intro hxA hyA hxB hyB
    refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
    · rw [hR.1 p hp x hxA y hyA, hS.1 p hp x hxB y hyB]
      exact memClause_congr hp fun c z hb hc ↦
        (ih (x, z) (descent_right hb) hxA (branch_mem_domain hA hyA hb) hxB
          (branch_mem_domain hB hyB hb)).2
    · rw [hR.2 p hp x hxA y hyA, hS.2 p hp x hxB y hyB]
      refine eqClause_congr (fun c z hb hc q ↦ denseMem_congr ?_)
        (fun c z hb hc q ↦ denseMem_congr ?_)
      · exact (ih (z, y) (descent_left hb) (branch_mem_domain hA hxA hb) hyA
          (branch_mem_domain hB hxB hb) hyB).1
      · exact (ih (z, x) (descent_swap hb) (branch_mem_domain hA hyA hb) hxA
          (branch_mem_domain hB hyB hb) hxB).1

/-- **Observational uniqueness**: two graphs coherent over the same domain agree at every
state of it. This is also the junk-independence certificate — coherence never mentions
elements outside the two tagged slices, so candidate graphs may differ arbitrarily elsewhere
with no semantic effect, and equality of graphs is neither claimed nor true. -/
theorem agreeAt_of_coherent_same {A R S : ZFSet.{u}} (hA : A.IsTransitive)
    (hR : AtomicCoherentOn condSet orderCode A R)
    (hS : AtomicCoherentOn condSet orderCode A S) :
    ∀ x y, x ∈ A → y ∈ A → AgreeAt condSet R S x y :=
  fun x y hx hy ↦ agreeAt_of_coherent hA hA hR hS x y hx hy hx hy

end Locality

/-! ### Stages

The recursion is built stage by stage: the stage at a state is the single set holding **both**
tagged slices there, computed from the already-collected predecessor history. Naming it before
any scheme is consumed is what makes the first ledger charge describe the *construction*
rather than two arbitrary sentences.

Three facts matter before Separation and Collection appear. The relation is **functional** in
its value, so a stage is determined by its history. It is **total** — every state has a stage,
including malformed ones — which is the Collection pressure test: Collection needs a total
witness relation on its indexing set, and here malformed members simply fail the clause
guards and contribute nothing, exactly as they do in coherence. And it depends only on the
**observable predecessor slices**, so histories agreeing there give equal stages. -/

section Stage

variable {condSet orderCode : ZFSet.{u}}

/-- A **stage entry** at a state: one of the two tagged entries whose clause succeeds against
`history`. Members of `x` and `y` that are not branch-shaped are ignored exactly as the
coherence clauses ignore them — the clause guards do the work, so no separate validity filter
is needed. -/
def StageEntry (condSet orderCode history x y e : ZFSet.{u}) : Prop :=
  (∃ p ∈ condSet, e = entry memWitnessTag p x y ∧
    MemClause condSet orderCode history p x y) ∨
  (∃ p ∈ condSet, e = entry eqTag p x y ∧ EqClause condSet orderCode history p x y)

/-- The stage at a state: the set holding both tagged slices, computed against `history`. -/
def StageValue (condSet orderCode history x y value : ZFSet.{u}) : Prop :=
  ∀ e, e ∈ value ↔ StageEntry condSet orderCode history x y e

/-- **Functionality**: a history determines the stage. -/
theorem stageValue_unique {history x y v₁ v₂ : ZFSet.{u}}
    (h₁ : StageValue condSet orderCode history x y v₁)
    (h₂ : StageValue condSet orderCode history x y v₂) : v₁ = v₂ :=
  ZFSet.ext fun e ↦ (h₁ e).trans (h₂ e).symm

/-- **Totality from a bound** — the Collection pressure test. Given any set containing the
candidate entries, the stage exists: it is carved out by separation, and the clause guards
discard whatever is not a genuine coded branch. **No assumption is made that every member of
`x` or `y` is a coded branch**, so the witness relation is total on its whole indexing set,
which is what Collection will require.

The bound is a parameter rather than constructed here, and deliberately so: this is exactly
the shape the internal argument takes, where a named Separation instance carves the stage
from a constructed bound. Externally the bound could be built by replacement, but that would
misrepresent the internal cost. -/
theorem stageValue_exists_of_bound {history x y bound : ZFSet.{u}}
    (hb : ∀ p ∈ condSet, entry memWitnessTag p x y ∈ bound ∧ entry eqTag p x y ∈ bound) :
    ∃ value, StageValue condSet orderCode history x y value := by
  classical
  refine ⟨ZFSet.sep (StageEntry condSet orderCode history x y) bound, fun e ↦ ?_⟩
  rw [ZFSet.mem_sep]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rcases h with ⟨p, hp, rfl, -⟩ | ⟨p, hp, rfl, -⟩
  · exact (hb p hp).1
  · exact (hb p hp).2

/-- **Dependence on observable predecessors only**: histories that agree at every state
consulted by the clauses give the same stage. The agreement needed is exactly the
observational one from locality. -/
theorem stageValue_congr {h₁ h₂ x y v₁ v₂ : ZFSet.{u}}
    (hmem : ∀ p ∈ condSet, MemClause condSet orderCode h₁ p x y ↔
      MemClause condSet orderCode h₂ p x y)
    (heq : ∀ p ∈ condSet, EqClause condSet orderCode h₁ p x y ↔
      EqClause condSet orderCode h₂ p x y)
    (hv₁ : StageValue condSet orderCode h₁ x y v₁)
    (hv₂ : StageValue condSet orderCode h₂ x y v₂) : v₁ = v₂ := by
  refine ZFSet.ext fun e ↦ (hv₁ e).trans (Iff.trans ?_ (hv₂ e).symm)
  unfold StageEntry
  constructor
  · rintro (⟨p, hp, he, hc⟩ | ⟨p, hp, he, hc⟩)
    · exact Or.inl ⟨p, hp, he, (hmem p hp).1 hc⟩
    · exact Or.inr ⟨p, hp, he, (heq p hp).1 hc⟩
  · rintro (⟨p, hp, he, hc⟩ | ⟨p, hp, he, hc⟩)
    · exact Or.inl ⟨p, hp, he, (hmem p hp).2 hc⟩
    · exact Or.inr ⟨p, hp, he, (heq p hp).2 hc⟩

/-- **Locality for stages**: two histories coherent over *different* transitive domains
produce the same stage at any state lying in both. This is the form the construction uses,
and it consumes exactly what locality consumes — coherence, transitivity, and rank. No
scheme, no name coding, and no forcing relation. -/
theorem stageValue_congr_of_coherent {A B h₁ h₂ x y v₁ v₂ : ZFSet.{u}}
    (hA : A.IsTransitive) (hB : B.IsTransitive)
    (hc₁ : AtomicCoherentOn condSet orderCode A h₁)
    (hc₂ : AtomicCoherentOn condSet orderCode B h₂)
    (hxA : x ∈ A) (hyA : y ∈ A) (hxB : x ∈ B) (hyB : y ∈ B)
    (hv₁ : StageValue condSet orderCode h₁ x y v₁)
    (hv₂ : StageValue condSet orderCode h₂ x y v₂) : v₁ = v₂ := by
  have hag := agreeAt_of_coherent hA hB hc₁ hc₂
  refine stageValue_congr (fun p hp ↦ ?_) (fun p hp ↦ ?_) hv₁ hv₂
  · exact memClause_congr hp fun c z hb hc ↦
      (hag x z hxA (mem_of_pair_mem hA hyA hb) hxB (mem_of_pair_mem hB hyB hb)).2
  · refine eqClause_congr (fun c z hb hc q ↦ denseMem_congr ?_)
      (fun c z hb hc q ↦ denseMem_congr ?_)
    · exact (hag z y (mem_of_pair_mem hA hxA hb) hyA (mem_of_pair_mem hB hxB hb) hyB).1
    · exact (hag z x (mem_of_pair_mem hA hyA hb) hxA (mem_of_pair_mem hB hyB hb) hxB).1

end Stage

/-! ### Rows

Aggregation, not recursion. A **row** collects the stage entries at every state sharing a
first coordinate. `rankPair` remains the recursion order throughout; rows exist only because
a set of entries has to be assembled *inside* the carrier, and Collection's outputs are sets
of stages rather than sets of entries.

`RowValue` is stated as an **exact membership characterization**, so a theorem producing a row
says precisely which entries it has. That is what keeps the eventual coherence result an
extensional consequence rather than a witness-containment argument. -/

section Row

variable {condSet orderCode : ZFSet.{u}}

/-- The row at `x` over the domain `A`: exactly the stage entries at `(x, y)` for `y ∈ A`. -/
def RowValue (condSet orderCode history A x row : ZFSet.{u}) : Prop :=
  ∀ e, e ∈ row ↔ ∃ y ∈ A, StageEntry condSet orderCode history x y e

/-- **Functionality**: the domain, the history, and the first coordinate determine the row. -/
theorem rowValue_unique {history A x r₁ r₂ : ZFSet.{u}}
    (h₁ : RowValue condSet orderCode history A x r₁)
    (h₂ : RowValue condSet orderCode history A x r₂) : r₁ = r₂ :=
  ZFSet.ext fun e ↦ (h₁ e).trans (h₂ e).symm

/-- A row is assembled from the stages along it: if every `y ∈ A` has a stage present in the
family and every member of the family is a stage along the row, the union of the family is
the row. This is the external form of the filter-then-flatten discipline — the second
hypothesis is the filter, and without it the union could contain arbitrary junk. -/
theorem rowValue_of_sUnion {history A x family : ZFSet.{u}}
    (hpresent : ∀ y ∈ A, ∃ v ∈ family, StageValue condSet orderCode history x y v)
    (hfiltered : ∀ v ∈ family, ∃ y ∈ A, StageValue condSet orderCode history x y v) :
    RowValue condSet orderCode history A x (ZFSet.sUnion family) := by
  intro e
  constructor
  · intro hmem
    obtain ⟨v, hv, hev⟩ := ZFSet.mem_sUnion.1 hmem
    obtain ⟨y, hy, hsv⟩ := hfiltered v hv
    exact ⟨y, hy, (hsv e).1 hev⟩
  · rintro ⟨y, hy, hse⟩
    obtain ⟨v, hv, hsv⟩ := hpresent y hy
    exact ZFSet.mem_sUnion.2 ⟨v, hv, (hsv e).2 hse⟩

/-- The graph over `A` relative to `history`: exactly the stage entries at states with both
coordinates in `A`. Still aggregation — the clauses are evaluated against `history`, **not**
against the graph being built. -/
def GraphValue (condSet orderCode history A graph : ZFSet.{u}) : Prop :=
  ∀ e, e ∈ graph ↔ ∃ x ∈ A, ∃ y ∈ A, StageEntry condSet orderCode history x y e

/-- **Functionality**: the domain and the history determine the graph. -/
theorem graphValue_unique {history A g₁ g₂ : ZFSet.{u}}
    (h₁ : GraphValue condSet orderCode history A g₁)
    (h₂ : GraphValue condSet orderCode history A g₂) : g₁ = g₂ :=
  ZFSet.ext fun e ↦ (h₁ e).trans (h₂ e).symm

/-- The graph is assembled from its rows, under the same filter-then-flatten discipline: the
second hypothesis is the filter. -/
theorem graphValue_of_sUnion {history A family : ZFSet.{u}}
    (hpresent : ∀ x ∈ A, ∃ r ∈ family, RowValue condSet orderCode history A x r)
    (hfiltered : ∀ r ∈ family, ∃ x ∈ A, RowValue condSet orderCode history A x r) :
    GraphValue condSet orderCode history A (ZFSet.sUnion family) := by
  intro e
  constructor
  · intro hmem
    obtain ⟨r, hr, her⟩ := ZFSet.mem_sUnion.1 hmem
    obtain ⟨x, hx, hrv⟩ := hfiltered r hr
    obtain ⟨y, hy, hse⟩ := (hrv e).1 her
    exact ⟨x, hx, y, hy, hse⟩
  · rintro ⟨x, hx, y, hy, hse⟩
    obtain ⟨r, hr, hrv⟩ := hpresent x hx
    exact ZFSet.mem_sUnion.2 ⟨r, hr, (hrv e).2 ⟨y, hy, hse⟩⟩

end Row

/-! ### From aggregation to coherence

**Exact aggregation is not coherence.** A graph built relative to `history` satisfies

```text
e ∈ R ↔ StageEntry history x y e
```

whereas `AtomicCoherentOn A R` requires each clause evaluated against **`R` itself**. The two
differ by exactly one thing: whether the graph observes the same slices the history does.

The bridge below isolates that difference. It is **observer-free** — no forcing relation, no
material carrier, and no rank. Given exact aggregation and agreement between `history` and `R`
at every state of the domain, coherence follows extensionally. Constructing that agreement is
the fixed-point problem, and *that* is where `rankPair` re-enters: at the recursion, not at
the set construction. -/

section Bridge

variable {condSet orderCode : ZFSet.{u}}

/-- **Slice reading**: an exactly aggregated graph has, at each tag, precisely the entries its
clause admits against `history`. The tag law is what separates the two slices. -/
private theorem mem_of_graphValue_memWitness {history A R q x y : ZFSet.{u}}
    (hG : GraphValue condSet orderCode history A R) (hq : q ∈ condSet) (hx : x ∈ A)
    (hy : y ∈ A) :
    entry memWitnessTag q x y ∈ R ↔ MemClause condSet orderCode history q x y := by
  refine (hG _).trans ⟨?_, fun hc ↦ ⟨x, hx, y, hy, Or.inl ⟨q, hq, rfl, hc⟩⟩⟩
  rintro ⟨x', -, y', -, ⟨p, -, hp, hc⟩ | ⟨p, -, hp, -⟩⟩
  · obtain ⟨-, rfl, rfl, rfl⟩ := entry_inj.1 hp
    exact hc
  · exact absurd hp entry_memWitness_ne_eq

private theorem mem_of_graphValue_eq {history A R p x y : ZFSet.{u}}
    (hG : GraphValue condSet orderCode history A R) (hp : p ∈ condSet) (hx : x ∈ A)
    (hy : y ∈ A) :
    entry eqTag p x y ∈ R ↔ EqClause condSet orderCode history p x y := by
  refine (hG _).trans ⟨?_, fun hc ↦ ⟨x, hx, y, hy, Or.inr ⟨p, hp, rfl, hc⟩⟩⟩
  rintro ⟨x', -, y', -, ⟨r, -, hr, -⟩ | ⟨r, -, hr, hc⟩⟩
  · exact absurd hr.symm entry_memWitness_ne_eq
  · obtain ⟨-, rfl, rfl, rfl⟩ := entry_inj.1 hr
    exact hc

/-- **The bridge**: exact aggregation plus observational agreement gives coherence.

Aggregation fixes *which* entries the graph has, relative to `history`; the agreement
hypothesis says the graph and the history are indistinguishable to the clauses across the
domain, so the clauses may be re-read against `R`. Transitivity of `A` is what puts the
branch components consulted by the clauses back inside the domain.

Consumes no rank, no forcing relation, and no material membership. -/
theorem atomicCoherentOn_of_graphValue {history A R : ZFSet.{u}} (hA : A.IsTransitive)
    (hG : GraphValue condSet orderCode history A R)
    (hagree : ∀ x ∈ A, ∀ y ∈ A, AgreeAt condSet history R x y) :
    AtomicCoherentOn condSet orderCode A R := by
  refine ⟨fun q hq x hx y hy ↦ ?_, fun p hp x hx y hy ↦ ?_⟩
  · refine (mem_of_graphValue_memWitness hG hq hx hy).trans (memClause_congr hq ?_)
    exact fun c z hb hc ↦ (hagree x hx z (mem_of_pair_mem hA hy hb)).2
  · refine (mem_of_graphValue_eq hG hp hx hy).trans
      (eqClause_congr (fun c z hb hc q ↦ denseMem_congr ?_)
        (fun c z hb hc q ↦ denseMem_congr ?_))
    · exact (hagree z (mem_of_pair_mem hA hx hb) y hy).1
    · exact (hagree z (mem_of_pair_mem hA hy hb) x hx).1

end Bridge

/-! ### Descent-closed correctness

The form the fixed-point recursion is built in. Two changes from the aggregation layer, both
essential.

**Correctness is self-referential.** `CorrectOn D R` evaluates the clauses against `R` itself,
not against a separate history, so no agreement hypothesis is needed and no fixed point is
left implicit. It is a single statement combining *exact support* — `R` has no members beyond
the entries its own clauses admit at states in `D` — with clause correctness at every state of
`D`. Exact support is what `AtomicCoherentOn` deliberately does **not** control: coherence
permits junk outside the observed slices, which is harmless in isolation but corrupts a
neighbouring approximation once its domain grows to observe that junk. Approximations that
will be unioned must therefore control support.

**Domains are sets of states, not squares.** A square domain `B × B` would force `B` to be a
transitive set containing both coordinates and closed under the descent — the transitive
closure of a pair, which costs Infinity. `DescentClosed` instead requires only that each
member of `D` decodes to a state over `A` and that all three direct predecessor shapes stay
in `D`. That is exactly what the induction consumes, and it is reachable without Infinity.

Generalized locality below is the old proof verbatim with domain-membership routing changed
from `x ∈ A ∧ y ∈ A` to `pair x y ∈ D`. -/

section DescentClosed

variable {condSet orderCode : ZFSet.{u}}

/-- `D` is a set of states over `A`, closed under the three direct predecessor shapes: the
membership clause's `(x, z)`, and the equality clause's `(z, y)` and `(z, x)`. -/
def DescentClosed (condSet A D : ZFSet.{u}) : Prop :=
  (∀ s ∈ D, ∃ x ∈ A, ∃ y ∈ A, s = ZFSet.pair x y) ∧
    ∀ x y, ZFSet.pair x y ∈ D →
      (∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet → ZFSet.pair x z ∈ D) ∧
        (∀ c z, ZFSet.pair c z ∈ x → c ∈ condSet → ZFSet.pair z y ∈ D) ∧
        (∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet → ZFSet.pair z x ∈ D)

/-- **Correctness on a descent-closed domain**: `R` holds exactly the entries its own clauses
admit at the states of `D`. Support and clause correctness in one statement — `R` occurs on
both sides, so this *is* the fixed-point equation, restricted to `D`. -/
def CorrectOn (condSet orderCode D R : ZFSet.{u}) : Prop :=
  ∀ e, e ∈ R ↔ ∃ x y, ZFSet.pair x y ∈ D ∧ StageEntry condSet orderCode R x y e

/-- Slice reading at the membership tag. The tag law kills the wrong disjunct. -/
private theorem correctOn_memWitness {D R q x y : ZFSet.{u}}
    (hR : CorrectOn condSet orderCode D R) (hq : q ∈ condSet)
    (hs : ZFSet.pair x y ∈ D) :
    entry memWitnessTag q x y ∈ R ↔ MemClause condSet orderCode R q x y := by
  refine (hR _).trans ⟨?_, fun hc ↦ ⟨x, y, hs, Or.inl ⟨q, hq, rfl, hc⟩⟩⟩
  rintro ⟨x', y', -, ⟨p, -, hp, hc⟩ | ⟨p, -, hp, -⟩⟩
  · obtain ⟨-, rfl, rfl, rfl⟩ := entry_inj.1 hp
    exact hc
  · exact absurd hp entry_memWitness_ne_eq

/-- Slice reading at the equality tag. -/
private theorem correctOn_eq {D R p x y : ZFSet.{u}}
    (hR : CorrectOn condSet orderCode D R) (hp : p ∈ condSet)
    (hs : ZFSet.pair x y ∈ D) :
    entry eqTag p x y ∈ R ↔ EqClause condSet orderCode R p x y := by
  refine (hR _).trans ⟨?_, fun hc ↦ ⟨x, y, hs, Or.inr ⟨p, hp, rfl, hc⟩⟩⟩
  rintro ⟨x', y', -, ⟨r, -, hr, -⟩ | ⟨r, -, hr, hc⟩⟩
  · exact absurd hr.symm entry_memWitness_ne_eq
  · obtain ⟨-, rfl, rfl, rfl⟩ := entry_inj.1 hr
    exact hc

/-- **Generalized locality**: approximations correct on *different* descent-closed domains
agree at every state lying in both. The old locality proof with domain routing changed; the
descent shapes already land exactly where `DescentClosed` guarantees membership. Consumes
only correctness, descent-closure, and ambient rank. -/
theorem agreeAt_of_correctOn {A B D E R S : ZFSet.{u}}
    (hD : DescentClosed condSet A D) (hE : DescentClosed condSet B E)
    (hR : CorrectOn condSet orderCode D R) (hS : CorrectOn condSet orderCode E S) :
    ∀ x y, ZFSet.pair x y ∈ D → ZFSet.pair x y ∈ E → AgreeAt condSet R S x y := by
  have hwf : WellFounded fun u v : ZFSet.{u} × ZFSet.{u} ↦
      Sym2.GameAdd (· < ·) (rankPair u.1 u.2) (rankPair v.1 v.2) :=
    InvImage.wf _ rankPair_wf
  suffices H : ∀ u : ZFSet.{u} × ZFSet.{u}, ZFSet.pair u.1 u.2 ∈ D →
      ZFSet.pair u.1 u.2 ∈ E → AgreeAt condSet R S u.1 u.2 from
    fun x y hxD hxE ↦ H (x, y) hxD hxE
  intro u
  induction u using hwf.induction with
  | _ u ih =>
    obtain ⟨x, y⟩ := u
    intro hxyD hxyE
    refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
    · rw [correctOn_memWitness hR hp hxyD, correctOn_memWitness hS hp hxyE]
      exact memClause_congr hp fun c z hb hc ↦
        (ih (x, z) (descent_right hb) ((hD.2 x y hxyD).1 c z hb hc)
          ((hE.2 x y hxyE).1 c z hb hc)).2
    · rw [correctOn_eq hR hp hxyD, correctOn_eq hS hp hxyE]
      refine eqClause_congr (fun c z hb hc q ↦ denseMem_congr ?_)
        (fun c z hb hc q ↦ denseMem_congr ?_)
      · exact (ih (z, y) (descent_left hb) ((hD.2 x y hxyD).2.1 c z hb hc)
          ((hE.2 x y hxyE).2.1 c z hb hc)).1
      · exact (ih (z, x) (descent_swap hb) ((hD.2 x y hxyD).2.2 c z hb hc)
          ((hE.2 x y hxyE).2.2 c z hb hc)).1

/-- Clause values agree wherever the two approximations do. -/
private theorem stageEntry_congr_of_agree {A D R S x y : ZFSet.{u}}
    (hD : DescentClosed condSet A D) (hs : ZFSet.pair x y ∈ D)
    (hag : ∀ u v, ZFSet.pair u v ∈ D → AgreeAt condSet R S u v) (e : ZFSet.{u}) :
    StageEntry condSet orderCode R x y e ↔ StageEntry condSet orderCode S x y e := by
  have hmem : ∀ q ∈ condSet, MemClause condSet orderCode R q x y ↔
      MemClause condSet orderCode S q x y := fun q hq ↦
    memClause_congr hq fun c z hb hc ↦ (hag x z ((hD.2 x y hs).1 c z hb hc)).2
  have heq : ∀ q, EqClause condSet orderCode R q x y ↔ EqClause condSet orderCode S q x y :=
    fun _ ↦ eqClause_congr
      (fun c z hb hc q ↦ denseMem_congr (hag z y ((hD.2 x y hs).2.1 c z hb hc)).1)
      (fun c z hb hc q ↦ denseMem_congr (hag z x ((hD.2 x y hs).2.2 c z hb hc)).1)
  unfold StageEntry
  constructor
  · rintro (⟨p, hp, hv, hc⟩ | ⟨p, hp, hv, hc⟩)
    · exact Or.inl ⟨p, hp, hv, (hmem p hp).1 hc⟩
    · exact Or.inr ⟨p, hp, hv, (heq p).1 hc⟩
  · rintro (⟨p, hp, hv, hc⟩ | ⟨p, hp, hv, hc⟩)
    · exact Or.inl ⟨p, hp, hv, (hmem p hp).2 hc⟩
    · exact Or.inr ⟨p, hp, hv, (heq p).2 hc⟩

/-- **Exact support upgrades agreement to equality.** Two approximations correct on the *same*
descent-closed domain are the same set — not merely observationally indistinguishable.

This is the payoff of controlling support. `AtomicCoherentOn` gives only `AgreeAt`, because it
permits arbitrary junk outside the observed slices; that junk is invisible in isolation but
becomes visible, and wrong, once a neighbouring approximation's domain grows to observe it.
`CorrectOn` rules it out, which is what makes unioning approximations safe. -/
theorem correctOn_unique {A D R S : ZFSet.{u}} (hD : DescentClosed condSet A D)
    (hR : CorrectOn condSet orderCode D R) (hS : CorrectOn condSet orderCode D S) :
    R = S := by
  have hag : ∀ u v, ZFSet.pair u v ∈ D → AgreeAt condSet R S u v :=
    fun u v h ↦ agreeAt_of_correctOn hD hD hR hS u v h h
  refine ZFSet.ext fun e ↦ ((hR e).trans (Iff.trans ?_ (hS e).symm))
  exact ⟨fun ⟨x, y, hs, hse⟩ ↦ ⟨x, y, hs, (stageEntry_congr_of_agree hD hs hag e).1 hse⟩,
    fun ⟨x, y, hs, hse⟩ ↦ ⟨x, y, hs, (stageEntry_congr_of_agree hD hs hag e).2 hse⟩⟩

/-- **The endpoint shape**: an approximation correct on a domain covering every state over `A`
is coherent on `A`. No agreement hypothesis, no transitivity, and no rank — the fixed-point
equation was already discharged by `CorrectOn`. -/
theorem atomicCoherentOn_of_correctOn {A D R : ZFSet.{u}}
    (hcov : ∀ x ∈ A, ∀ y ∈ A, ZFSet.pair x y ∈ D)
    (hR : CorrectOn condSet orderCode D R) :
    AtomicCoherentOn condSet orderCode A R :=
  ⟨fun _ hq x hx y hy ↦ correctOn_memWitness hR hq (hcov x hx y hy),
    fun _ hp x hx y hy ↦ correctOn_eq hR hp (hcov x hx y hy)⟩

end DescentClosed

/-! ### Typed readings of the clauses

Where `InternalNameCoding` finally enters. Each clause is translated into the typed
vocabulary: `code_surjective` turns quantified condition codes back into conditions,
`order_iff` transports every strengthening comparison, and `branch_mem_code_iff` turns raw
coded branches into typed indices. These are what make the correctness induction pure
routing, exactly as the congruence lemmas did for locality — and they consume no theory
axiom and no `A ∈ M`. -/

section Typed

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
  (Pres : InternalForcingPresentation M P) (N : InternalNamePresentation M P)

/-- The condition code of a typed condition. Public: it appears in the statements of the
typed readings and the correctness projections. -/
def condCode (p : P) : ZFSet.{u} :=
  ZFSet.mk (Pres.conditionCode.repr p)

/-- **Typed reading of the density clause**: density below a coded condition is density below
the typed one. Uses condition no-junk and the order transport; no name coding needed. -/
theorem denseMem_iff_typed {R x y : ZFSet.{u}} {q : P} :
    DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R (condCode Pres q) x y ↔
      ∀ r : P, r ≤ q → ∃ s : P, s ≤ r ∧ entry memWitnessTag (condCode Pres s) x y ∈ R := by
  constructor
  · intro hd r hrq
    obtain ⟨s, hs, hsr, he⟩ := hd (condCode Pres r) (Pres.code_mem r)
      ((pair_mem_orderCode_iff Pres r q).2 hrq)
    obtain ⟨s', rfl⟩ := Pres.code_surjective s hs
    exact ⟨s', (pair_mem_orderCode_iff Pres s' r).1 hsr, he⟩
  · intro hd r hr hrq
    obtain ⟨r', rfl⟩ := Pres.code_surjective r hr
    obtain ⟨s, hsr, he⟩ := hd r' ((pair_mem_orderCode_iff Pres r' q).1 hrq)
    exact ⟨condCode Pres s, Pres.code_mem s, (pair_mem_orderCode_iff Pres s r').2 hsr, he⟩

/-- **Typed reading of the membership clause**: the raw coded branch becomes a typed index
of the decoded name. -/
theorem memClause_iff_typed (hc : InternalNameCoding Pres N) {R : ZFSet.{u}} {i j : N.Code}
    {q : P} :
    MemClause (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R (condCode Pres q)
        (N.code i) (N.code j) ↔
      ∃ (k : (N.decode j).Idx) (j' : N.Code), N.decode j' = (N.decode j).elems k ∧
        q ≤ (N.decode j).conds k ∧
        entry eqTag (condCode Pres q) (N.code i) (N.code j') ∈ R := by
  constructor
  · rintro ⟨c, z, hb, -, hord, he⟩
    obtain ⟨k, j', hj', heq⟩ := (hc.branch_mem_code_iff j _).1 hb
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 heq
    exact ⟨k, j', hj', (pair_mem_orderCode_iff Pres q _).1 hord, he⟩
  · rintro ⟨k, j', hj', hle, he⟩
    exact ⟨condCode Pres ((N.decode j).conds k), N.code j',
      (hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩,
      Pres.code_mem _, (pair_mem_orderCode_iff Pres q _).2 hle, he⟩

/-- **Typed reading of the equality clause**: both inclusions, with branches as typed indices
and every comparison transported. -/
theorem eqClause_iff_typed (hc : InternalNameCoding Pres N) {R : ZFSet.{u}} {i j : N.Code}
    {p : P} :
    EqClause (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R (condCode Pres p)
        (N.code i) (N.code j) ↔
      (∀ (k : (N.decode i).Idx) (i' : N.Code), N.decode i' = (N.decode i).elems k →
          ∀ q : P, q ≤ p → q ≤ (N.decode i).conds k →
            DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R
              (condCode Pres q) (N.code i') (N.code j)) ∧
        (∀ (k : (N.decode j).Idx) (j' : N.Code), N.decode j' = (N.decode j).elems k →
          ∀ q : P, q ≤ p → q ≤ (N.decode j).conds k →
            DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R
              (condCode Pres q) (N.code j') (N.code i)) := by
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨fun k i' hi' q hqp hqc ↦ ?_, fun k j' hj' q hqp hqc ↦ ?_⟩
    · exact hx _ (N.code i') ((hc.branch_mem_code_iff i _).2 ⟨k, i', hi', rfl⟩)
        (Pres.code_mem _) (condCode Pres q) (Pres.code_mem q)
        ((pair_mem_orderCode_iff Pres q p).2 hqp)
        ((pair_mem_orderCode_iff Pres q _).2 hqc)
    · exact hy _ (N.code j') ((hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩)
        (Pres.code_mem _) (condCode Pres q) (Pres.code_mem q)
        ((pair_mem_orderCode_iff Pres q p).2 hqp)
        ((pair_mem_orderCode_iff Pres q _).2 hqc)
  · rintro ⟨hx, hy⟩
    constructor
    · rintro c z hb - q hq hqp hqc
      obtain ⟨k, i', hi', heq⟩ := (hc.branch_mem_code_iff i _).1 hb
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 heq
      obtain ⟨q', rfl⟩ := Pres.code_surjective q hq
      exact hx k i' hi' q' ((pair_mem_orderCode_iff Pres q' p).1 hqp)
        ((pair_mem_orderCode_iff Pres q' _).1 hqc)
    · rintro c z hb - q hq hqp hqc
      obtain ⟨k, j', hj', heq⟩ := (hc.branch_mem_code_iff j _).1 hb
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 heq
      obtain ⟨q', rfl⟩ := Pres.code_surjective q hq
      exact hy k j' hj' q' ((pair_mem_orderCode_iff Pres q' p).1 hqp)
        ((pair_mem_orderCode_iff Pres q' _).1 hqc)

/-- Density against a coherent graph is exactly forced membership, given agreement of the
membership slice at the relevant state. The bridge the correctness induction reuses. -/
theorem denseMem_iff_forcesMem_of {R x y : ZFSet.{u}} {τ σ : PName P} {q : P}
    (h : ∀ p : P, entry memWitnessTag (condCode Pres p) x y ∈ R ↔ MemWitness p τ σ) :
    DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R
        (condCode Pres q) x y ↔ ForcesMem q τ σ := by
  rw [denseMem_iff_typed Pres]
  constructor
  · intro hd r hr
    obtain ⟨s, hsr, he⟩ := hd r (Set.mem_Iic.1 hr)
    exact ⟨s, (h s).1 he, hsr⟩
  · intro hd r hrq
    obtain ⟨s, hs, hsr⟩ := hd (Set.mem_Iic.2 hrq)
    exact ⟨s, hsr, (h s).2 hs⟩

end Typed

/-! ### Conditional correctness

For *any* coherent candidate graph, its two tagged slices are the external atomic relations
on genuine name codes. Proved by the same rank-pair induction as locality, but with the
measure taken on `N.Code × N.Code`, so the indices and decoded names stay in the motive
instead of being reconstructed from raw code equalities.

Hypotheses are only transitivity of the domain, coherence, membership of the two codes in the
domain, and the name coding: **no `A ∈ M` and no theory axiom**. This pressure-tests the
semantic clauses before the scheme-driven existence proof — if the slices are the right
relations here, the internal formula compiled from them targets the right relation too. -/

section Correctness

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
  {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}
  {A R : ZFSet.{u}}

private theorem correctAt (hA : A.IsTransitive)
    (hR : AtomicCoherentOn (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) A R)
    (hc : InternalNameCoding Pres N) :
    ∀ u : N.Code × N.Code, N.code u.1 ∈ A → N.code u.2 ∈ A →
      ((∀ p : P, entry memWitnessTag (condCode Pres p) (N.code u.1) (N.code u.2) ∈ R ↔
          MemWitness p (N.decode u.1) (N.decode u.2)) ∧
        (∀ p : P, entry eqTag (condCode Pres p) (N.code u.1) (N.code u.2) ∈ R ↔
          ForcesEq p (N.decode u.1) (N.decode u.2))) := by
  have hwf : WellFounded fun u v : N.Code × N.Code ↦
      Sym2.GameAdd (· < ·) (rankPair (N.code u.1) (N.code u.2))
        (rankPair (N.code v.1) (N.code v.2)) :=
    InvImage.wf _ rankPair_wf
  intro u
  induction u using hwf.induction with
  | _ u ih =>
    obtain ⟨i, j⟩ := u
    intro hi hj
    constructor
    · intro p
      rw [hR.1 (condCode Pres p) (Pres.code_mem p) _ hi _ hj, memClause_iff_typed Pres N hc]
      constructor
      · rintro ⟨k, j', hj', hle, he⟩
        have hb : ZFSet.pair (condCode Pres ((N.decode j).conds k)) (N.code j') ∈ N.code j :=
          (hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩
        have hstep := (ih (i, j') (descent_right hb) hi (branch_mem_domain hA hj hb)).2 p
        rw [hj'] at hstep
        exact mem_memWitness_iff.2 ⟨k, hle, hstep.1 he⟩
      · intro hmw
        obtain ⟨k, hle, heq⟩ := mem_memWitness_iff.1 hmw
        obtain ⟨j', hj'⟩ := N.subname_closed j k
        have hb : ZFSet.pair (condCode Pres ((N.decode j).conds k)) (N.code j') ∈ N.code j :=
          (hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩
        have hstep := (ih (i, j') (descent_right hb) hi (branch_mem_domain hA hj hb)).2 p
        rw [hj'] at hstep
        exact ⟨k, j', hj', hle, hstep.2 heq⟩
    · intro p
      rw [hR.2 (condCode Pres p) (Pres.code_mem p) _ hi _ hj, eqClause_iff_typed Pres N hc,
        forcesEq_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun k q hqp hqc ↦ ?_, fun k q hqp hqc ↦ ?_⟩
        · obtain ⟨i', hi'⟩ := N.subname_closed i k
          have hb : ZFSet.pair (condCode Pres ((N.decode i).conds k)) (N.code i') ∈ N.code i :=
            (hc.branch_mem_code_iff i _).2 ⟨k, i', hi', rfl⟩
          have hstep := (ih (i', j) (descent_left hb) (branch_mem_domain hA hi hb) hj).1
          have := (denseMem_iff_forcesMem_of Pres hstep (q := q)).1 (h₁ k i' hi' q hqp hqc)
          rwa [hi'] at this
        · obtain ⟨j', hj'⟩ := N.subname_closed j k
          have hb : ZFSet.pair (condCode Pres ((N.decode j).conds k)) (N.code j') ∈ N.code j :=
            (hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩
          have hstep := (ih (j', i) (descent_swap hb) (branch_mem_domain hA hj hb) hi).1
          have := (denseMem_iff_forcesMem_of Pres hstep (q := q)).1 (h₂ k j' hj' q hqp hqc)
          rwa [hj'] at this
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun k i' hi' q hqp hqc ↦ ?_, fun k j' hj' q hqp hqc ↦ ?_⟩
        · have hb : ZFSet.pair (condCode Pres ((N.decode i).conds k)) (N.code i') ∈ N.code i :=
            (hc.branch_mem_code_iff i _).2 ⟨k, i', hi', rfl⟩
          have hstep := (ih (i', j) (descent_left hb) (branch_mem_domain hA hi hb) hj).1
          refine (denseMem_iff_forcesMem_of Pres hstep (q := q)).2 ?_
          rw [hi']
          exact h₁ k q hqp hqc
        · have hb : ZFSet.pair (condCode Pres ((N.decode j).conds k)) (N.code j') ∈ N.code j :=
            (hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩
          have hstep := (ih (j', i) (descent_swap hb) (branch_mem_domain hA hj hb) hi).1
          refine (denseMem_iff_forcesMem_of Pres hstep (q := q)).2 ?_
          rw [hj']
          exact h₂ k q hqp hqc

/-- **Correctness, membership**: the membership slice of any coherent graph is the external
membership-witness relation. -/
theorem memWitness_entry_iff (hA : A.IsTransitive)
    (hR : AtomicCoherentOn (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) A R)
    (hc : InternalNameCoding Pres N) {i j : N.Code} (hi : N.code i ∈ A) (hj : N.code j ∈ A)
    (p : P) :
    entry memWitnessTag (condCode Pres p) (N.code i) (N.code j) ∈ R ↔
      MemWitness p (N.decode i) (N.decode j) :=
  (correctAt hA hR hc (i, j) hi hj).1 p

/-- **Correctness, equality**: the equality slice of any coherent graph is external forced
equality. -/
theorem forcesEq_entry_iff (hA : A.IsTransitive)
    (hR : AtomicCoherentOn (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) A R)
    (hc : InternalNameCoding Pres N) {i j : N.Code} (hi : N.code i ∈ A) (hj : N.code j ∈ A)
    (p : P) :
    entry eqTag (condCode Pres p) (N.code i) (N.code j) ∈ R ↔
      ForcesEq p (N.decode i) (N.decode j) :=
  (correctAt hA hR hc (i, j) hi hj).2 p

/-- **Correctness, forced membership**: the derived density of the membership slice is
external forced membership. -/
theorem denseMem_iff_forcesMem (hA : A.IsTransitive)
    (hR : AtomicCoherentOn (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) A R)
    (hc : InternalNameCoding Pres N) {i j : N.Code} (hi : N.code i ∈ A) (hj : N.code j ∈ A)
    (q : P) :
    DenseMem (Pres.conditionSet : ZFSet.{u}) (Pres.orderCode : ZFSet.{u}) R
        (condCode Pres q) (N.code i) (N.code j) ↔
      ForcesMem q (N.decode i) (N.decode j) :=
  denseMem_iff_forcesMem_of Pres (memWitness_entry_iff hA hR hc hi hj)

end Correctness

end AtomicRecursion

end Forcing
