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
-/

namespace Forcing

namespace AtomicRecursion

/-! ### The two descent facts -/

/-- A branch code sits three Kuratowski levels above the subname code it carries, so the
subname code has strictly smaller rank. *Rank only* — nothing about the domain. -/
private theorem rank_lt_of_pair_mem {c z w : ZFSet.{0}} (h : ZFSet.pair c z ∈ w) :
    z.rank < w.rank := by
  have h₁ : z.rank < ({c, z} : ZFSet.{0}).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  have h₂ : ({c, z} : ZFSet.{0}).rank < (ZFSet.pair c z).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  exact (h₁.trans h₂).trans (ZFSet.rank_lt_of_mem h)

/-- In a transitive domain, the subname code carried by a branch of a member is itself a
member. *Domain closure only* — nothing about rank. -/
private theorem mem_of_pair_mem {A c z w : ZFSet.{0}} (hA : A.IsTransitive) (hw : w ∈ A)
    (h : ZFSet.pair c z ∈ w) : z ∈ A :=
  hA.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
    (hA.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) (hA.mem_trans h hw))

/-! ### The measure, and the three descent shapes

The unordered pair of ranks under `Sym2.GameAdd (· < ·)`, reproducing exactly the three
descent shapes of the external kernel: lower the right coordinate, lower the left, and
lower-after-swap. -/

private noncomputable def rankPair (x y : ZFSet.{0}) : Sym2 Ordinal.{0} :=
  s(x.rank, y.rank)

private theorem rankPair_wf : WellFounded (Sym2.GameAdd ((· < ·) : Ordinal → Ordinal → Prop)) :=
  (Ordinal.lt_wf).sym2_gameAdd

/-- Shape 1 — a membership witness descends to forced equality against a branch of the right
coordinate. -/
private theorem descent_right {c z x y : ZFSet.{0}} (h : ZFSet.pair c z ∈ y) :
    Sym2.GameAdd (· < ·) (rankPair x z) (rankPair x y) :=
  Sym2.GameAdd.snd (rank_lt_of_pair_mem h)

/-- Shape 2 — forced equality descends to a membership witness for a branch of the left
coordinate. -/
private theorem descent_left {c z x y : ZFSet.{0}} (h : ZFSet.pair c z ∈ x) :
    Sym2.GameAdd (· < ·) (rankPair z y) (rankPair x y) :=
  Sym2.GameAdd.fst (rank_lt_of_pair_mem h)

/-- Shape 3 — forced equality descends to a membership witness for a branch of the right
coordinate, with the arguments swapped. -/
private theorem descent_swap {c z x y : ZFSet.{0}} (h : ZFSet.pair c z ∈ y) :
    Sym2.GameAdd (· < ·) (rankPair z x) (rankPair x y) :=
  Sym2.GameAdd.fst_snd (rank_lt_of_pair_mem h)

/-! ### The coherence clauses -/

section Clauses

variable (condSet orderCode : ZFSet.{0})

/-- **Density of the membership-witness slice** below a condition: every strengthening has a
further strengthening carrying a witness. -/
def DenseMem (R q x y : ZFSet.{0}) : Prop :=
  ∀ r ∈ condSet, ZFSet.pair r q ∈ orderCode →
    ∃ s ∈ condSet, ZFSet.pair s r ∈ orderCode ∧ entry memWitnessTag s x y ∈ R

/-- **The membership-witness clause**: some branch of `y` is activated by `q` and its subname
is forced equal to `x`. -/
def MemClause (R q x y : ZFSet.{0}) : Prop :=
  ∃ c z, ZFSet.pair c z ∈ y ∧ c ∈ condSet ∧ ZFSet.pair q c ∈ orderCode ∧
    entry eqTag q x z ∈ R

/-- **The forced-equality clause**: the two inclusions, each saying that every branch
activated below `p` on one side is densely a member of the other. Branch quantifiers range
only over branches whose first coordinate is a condition code, so the clause is total on
arbitrary domain elements. -/
def EqClause (R p x y : ZFSet.{0}) : Prop :=
  (∀ c z, ZFSet.pair c z ∈ x → c ∈ condSet → ∀ q ∈ condSet,
      ZFSet.pair q p ∈ orderCode → ZFSet.pair q c ∈ orderCode →
      DenseMem condSet orderCode R q z y) ∧
    (∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet → ∀ q ∈ condSet,
      ZFSet.pair q p ∈ orderCode → ZFSet.pair q c ∈ orderCode →
      DenseMem condSet orderCode R q z x)

/-- **Coherence on a domain**: each tagged slice of the graph is *exactly* its clause, at
valid condition codes and domain elements. Elements outside those slices are unconstrained —
uniqueness will therefore be observational. -/
def AtomicCoherentOn (A R : ZFSet.{0}) : Prop :=
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
theorem branch_mem_domain {A c z y : ZFSet.{0}} (hA : A.IsTransitive) (hy : y ∈ A)
    (h : ZFSet.pair c z ∈ y) : z ∈ A :=
  mem_of_pair_mem hA hy h

/-- The recursive argument of the membership-witness clause stays in the domain. -/
theorem memClause_domain {condSet orderCode A R q x y : ZFSet.{0}} (hA : A.IsTransitive)
    (hy : y ∈ A) (h : MemClause condSet orderCode R q x y) :
    ∃ c z, ZFSet.pair c z ∈ y ∧ z ∈ A ∧ ZFSet.pair q c ∈ orderCode ∧
      entry eqTag q x z ∈ R := by
  obtain ⟨c, z, hb, -, hord, he⟩ := h
  exact ⟨c, z, hb, branch_mem_domain hA hy hb, hord, he⟩

/-! ### Orientation

Each order comparison of the clauses gets a named typed reading. A reversal would still
typecheck against the raw `ZFSet` definitions, so these are the guard rails. -/

section Orientation

variable {M : MaterialCarrier.{0}} {P : Type} [Preorder P]
  (Pres : InternalForcingPresentation M P)

/-- The stored orientation: a coded pair lies in the order code exactly when the *first*
condition strengthens the second (smaller is stronger). -/
theorem pair_mem_orderCode_iff (a b : P) :
    ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr a)) (ZFSet.mk (Pres.conditionCode.repr b)) ∈
        (Pres.orderCode : ZFSet.{0}) ↔ a ≤ b :=
  Pres.order_iff b a

/-- Orientation of `MemClause`: its comparison says the witness condition **strengthens the
branch's** condition. -/
theorem memClause_orientation {R x y z : ZFSet.{0}} {q c : P}
    (hb : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr c)) z ∈ y)
    (hc : ZFSet.mk (Pres.conditionCode.repr c) ∈ (Pres.conditionSet : ZFSet.{0}))
    (hle : q ≤ c)
    (he : entry eqTag (ZFSet.mk (Pres.conditionCode.repr q)) x z ∈ R) :
    MemClause (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R
      (ZFSet.mk (Pres.conditionCode.repr q)) x y :=
  ⟨_, z, hb, hc, (pair_mem_orderCode_iff Pres q c).2 hle, he⟩

/-- Orientation of `DenseMem`: the hypothesis reads "`r` strengthens `q`" and the conclusion
"`s` strengthens `r`" — density *below*, not above. -/
theorem denseMem_orientation {R q x y : ZFSet.{0}} {r : P}
    (h : DenseMem (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R q x y)
    (hr : ZFSet.mk (Pres.conditionCode.repr r) ∈ (Pres.conditionSet : ZFSet.{0}))
    (hrq : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr r)) q ∈ (Pres.orderCode : ZFSet.{0})) :
    ∃ s ∈ (Pres.conditionSet : ZFSet.{0}),
      ZFSet.pair s (ZFSet.mk (Pres.conditionCode.repr r)) ∈ (Pres.orderCode : ZFSet.{0}) ∧
        entry memWitnessTag s x y ∈ R :=
  h _ hr hrq

/-- Orientation of `EqClause`: its comparisons read "`q` strengthens `p`" and "`q`
strengthens the branch's condition" — both downward. -/
theorem eqClause_orientation {R p x y z : ZFSet.{0}} {c q : P}
    (h : EqClause (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R p x y)
    (hb : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr c)) z ∈ x)
    (hc : ZFSet.mk (Pres.conditionCode.repr c) ∈ (Pres.conditionSet : ZFSet.{0}))
    (hq : ZFSet.mk (Pres.conditionCode.repr q) ∈ (Pres.conditionSet : ZFSet.{0}))
    (hqp : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q)) p ∈
      (Pres.orderCode : ZFSet.{0}))
    (hqc : q ≤ c) :
    DenseMem (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R
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

variable {condSet orderCode : ZFSet.{0}}

/-- Two candidate graphs **agree at a state**: their two tagged slices coincide there. -/
def AgreeAt (condSet R S x y : ZFSet.{0}) : Prop :=
  (∀ p ∈ condSet, entry memWitnessTag p x y ∈ R ↔ entry memWitnessTag p x y ∈ S) ∧
    (∀ p ∈ condSet, entry eqTag p x y ∈ R ↔ entry eqTag p x y ∈ S)

/-- Congruence for the density clause: agreement of the membership slice suffices. -/
private theorem denseMem_congr {R S q x y : ZFSet.{0}}
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
private theorem memClause_congr {R S q x y : ZFSet.{0}} (hq : q ∈ condSet)
    (h : ∀ c z, ZFSet.pair c z ∈ y → c ∈ condSet →
      ∀ p ∈ condSet, (entry eqTag p x z ∈ R ↔ entry eqTag p x z ∈ S)) :
    MemClause condSet orderCode R q x y ↔ MemClause condSet orderCode S q x y := by
  constructor
  · rintro ⟨c, z, hb, hc, hord, he⟩
    exact ⟨c, z, hb, hc, hord, (h c z hb hc q hq).1 he⟩
  · rintro ⟨c, z, hb, hc, hord, he⟩
    exact ⟨c, z, hb, hc, hord, (h c z hb hc q hq).2 he⟩

/-- Congruence for the equality clause: the two families of density agreements suffice. -/
private theorem eqClause_congr {R S p x y : ZFSet.{0}}
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
theorem agreeAt_of_coherent {A B R S : ZFSet.{0}} (hA : A.IsTransitive) (hB : B.IsTransitive)
    (hR : AtomicCoherentOn condSet orderCode A R)
    (hS : AtomicCoherentOn condSet orderCode B S) :
    ∀ x y, x ∈ A → y ∈ A → x ∈ B → y ∈ B → AgreeAt condSet R S x y := by
  have hwf : WellFounded fun u v : ZFSet.{0} × ZFSet.{0} ↦
      Sym2.GameAdd (· < ·) (rankPair u.1 u.2) (rankPair v.1 v.2) :=
    InvImage.wf _ rankPair_wf
  suffices H : ∀ u : ZFSet.{0} × ZFSet.{0}, u.1 ∈ A → u.2 ∈ A → u.1 ∈ B → u.2 ∈ B →
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
theorem agreeAt_of_coherent_same {A R S : ZFSet.{0}} (hA : A.IsTransitive)
    (hR : AtomicCoherentOn condSet orderCode A R)
    (hS : AtomicCoherentOn condSet orderCode A S) :
    ∀ x y, x ∈ A → y ∈ A → AgreeAt condSet R S x y :=
  fun x y hx hy ↦ agreeAt_of_coherent hA hA hR hS x y hx hy hx hy

end Locality

/-! ### Typed readings of the clauses

Where `InternalNameCoding` finally enters. Each clause is translated into the typed
vocabulary: `code_surjective` turns quantified condition codes back into conditions,
`order_iff` transports every strengthening comparison, and `branch_mem_code_iff` turns raw
coded branches into typed indices. These are what make the correctness induction pure
routing, exactly as the congruence lemmas did for locality — and they consume no theory
axiom and no `A ∈ M`. -/

section Typed

variable {M : MaterialCarrier.{0}} {P : Type} [Preorder P]
  (Pres : InternalForcingPresentation M P) (N : InternalNamePresentation M P)

/-- Abbreviation for the condition code of a typed condition. -/
private def cc (p : P) : ZFSet.{0} :=
  ZFSet.mk (Pres.conditionCode.repr p)

/-- **Typed reading of the density clause**: density below a coded condition is density below
the typed one. Uses condition no-junk and the order transport; no name coding needed. -/
theorem denseMem_iff_typed {R x y : ZFSet.{0}} {q : P} :
    DenseMem (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R (cc Pres q) x y ↔
      ∀ r : P, r ≤ q → ∃ s : P, s ≤ r ∧ entry memWitnessTag (cc Pres s) x y ∈ R := by
  constructor
  · intro hd r hrq
    obtain ⟨s, hs, hsr, he⟩ := hd (cc Pres r) (Pres.code_mem r)
      ((pair_mem_orderCode_iff Pres r q).2 hrq)
    obtain ⟨s', rfl⟩ := Pres.code_surjective s hs
    exact ⟨s', (pair_mem_orderCode_iff Pres s' r).1 hsr, he⟩
  · intro hd r hr hrq
    obtain ⟨r', rfl⟩ := Pres.code_surjective r hr
    obtain ⟨s, hsr, he⟩ := hd r' ((pair_mem_orderCode_iff Pres r' q).1 hrq)
    exact ⟨cc Pres s, Pres.code_mem s, (pair_mem_orderCode_iff Pres s r').2 hsr, he⟩

/-- **Typed reading of the membership clause**: the raw coded branch becomes a typed index
of the decoded name. -/
theorem memClause_iff_typed (hc : InternalNameCoding Pres N) {R : ZFSet.{0}} {i j : N.Code}
    {q : P} :
    MemClause (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R (cc Pres q)
        (N.code i) (N.code j) ↔
      ∃ (k : (N.decode j).Idx) (j' : N.Code), N.decode j' = (N.decode j).elems k ∧
        q ≤ (N.decode j).conds k ∧
        entry eqTag (cc Pres q) (N.code i) (N.code j') ∈ R := by
  constructor
  · rintro ⟨c, z, hb, -, hord, he⟩
    obtain ⟨k, j', hj', heq⟩ := (hc.branch_mem_code_iff j _).1 hb
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 heq
    exact ⟨k, j', hj', (pair_mem_orderCode_iff Pres q _).1 hord, he⟩
  · rintro ⟨k, j', hj', hle, he⟩
    exact ⟨cc Pres ((N.decode j).conds k), N.code j',
      (hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩,
      Pres.code_mem _, (pair_mem_orderCode_iff Pres q _).2 hle, he⟩

/-- **Typed reading of the equality clause**: both inclusions, with branches as typed indices
and every comparison transported. -/
theorem eqClause_iff_typed (hc : InternalNameCoding Pres N) {R : ZFSet.{0}} {i j : N.Code}
    {p : P} :
    EqClause (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R (cc Pres p)
        (N.code i) (N.code j) ↔
      (∀ (k : (N.decode i).Idx) (i' : N.Code), N.decode i' = (N.decode i).elems k →
          ∀ q : P, q ≤ p → q ≤ (N.decode i).conds k →
            DenseMem (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R
              (cc Pres q) (N.code i') (N.code j)) ∧
        (∀ (k : (N.decode j).Idx) (j' : N.Code), N.decode j' = (N.decode j).elems k →
          ∀ q : P, q ≤ p → q ≤ (N.decode j).conds k →
            DenseMem (Pres.conditionSet : ZFSet.{0}) (Pres.orderCode : ZFSet.{0}) R
              (cc Pres q) (N.code j') (N.code i)) := by
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨fun k i' hi' q hqp hqc ↦ ?_, fun k j' hj' q hqp hqc ↦ ?_⟩
    · exact hx _ (N.code i') ((hc.branch_mem_code_iff i _).2 ⟨k, i', hi', rfl⟩)
        (Pres.code_mem _) (cc Pres q) (Pres.code_mem q)
        ((pair_mem_orderCode_iff Pres q p).2 hqp)
        ((pair_mem_orderCode_iff Pres q _).2 hqc)
    · exact hy _ (N.code j') ((hc.branch_mem_code_iff j _).2 ⟨k, j', hj', rfl⟩)
        (Pres.code_mem _) (cc Pres q) (Pres.code_mem q)
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

end Typed

end AtomicRecursion

end Forcing
