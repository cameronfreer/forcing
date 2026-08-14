/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.GameAdd
import Mathlib.SetTheory.ZFC.Rank
import Forcing.Material.RecursionEntry

/-!
# The atomic recursion: descent machinery

**Checkpoint module.** The coherence clauses, uniqueness, locality, existence, and
correctness of the recursion graph are built here in subsequent steps; this file currently
establishes only the descent machinery those proofs run on, and exports nothing.

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

end Forcing
