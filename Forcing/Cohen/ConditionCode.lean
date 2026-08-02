/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.ZFC.Rank
import Forcing.Cohen.Basic
import Forcing.Name.GenName

/-!
# A structural condition code for Cohen conditions

A `ConditionCode Cond` by the **finite-graph representation**: a condition is coded as the set
of Kuratowski pairs `⟨ň, b̌⟩` over its graph, with the von Neumann naturals coding coordinates
and values. Chosen over the choice-based route (`Countable → Encodable → ℕ`) deliberately: that
coding would be noncanonical and support no membership theorem, whereas the structural code
comes with the characterization an internal presentation needs —

```text
pair (natCode n) (boolCode b) ∈ mk (repr p)  ↔  p.lookup n = some b
```

(`pair_mem_cohenConditionCode_iff`). Injectivity of the code then *follows* from lookup
extensionality; it is not an assumption.

The generic prerequisite is `natCode : ℕ ↪ ZFSet`, injectivity of the von Neumann naturals.
The pinned mathlib has `PSet.ofNat` but no injectivity theorem for it; the rank computation
`rank (ofNat n) = n` (`rank_ofNat`) gives a short proof and is a candidate for generic
factoring or upstreaming.

## Main definitions

* `Forcing.Cohen.natCode`, `Forcing.Cohen.boolCode`: injective codes for coordinates and
  values.
* `Forcing.Cohen.cohenConditionCode`: the finite-graph `ConditionCode Cond`.

## Main results

* `Forcing.Cohen.rank_ofNat`: the rank of the `n`-th von Neumann natural is `n`.
* `Forcing.Cohen.pair_mem_cohenConditionCode_iff`: the membership characterization — the real
  payoff, and exactly what an internal presentation later needs.
-/

namespace Forcing.Cohen

open FinitePartialFunction

/-! ### Injectivity of the von Neumann naturals, by rank -/

/-- The rank of the `n`-th von Neumann natural is `n`. Not in the pinned mathlib; a candidate
for generic factoring or upstreaming. -/
theorem rank_ofNat : ∀ n : ℕ, (PSet.ofNat n).rank = n
  | 0 => PSet.rank_empty
  | n + 1 => by
    rw [PSet.ofNat, PSet.rank_insert, rank_ofNat n, max_eq_left (Order.le_succ _),
      Nat.cast_succ, Order.succ_eq_add_one]

/-- The `n`-th von Neumann natural, as a `ZFSet`; injective by the rank computation. -/
def natCode : ℕ ↪ ZFSet.{0} where
  toFun n := ZFSet.mk (PSet.ofNat n)
  inj' m n h := by
    have hr := congrArg ZFSet.rank h
    rw [ZFSet.rank_mk, ZFSet.rank_mk, rank_ofNat, rank_ofNat] at hr
    exact_mod_cast hr

/-- Booleans coded as the first two von Neumann naturals. -/
def boolCode : Bool ↪ ZFSet.{0} where
  toFun b := natCode (cond b 1 0)
  inj' b c h := by
    cases b <;> cases c <;> first | rfl | simpa using natCode.injective h

/-! ### The finite-graph code -/

/-- The underlying `PSet` of a Kuratowski pair, chosen so that `ZFSet.mk` sends it to
`ZFSet.pair` definitionally (`mk_pairP`). -/
private def pairP (x y : PSet.{0}) : PSet.{0} :=
  {({x} : PSet), ({x, y} : PSet)}

private theorem mk_pairP (x y : PSet.{0}) :
    ZFSet.mk (pairP x y) = ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) :=
  rfl

/-- Membership in the `ZFSet` of an explicitly indexed `PSet`. -/
private theorem mem_mk_mk_iff {σ : Type} {f : σ → PSet.{0}} {y : ZFSet.{0}} :
    y ∈ ZFSet.mk (PSet.mk σ f) ↔ ∃ i, y = ZFSet.mk (f i) := by
  induction y using Quotient.inductionOn with
  | h z =>
    exact ⟨fun ⟨i, h⟩ ↦ ⟨i, ZFSet.sound h⟩, fun ⟨i, h⟩ ↦ ⟨i, ZFSet.exact h⟩⟩

/-- The finite graph of a condition, as a `PSet` indexed by the decided coordinates. -/
private def graphRepr (p : Cond) : PSet.{0} :=
  PSet.mk {n : ℕ // n ∈ p} fun i ↦
    pairP (PSet.ofNat i.1)
      (PSet.ofNat (cond ((p.lookup i.1).get (mem_iff_isSome.1 i.2)) 1 0))

private theorem mem_mk_graphRepr_iff {p : Cond} {y : ZFSet.{0}} :
    y ∈ ZFSet.mk (graphRepr p) ↔
      ∃ n b, p.lookup n = some b ∧ y = ZFSet.pair (natCode n) (boolCode b) := by
  refine mem_mk_mk_iff.trans ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, (p.lookup i.1).get (mem_iff_isSome.1 i.2), (Option.some_get _).symm,
      mk_pairP _ _⟩
  · rintro ⟨n, b, hb, rfl⟩
    have hn : n ∈ p := mem_iff_isSome.2 (by rw [hb]; rfl)
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [mk_pairP]
    have hg : (p.lookup n).get (mem_iff_isSome.1 hn) = b :=
      Option.some.inj ((Option.some_get _).trans hb)
    rw [hg]
    rfl

private theorem pair_mem_graphRepr_iff {p : Cond} {n : ℕ} {b : Bool} :
    ZFSet.pair (natCode n) (boolCode b) ∈ ZFSet.mk (graphRepr p) ↔ p.lookup n = some b := by
  refine mem_mk_graphRepr_iff.trans ⟨?_, fun h ↦ ⟨n, b, h, rfl⟩⟩
  rintro ⟨m, c, hc, he⟩
  obtain ⟨hn, hb⟩ := ZFSet.pair_inj.1 he
  rwa [natCode.injective hn, boolCode.injective hb]

/-- **The structural condition code**: a Cohen condition is coded by the set of Kuratowski
pairs over its graph. Injectivity follows from the membership characterization plus lookup
extensionality — it is derived, not assumed. -/
def cohenConditionCode : ConditionCode Cond where
  repr := graphRepr
  injective_mk := by
    intro p q h
    have h' : ZFSet.mk (graphRepr p) = ZFSet.mk (graphRepr q) := h
    refine ext_lookup fun n ↦ Option.ext fun b ↦ ?_
    rw [← pair_mem_graphRepr_iff, ← pair_mem_graphRepr_iff, h']

/-- The full membership description of the code. -/
theorem mem_mk_repr_iff {p : Cond} {y : ZFSet.{0}} :
    y ∈ ZFSet.mk (cohenConditionCode.repr p) ↔
      ∃ n b, p.lookup n = some b ∧ y = ZFSet.pair (natCode n) (boolCode b) :=
  mem_mk_graphRepr_iff

/-- **The membership characterization** — the real payoff of the structural code, and exactly
what an internal presentation later needs: the coded graph decides membership of a coded pair
exactly as the condition decides the coordinate. -/
theorem pair_mem_cohenConditionCode_iff {p : Cond} {n : ℕ} {b : Bool} :
    ZFSet.pair (natCode n) (boolCode b) ∈ ZFSet.mk (cohenConditionCode.repr p) ↔
      p.lookup n = some b :=
  pair_mem_graphRepr_iff

end Forcing.Cohen
