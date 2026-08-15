/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.ZFC.Rank

/-!
# Coding the naturals as sets

The von Neumann naturals as an injective code `ℕ ↪ ZFSet`, with the rank computation that
proves the injectivity. Neutral set-coding infrastructure: nothing here mentions forcing,
conditions, names, or any carrier.

Universe-polymorphic, so the material layers that consume it are too; the Cohen carrier
simply infers `u = 0`. Factored out when its second consumer arrived (formula coding,
after the Cohen condition code). The pinned mathlib has `PSet.ofNat` but no injectivity
theorem for it; `rank_ofNat` is the short proof and remains a plausible upstream
contribution.

`natCode_succ` exposes the recursion the material-membership arguments run on: the successor
code is an `insert`, which is what prices those arguments at binary union.

## Main definitions

* `Forcing.natCode`: the von Neumann code of a natural, injective.

## Main results

* `Forcing.rank_ofNat`: the rank of the `n`-th von Neumann natural is `n`.
* `Forcing.natCode_zero`, `Forcing.natCode_succ`: the recursion.
-/

universe u

namespace Forcing

/-- The rank of the `n`-th von Neumann natural is `n`. Not in the pinned mathlib; a plausible
upstream contribution. -/
theorem rank_ofNat : ∀ n : ℕ, (PSet.ofNat.{u} n).rank = n
  | 0 => PSet.rank_empty
  | n + 1 => by
    rw [PSet.ofNat, PSet.rank_insert, rank_ofNat n, max_eq_left (Order.le_succ _),
      Nat.cast_succ, Order.succ_eq_add_one]

/-- The `n`-th von Neumann natural, as a `ZFSet`; injective by the rank computation. -/
def natCode : ℕ ↪ ZFSet.{u} where
  toFun n := ZFSet.mk (PSet.ofNat n)
  inj' m n h := by
    have hr := congrArg ZFSet.rank h
    rw [ZFSet.rank_mk, ZFSet.rank_mk, rank_ofNat, rank_ofNat] at hr
    exact_mod_cast hr

@[simp] theorem natCode_zero : natCode.{u} 0 = ∅ :=
  rfl

/-- The successor code is an `insert` — the shape material-membership arguments recurse on. -/
@[simp] theorem natCode_succ (n : ℕ) :
    natCode.{u} (n + 1) = insert (natCode.{u} n) (natCode.{u} n) :=
  rfl

end Forcing
