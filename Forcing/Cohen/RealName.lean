/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.ConditionCode
import Forcing.Cohen.Generic

/-!
# The real code and the external Cohen-real name

The second consumer of the partial graph code: a total real is coded by the graph code of its
total graph (`realCode`), faithful by the faithfulness of the graph code. The Cohen-real name
(`cohenRealName`) is the typed external name whose branches carry the checked coded pairs,
each conditioned on the single-coordinate condition that decides it.

The main theorem is the **strong partial-union theorem** (`zval_cohenRealName`): along
*every* forcing filter — no genericity, no totality — the name values to the graph code of
the partial union,

```text
zval ↑G cohenRealName = graphCode (genericFun G)
```

because upward closure makes membership of the single-coordinate condition equivalent to the
union deciding that coordinate (`singleCond_mem_iff`). Totality is then a specialization:
`zval ↑G cohenRealName = realCode (totalUnion G htotal)`.

Everything here is external and typed: no material imports, no visibility, no `M[G]`. The
reserved phrase stays reserved — this file supplies the *object* `realCode c_G` and its name;
"adds a new real" is earned only by the material adapter's combination.

## Main definitions

* `Forcing.Cohen.realCode`: the total-graph code of a real, injective.
* `Forcing.Cohen.cohenRealName`: the external Cohen-real name.

## Main results

* `Forcing.Cohen.zval_cohenRealName`: the strong partial-union theorem — every filter values
  the name to the graph code of its partial union.
* `Forcing.Cohen.zval_cohenRealName_totalUnion`: the total specialization, landing at
  `realCode`.
-/

namespace Forcing.Cohen

open FinitePartialFunction PName Order

/-! ### The real code -/

/-- The total-graph code of a real: the graph code of `fun n ↦ some (c n)`. The second
consumer of `graphCode`, sharing the representation with `cohenConditionCode`. -/
def realCode (c : ℕ → Bool) : ZFSet.{0} :=
  graphCode fun n ↦ some (c n)

/-- The membership characterization for real codes: total, so every coordinate is decided. -/
theorem pair_mem_realCode_iff {c : ℕ → Bool} {n : ℕ} {b : Bool} :
    ZFSet.pair (natCode n) (boolCode b) ∈ realCode c ↔ c n = b :=
  pair_mem_graphCode_iff.trans (by simp)

/-- The real code is faithful. -/
theorem realCode_injective : Function.Injective realCode := fun _ _ h ↦
  funext fun n ↦ Option.some.inj (congrFun (graphCode_injective h) n)

/-! ### The single-coordinate condition and the Cohen-real name -/

/-- The condition deciding exactly one coordinate. -/
def singleCond (n : ℕ) (b : Bool) : Cond :=
  (∅ : Cond).insert n b

@[simp] theorem lookup_singleCond_self {n : ℕ} {b : Bool} :
    (singleCond n b).lookup n = some b :=
  lookup_insert_self

theorem lookup_singleCond_of_ne {m n : ℕ} {b : Bool} (h : m ≠ n) :
    (singleCond n b).lookup m = none := by
  rw [singleCond, lookup_insert_of_ne h, lookup_empty]

/-- **The upward-closure bridge**: a filter contains the single-coordinate condition exactly
when its partial union decides that coordinate that way. The forward direction is a witness;
the reverse is upward closure — any member deciding the coordinate is a strengthening of the
single-coordinate condition. -/
theorem singleCond_mem_iff {G : PFilter Cond} {n : ℕ} {b : Bool} :
    singleCond n b ∈ G ↔ genericFun G n = some b := by
  rw [genericFun_eq_some_iff]
  constructor
  · exact fun h ↦ ⟨singleCond n b, h, lookup_singleCond_self⟩
  · rintro ⟨p, hp, hpn⟩
    refine G.mem_of_le (le_def.2 fun i b' hi ↦ ?_) hp
    rcases eq_or_ne i n with rfl | hne
    · rw [lookup_singleCond_self] at hi
      rwa [← Option.some.inj hi]
    · rw [lookup_singleCond_of_ne hne] at hi
      exact absurd hi (by simp)

/-- **The Cohen-real name**: one branch per (coordinate, bit), carrying the checked coded
pair, conditioned on the single-coordinate condition that decides it. -/
def cohenRealName : PName Cond :=
  .mk (ℕ × Bool)
    (fun x ↦ check (pairRepr (PSet.ofNat x.1) (PSet.ofNat (cond x.2 1 0))))
    fun x ↦ singleCond x.1 x.2

/-- **The strong partial-union theorem**: along every forcing filter — no genericity, no
totality — the Cohen-real name values to the graph code of the partial union. -/
theorem zval_cohenRealName (G : PFilter Cond) :
    zval (G : Set Cond) cohenRealName = graphCode (genericFun G) := by
  ext y
  rw [mem_zval_iff, mem_graphCode_iff]
  constructor
  · rintro ⟨⟨n, b⟩, hmem, rfl⟩
    refine ⟨n, b, singleCond_mem_iff.1 hmem, ?_⟩
    rw [show (cohenRealName.elems (⟨n, b⟩ : ℕ × Bool)) =
        check (pairRepr (PSet.ofNat n) (PSet.ofNat (cond b 1 0))) from rfl,
      zval_check G.top_mem, mk_pairRepr]
    rfl
  · rintro ⟨n, b, hnb, rfl⟩
    refine ⟨(⟨n, b⟩ : ℕ × Bool), singleCond_mem_iff.2 hnb, ?_⟩
    rw [show (cohenRealName.elems (⟨n, b⟩ : ℕ × Bool)) =
        check (pairRepr (PSet.ofNat n) (PSet.ofNat (cond b 1 0))) from rfl,
      zval_check G.top_mem, mk_pairRepr]
    rfl

/-- The total specialization: a filter with a total union values the Cohen-real name to the
real code of its extracted real. This is the object the material adapter internalizes. -/
theorem zval_cohenRealName_totalUnion {G : PFilter Cond}
    (h : ∀ n, (genericFun G n).isSome) :
    zval (G : Set Cond) cohenRealName = realCode (totalUnion G h) := by
  rw [zval_cohenRealName, realCode]
  congr 1
  funext n
  exact unionFun_totalUnion h n

end Forcing.Cohen
