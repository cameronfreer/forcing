/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Coding.Nat
import Forcing.Cohen.Basic
import Forcing.Name.GenName

/-!
# The partial graph code, and the structural condition code

The shared material coding of Cohen data: a partial function `ℕ → Option Bool` is coded as
the set of Kuratowski pairs `⟨ň, b̌⟩` over its graph (`graphCode`), with the von Neumann
naturals coding coordinates and values. Two consumers share the representation — conditions
(finite graphs, `cohenConditionCode`) and total reals (`realCode`, in
`Forcing/Cohen/RealName.lean`) — which is why the graph code is the public object here.

The structural code was chosen over the choice-based route (`Countable → Encodable → ℕ`)
deliberately: that coding would be noncanonical and support no membership theorem, whereas
the graph code comes with the characterization an internal presentation needs —

```text
pair (natCode n) (boolCode b) ∈ graphCode f  ↔  f n = some b
```

(`pair_mem_graphCode_iff`). Injectivity of the codes then *follows* from extensionality
(`graphCode_injective`); it is never an assumption.

The generic prerequisite `natCode : ℕ ↪ ZFSet` now lives in `Forcing/Coding/Nat.lean`,
factored out when formula coding became its second consumer; the Cohen-facing name is kept as
an abbreviation so downstream statements are unchanged.

## Main definitions

* `Forcing.Cohen.natCode` (the generic code, re-exposed), `Forcing.Cohen.boolCode`: injective
  codes for coordinates and values.
* `Forcing.Cohen.graphCode`: the partial graph code, shared by conditions and reals.
* `Forcing.Cohen.cohenConditionCode`: the finite-graph `ConditionCode Cond`.

## Main results

* `Forcing.Cohen.pair_mem_graphCode_iff`: the membership characterization — the real payoff,
  and exactly what an internal presentation later needs.
* `Forcing.Cohen.graphCode_injective`: the code is faithful, by extensionality.
* `Forcing.Cohen.pair_mem_cohenConditionCode_iff`, `Forcing.Cohen.mem_cohenConditionCode_iff`:
  the condition-code instances.
-/

namespace Forcing.Cohen

open FinitePartialFunction

/-! ### The coordinate and value codes -/

/-- The von Neumann code of a coordinate — the generic `Forcing.natCode`, kept under the
Cohen-facing name. -/
abbrev natCode : ℕ ↪ ZFSet.{0} := Forcing.natCode

/-- Booleans coded as the first two von Neumann naturals. -/
def boolCode : Bool ↪ ZFSet.{0} where
  toFun b := natCode (cond b 1 0)
  inj' b c h := by
    cases b <;> cases c <;> first | rfl | simpa using natCode.injective h

/-! ### The partial graph code -/

/-- The underlying `PSet` of a Kuratowski pair, chosen so that `ZFSet.mk` sends it to
`ZFSet.pair` definitionally (`mk_pairRepr`). -/
def pairRepr (x y : PSet.{0}) : PSet.{0} :=
  {({x} : PSet), ({x, y} : PSet)}

theorem mk_pairRepr (x y : PSet.{0}) :
    ZFSet.mk (pairRepr x y) = ZFSet.pair (ZFSet.mk x) (ZFSet.mk y) :=
  rfl

/-- Membership in the `ZFSet` of an explicitly indexed `PSet`. -/
private theorem mem_mk_mk_iff {σ : Type} {f : σ → PSet.{0}} {y : ZFSet.{0}} :
    y ∈ ZFSet.mk (PSet.mk σ f) ↔ ∃ i, y = ZFSet.mk (f i) := by
  induction y using Quotient.inductionOn with
  | h z =>
    exact ⟨fun ⟨i, h⟩ ↦ ⟨i, ZFSet.sound h⟩, fun ⟨i, h⟩ ↦ ⟨i, ZFSet.exact h⟩⟩

/-- The graph of a partial function `ℕ → Option Bool`, as a `PSet` indexed by the decided
coordinates. -/
def graphRepr (f : ℕ → Option Bool) : PSet.{0} :=
  PSet.mk {n : ℕ // (f n).isSome} fun i ↦
    pairRepr (PSet.ofNat i.1) (PSet.ofNat (cond ((f i.1).get i.2) 1 0))

/-- **The partial graph code**: the set of Kuratowski pairs over the graph. Shared by the
condition code (`cohenConditionCode`, via `lookup`) and the real code (`realCode`, via total
graphs). -/
def graphCode (f : ℕ → Option Bool) : ZFSet.{0} :=
  ZFSet.mk (graphRepr f)

/-- The full membership description of a graph code. -/
theorem mem_graphCode_iff {f : ℕ → Option Bool} {y : ZFSet.{0}} :
    y ∈ graphCode f ↔
      ∃ n b, f n = some b ∧ y = ZFSet.pair (natCode n) (boolCode b) := by
  refine mem_mk_mk_iff.trans ⟨?_, ?_⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.1, (f i.1).get i.2, (Option.some_get _).symm, mk_pairRepr _ _⟩
  · rintro ⟨n, b, hb, rfl⟩
    have hn : (f n).isSome := by rw [hb]; rfl
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [mk_pairRepr]
    have hg : (f n).get hn = b := Option.some.inj ((Option.some_get _).trans hb)
    rw [hg]
    rfl

/-- **The membership characterization** — the real payoff of the structural coding: the coded
graph decides membership of a coded pair exactly as the partial function decides the
coordinate. -/
theorem pair_mem_graphCode_iff {f : ℕ → Option Bool} {n : ℕ} {b : Bool} :
    ZFSet.pair (natCode n) (boolCode b) ∈ graphCode f ↔ f n = some b := by
  refine mem_graphCode_iff.trans ⟨?_, fun h ↦ ⟨n, b, h, rfl⟩⟩
  rintro ⟨m, c, hc, he⟩
  obtain ⟨hn, hb⟩ := ZFSet.pair_inj.1 he
  rwa [natCode.injective hn, boolCode.injective hb]

/-- The graph code is faithful: the partial function is recovered from pair membership. -/
theorem graphCode_injective : Function.Injective graphCode := by
  intro f g h
  funext n
  refine Option.ext fun b ↦ ?_
  rw [← pair_mem_graphCode_iff (f := f), ← pair_mem_graphCode_iff (f := g), h]

/-! ### The condition code -/

/-- **The structural condition code**: a Cohen condition is coded by the graph code of its
lookup function. Injectivity follows from the faithfulness of the graph code plus lookup
extensionality — it is derived, not assumed. -/
def cohenConditionCode : ConditionCode Cond where
  repr p := graphRepr p.lookup
  injective_mk := by
    intro p q h
    exact ext_lookup (congrFun (graphCode_injective (show graphCode p.lookup = _ from h)))

/-- The condition code is the graph code of the lookup function, on the nose. -/
theorem mk_repr_eq_graphCode (p : Cond) :
    ZFSet.mk (cohenConditionCode.repr p) = graphCode p.lookup :=
  rfl

/-- The full membership description of the condition code. -/
theorem mem_cohenConditionCode_iff {p : Cond} {y : ZFSet.{0}} :
    y ∈ ZFSet.mk (cohenConditionCode.repr p) ↔
      ∃ n b, p.lookup n = some b ∧ y = ZFSet.pair (natCode n) (boolCode b) :=
  mem_graphCode_iff

/-- The membership characterization for conditions: the coded graph decides membership of a
coded pair exactly as the condition decides the coordinate. -/
theorem pair_mem_cohenConditionCode_iff {p : Cond} {n : ℕ} {b : Bool} :
    ZFSet.pair (natCode n) (boolCode b) ∈ ZFSet.mk (cohenConditionCode.repr p) ↔
      p.lookup n = some b :=
  pair_mem_graphCode_iff

end Forcing.Cohen
