/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Omega
import Forcing.Material.UnionIterationFormula

/-!
# Union iteration: the internally priced results

Where the iteration starts costing something. `UnionIteration.lean` establishes that the four
clauses determine values; this module establishes it *inside the ground*, by formula-relative
induction over internal `ω`.

## Existence, and what it costs

`exists_isApprox` charges **Pairing**, **Binary Union**, **General Union**, and one named
induction instance. It does **not** charge Empty Set: the induction's base hands over a
carrier element already equal to `∅`, so the empty set arrives through the binder. No
Collection, Infinity, Foundation, or Power Set, and existence never consults uniqueness.

## Uniqueness, and what it costs

`isApprox_unique` charges:

* one membership for `omegaMemTransFormula` — via `omegaValue_mem_isTransitive`;
* one new named induction instance, `approxAgreeFormula`.

and **nothing else**. In particular no Pairing, no Union of either kind, no Collection, no
Infinity, no Foundation, no Power Set. Nothing is constructed here: the argument only compares
two traces that are already given.

`omegaTransFormula` is deliberately **not** used. Transitivity of `ω` is the wrong fact for
this argument — what the successor step needs is transitivity of the *bound* `N`, so that
`succ n` in `N`'s domain returns `n` to it. That is `omegaValue_mem_isTransitive`.

## The shape of the induction

Bounded-prefix rather than pointwise: the predicate carries agreement across a whole prefix,

```text
P n := InApproxDomain N n → ∀ k, InApproxDomain n k → ValuesAgreeAt t u k
```

so the successor step can reuse the predecessor's value instead of re-deriving it. Proving
agreement independently at each index would need the recurrence to be re-entered every time.

The semantic extensionality argument (`isApprox_eq_of_prefixAgree`) stays in the semantic
module; only the induction that establishes its hypothesis is priced here.
-/

universe u

namespace Forcing

open FirstOrder Language UnionIteration

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **Approximation uniqueness.** Two approximations over the same seed and bound are equal.

Charged: one membership for `omegaMemTransFormula`, one for `approxAgreeFormula`. Nothing is
constructed, so no closure axiom is consumed. -/
theorem isApprox_unique (hmem : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    {w : ZFSet.{u}} {omega : ↥M.toMaterialCarrier}
    (hw : IsInductive w)
    (hom : OmegaValue M.toMaterialCarrier w (omega : ZFSet.{u}))
    (seed N t u : ↥M.toMaterialCarrier)
    (hN : (N : ZFSet.{u}) ∈ (omega : ZFSet.{u}))
    (ht : IsApprox (seed : ZFSet.{u}) (N : ZFSet.{u}) (t : ZFSet.{u}))
    (hu : IsApprox (seed : ZFSet.{u}) (N : ZFSet.{u}) (u : ZFSet.{u})) :
    (t : ZFSet.{u}) = (u : ZFSet.{u}) := by
  have hNtrans : (N : ZFSet.{u}).IsTransitive :=
    M.omegaValue_mem_isTransitive hmem hw hom N hN
  -- The prefix induction, over internal `ω`.
  have key : ∀ n : ↥M.toMaterialCarrier, (n : ZFSet.{u}) ∈ (omega : ZFSet.{u}) →
      approxAgreeFormula.Realize ![N, t, u] ![n] := by
    refine M.omega_induction hagree ![N, t, u] hw hom (fun z hz ↦ ?_) (fun n hn hφ s hs ↦ ?_)
    · rw [realize_approxAgreeFormula, hz]
      exact prefixAgree_empty ht hu
    · rw [realize_approxAgreeFormula, hs]
      exact prefixAgree_succ ht hu hNtrans ((realize_approxAgreeFormula N t u n).1 hφ)
  -- Instantiate at the bound itself; reflexivity puts it in its own domain.
  have hNagree := (realize_approxAgreeFormula N t u N).1 (key N hN) (inApproxDomain_self _)
  exact isApprox_eq_of_prefixAgree ht hu hNagree

/-- **Approximation existence.** Every bound in `ω` carries an approximation inside the ground.

Charged, and no more: **Pairing** (the base entry, its singleton, and the successor entry),
**Binary Union** (inserting the successor entry), **General Union** (the successor value), and
one named induction instance, `approxExistsFormula`.

**No Empty Set.** The induction's base hands over a carrier element already equal to `∅`, so
the empty set arrives through the binder rather than through an axiom. **No Collection, no
Infinity, no Foundation, no Power Set**, and no uniqueness hypothesis — existence does not
consult `isApprox_unique`. -/
theorem exists_isApprox (hex : separationSentence approxExistsFormula ∈ T)
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T) (huni : unionSentence ∈ T)
    {w : ZFSet.{u}} {omega : ↥M.toMaterialCarrier}
    (hw : IsInductive w)
    (hom : OmegaValue M.toMaterialCarrier w (omega : ZFSet.{u}))
    (seed : ↥M.toMaterialCarrier) :
    ∀ n : ↥M.toMaterialCarrier, (n : ZFSet.{u}) ∈ (omega : ZFSet.{u}) →
      ∃ t : ↥M.toMaterialCarrier,
        IsApprox (seed : ZFSet.{u}) (n : ZFSet.{u}) (t : ZFSet.{u}) := by
  intro N hN
  refine (realize_approxExistsFormula seed N).1 ?_
  refine M.omega_induction hex ![seed] hw hom (fun z hz ↦ ?_) (fun n hn hφ s hs ↦ ?_) N hN
  · -- Base: the empty set arrives through the binder, so no Empty Set axiom is charged.
    rw [realize_approxExistsFormula, hz]
    have h0M : (∅ : ZFSet.{u}) ∈ M.toMaterialCarrier := hz ▸ z.2
    have hpairM : ZFSet.pair (∅ : ZFSet.{u}) (seed : ZFSet.{u}) ∈ M.toMaterialCarrier :=
      M.pair_mem hp h0M seed.2
    exact ⟨⟨{ZFSet.pair (∅ : ZFSet.{u}) (seed : ZFSet.{u})}, M.singleton_mem hp hpairM⟩,
      isApprox_base fun e ↦ by simp [ZFSet.mem_singleton]⟩
  · -- Step: read the old value, take its general union, and extend.
    rw [realize_approxExistsFormula, hs]
    obtain ⟨t, ht⟩ := (realize_approxExistsFormula seed n).1 hφ
    obtain ⟨S, hS, -⟩ := ht.2.1 (n : ZFSet.{u}) (inApproxDomain_self _)
    have hSM : S ∈ M.toMaterialCarrier :=
      (MaterialCarrier.pair_components_mem_of_mem t.2 hS).2
    have hsuccM : insert (n : ZFSet.{u}) (n : ZFSet.{u}) ∈ M.toMaterialCarrier := hs ▸ s.2
    have hentryM : ZFSet.pair (insert (n : ZFSet.{u}) (n : ZFSet.{u})) (ZFSet.sUnion S) ∈
        M.toMaterialCarrier := M.pair_mem hp hsuccM (M.sUnion_mem huni hSM)
    refine ⟨⟨insert (ZFSet.pair (insert (n : ZFSet.{u}) (n : ZFSet.{u})) (ZFSet.sUnion S))
        (t : ZFSet.{u}), M.insert_mem hp hu hentryM t.2⟩, ?_⟩
    exact isApprox_extend ht hS (fun e ↦ by rw [ZFSet.mem_insert_iff]; exact or_comm)

end MaterialGround

end Forcing
