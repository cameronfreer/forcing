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

end MaterialGround

end Forcing
