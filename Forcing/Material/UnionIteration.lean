/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.ZFC.Basic

/-!
# Union iteration: the approximation predicates

The semantic layer of the ambient-domain construction's iteration. Formulas and realization
laws live in `Forcing/Material/UnionIterationFormula.lean`, mirroring the split the atomic
recursion uses.

An **approximation** is a trace of the iteration `S₀ = seed`, `S_{k+1} = ⋃₀ Sₖ`, carried up to
a bound. It is factored into four independent conditions rather than one predicate, so that a
later proof's hypotheses show which of them it actually consumed:

| Component | What it controls |
| --- | --- |
| `ApproxSupport` | no entry outside the bounded domain |
| `ApproxTotalFunctional` | exactly one value at each index in that domain |
| `ApproxBase` | the value at `∅` |
| `ApproxStep` | the recurrence |

## Support is not exactness on its own

`ApproxSupport` says only that every entry is a coded pair whose index lies in the domain —
**bounded no-junk support**. It does not say every index *has* an entry. The domain becomes
exact only jointly with `ApproxTotalFunctional`, which supplies the missing direction. Calling
the first conjunct "exact support" would overstate it.

## Deliberately absent

No `ω`, no `MaterialGround`, no scheme instance, and no Infinity. Those enter only with
existence and uniqueness of approximations; the predicates themselves are ordinary statements
about sets, and keeping them so is what makes the component realization laws axiom-free.
-/

universe u

namespace Forcing

namespace UnionIteration

/-- The bounded index domain: `k` is below or equal to the bound `n`.

Named rather than written inline at its two use sites, and deliberately *not* called an order.
Membership happens to behave as `<` on the sets the construction meets, but nothing here
assumes that, and an order notation would suggest arbitrary `ZFSet`s carry one. -/
def InApproxDomain (n k : ZFSet.{u}) : Prop := k ∈ n ∨ k = n

theorem inApproxDomain_self (n : ZFSet.{u}) : InApproxDomain n n := Or.inr rfl

theorem inApproxDomain_of_mem {n k : ZFSet.{u}} (h : k ∈ n) : InApproxDomain n k := Or.inl h

/-- **Bounded no-junk support**: every entry is a coded pair indexed inside the domain. Not
exactness on its own — see the module docstring. -/
def ApproxSupport (n t : ZFSet.{u}) : Prop :=
  ∀ e ∈ t, ∃ k S, e = ZFSet.pair k S ∧ InApproxDomain n k

/-- **Totality and functionality**: each index in the domain carries exactly one value. -/
def ApproxTotalFunctional (n t : ZFSet.{u}) : Prop :=
  ∀ k, InApproxDomain n k →
    ∃ S, ZFSet.pair k S ∈ t ∧ ∀ U, ZFSet.pair k U ∈ t → U = S

/-- **The base value**. -/
def ApproxBase (seed t : ZFSet.{u}) : Prop := ZFSet.pair ∅ seed ∈ t

/-- **The recurrence**: a successor entry's value is the general union of its predecessor's.

Stated over *given* entries rather than asserting that successors exist — existence is
`ApproxTotalFunctional`'s job. Keeping them apart is what lets each be realized without the
other. -/
def ApproxStep (n t : ZFSet.{u}) : Prop :=
  ∀ k ∈ n, ∀ S U, ZFSet.pair k S ∈ t → ZFSet.pair (insert k k) U ∈ t → U = ZFSet.sUnion S

/-- **An approximation**: the four conditions together.

Assembled only after each component had its own realization law, so that a consumer's
hypotheses can name which condition it used. In particular the domain is exact only through
the conjunction — `ApproxSupport` bounds the entries and `ApproxTotalFunctional` populates the
bound, and neither does the other's work. -/
def IsApprox (seed n t : ZFSet.{u}) : Prop :=
  ApproxSupport n t ∧ ApproxTotalFunctional n t ∧ ApproxBase seed t ∧ ApproxStep n t

/-- The exact domain, as the conjunction delivers it: an index carries an entry **iff** it
lies in the bound. Neither conjunct gives this alone. -/
theorem isApprox_mem_domain_iff {seed n t : ZFSet.{u}} (h : IsApprox seed n t) (k : ZFSet.{u}) :
    (∃ S, ZFSet.pair k S ∈ t) ↔ InApproxDomain n k := by
  refine ⟨fun ⟨S, hS⟩ ↦ ?_, fun hdom ↦ ?_⟩
  · obtain ⟨k', S', hpair, hdom⟩ := h.1 _ hS
    obtain ⟨rfl, -⟩ := ZFSet.pair_inj.1 hpair
    exact hdom
  · obtain ⟨S, hS, -⟩ := h.2.1 k hdom
    exact ⟨S, hS⟩

end UnionIteration

end Forcing
