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

The **approximation algebra** below is likewise free: it establishes that the four clauses
determine values, before anything is paid for constructing a trace internally. Its three
successor facts — that a successor differs from its base, is fresh for its own bound, and is
injective — come from ambient well-foundedness, the same source that makes Foundation free
for material carriers.
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

/-! ### Approximation algebra

Pure consequences of the four clauses — no ground, no schemes, no `ω`. The point of proving
them first is to check that the clauses **determine values** before paying anything for their
internal construction.

Three small facts about successors are used throughout and are **free**, from ambient
well-foundedness (`ZFSet.mem_irrefl`, `ZFSet.mem_asymm`) — the same source that makes
Foundation free for material carriers. None of them is charged to a theory. -/

section Algebra

/-- A successor is not its own base. Free. -/
theorem succ_ne_self (k : ZFSet.{u}) : insert k k ≠ k := by
  intro h
  have hk : k ∈ insert k k := ZFSet.mem_insert_iff.2 (Or.inl rfl)
  rw [h] at hk
  exact ZFSet.mem_irrefl k hk

/-- **A successor is fresh for its own bound**: it lies outside the bounded domain. Free, and
it is what makes the extension step's disjointness automatic rather than hypothetical. -/
theorem succ_notMem_approxDomain (n : ZFSet.{u}) : ¬ InApproxDomain n (insert n n) := by
  rintro (hmem | heq)
  · exact ZFSet.mem_asymm hmem (ZFSet.mem_insert_iff.2 (Or.inl rfl))
  · exact succ_ne_self n heq

/-- **Successor injectivity.** Free. -/
theorem succ_inj {k k' : ZFSet.{u}} (h : insert k k = insert k' k') : k = k' := by
  by_contra hne
  have hk : k ∈ insert k' k' := by
    have : k ∈ insert k k := ZFSet.mem_insert_iff.2 (Or.inl rfl)
    rwa [h] at this
  have hk' : k' ∈ insert k k := by
    have : k' ∈ insert k' k' := ZFSet.mem_insert_iff.2 (Or.inl rfl)
    rwa [← h] at this
  rcases ZFSet.mem_insert_iff.1 hk with rfl | hkk'
  · exact hne rfl
  · rcases ZFSet.mem_insert_iff.1 hk' with rfl | hk'k
    · exact hne rfl
    · exact ZFSet.mem_asymm hkk' hk'k

/-- The successor domain, unfolded. -/
theorem inApproxDomain_succ_iff {n k : ZFSet.{u}} :
    InApproxDomain (insert n n) k ↔ InApproxDomain n k ∨ k = insert n n := by
  unfold InApproxDomain
  rw [ZFSet.mem_insert_iff]
  tauto

/-- **Values are determined inside a trace.** -/
theorem approx_value_unique {n t k S U : ZFSet.{u}} (hTF : ApproxTotalFunctional n t)
    (hdom : InApproxDomain n k) (hS : ZFSet.pair k S ∈ t) (hU : ZFSet.pair k U ∈ t) :
    S = U := by
  obtain ⟨V, -, hfun⟩ := hTF k hdom
  rw [hfun S hS, hfun U hU]

/-- **The consumer-earned `∅` fact.** `∅` lies in the domain of any approximation — support
applied to the base entry gives it. This is the fact deliberately left undeclared in
`Forcing/Material/Omega.lean`, appearing here where it is actually used and priced at nothing:
it is a consequence of the clauses, not an input to them. -/
theorem approx_empty_inApproxDomain {seed n t : ZFSet.{u}} (h : IsApprox seed n t) :
    InApproxDomain n (∅ : ZFSet.{u}) := by
  obtain ⟨k, S, hpair, hdom⟩ := h.1 _ h.2.2.1
  obtain ⟨rfl, -⟩ := ZFSet.pair_inj.1 hpair
  exact hdom

/-- **Reading the base value.** -/
theorem approx_base_value {seed n t S : ZFSet.{u}} (h : IsApprox seed n t)
    (hS : ZFSet.pair (∅ : ZFSet.{u}) S ∈ t) : S = seed :=
  approx_value_unique h.2.1 (approx_empty_inApproxDomain h) hS h.2.2.1

/-- **Extension by one step.** The new bound's value is the general union of the old bound's,
and no hypothesis of freshness is needed — `succ_notMem_approxDomain` supplies it. -/
theorem isApprox_extend {seed n t S t' : ZFSet.{u}} (h : IsApprox seed n t)
    (hS : ZFSet.pair n S ∈ t)
    (ht' : ∀ e, e ∈ t' ↔ e ∈ t ∨ e = ZFSet.pair (insert n n) (ZFSet.sUnion S)) :
    IsApprox seed (insert n n) t' := by
  obtain ⟨hsup, hTF, hbase, hstep⟩ := h
  have hfresh := succ_notMem_approxDomain n
  -- No old entry sits at the new index.
  have hold : ∀ U, ZFSet.pair (insert n n) U ∈ t → False := by
    intro U hU
    obtain ⟨k, V, hpair, hdom⟩ := hsup _ hU
    obtain ⟨rfl, -⟩ := ZFSet.pair_inj.1 hpair
    exact hfresh hdom
  refine ⟨fun e he ↦ ?_, fun k hdom ↦ ?_, (ht' _).2 (Or.inl hbase), fun k hk S' U hS' hU ↦ ?_⟩
  · rcases (ht' e).1 he with h1 | rfl
    · obtain ⟨k, V, hpair, hdom⟩ := hsup e h1
      exact ⟨k, V, hpair, inApproxDomain_succ_iff.2 (Or.inl hdom)⟩
    · exact ⟨insert n n, ZFSet.sUnion S, rfl, inApproxDomain_succ_iff.2 (Or.inr rfl)⟩
  · rcases inApproxDomain_succ_iff.1 hdom with hdom' | rfl
    · obtain ⟨V, hV, hfun⟩ := hTF k hdom'
      refine ⟨V, (ht' _).2 (Or.inl hV), fun U hU ↦ ?_⟩
      rcases (ht' _).1 hU with h1 | h1
      · exact hfun U h1
      · obtain ⟨rfl, -⟩ := ZFSet.pair_inj.1 h1
        exact absurd hdom' hfresh
    · refine ⟨ZFSet.sUnion S, (ht' _).2 (Or.inr rfl), fun U hU ↦ ?_⟩
      rcases (ht' _).1 hU with h1 | h1
      · exact absurd h1 (fun hc ↦ hold U hc)
      · exact (ZFSet.pair_inj.1 h1).2
  · -- the recurrence, at the new bound and below it
    rcases ZFSet.mem_insert_iff.1 hk with rfl | hkn
    · have hS'old : ZFSet.pair k S' ∈ t := by
        rcases (ht' _).1 hS' with h1 | h1
        · exact h1
        · exact absurd (ZFSet.pair_inj.1 h1).1 (succ_ne_self k).symm
      have hUnew : U = ZFSet.sUnion S := by
        rcases (ht' _).1 hU with h1 | h1
        · exact absurd h1 (fun hc ↦ hold U hc)
        · exact (ZFSet.pair_inj.1 h1).2
      rw [hUnew, approx_value_unique hTF (Or.inr rfl) hS hS'old]
    · have hS'old : ZFSet.pair k S' ∈ t := by
        rcases (ht' _).1 hS' with h1 | h1
        · exact h1
        · exact absurd ((ZFSet.pair_inj.1 h1).1 ▸ hkn) (fun hc ↦ hfresh (Or.inl hc))
      have hUold : ZFSet.pair (insert k k) U ∈ t := by
        rcases (ht' _).1 hU with h1 | h1
        · exact h1
        · have : k = n := succ_inj (ZFSet.pair_inj.1 h1).1
          exact absurd (this ▸ hkn) (ZFSet.mem_irrefl n)
      exact hstep k hkn S' U hS'old hUold

end Algebra

end UnionIteration

end Forcing
