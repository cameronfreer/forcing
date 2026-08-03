/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Insert
import Forcing.Order.Basic

/-!
# Linked and centered families

Wave B1 of the external property kernel (width axis of `docs/property-zoo.md`): linked and
centered sets of conditions, their σ-variants as explicit `ℕ`-indexed covers, and the
implication chain. Everything here is **external and order-theoretic**; no cardinal
preservation is claimed, and the chain stops before ccc, which arrives with the external
chain-condition wave.

Scope warning, certified rather than merely stated: external width notions carry essentially
no information over countable presentations — every countable preorder is σ-centered by
singleton decomposition (`isSigmaCentered_of_countable`). This is the external-vacuity
instance of architecture constraint 9; the hypotheses that can do preservation work are
`M`-internal, and belong to a much later layer.

Convention: the kernel has no top condition, so `IsCentered` demands common strengthenings
only for **nonempty** finite subsets — the empty subset would otherwise smuggle `Nonempty P`
into every centered family.

## Main definitions

* `Forcing.IsLinked`, `Forcing.IsCentered`: pairwise compatibility; common strengthenings of
  nonempty finite subsets.
* `Forcing.IsSigmaLinked`, `Forcing.IsSigmaCentered`: countable covers by linked/centered
  pieces.

## Main results

* `Forcing.IsCentered.isLinked`, `Forcing.IsSigmaCentered.isSigmaLinked`: the implication
  chain.
* `Forcing.isSigmaCentered_of_countable`: the certified external-vacuity warning.
-/

namespace Forcing

variable {P : Type*} [Preorder P] {A : Set P} {p q : P}

/-- A set of conditions is *linked* if any two of its members are compatible. -/
def IsLinked (A : Set P) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, Compatible p q

/-- A set of conditions is *centered* if every **nonempty** finite subset has a common
strengthening. Nonemptiness is deliberate: the kernel has no top, and the empty finite subset
would otherwise demand `Nonempty P` of every centered family. -/
def IsCentered (A : Set P) : Prop :=
  ∀ s : Finset P, s.Nonempty → ↑s ⊆ A → ∃ r, ∀ p ∈ s, r ≤ p

/-- σ-linked: an explicit countable cover by linked pieces. External formulation; the cover
is data-like on purpose, so the chain-condition wave can consume it. -/
def IsSigmaLinked (P : Type*) [Preorder P] : Prop :=
  ∃ c : ℕ → Set P, (∀ n, IsLinked (c n)) ∧ ∀ p : P, ∃ n, p ∈ c n

/-- σ-centered: an explicit countable cover by centered pieces. -/
def IsSigmaCentered (P : Type*) [Preorder P] : Prop :=
  ∃ c : ℕ → Set P, (∀ n, IsCentered (c n)) ∧ ∀ p : P, ∃ n, p ∈ c n

/-- Centered implies linked: a common strengthening of `{p, q}` witnesses compatibility. -/
theorem IsCentered.isLinked (h : IsCentered A) : IsLinked A := by
  classical
  intro p hp q hq
  obtain ⟨r, hr⟩ := h {p, q} ⟨p, by simp⟩ (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hp
    · exact Finset.mem_singleton.1 hx ▸ hq)
  exact ⟨r, hr p (by simp), hr q (by simp)⟩

/-- σ-centered implies σ-linked, piecewise. -/
theorem IsSigmaCentered.isSigmaLinked (h : IsSigmaCentered P) : IsSigmaLinked P :=
  h.imp fun _ ⟨hc, hcov⟩ ↦ ⟨fun n ↦ (hc n).isLinked, hcov⟩

/-- A singleton is centered: the point strengthens itself. -/
theorem isCentered_singleton (p : P) : IsCentered ({p} : Set P) :=
  fun _ _ hsub ↦ ⟨p, fun _ hq ↦ le_of_eq (hsub hq).symm⟩

/-- The empty family is centered, vacuously. -/
theorem isCentered_empty : IsCentered (∅ : Set P) :=
  fun _ hs hsub ↦ absurd (hsub hs.choose_spec) (Set.notMem_empty _)

/-- **The certified external-vacuity warning** (architecture constraint 9): every countable
preorder is σ-centered, by singleton decomposition. External width notions carry essentially
no information over countable presentations; the hypotheses that preserve anything are
`M`-internal and arrive with the material layer. -/
theorem isSigmaCentered_of_countable [Countable P] : IsSigmaCentered P := by
  cases isEmpty_or_nonempty P with
  | inl h => exact ⟨fun _ ↦ ∅, fun _ ↦ isCentered_empty, fun p ↦ (h.false p).elim⟩
  | inr h =>
    obtain ⟨f, hf⟩ := exists_surjective_nat P
    exact ⟨fun n ↦ {f n}, fun n ↦ isCentered_singleton (f n),
      fun p ↦ (hf p).imp fun _ hn ↦ hn.symm⟩

/-!
### Sanity examples

A linked set need not be centered-witnessed by anything in this file — the strictness column
of the property card stays deferred until separating examples exist. What can be certified
now: linkedness of any subset of a centered family, and the two-element instance of the
chain.
-/

example (h : IsCentered A) {B : Set P} (hBA : B ⊆ A) : IsLinked B :=
  fun p hp q hq ↦ h.isLinked p (hBA hp) q (hBA hq)

example (h : IsCentered A) (hp : p ∈ A) (hq : q ∈ A) : Compatible p q :=
  h.isLinked p hp q hq

end Forcing
