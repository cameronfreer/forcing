/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.GameAdd
import Forcing.Name.Subname
import Forcing.Order.Basic

/-!
# Atomic external forcing: membership and equality on typed names

The atomic forcing relations, by the standard density clauses:

```text
p ⊩ τ ∈ σ   iff   {q | ∃ i, q ≤ σ.conds i ∧ q ⊩ τ = σ.elems i} is dense below p
p ⊩ τ = σ   iff   every branch activated below p on either side is forced to belong
                  to the other side
```

**The recursion kernel is pair recursion, not rank**: equality invokes membership in both
orientations, so the well-founded measure is the *unordered* pair of names under
`Sym2.GameAdd Subname` — the `fst_snd` constructor supplies exactly the argument swap that
equality's second inclusion needs, so no separate left/right membership components and no
coherence proof are required. Only the ordinary membership and equality relations are
exposed.

The unfolding laws (`forcesMem_iff`, `forcesEq_iff`) are named `↔`-laws, deliberately **not**
`@[simp]` until their rewriting behavior is understood. **Persistence** (`ForcesMem.mono`,
`ForcesEq.mono`) follows immediately from pullback stability of `IsDenseBelow`
(`mono_condition`) and narrowing the equality quantifiers; **equality symmetry**
(`ForcesEq.symm`) is the orientation sanity check, and reflexivity
(`forcesEq_refl`) certifies the clause shape by structural induction.

Scope (M6 discipline): external and typed; no name-family parameter yet (that arrives with
the formula relation `p ⊩[𝒩] φ`); no genericity, no visibility, no truth-lemma claims here.

## Main definitions

* `Forcing.ForcesMem`, `Forcing.ForcesEq`: the atomic forcing relations.

## Main results

* `Forcing.forcesMem_iff`, `Forcing.forcesEq_iff`: the named unfolding laws.
* `Forcing.ForcesMem.mono`, `Forcing.ForcesEq.mono`: persistence under strengthening.
* `Forcing.ForcesEq.symm`, `Forcing.forcesEq_refl`: symmetry and reflexivity.
-/

universe u v

namespace Forcing

open PName

variable {P : Type u} [Preorder P] {p q : P} {τ σ : PName P}

/-- The well-founded measure of the atomic kernel: unordered pairs of names, one coordinate
descending at a time. -/
instance : WellFoundedRelation (Sym2 (PName P)) where
  rel := Sym2.GameAdd Subname
  wf := subname_wellFounded.sym2_gameAdd

mutual

/-- Atomic forcing, membership: the branches of `σ` that decide agreement with `τ` are dense
below `p`. -/
def ForcesMem (p : P) (τ σ : PName P) : Prop :=
  IsDenseBelow {q | ∃ i : σ.Idx, q ≤ σ.conds i ∧ ForcesEq q τ (σ.elems i)} p
termination_by s(τ, σ)
decreasing_by
  exact Sym2.GameAdd.snd (subname_elems σ i)

/-- Atomic forcing, equality: every branch activated below `p`, on either side, is forced to
belong to the other side. -/
def ForcesEq (p : P) (τ σ : PName P) : Prop :=
  (∀ i : τ.Idx, ∀ q ≤ p, q ≤ τ.conds i → ForcesMem q (τ.elems i) σ) ∧
    (∀ j : σ.Idx, ∀ q ≤ p, q ≤ σ.conds j → ForcesMem q (σ.elems j) τ)
termination_by s(τ, σ)
decreasing_by
  · exact Sym2.GameAdd.fst (subname_elems τ i)
  · exact Sym2.GameAdd.fst_snd (subname_elems σ j)

end

/-- The named unfolding law for membership. Deliberately not `@[simp]`. -/
theorem forcesMem_iff :
    ForcesMem p τ σ ↔
      IsDenseBelow {q | ∃ i : σ.Idx, q ≤ σ.conds i ∧ ForcesEq q τ (σ.elems i)} p := by
  rw [ForcesMem]

/-- The named unfolding law for equality. Deliberately not `@[simp]`. -/
theorem forcesEq_iff :
    ForcesEq p τ σ ↔
      (∀ i : τ.Idx, ∀ q ≤ p, q ≤ τ.conds i → ForcesMem q (τ.elems i) σ) ∧
        (∀ j : σ.Idx, ∀ q ≤ p, q ≤ σ.conds j → ForcesMem q (σ.elems j) τ) := by
  rw [ForcesEq]

/-- **Persistence** for membership: pullback stability of `IsDenseBelow`. -/
theorem ForcesMem.mono (h : ForcesMem p τ σ) (hqp : q ≤ p) : ForcesMem q τ σ := by
  rw [forcesMem_iff] at h ⊢
  exact h.mono_condition hqp

/-- **Persistence** for equality: narrow the quantifiers. -/
theorem ForcesEq.mono (h : ForcesEq p τ σ) (hqp : q ≤ p) : ForcesEq q τ σ := by
  rw [forcesEq_iff] at h ⊢
  exact ⟨fun i r hrq hri ↦ h.1 i r (hrq.trans hqp) hri,
    fun j r hrq hrj ↦ h.2 j r (hrq.trans hqp) hrj⟩

/-- **Symmetry** of atomic equality — the orientation sanity check: the two inclusions of the
clause swap. -/
theorem ForcesEq.symm (h : ForcesEq p τ σ) : ForcesEq p σ τ := by
  rw [forcesEq_iff] at h ⊢
  exact ⟨h.2, h.1⟩

theorem forcesEq_comm : ForcesEq p τ σ ↔ ForcesEq p σ τ :=
  ⟨.symm, .symm⟩

/-- **Reflexivity** of atomic equality, by structural induction — certifying the clause
shape: each activated branch of `τ` is densely forced equal to itself inside `τ`. -/
theorem forcesEq_refl : ∀ (τ : PName P) (p : P), ForcesEq p τ τ := by
  intro τ
  induction τ with
  | mk ι e c ih =>
    intro p
    rw [forcesEq_iff]
    refine ⟨?_, ?_⟩ <;>
    · intro i q _ hqi
      rw [forcesMem_iff]
      intro r hr
      exact ⟨r, ⟨i, (Set.mem_Iic.1 hr).trans hqi, ih i r⟩, le_rfl⟩

end Forcing
