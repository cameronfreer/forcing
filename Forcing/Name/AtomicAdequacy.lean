/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.Atomic
import Forcing.Name.Valuation
import Forcing.Order.Localize
import Forcing.Model.GenericOver

/-!
# Atomic semantic adequacy

The mutual endpoint connecting atomic forcing to actual valuation, for names from a
subname-closed family `𝒩`:

```text
zval ↑G τ ∈ zval ↑G σ  ↔  ∃ p ∈ G, ForcesMem p τ σ
zval ↑G τ = zval ↑G σ  ↔  ∃ p ∈ G, ForcesEq p τ σ
```

The atomic relations themselves are family-independent; only the **visibility budget** is
family-relative, and it consists of exactly two test families:

* the **localized membership tests** `localizeBelow (memWitness τ σ) p` — soundness's budget:
  they transfer `p ⊩ τ ∈ σ` to actual valuation membership;
* the **equality decision test** `eqDecision τ σ` — completeness's budget: conditions forcing
  equality, padded with the two membership-obstruction families. Failure of `ForcesEq` below
  a condition yields an obstruction below it (from failure of the relevant `IsDenseBelow`),
  so the test is globally dense open (`isDenseOpen_eqDecision`); when the valuations are
  equal, membership completeness for the smaller pair rules out either obstruction inside
  `G`, leaving a condition forcing equality. (The forcing-equality set plus two obstruction
  families is the standard direct atomic truth-lemma pattern.)

The mutual induction runs on the same `Sym2.GameAdd Subname` descent already certified by
the kernel, and subname closure keeps it inside `𝒩`. Two layers, deliberately: the
observer-free theorem (`forces_adequacy`) consumes `Meets` hypotheses; the `GenericOver`
corollary (`forces_adequacy_of_genericOver`) discharges them from visibility — genericity is
*only* the bridge from visible tests to meetings. No countability anywhere.

## Main definitions

* `Forcing.eqObstruction`, `Forcing.eqDecision`: the equality obstruction and decision tests.

## Main results

* `Forcing.isDenseOpen_eqDecision`: the decision test is globally dense open.
* `Forcing.forces_adequacy`: the mutual endpoint, observer-free.
* `Forcing.forces_adequacy_of_genericOver`: the visibility corollary.
-/

universe u

namespace Forcing

open PName Order

variable {P : Type u} [Preorder P] {p q : P} {τ σ : PName P} {𝒩 : Set (PName P)}
variable {G : PFilter P}

/-- The **membership obstruction**: conditions activating a branch of `τ` no strengthening of
which forces the corresponding membership in `σ`. Lower by quantifier narrowing. -/
def eqObstruction (τ σ : PName P) : Set P :=
  {r | ∃ i : τ.Idx, r ≤ τ.conds i ∧ ∀ q ≤ r, ¬ForcesMem q (τ.elems i) σ}

/-- The **equality decision test**: conditions forcing equality, padded with the two
obstruction families. Globally dense open (`isDenseOpen_eqDecision`) — completeness's
visibility budget. -/
def eqDecision (τ σ : PName P) : Set P :=
  {p | ForcesEq p τ σ} ∪ eqObstruction τ σ ∪ eqObstruction σ τ

/-- Failure of forced membership yields a *blocker*: a strengthening below which no
membership witness lies. -/
theorem exists_blocker_of_not_forcesMem (h : ¬ForcesMem q τ σ) :
    ∃ r ≤ q, ∀ s ∈ memWitness τ σ, ¬s ≤ r := by
  by_contra hcon
  push Not at hcon
  exact h fun a ha ↦ hcon a ha

/-- **The decision test is globally dense open**: below any condition, either equality is
forced, or the failing inclusion produces an obstruction below it. -/
theorem isDenseOpen_eqDecision (τ σ : PName P) : IsDenseOpen (eqDecision τ σ) := by
  constructor
  · intro p
    by_cases h : ForcesEq p τ σ
    · exact ⟨p, Or.inl (Or.inl h), le_rfl⟩
    · rw [forcesEq_iff, not_and_or] at h
      rcases h with h | h
      · push Not at h
        obtain ⟨i, q, hqp, hqc, hq⟩ := h
        obtain ⟨r, hrq, hblock⟩ := exists_blocker_of_not_forcesMem hq
        refine ⟨r, Or.inl (Or.inr ⟨i, hrq.trans hqc, fun s hsr hFs ↦ ?_⟩), hrq.trans hqp⟩
        obtain ⟨y, hyW, hys⟩ := hFs (Set.mem_Iic.2 le_rfl)
        exact hblock y hyW (hys.trans hsr)
      · push Not at h
        obtain ⟨j, q, hqp, hqc, hq⟩ := h
        obtain ⟨r, hrq, hblock⟩ := exists_blocker_of_not_forcesMem hq
        refine ⟨r, Or.inr ⟨j, hrq.trans hqc, fun s hsr hFs ↦ ?_⟩, hrq.trans hqp⟩
        obtain ⟨y, hyW, hys⟩ := hFs (Set.mem_Iic.2 le_rfl)
        exact hblock y hyW (hys.trans hsr)
  · refine IsLowerSet.union (IsLowerSet.union ?_ ?_) ?_
    · exact fun a b hba ha ↦ ForcesEq.mono ha hba
    · rintro a b hba ⟨i, hac, hblock⟩
      exact ⟨i, hba.trans hac, fun s hsb ↦ hblock s (hsb.trans hba)⟩
    · rintro a b hba ⟨j, hac, hblock⟩
      exact ⟨j, hba.trans hac, fun s hsb ↦ hblock s (hsb.trans hba)⟩

/-- **Atomic semantic adequacy**, observer-free: over a subname-closed family, and given the
two test-meeting budgets, forced membership and equality along `G` coincide with actual
membership and equality of the valuations. The induction is `Sym2.GameAdd` on the unordered
pair — the same descent certified by the kernel. -/
theorem forces_adequacy (h𝒩 : SubnameClosed 𝒩)
    (hmem : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, ∀ p ∈ G, ForcesMem p τ σ →
      Meets G (localizeBelow (memWitness τ σ) p))
    (heq : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, Meets G (eqDecision τ σ)) :
    ∀ τ σ : PName P, τ ∈ 𝒩 → σ ∈ 𝒩 →
      ((zval (G : Set P) τ ∈ zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesMem p τ σ) ∧
        (zval (G : Set P) τ = zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesEq p τ σ)) := by
  refine Sym2.GameAdd.recursion subname_wellFounded fun τ σ IH hτ hσ ↦ ?_
  have memAdeq :
      zval (G : Set P) τ ∈ zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesMem p τ σ := by
    constructor
    · intro hy
      rw [mem_zval_iff] at hy
      obtain ⟨i, hci, hval⟩ := hy
      obtain ⟨q, hqG, hqEq⟩ :=
        ((IH τ (σ.elems i) (Sym2.GameAdd.snd (subname_elems σ i)) hτ (h𝒩 σ hσ i)).2).1 hval
      obtain ⟨r, hrG, hrq, hrc⟩ := exists_mem_le_le hqG hci
      refine ⟨r, hrG, fun a ha ↦ ?_⟩
      exact ⟨a, mem_memWitness_iff.2
        ⟨i, (Set.mem_Iic.1 ha).trans hrc, hqEq.mono ((Set.mem_Iic.1 ha).trans hrq)⟩, le_rfl⟩
    · rintro ⟨p, hpG, hpF⟩
      obtain ⟨w, hwG, hwW⟩ := (meets_localizeBelow_iff hpG).1 (hmem τ hτ σ hσ p hpG hpF)
      obtain ⟨i, hwc, hwEq⟩ := mem_memWitness_iff.1 hwW
      rw [mem_zval_iff]
      exact ⟨i, G.mem_of_le hwc hwG,
        ((IH τ (σ.elems i) (Sym2.GameAdd.snd (subname_elems σ i)) hτ (h𝒩 σ hσ i)).2).2
          ⟨w, hwG, hwEq⟩⟩
  have eqAdeq :
      zval (G : Set P) τ = zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesEq p τ σ := by
    constructor
    · intro hval
      obtain ⟨p, hpG, hp⟩ := heq τ hτ σ hσ
      rcases hp with (hp | hp) | hp
      · exact ⟨p, hpG, hp⟩
      · exfalso
        obtain ⟨i, hpc, hblock⟩ := hp
        have hmemi : zval (G : Set P) (τ.elems i) ∈ zval (G : Set P) σ := by
          rw [← hval, mem_zval_iff]
          exact ⟨i, G.mem_of_le hpc hpG, rfl⟩
        obtain ⟨q, hqG, hqF⟩ :=
          ((IH (τ.elems i) σ (Sym2.GameAdd.fst (subname_elems τ i)) (h𝒩 τ hτ i) hσ).1).1 hmemi
        obtain ⟨r, hrG, hrp, hrq⟩ := exists_mem_le_le hpG hqG
        exact hblock r hrp (hqF.mono hrq)
      · exfalso
        obtain ⟨j, hpc, hblock⟩ := hp
        have hmemj : zval (G : Set P) (σ.elems j) ∈ zval (G : Set P) τ := by
          rw [hval, mem_zval_iff]
          exact ⟨j, G.mem_of_le hpc hpG, rfl⟩
        obtain ⟨q, hqG, hqF⟩ :=
          ((IH (σ.elems j) τ (Sym2.GameAdd.fst_snd (subname_elems σ j)) (h𝒩 σ hσ j) hτ).1).1
            hmemj
        obtain ⟨r, hrG, hrp, hrq⟩ := exists_mem_le_le hpG hqG
        exact hblock r hrp (hqF.mono hrq)
    · rintro ⟨p, hpG, hpEq⟩
      rw [forcesEq_iff] at hpEq
      refine ZFSet.ext fun y ↦ ⟨?_, ?_⟩
      · intro hy
        rw [mem_zval_iff] at hy
        obtain ⟨i, hci, rfl⟩ := hy
        obtain ⟨r, hrG, hrp, hrc⟩ := exists_mem_le_le hpG hci
        exact ((IH (τ.elems i) σ (Sym2.GameAdd.fst (subname_elems τ i)) (h𝒩 τ hτ i) hσ).1).2
          ⟨r, hrG, hpEq.1 i r hrp hrc⟩
      · intro hy
        rw [mem_zval_iff] at hy
        obtain ⟨j, hcj, rfl⟩ := hy
        obtain ⟨r, hrG, hrp, hrc⟩ := exists_mem_le_le hpG hcj
        exact ((IH (σ.elems j) τ (Sym2.GameAdd.fst_snd (subname_elems σ j)) (h𝒩 σ hσ j) hτ).1).2
          ⟨r, hrG, hpEq.2 j r hrp hrc⟩
  exact ⟨memAdeq, eqAdeq⟩

/-- Membership adequacy, projected. -/
theorem zval_mem_zval_iff_exists_forcesMem (h𝒩 : SubnameClosed 𝒩)
    (hmem : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, ∀ p ∈ G, ForcesMem p τ σ →
      Meets G (localizeBelow (memWitness τ σ) p))
    (heq : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, Meets G (eqDecision τ σ))
    (hτ : τ ∈ 𝒩) (hσ : σ ∈ 𝒩) :
    zval (G : Set P) τ ∈ zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesMem p τ σ :=
  (forces_adequacy h𝒩 hmem heq τ σ hτ hσ).1

/-- Equality adequacy, projected. -/
theorem zval_eq_zval_iff_exists_forcesEq (h𝒩 : SubnameClosed 𝒩)
    (hmem : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, ∀ p ∈ G, ForcesMem p τ σ →
      Meets G (localizeBelow (memWitness τ σ) p))
    (heq : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, Meets G (eqDecision τ σ))
    (hτ : τ ∈ 𝒩) (hσ : σ ∈ 𝒩) :
    zval (G : Set P) τ = zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesEq p τ σ :=
  (forces_adequacy h𝒩 hmem heq τ σ hτ hσ).2

/-- **The visibility corollary**: over a generic filter, the two `Meets` budgets are
discharged from visibility of the two test families — genericity is only the bridge from
visible tests to meetings. -/
theorem forces_adequacy_of_genericOver {M : VisibilityContext P} (hG : GenericOver M G)
    (h𝒩 : SubnameClosed 𝒩)
    (hvmem : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, ∀ p ∈ G, ForcesMem p τ σ →
      M.Visible (localizeBelow (memWitness τ σ) p))
    (hveq : ∀ τ ∈ 𝒩, ∀ σ ∈ 𝒩, M.Visible (eqDecision τ σ)) :
    ∀ τ σ : PName P, τ ∈ 𝒩 → σ ∈ 𝒩 →
      ((zval (G : Set P) τ ∈ zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesMem p τ σ) ∧
        (zval (G : Set P) τ = zval (G : Set P) σ ↔ ∃ p ∈ G, ForcesEq p τ σ)) :=
  forces_adequacy h𝒩
    (fun τ hτ σ hσ p hpG hF ↦
      hG _ ⟨hvmem τ hτ σ hσ p hpG hF, isDenseOpen_localizeBelow hF⟩)
    (fun τ hτ σ hσ ↦ hG _ ⟨hveq τ hτ σ hσ, isDenseOpen_eqDecision τ σ⟩)

/-!
### Sanity examples

The universal family is subname-closed, and the material name family will be the intended
instance (via `elems_mem_names`, not consumed here).
-/

example : SubnameClosed (Set.univ : Set (PName P)) :=
  fun _ _ _ ↦ trivial

end Forcing
