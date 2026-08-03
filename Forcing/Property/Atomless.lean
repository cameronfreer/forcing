/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Model.GenericOver

/-!
# Atomlessness: branching, and the visibility refutation of genericity

The first module of the external property kernel (the *vertical* track of
`docs/property-zoo.md`). `IsAtomless` says every condition leaves at least two incompatible
possible futures. Scope: **external**, on the raw preorder; the presentation-independent form
lives on the separative quotient and is deferred.

The payoff is the correct abstract version of "an atomless forcing adds a new generic", as a
pair with the roles kept apart:

* **branching**: over an atomless order, the complement of every forcing filter is a
  dense-open test (`isDenseOpen_compl_pfilter`) — density from splitting plus directedness,
  openness because the complement of an up-set is a lower set;
* **observer-relativity**: a filter cannot be generic over any observer that can see its
  complement (`not_genericOver_of_visible_compl`).

Branching alone produces no newness; visibility turns it into a refutation. No semantic
preservation claims are made anywhere in this file.

## Main definitions

* `Forcing.IsAtomless`: every condition splits into two incompatible strengthenings.

## Main results

* `Forcing.isDenseOpen_compl_pfilter`: the complement of a forcing filter is dense open.
* `Forcing.not_genericOver_of_visible_compl`: no observer that sees the complement admits
  the filter as generic.
-/

namespace Forcing

open Order

variable {P : Type*} [Preorder P] {G : PFilter P}

/-- Every condition splits: it has two incompatible strengthenings. External and stated on
the raw preorder; the presentation-independent form belongs to the separative quotient. -/
def IsAtomless (P : Type*) [Preorder P] : Prop :=
  ∀ p : P, ∃ q r, q ≤ p ∧ r ≤ p ∧ Incompatible q r

/-- **Branching**: over an atomless order, the complement of every forcing filter is a
dense-open test. Density: split below any `p ∈ G` — directedness forbids the filter from
containing both pieces. Openness: the complement of an up-set is a lower set. -/
theorem isDenseOpen_compl_pfilter (h : IsAtomless P) (G : PFilter P) :
    IsDenseOpen ((G : Set P)ᶜ) := by
  constructor
  · intro p
    by_cases hp : p ∈ G
    · obtain ⟨q, r, hqp, hrp, hqr⟩ := h p
      by_cases hq : q ∈ G
      · refine ⟨r, fun hr ↦ ?_, hrp⟩
        obtain ⟨s, hsG, hsq, hsr⟩ := exists_mem_le_le hq hr
        exact hqr ⟨s, hsq, hsr⟩
      · exact ⟨q, hq, hqp⟩
    · exact ⟨p, hp, le_rfl⟩
  · exact fun p q hqp hp hq ↦ hp (G.mem_of_le hqp hq)

/-- **The visibility refutation**: a filter cannot be generic over any observer that can see
its complement. Branching supplies the dense-open test; visibility makes it count; the filter
cannot meet its own complement. -/
theorem not_genericOver_of_visible_compl (h : IsAtomless P) {M : VisibilityContext P}
    (hvis : M.Visible ((G : Set P)ᶜ)) : ¬GenericOver M G := by
  intro hG
  obtain ⟨p, hpG, hpc⟩ := hG _ ⟨hvis, isDenseOpen_compl_pfilter h G⟩
  exact hpc hpG

/-!
### Sanity examples

A preorder with a least element is not atomless: every two conditions are compatible through
`⊥`. And over the full observer, the refutation applies to every filter of an atomless
order — the familiar "no filter is fully generic over an atomless forcing" as long as the
observer sees everything.
-/

example [OrderBot P] : ¬IsAtomless P := by
  intro h
  obtain ⟨q, r, -, -, hqr⟩ := h ⊥
  exact hqr ⟨⊥, bot_le, bot_le⟩

example (h : IsAtomless P) (G : PFilter P) :
    ¬GenericOver (VisibilityContext.full P) G :=
  not_genericOver_of_visible_compl h VisibilityContext.visible_full

end Forcing
