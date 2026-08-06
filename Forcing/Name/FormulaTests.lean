/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.FormulaForcing
import Forcing.Order.Filter

/-!
# The formula test families

The **constructor-specific** decision tests of the truth lemma, per the frozen item-7 design:
a uniform "forcers-plus-blockers of `φ`" set is deliberately avoided — its
obstruction-soundness would be circular at the current formula. Instead each connective gets
its own decision test, made globally dense open by density-regularity:

* a failed implication supplies a forced antecedent together with a consequent blocker
  (`impObstruction`, `impDecision`);
* a failed universal supplies a name and a blocker for that instance (`allObstruction`,
  `allDecision`).

The recursively required tests are packaged as an actual family (`formulaTests`): empty at
`falsum` and the atomics, the implication decision plus both subformula families, the
universal decision plus the body families for every `τ ∈ 𝒩`. Every member is dense open,
structurally (`isDenseOpen_of_mem_formulaTests`) — so an observer's only obligation toward
the truth lemma is *visibility* of the family; dense-openness is never a hypothesis.

## Main definitions

* `Forcing.impDecision`, `Forcing.allDecision`: the connective decision tests.
* `Forcing.formulaTests`: the packaged family.

## Main results

* `Forcing.exists_blocker_of_not_forcesFormula`: formula-level blocker extraction.
* `Forcing.isDenseOpen_impDecision`, `Forcing.isDenseOpen_allDecision`,
  `Forcing.isDenseOpen_of_mem_formulaTests`: dense-openness, structural.
-/

universe u v

namespace Forcing

open FirstOrder PName Order

variable {P : Type u} [Preorder P] {β : Type v} {𝒩 : Set (PName P)} {v : β → PName P}
variable {p q : P}

/-- Formula-level blocker extraction, from density-regularity: failure of forcing yields a
strengthening below which forcing is impossible. -/
theorem exists_blocker_of_not_forcesFormula {n} {φ : memLang.BoundedFormula β n}
    {xs : Fin n → PName P} (h : ¬ForcesFormula 𝒩 v p φ xs) :
    ∃ s ≤ p, ∀ t ≤ s, ¬ForcesFormula 𝒩 v t φ xs := by
  by_contra hcon
  push Not at hcon
  refine h (forcesFormula_of_isDenseBelow φ fun s hs ↦ ?_)
  obtain ⟨t, hts, htF⟩ := hcon s (Set.mem_Iic.1 hs)
  exact ⟨t, htF, hts⟩

/-- The implication obstruction: a forced antecedent together with a consequent blocker. -/
def impObstruction (𝒩 : Set (PName P)) (v : β → PName P) {n}
    (φ ψ : memLang.BoundedFormula β n) (xs : Fin n → PName P) : Set P :=
  {r | ForcesFormula 𝒩 v r φ xs ∧ ∀ q ≤ r, ¬ForcesFormula 𝒩 v q ψ xs}

/-- The implication decision test. -/
def impDecision (𝒩 : Set (PName P)) (v : β → PName P) {n}
    (φ ψ : memLang.BoundedFormula β n) (xs : Fin n → PName P) : Set P :=
  {p | ForcesFormula 𝒩 v p (φ.imp ψ) xs} ∪ impObstruction 𝒩 v φ ψ xs

/-- The universal obstruction: a name of the family together with a blocker for that
instance. -/
def allObstruction (𝒩 : Set (PName P)) (v : β → PName P) {n}
    (φ : memLang.BoundedFormula β (n + 1)) (xs : Fin n → PName P) : Set P :=
  {r | ∃ τ ∈ 𝒩, ∀ q ≤ r, ¬ForcesFormula 𝒩 v q φ (Fin.snoc xs τ)}

/-- The universal decision test. -/
def allDecision (𝒩 : Set (PName P)) (v : β → PName P) {n}
    (φ : memLang.BoundedFormula β (n + 1)) (xs : Fin n → PName P) : Set P :=
  {p | ForcesFormula 𝒩 v p φ.all xs} ∪ allObstruction 𝒩 v φ xs

/-- The implication decision test is globally dense open. -/
theorem isDenseOpen_impDecision {n} (φ ψ : memLang.BoundedFormula β n)
    (xs : Fin n → PName P) : IsDenseOpen (impDecision 𝒩 v φ ψ xs) := by
  constructor
  · intro r
    by_cases h : ForcesFormula 𝒩 v r (φ.imp ψ) xs
    · exact ⟨r, Or.inl h, le_rfl⟩
    · rw [forcesFormula_imp] at h
      push Not at h
      obtain ⟨q, hqr, hqφ, hqψ⟩ := h
      obtain ⟨s, hsq, hblock⟩ := exists_blocker_of_not_forcesFormula hqψ
      exact ⟨s, Or.inr ⟨ForcesFormula.mono φ hqφ hsq, hblock⟩, hsq.trans hqr⟩
  · refine IsLowerSet.union (fun a b hba h ↦ ForcesFormula.mono _ h hba) ?_
    rintro a b hba ⟨hφ, hblock⟩
    exact ⟨ForcesFormula.mono φ hφ hba, fun t htb ↦ hblock t (htb.trans hba)⟩

/-- The universal decision test is globally dense open. -/
theorem isDenseOpen_allDecision {n} (φ : memLang.BoundedFormula β (n + 1))
    (xs : Fin n → PName P) : IsDenseOpen (allDecision 𝒩 v φ xs) := by
  constructor
  · intro r
    by_cases h : ForcesFormula 𝒩 v r φ.all xs
    · exact ⟨r, Or.inl h, le_rfl⟩
    · rw [forcesFormula_all] at h
      push Not at h
      obtain ⟨τ, hτ, hτF⟩ := h
      obtain ⟨s, hsr, hblock⟩ := exists_blocker_of_not_forcesFormula hτF
      exact ⟨s, Or.inr ⟨τ, hτ, hblock⟩, hsr⟩
  · refine IsLowerSet.union (fun a b hba h ↦ ForcesFormula.mono _ h hba) ?_
    rintro a b hba ⟨τ, hτ, hblock⟩
    exact ⟨τ, hτ, fun t htb ↦ hblock t (htb.trans hba)⟩

/-- The packaged family of connective tests: empty at `falsum` and the atomics; the
implication decision plus both subformula families; the universal decision plus the body
families for every name of the family. -/
def formulaTests (𝒩 : Set (PName P)) (v : β → PName P) :
    ∀ {n}, memLang.BoundedFormula β n → (Fin n → PName P) → Set (Set P)
  | _, .falsum, _ => ∅
  | _, .equal _ _, _ => ∅
  | _, .rel _ _, _ => ∅
  | _, .imp φ ψ, xs =>
      insert (impDecision 𝒩 v φ ψ xs) (formulaTests 𝒩 v φ xs ∪ formulaTests 𝒩 v ψ xs)
  | _, .all φ, xs =>
      insert (allDecision 𝒩 v φ xs) (⋃ τ ∈ 𝒩, formulaTests 𝒩 v φ (Fin.snoc xs τ))

/-- Every member of the family is dense open — structurally, so the truth lemma's observer
owes only visibility. -/
theorem isDenseOpen_of_mem_formulaTests :
    ∀ {n} (φ : memLang.BoundedFormula β n) (xs : Fin n → PName P),
      ∀ D ∈ formulaTests 𝒩 v φ xs, IsDenseOpen D
  | _, .falsum, _, _, hD => absurd hD (Set.notMem_empty _)
  | _, .equal _ _, _, _, hD => absurd hD (Set.notMem_empty _)
  | _, .rel _ _, _, _, hD => absurd hD (Set.notMem_empty _)
  | _, .imp φ ψ, xs, D, hD => by
    rcases Set.mem_insert_iff.1 hD with rfl | hD
    · exact isDenseOpen_impDecision φ ψ xs
    · rcases hD with hD | hD
      · exact isDenseOpen_of_mem_formulaTests φ xs D hD
      · exact isDenseOpen_of_mem_formulaTests ψ xs D hD
  | _, .all φ, xs, D, hD => by
    rcases Set.mem_insert_iff.1 hD with rfl | hD
    · exact isDenseOpen_allDecision φ xs
    · obtain ⟨τ, hτ, hD⟩ := Set.mem_iUnion₂.1 hD
      exact isDenseOpen_of_mem_formulaTests φ (Fin.snoc xs τ) D hD

end Forcing
