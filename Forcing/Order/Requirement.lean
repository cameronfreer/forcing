/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Order.Filter

/-!
# Requirements: a presentation layer for genericity

Dense sets can look like an inspired combinatorial trick. They are not: they are exactly the
*requirements* one can impose on an object built by finite approximation. A requirement is a
task on conditions that is

* **persistent** — once achieved, acquiring more information cannot destroy it; and
* **attainable** — from any current state it can still be achieved.

`Requirement.equivDenseOpen` proves that requirements in this sense are precisely the dense open
sets, so nothing is lost by explaining genericity through requirements rather than announcing
density. And `meets_lowerClosure` (restated here as `meets_normalize_iff`) shows that
restricting attention to *persistent* tasks costs nothing either: every dense test has a
canonical persistent form — its downward closure — which the same filters meet.

This file is presentation only. There is deliberately **no** second genericity predicate:
genericity for a family of requirements is `GenericFor` applied to the family of supports.

## Main definitions

* `Forcing.Requirement P`: a persistent, locally attainable task on conditions.
* `Forcing.Requirement.support`: the set of conditions meeting the requirement.
* `Forcing.Requirement.ofDenseOpen`, `Forcing.Requirement.equivDenseOpen`: requirements are
  exactly the dense open sets.
* `Forcing.Requirement.normalize`: the canonical persistent form of an arbitrary dense set.

## Main results

* `Forcing.Requirement.equivDenseOpen`: the presentation is faithful.
* `Forcing.meets_normalize_iff`: a filter meets a dense set iff it meets its canonical
  persistent form — so the restriction to requirements loses no genericity.
* `Forcing.genericFor_support_iff`: genericity for requirements is `GenericFor` of the supports
  — obtained directly, by unpacking `Set.range`.
-/

namespace Forcing

variable {P : Type*} [Preorder P] {D : Set P} {G : Order.PFilter P}

/-- A *requirement* on conditions: a task that, once achieved, survives further information
(`persistent`), and that can always still be achieved from any condition (`attainable`).

These are exactly the dense open sets (`Requirement.equivDenseOpen`); the point of the packaging
is that persistence and attainability are the properties one actually wants when building an
object by finite approximation, whereas "dense" and "open" are their names after the fact. -/
structure Requirement (P : Type*) [Preorder P] where
  /-- The task: which conditions have achieved it. -/
  holds : P → Prop
  /-- Achieving the task survives strengthening. -/
  persistent : ∀ ⦃q p⦄, q ≤ p → holds p → holds q
  /-- The task can always still be achieved. -/
  attainable : ∀ p, ∃ q ≤ p, holds q

namespace Requirement

variable (R : Requirement P)

/-- The set of conditions that have achieved the requirement. -/
def support : Set P :=
  {p | R.holds p}

@[simp] theorem mem_support {p : P} : p ∈ R.support ↔ R.holds p :=
  .rfl

theorem isLowerSet_support : IsLowerSet R.support :=
  fun _ _ hba ha ↦ R.persistent hba ha

theorem isDense_support : IsDense R.support :=
  fun p ↦ let ⟨q, hqp, hq⟩ := R.attainable p; ⟨q, hq, hqp⟩

/-- The support of a requirement is dense open. -/
theorem isDenseOpen_support : IsDenseOpen R.support :=
  ⟨R.isDense_support, R.isLowerSet_support⟩

/-- Conversely, a dense open set is a requirement. -/
def ofDenseOpen (D : Set P) (hD : IsDenseOpen D) : Requirement P where
  holds p := p ∈ D
  persistent _ _ hba ha := hD.2 hba ha
  attainable p := let ⟨q, hqD, hqp⟩ := hD.1 p; ⟨q, hqp, hqD⟩

@[simp] theorem support_ofDenseOpen (hD : IsDenseOpen D) : (ofDenseOpen D hD).support = D :=
  rfl

/-- **Requirements are exactly the dense open sets.** Persistence and attainability — the
properties one wants when constructing an object by finite approximation — carve out precisely
the sets that forcing calls dense open. -/
def equivDenseOpen : Requirement P ≃ {D : Set P // IsDenseOpen D} where
  toFun R := ⟨R.support, R.isDenseOpen_support⟩
  invFun D := ofDenseOpen D.1 D.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical persistent form of an arbitrary dense set: its downward closure. -/
def normalize (D : Set P) (hD : IsDense D) : Requirement P :=
  ofDenseOpen (↑(lowerClosure D)) hD.isDenseOpen_lowerClosure

@[simp] theorem support_normalize (hD : IsDense D) :
    (normalize D hD).support = ↑(lowerClosure D) :=
  rfl

end Requirement

/-- **Normalization loses no genericity**: a filter meets a dense test exactly when it meets the
test's canonical persistent form. So insisting that requirements be persistent — as the
`Requirement` packaging does — costs nothing. -/
theorem meets_normalize_iff (hD : IsDense D) :
    Meets G (Requirement.normalize D hD).support ↔ Meets G D :=
  meets_lowerClosure

/-- Genericity for a family of requirements is `GenericFor` of the family of supports. This is
immediate — though not literally definitional, since `Set.range` must be unpacked — and it is
the only genericity statement about requirements: no competing predicate is introduced. -/
theorem genericFor_support_iff {ι : Type*} {ℛ : ι → Requirement P} :
    GenericFor (Set.range fun i ↦ (ℛ i).support) G ↔ ∀ i, Meets G (ℛ i).support := by
  constructor
  · exact fun h i ↦ h _ ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    exact h i

/-!
### Sanity examples

The trivial requirement is achieved by everything; and a requirement obtained by normalizing a
dense set is met by exactly the filters meeting the original set.
-/

example : Requirement P where
  holds _ := True
  persistent _ _ _ _ := trivial
  attainable p := ⟨p, le_rfl, trivial⟩

example (hD : IsDense D) (h : Meets G D) : Meets G (Requirement.normalize D hD).support :=
  (meets_normalize_iff hD).2 h

end Forcing
