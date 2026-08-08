/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.FormulaForcing

/-!
# The homogeneity shadow, at one formula

The first **shadow** in the sense of `docs/base-theories-and-shadows.md`: a theorem-local
structural interface, stated for *one* formula and one parameter assignment, of which the
classical weak homogeneity is the universal envelope
(`WeaklyHomogeneousFor` — only a wrapper, never the primitive).

The package is exactly the components the argument consumes: an external action on conditions
and names, preservation of the selected family, fixed parameters, equivariance for this
formula, and orbit compatibility of deciding conditions — together with density of deciders,
supplied separately since it is a hypothesis about the order rather than about the symmetry.

The payoff is **condition-local**, deliberately avoiding `[OrderTop P]`: if any condition
forces the formula, then *every* condition does (`forcesFormula_of_exists`), because the
deciders are dense and no decider can force the negation. With a top condition this
specializes to the familiar "the top condition decides"
(`forcesFormula_top_of_exists`).

Scope: external and typed throughout — no material imports, no typeclasses, and no general
automorphism framework. `Symmetry` is a record of the data the theorem consumes, nothing
more. In particular this file cannot influence the material-ground interface, which is the
point of running it in parallel.

## Main definitions

* `Forcing.Symmetry`: the action data a symmetry supplies.
* `Forcing.Decides`: the deciders of a formula.
* `Forcing.HomogeneousFor`: the shadow.

## Main results

* `Forcing.incompatible_of_forces_of_forces_not`: forcing and forcing the negation are
  incompatible.
* `Forcing.HomogeneousFor.forcesFormula_of_exists`: the condition-local payoff.
-/

universe u v

namespace Forcing

open FirstOrder PName

variable {P : Type u} [Preorder P] {β : Type v} {𝒩 : Set (PName P)} {v : β → PName P}
variable {p q : P} {n : ℕ} {φ : memLang.BoundedFormula β n} {xs : Fin n → PName P}

/-- The data of a symmetry: an action on conditions together with one on names. Deliberately
not a framework — exactly what the shadow consumes. -/
structure Symmetry (P : Type u) where
  /-- The action on conditions. -/
  cond : P → P
  /-- The action on names. -/
  name : PName P → PName P

variable {H : Set (Symmetry P)}

/-- `p` **decides** `φ`: it forces the formula or forces its negation. -/
def Decides (𝒩 : Set (PName P)) (v : β → PName P) (p : P)
    (φ : memLang.BoundedFormula β n) (xs : Fin n → PName P) : Prop :=
  ForcesFormula 𝒩 v p φ xs ∨ ForcesFormula 𝒩 v p (∼φ) xs

/-- Forcing a formula and forcing its negation are **incompatible**: a common strengthening
would force falsum. The engine of the homogeneity argument, and pure order theory. -/
theorem incompatible_of_forces_of_forces_not (hp : ForcesFormula 𝒩 v p φ xs)
    (hq : ForcesFormula 𝒩 v q (∼φ) xs) : Incompatible p q := by
  rintro ⟨r, hrp, hrq⟩
  exact hq r hrq (ForcesFormula.mono φ hp hrp)

/-- **The homogeneity shadow at one formula**: the local interface of which classical weak
homogeneity is the universal envelope. Equivariance is a component, not a consequence —
proving it requires the action to commute with valuation, which is out of scope here. -/
structure HomogeneousFor (𝒩 : Set (PName P)) (v : β → PName P)
    (φ : memLang.BoundedFormula β n) (xs : Fin n → PName P) (H : Set (Symmetry P)) : Prop where
  /-- The selected name family is preserved. -/
  family_preserved : ∀ π ∈ H, ∀ τ ∈ 𝒩, π.name τ ∈ 𝒩
  /-- The parameters are fixed. -/
  params_fixed : ∀ π ∈ H, (∀ b, π.name (v b) = v b) ∧ ∀ i, π.name (xs i) = xs i
  /-- Equivariance **for this formula**: the action preserves forcing it. -/
  equivariant : ∀ π ∈ H, ∀ r : P, ForcesFormula 𝒩 v r φ xs →
    ForcesFormula 𝒩 v (π.cond r) φ xs
  /-- Orbit compatibility: deciding conditions can be moved to compatibility. -/
  orbit_compatible : ∀ r s : P, Decides 𝒩 v r φ xs → Decides 𝒩 v s φ xs →
    ∃ π ∈ H, Compatible (π.cond r) s

namespace HomogeneousFor

/-- Under the shadow, no condition forces the negation once some condition forces the
formula: the symmetry moves the forcer into compatibility with the refuter, and forcing
against forcing-the-negation is incompatible. -/
theorem not_forcesFormula_not (h : HomogeneousFor 𝒩 v φ xs H)
    (hp : ForcesFormula 𝒩 v p φ xs) (q : P) : ¬ForcesFormula 𝒩 v q (∼φ) xs := by
  intro hq
  obtain ⟨π, hπ, hcompat⟩ := h.orbit_compatible p q (Or.inl hp) (Or.inr hq)
  exact incompatible_of_forces_of_forces_not (h.equivariant π hπ p hp) hq hcompat

/-- **The condition-local payoff**: if any condition forces the formula, every condition
does. Deciders are dense, no decider can force the negation, so the forcers are dense below
every condition — and density-regularity closes it. No `[OrderTop P]` is used. -/
theorem forcesFormula_of_exists (h : HomogeneousFor 𝒩 v φ xs H)
    (hdense : IsDense {r | Decides 𝒩 v r φ xs}) (hp : ForcesFormula 𝒩 v p φ xs) (q : P) :
    ForcesFormula 𝒩 v q φ xs := by
  refine forcesFormula_of_isDenseBelow φ fun r hr ↦ ?_
  obtain ⟨s, hsD, hsr⟩ := hdense r
  rcases hsD with hs | hs
  · exact ⟨s, hs, hsr⟩
  · exact absurd hs (h.not_forcesFormula_not hp s)

/-- The familiar form when a weakest condition exists: the top condition forces. -/
theorem forcesFormula_top_of_exists [OrderTop P] (h : HomogeneousFor 𝒩 v φ xs H)
    (hdense : IsDense {r | Decides 𝒩 v r φ xs}) (hp : ForcesFormula 𝒩 v p φ xs) :
    ForcesFormula 𝒩 v ⊤ φ xs :=
  h.forcesFormula_of_exists hdense hp ⊤

end HomogeneousFor

/-- Classical weak homogeneity, **only as the universal envelope** of the shadow: the local
package, quantified over formulas and parameter assignments. -/
def WeaklyHomogeneousFor (𝒩 : Set (PName P)) (H : Set (Symmetry P)) : Prop :=
  ∀ {β : Type v} (v : β → PName P) {n : ℕ} (φ : memLang.BoundedFormula β n)
    (xs : Fin n → PName P), HomogeneousFor 𝒩 v φ xs H

theorem WeaklyHomogeneousFor.homogeneousFor (h : WeaklyHomogeneousFor.{u, v} 𝒩 H)
    (v : β → PName P) (φ : memLang.BoundedFormula β n) (xs : Fin n → PName P) :
    HomogeneousFor 𝒩 v φ xs H :=
  h v φ xs

/-!
### Sanity example

The shadow is genuinely local: it constrains one formula with one assignment, and the
envelope is obtained only by quantifying — never the other way round.
-/

example (h : WeaklyHomogeneousFor.{u, v} 𝒩 H)
    (hdense : IsDense {r | Decides 𝒩 v r φ xs})
    (hp : ForcesFormula 𝒩 v p φ xs) (q : P) : ForcesFormula 𝒩 v q φ xs :=
  (h.homogeneousFor v φ xs).forcesFormula_of_exists hdense hp q

end Forcing
