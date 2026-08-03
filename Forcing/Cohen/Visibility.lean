/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Diagonal
import Forcing.Model.Requirement

/-!
# The Cohen visibility context and its obligations

A `CohenVisibilityContext` is a visibility context over Cohen conditions together with its
designated reals. The name says *context*: this is the deliberately abstract interface,
not a model — the reals are designated, not derived, and no claim is made that they are the
reals of anything.

`Sees` states the visibility obligations of the avoidance argument: every coordinate requirement
is visible, and — the **M3 bridge** — the diagonal requirement of every designated real
is visible. The abstract context *exposes* these obligations as an explicit hypothesis; a later
material ground model must *prove* them. They are deliberately not baked into `GenericOver`,
and the separating test `oddTrue` is deliberately not among them: the spectrum theorem consumes
a visibility budget incomparable with the avoidance theorem's, so its obligation stays separate.

Downstream statements use the forwarding projections (`Visible`, `visibleDenseOpen`,
`GenericOver`) and never write `M.toVisibilityContext`.

## Main definitions

* `Forcing.Cohen.CohenVisibilityContext`: a visibility context over `Cond` with designated
  reals.
* `Forcing.Cohen.CohenVisibilityContext.Sees`: the visibility obligations of the avoidance argument.

## Main results

* `Forcing.Cohen.CohenVisibilityContext.Sees.meets_coordReq`,
  `Forcing.Cohen.CohenVisibilityContext.Sees.meets_diagReq`: a filter generic over a context that
  meets its obligations meets every coordinate requirement and every diagonal requirement
  against the designated reals — the bridge lemmas the avoidance theorem consumes.
* `Forcing.Cohen.CohenVisibilityContext.sees_full`: the full context satisfies the obligations for
  any choice of designated reals.
-/

namespace Forcing.Cohen

open Order

/-- A visibility context over Cohen conditions together with its designated reals. The name
says *context*: this is the deliberately abstract interface, not a model — the reals are
designated, not derived, and no claim is made that they are the reals of anything. The two
fields are different in kind, deliberately: `visible` is a vocabulary of *tests*, `designatedReals`
a designated vocabulary of *objects* — the pairing a material ground will later derive from one
carrier rather than supply as independent data. -/
@[ext] structure CohenVisibilityContext extends VisibilityContext Cond where
  /-- The designated reals: the family the avoidance theorem concludes against. -/
  designatedReals : Set (ℕ → Bool)

namespace CohenVisibilityContext

variable {M : CohenVisibilityContext} {G : PFilter Cond} {D : Set Cond}

/-- Forwarding projection: `M` can see the set of conditions `D`. -/
abbrev Visible (M : CohenVisibilityContext) (D : Set Cond) : Prop :=
  M.toVisibilityContext.Visible D

/-- Forwarding projection: the visible dense-open family of the underlying context. -/
abbrev visibleDenseOpen (M : CohenVisibilityContext) : Set (Set Cond) :=
  M.toVisibilityContext.visibleDenseOpen

/-- Forwarding projection: genericity over the underlying context. -/
abbrev GenericOver (M : CohenVisibilityContext) (G : PFilter Cond) : Prop :=
  Forcing.GenericOver M.toVisibilityContext G

/-- The visibility obligations of the Cohen avoidance argument, bundled as a `Prop` so theorems
can take them as one explicit hypothesis. `visible_diagReq` is the **M3 bridge**
`x ∈ M.designatedReals → Visible M ((diagReq x).support)`: the abstract context exposes it, and a
later material ground model must prove it. -/
structure Sees (M : CohenVisibilityContext) : Prop where
  /-- Every coordinate requirement is visible. -/
  visible_coordReq : ∀ n, M.Visible (coordReq n).support
  /-- The M3 bridge: the diagonal requirement of every designated real is visible. -/
  visible_diagReq : ∀ x ∈ M.designatedReals, M.Visible (diagReq x).support

/-- Under the obligations, each coordinate requirement is a visible dense-open test. A thin
specialization of the generic bridge `Requirement.mem_visibleDenseOpen`. -/
theorem Sees.coordReq_mem_visibleDenseOpen (hM : M.Sees) (n : ℕ) :
    (coordReq n).support ∈ M.visibleDenseOpen :=
  (coordReq n).mem_visibleDenseOpen (hM.visible_coordReq n)

/-- Under the bridge, the diagonal requirement of each designated real is a visible dense-open
test. A thin specialization of the generic bridge `Requirement.mem_visibleDenseOpen`. -/
theorem Sees.diagReq_mem_visibleDenseOpen (hM : M.Sees) {x : ℕ → Bool}
    (hx : x ∈ M.designatedReals) :
    (diagReq x).support ∈ M.visibleDenseOpen :=
  (diagReq x).mem_visibleDenseOpen (hM.visible_diagReq x hx)

/-- A filter generic over `M` meets every coordinate requirement. A thin specialization of the
generic `GenericOver.meets_requirement`. -/
theorem Sees.meets_coordReq (hM : M.Sees) (hG : M.GenericOver G) (n : ℕ) :
    Meets G (coordReq n).support :=
  hG.meets_requirement (hM.visible_coordReq n)

/-- A filter generic over `M` meets the diagonal requirement of every designated real. A thin
specialization of the generic `GenericOver.meets_requirement`. -/
theorem Sees.meets_diagReq (hM : M.Sees) (hG : M.GenericOver G) {x : ℕ → Bool}
    (hx : x ∈ M.designatedReals) :
    Meets G (diagReq x).support :=
  hG.meets_requirement (hM.visible_diagReq x hx)

/-- The full Cohen context: sees everything, over any designated reals. -/
def full (R : Set (ℕ → Bool)) : CohenVisibilityContext :=
  ⟨VisibilityContext.full Cond, R⟩

/-- The full context satisfies the visibility obligations for any choice of designated reals. -/
theorem sees_full (R : Set (ℕ → Bool)) : (full R).Sees :=
  ⟨fun _ ↦ VisibilityContext.visible_full, fun _ _ ↦ VisibilityContext.visible_full⟩

/-!
### Sanity examples

The forwarding projections are definitionally the underlying notions, so no downstream
statement needs `M.toVisibilityContext`; and the obligations do not mention `oddTrue`, whose
visibility is a separate hypothesis of the spectrum theorem.
-/

example : M.GenericOver G ↔ Forcing.GenericOver M.toVisibilityContext G :=
  .rfl

example : M.Visible D ↔ M.toVisibilityContext.Visible D :=
  .rfl

example (hM : M.Sees) (hG : M.GenericOver G) (n : ℕ) : Meets G (coordReq n).support :=
  hM.meets_coordReq hG n

end CohenVisibilityContext

end Forcing.Cohen
