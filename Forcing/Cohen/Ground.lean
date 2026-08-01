/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Diagonal
import Forcing.Model.GenericOver

/-!
# The Cohen ground context and its visibility obligations

A `CohenGroundContext` is a ground/visibility context over Cohen conditions together with its
designated ground reals. The name says *context*: this is the deliberately abstract interface,
not a model — the reals are designated, not derived, and no claim is made that they are the
reals of anything.

`Sees` states the visibility obligations of the new-real argument: every coordinate requirement
is visible, and — the **M3 bridge** — the diagonal requirement of every designated ground real
is visible. The abstract context *exposes* these obligations as an explicit hypothesis; a later
material ground model must *prove* them. They are deliberately not baked into `GenericOver`,
and the separating test `oddTrue` is deliberately not among them: the spectrum theorem consumes
a visibility budget incomparable with the new-real theorem's, so its obligation stays separate.

Downstream statements use the forwarding projections (`Visible`, `visibleDenseOpen`,
`GenericOver`) and never write `M.toGroundContext`.

## Main definitions

* `Forcing.Cohen.CohenGroundContext`: a ground context over `Cond` with designated ground
  reals.
* `Forcing.Cohen.CohenGroundContext.Sees`: the visibility obligations of the new-real argument.

## Main results

* `Forcing.Cohen.CohenGroundContext.Sees.meets_coordReq`,
  `Forcing.Cohen.CohenGroundContext.Sees.meets_diagReq`: a filter generic over a context that
  meets its obligations meets every coordinate requirement and every diagonal requirement
  against the ground reals — the bridge lemmas the new-real theorem consumes.
* `Forcing.Cohen.CohenGroundContext.sees_full`: the full context satisfies the obligations for
  any choice of ground reals.
-/

namespace Forcing.Cohen

open Order

/-- A ground context over Cohen conditions together with its designated ground reals. The name
says *context*: this is the deliberately abstract interface, not a model — the reals are
designated, not derived, and no claim is made that they are the reals of anything. -/
@[ext] structure CohenGroundContext extends GroundContext Cond where
  /-- The designated ground reals: the family the new-real theorem concludes against. -/
  groundReals : Set (ℕ → Bool)

namespace CohenGroundContext

variable {M : CohenGroundContext} {G : PFilter Cond} {D : Set Cond}

/-- Forwarding projection: `M` can see the set of conditions `D`. -/
abbrev Visible (M : CohenGroundContext) (D : Set Cond) : Prop :=
  M.toGroundContext.Visible D

/-- Forwarding projection: the visible dense-open family of the underlying context. -/
abbrev visibleDenseOpen (M : CohenGroundContext) : Set (Set Cond) :=
  M.toGroundContext.visibleDenseOpen

/-- Forwarding projection: genericity over the underlying context. -/
abbrev GenericOver (M : CohenGroundContext) (G : PFilter Cond) : Prop :=
  Forcing.GenericOver M.toGroundContext G

/-- The visibility obligations of the Cohen new-real argument, bundled as a `Prop` so theorems
can take them as one explicit hypothesis. `visible_diagReq` is the **M3 bridge**
`x ∈ M.groundReals → Visible M ((diagReq x).support)`: the abstract context exposes it, and a
later material ground model must prove it. -/
structure Sees (M : CohenGroundContext) : Prop where
  /-- Every coordinate requirement is visible. -/
  visible_coordReq : ∀ n, M.Visible (coordReq n).support
  /-- The M3 bridge: the diagonal requirement of every designated ground real is visible. -/
  visible_diagReq : ∀ x ∈ M.groundReals, M.Visible (diagReq x).support

/-- Under the obligations, each coordinate requirement is a visible dense-open test. -/
theorem Sees.coordReq_mem_visibleDenseOpen (hM : M.Sees) (n : ℕ) :
    (coordReq n).support ∈ M.visibleDenseOpen :=
  ⟨hM.visible_coordReq n, (coordReq n).isDenseOpen_support⟩

/-- Under the bridge, the diagonal requirement of each ground real is a visible dense-open
test. -/
theorem Sees.diagReq_mem_visibleDenseOpen (hM : M.Sees) {x : ℕ → Bool}
    (hx : x ∈ M.groundReals) :
    (diagReq x).support ∈ M.visibleDenseOpen :=
  ⟨hM.visible_diagReq x hx, (diagReq x).isDenseOpen_support⟩

/-- A filter generic over `M` meets every coordinate requirement. -/
theorem Sees.meets_coordReq (hM : M.Sees) (hG : M.GenericOver G) (n : ℕ) :
    Meets G (coordReq n).support :=
  hG _ (hM.coordReq_mem_visibleDenseOpen n)

/-- A filter generic over `M` meets the diagonal requirement of every ground real. -/
theorem Sees.meets_diagReq (hM : M.Sees) (hG : M.GenericOver G) {x : ℕ → Bool}
    (hx : x ∈ M.groundReals) :
    Meets G (diagReq x).support :=
  hG _ (hM.diagReq_mem_visibleDenseOpen hx)

/-- The full Cohen context: sees everything, over any designated ground reals. -/
def full (R : Set (ℕ → Bool)) : CohenGroundContext :=
  ⟨GroundContext.full Cond, R⟩

/-- The full context satisfies the visibility obligations for any choice of ground reals. -/
theorem sees_full (R : Set (ℕ → Bool)) : (full R).Sees :=
  ⟨fun _ ↦ GroundContext.visible_full, fun _ _ ↦ GroundContext.visible_full⟩

/-!
### Sanity examples

The forwarding projections are definitionally the underlying notions, so no downstream
statement needs `M.toGroundContext`; and the obligations do not mention `oddTrue`, whose
visibility is a separate hypothesis of the spectrum theorem.
-/

example : M.GenericOver G ↔ Forcing.GenericOver M.toGroundContext G :=
  .rfl

example : M.Visible D ↔ M.toGroundContext.Visible D :=
  .rfl

example (hM : M.Sees) (hG : M.GenericOver G) (n : ℕ) : Meets G (coordReq n).support :=
  hM.meets_coordReq hG n

end CohenGroundContext

end Forcing.Cohen
