/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Model.Visibility
import Forcing.Order.RasiowaSikorski

/-!
# Genericity over a visibility context

`GenericOver M G` says the filter `G` meets every dense-open test visible to the context `M`.
By definition it is `GenericFor` of the visible dense-open family: model-relative genericity is
not a new notion, it is family-relative genericity at a family determined by the observer.

Existence comes from **external** countability of the visible family via Rasiowa–Sikorski.
Countability is a hypothesis of the existence statement, never a field of the context, and
adequacy statements never mention it.

The last two results record where the ground model's closure properties first matter: meeting
every visible *dense* set implies genericity outright (`genericOver_of_forall_isDense`), but it
is a priori the stronger demand — the converse requires the persistent form of each visible
test to be visible, i.e. the visible family closed under downward closure, stated as an
explicit hypothesis and deliberately not a field of `VisibilityContext`.

## Main definitions

* `Forcing.GenericOver M G`: `G` meets every visible dense-open test.

## Main results

* `Forcing.exists_pfilter_genericOver`: existence through any condition, from external
  countability of the visible dense-open family.
* `Forcing.GenericOver.anti`: an observer that sees more demands more.
* `Forcing.genericOver_full_iff`: over the full context, genericity is genericity for every
  dense open set.
* `Forcing.genericOver_iff_forall_isDense`: with visibility closed under downward closure,
  genericity over `M` is equivalent to meeting every visible dense set.
-/

namespace Forcing

open Order VisibilityContext

variable {P : Type*} [Preorder P] {M M' : VisibilityContext P} {G : PFilter P}

/-- Genericity over a visibility context: meeting every visible dense-open test. By definition this
is `GenericFor` of the visible dense-open family — no new predicate machinery. -/
def GenericOver (M : VisibilityContext P) (G : PFilter P) : Prop :=
  GenericFor M.visibleDenseOpen G

theorem genericOver_iff :
    GenericOver M G ↔ ∀ D, M.Visible D → IsDenseOpen D → Meets G D :=
  ⟨fun h D hD hDO ↦ h D ⟨hD, hDO⟩, fun h D hD ↦ h D hD.1 hD.2⟩

/-- **Existence** through any condition, from **external** countability of the visible
dense-open family (Rasiowa–Sikorski). Countability is a hypothesis here, never a field of the
context, and the adequacy statements built on `GenericOver` never mention it. -/
theorem exists_pfilter_genericOver (p : P) (h : M.visibleDenseOpen.Countable) :
    ∃ G : PFilter P, p ∈ G ∧ GenericOver M G :=
  exists_pfilter_genericFor' p h fun _ hD ↦ hD.2.1

/-- Seeing more means owing more: genericity over a larger observer implies genericity over a
smaller one. -/
theorem GenericOver.anti (h : GenericOver M' G) (hMM' : M.visible ⊆ M'.visible) :
    GenericOver M G :=
  GenericFor.anti h (visibleDenseOpen_mono hMM')

/-- Over the empty context every filter is generic. -/
@[simp] theorem genericOver_empty : GenericOver (empty P) G :=
  fun _ hD ↦ absurd hD.1 not_visible_empty

/-- Over the full context, genericity is genericity for every dense open test — the family the
exposition calls `J_full`. -/
theorem genericOver_full_iff :
    GenericOver (full P) G ↔ GenericFor {D | IsDenseOpen D} G :=
  (congrArg (GenericFor · G) visibleDenseOpen_full).to_iff

/-- Meeting every visible dense set implies genericity, with no closure hypothesis: a visible
dense-open test is in particular a visible dense set. -/
theorem genericOver_of_forall_isDense
    (h : ∀ D, M.Visible D → IsDense D → Meets G D) :
    GenericOver M G :=
  fun D hD ↦ h D hD.1 hD.2.1

/-- Where the ground model's closure properties first matter: if the visible family is closed
under downward closure, genericity over `M` is equivalent to meeting every visible *dense* set.
The reverse implication needs no closure (`genericOver_of_forall_isDense`); it is the forward
one — a generic filter meets every visible dense set — that requires the persistent form of
each visible test to be visible. The closure is an explicit hypothesis, deliberately not a
field of `VisibilityContext`. -/
theorem genericOver_iff_forall_isDense
    (hM : ∀ D, M.Visible D → M.Visible ↑(lowerClosure D)) :
    GenericOver M G ↔ ∀ D, M.Visible D → IsDense D → Meets G D :=
  ⟨fun h D hD hdense ↦
    meets_lowerClosure.1 (h _ ⟨hM D hD, hdense.isDenseOpen_lowerClosure⟩),
    genericOver_of_forall_isDense⟩

/-!
### Sanity examples

Genericity over any context follows from genericity over the full context; and over the empty
context, existence is trivial — through any condition, any filter at all is generic, so the
principal filter witnesses it.
-/

example (h : GenericOver (full P) G) : GenericOver M G :=
  h.anti (Set.subset_univ _)

example (p : P) : ∃ G : PFilter P, p ∈ G ∧ GenericOver (empty P) G :=
  ⟨PFilter.principal p, PFilter.mem_principal.2 le_rfl, genericOver_empty⟩

end Forcing
