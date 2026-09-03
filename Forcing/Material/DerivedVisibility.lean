/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.ForcingPresentation
import Forcing.Model.Visibility

/-!
# The derived visibility context

What an internal forcing presentation can *see*: exactly the externalizations of its internal
subsets. Derived from the presentation, never stored — the observer vocabulary is a projection
of the material data, so no visibility obligation is ever assumed.

This is the general form of the context the Cohen material adapter has used since M5
(`CohenMaterialPresentation.derivedContext`), which is now defined by extending this one with its
designated reals; its visibility and countability facts are specializations of the ones here.

## Main definitions

* `Forcing.InternalForcingPresentation.derivedContext`: the derived context.

## Main results

* `Forcing.InternalForcingPresentation.visible_derivedContext_iff`: visibility is internal-subset
  externalization, definitionally.
* `Forcing.InternalForcingPresentation.countable_visibleDenseOpen_derivedContext`: external
  countability of the carrier bounds the visible dense-open family — the hypothesis
  Rasiowa–Sikorski existence consumes.
-/

universe u

namespace Forcing.InternalForcingPresentation

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- **The derived visibility context**: visible sets are exactly the externalizations of
internal subsets. -/
def derivedContext : VisibilityContext P where
  visible := Set.range fun d : Pres.InternalSubset ↦ d.externalize

/-- Visibility in the derived context is exactly internal-subset externalization. -/
theorem visible_derivedContext_iff {D : Set P} :
    Pres.derivedContext.Visible D ↔ ∃ d : Pres.InternalSubset, d.externalize = D :=
  Iff.rfl

/-- Stage one of countability: a countable carrier admits only countably many visible sets,
since every visible set is the externalization of a carrier element. -/
theorem countable_visible_derivedContext (hM : (M : Set ZFSet.{u}).Countable) :
    Pres.derivedContext.visible.Countable := by
  refine Set.Countable.mono ?_ (hM.image Pres.externalizeSubset)
  rintro D ⟨d, rfl⟩
  exact ⟨(d.1 : ZFSet.{u}), d.1.2, rfl⟩

/-- Stage two: the visible dense-open family is countable. -/
theorem countable_visibleDenseOpen_derivedContext (hM : (M : Set ZFSet.{u}).Countable) :
    Pres.derivedContext.visibleDenseOpen.Countable :=
  (Pres.countable_visible_derivedContext hM).mono (Set.sep_subset _ _)

end Forcing.InternalForcingPresentation
