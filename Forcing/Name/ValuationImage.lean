/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.GenName

/-!
# Selected-name valuation images

The valuation image of a **chosen family of names** over a condition set. The restriction to a
family is not bureaucracy — it is the entire point, and the failure of the unrestricted version
is certified rather than avoided: every ambient set has a check name, so along any condition
set containing `⊤` the image of *all* names is the whole universe
(`valuationImage_univ_eq_univ`). Restricting which names belong to the ground is what makes a
genuine extension possible.

This file is entirely model-independent: no `GenericOver`, no ground contexts, no composition
with genericity. That composition is the business of the material layer — the unique point
where external semantics becomes a material extension — and importing the model layer here
would reverse the intended dependency. Accordingly there is no `M[G]` here, no ZFC, no truth
lemma, and no minimality claim.

Membership is kept separate from faithfulness: placing the generic's name in the family costs
nothing (`zval_genName_mem_valuationImage` takes no `⊤ ∈ S`); the additional `⊤ ∈ S` is what
lets `mem_zval_genName_iff` identify that element as a faithful code.

## Main definitions

* `Forcing.valuationImage`: the valuation image of a name family over a condition set.

## Main results

* `Forcing.valuationImage_univ_eq_univ`: the certified collapse of the unrestricted image.
* `Forcing.mem_valuationImage_of_checkZF_mem`: the ground-copy boundary, `ZFSet` form.
* `Forcing.zval_genName_mem_valuationImage`: the generic's code lands in the image.
-/

universe u

namespace Forcing

open PName

variable {P : Type u} {N N' : Set (PName P)} {S : Set P} {τ : PName P}

/-- The valuation image of a chosen family of names over a condition set. Deliberately
parameterized by the family: the unrestricted image collapses
(`valuationImage_univ_eq_univ`). Filters enter only through coercion and corollaries. -/
def valuationImage (N : Set (PName P)) (S : Set P) : Set ZFSet.{u} :=
  zval S '' N

theorem mem_valuationImage (hn : τ ∈ N) : zval S τ ∈ valuationImage N S :=
  Set.mem_image_of_mem _ hn

/-- The image is monotone in the *family*. Contrast: valuation is **not** monotone in the
*condition set* (`exists_not_zval_subset_zval`). -/
theorem valuationImage_mono (h : N ⊆ N') : valuationImage N S ⊆ valuationImage N' S :=
  Set.image_mono h

/-- The ground-copy boundary, `ZFSet` form: a set whose check name belongs to the family lands
in the image with its identity intact. -/
theorem mem_valuationImage_of_checkZF_mem [Top P] (hS : (⊤ : P) ∈ S) {x : ZFSet.{u}}
    (hx : checkZF x ∈ N) :
    x ∈ valuationImage N S := by
  have h := mem_valuationImage (S := S) hx
  rwa [zval_checkZF hS] at h

/-- The ground-copy boundary, `PSet` form. -/
theorem mk_mem_valuationImage_of_check_mem [Top P] (hS : (⊤ : P) ∈ S) {x : PSet.{u}}
    (hx : check x ∈ N) :
    ZFSet.mk x ∈ valuationImage N S := by
  have h := mem_valuationImage (S := S) hx
  rwa [zval_check hS] at h

/-- The generic's code lands in the image — under only the explicit hypothesis that its name
belongs to the family. **No `⊤ ∈ S`**: membership in the image is separate from faithfulness,
which is what the additional `⊤ ∈ S` buys via `mem_zval_genName_iff`. -/
theorem zval_genName_mem_valuationImage [Top P] {κ : ConditionCode P}
    (hg : genName κ ∈ N) :
    zval S (genName κ) ∈ valuationImage N S :=
  mem_valuationImage hg

/-- **The failed construction, certified.** Allowing every name makes the valuation image the
entire ambient universe, along any condition set containing `⊤`: every set has a check name.
Restricting which names belong to the ground is what makes a genuine extension possible. -/
theorem valuationImage_univ_eq_univ [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) :
    valuationImage (Set.univ : Set (PName P)) S = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_valuationImage_of_checkZF_mem hS trivial

/-- The filter form of the collapse, via `Order.PFilter.top_mem`. -/
theorem valuationImage_univ_eq_univ_pfilter [Preorder P] [OrderTop P] (G : Order.PFilter P) :
    valuationImage (Set.univ : Set (PName P)) (G : Set P) = Set.univ :=
  valuationImage_univ_eq_univ G.top_mem

end Forcing
