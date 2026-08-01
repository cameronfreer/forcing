/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Ground

/-!
# The context-relative spectrum: new over `M` is not `M`-generic

The context-relative form of `parity_separation`: a filter can be total, avoid every designated
ground real, and still fail to be generic over `M` — provided `M` can see the separating test.
Visibility of `oddTrue` is the explicit hypothesis, exactly the obligation that is easy to
forget when "dense sets in `M`" stays informal.

Two deliberate asymmetries, both load-bearing:

* **No `Sees` hypothesis.** The proof does not use it: totality comes from `ofFunction`,
  newness from the enumeration and `parityReal`, and non-genericity from `hodd` with
  `isDenseOpen_oddTrue`. The spectrum therefore consumes a visibility budget *incomparable*
  with the new-real theorem's — `oddTrue` only, versus coordinates plus ground-real diagonals —
  and the two results are independent.
* **A different countability.** The new-real theorem's existence half consumes countability of
  the *visible tests*; here it is countability of the *ground reals*, supplied as an enumeration
  covering them, that constructs the witness. The two roles never mix.

## Main results

* `Forcing.Cohen.newness_not_genericOver`: the spectrum separation over a context.
-/

namespace Forcing.Cohen

open Order FinitePartialFunction

variable {M : CohenGroundContext}

/-- **New over `M` is not `M`-generic.** Given an enumeration covering the designated ground
reals (countability of the ground reals, as data) and visibility of the separating test
`oddTrue`, the canonical filter of `parityReal x` is total and its real avoids every ground
real, yet it is not generic over `M`.

There is no `Sees` hypothesis: the spectrum needs only that `M` sees `oddTrue`, a visibility
budget incomparable with the new-real theorem's. -/
theorem newness_not_genericOver {x : ℕ → ℕ → Bool}
    (hx : M.groundReals ⊆ Set.range x) (hodd : M.Visible oddTrue) :
    (∀ n, (genericFun (ofFunction (parityReal x)) n).isSome) ∧
      parityReal x ∉ M.groundReals ∧
      ¬M.GenericOver (ofFunction (parityReal x)) := by
  refine ⟨fun n ↦ isSome_genericFun (meets_coordReq_ofFunction _) n, ?_, ?_⟩
  · intro hmem
    obtain ⟨i, hi⟩ := hx hmem
    have h2i : x i (2 * i) = parityReal x (2 * i) := congrFun hi (2 * i)
    rw [parityReal_even] at h2i
    cases x i (2 * i) <;> simp at h2i
  · intro hG
    exact (parity_separation x).2.2 (hG oddTrue ⟨hodd, isDenseOpen_oddTrue⟩)

/-!
### Sanity example

Over the full context — which sees `oddTrue` outright — the separation applies to any
enumeration of any family of designated ground reals it covers.
-/

example (x : ℕ → ℕ → Bool) :
    ¬(CohenGroundContext.full (Set.range x)).GenericOver (ofFunction (parityReal x)) :=
  (newness_not_genericOver subset_rfl GroundContext.visible_full).2.2

end Forcing.Cohen
