/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Visibility

/-!
# The context-relative spectrum: newness over `M` does not imply `M`-genericity

The context-relative form of `parity_separation`. The statement is an implication failure
witnessed by `parityReal`, not a universal claim about new reals: the witness's canonical
filter is total, its real avoids every designated ground real, and yet it is not generic over
`M` — provided `M` can see the separating test. Visibility of `oddTrue` is the explicit
hypothesis, exactly the obligation that is easy to forget when "dense sets in `M`" stays
informal.

The two legs consume *incomparable* hypothesis budgets, and the public API keeps them apart:

* `parityReal_not_mem_groundReals` uses only the covering enumeration — countability of the
  ground reals, as data — and no visibility at all;
* `not_genericOver_parityReal` uses only the visibility of `oddTrue` — no enumeration, no
  `Sees`.

The combined theorem `parityReal_new_not_genericOver` is derived from the two, so the
incomparability is visible in signatures, not just in the implementation. In particular there
is no `Sees` hypothesis anywhere: the spectrum's visibility budget (`oddTrue` only) and the
new-real theorem's (coordinates plus ground-real diagonals) are incomparable, and the two
results are independent. Likewise the countability here (ground reals) is not the countability
of the new-real existence theorem (visible tests); the two roles never mix.

## Main results

* `Forcing.Cohen.parityReal_not_mem_groundReals`: the witness avoids the ground reals.
* `Forcing.Cohen.not_genericOver_parityReal`: the witness's filter is not generic over `M`.
* `Forcing.Cohen.parityReal_new_not_genericOver`: the combined spectrum separation.
-/

namespace Forcing.Cohen

open Order FinitePartialFunction

variable {M : CohenVisibilityContext} {x : ℕ → ℕ → Bool}

/-- The witness avoids the ground reals: `parityReal x` differs from `x i` at coordinate
`2 * i`, and the enumeration covers `M.groundReals`. Uses only the covering enumeration — no
visibility hypothesis at all. -/
theorem parityReal_not_mem_groundReals (hx : M.groundReals ⊆ Set.range x) :
    parityReal x ∉ M.groundReals := by
  intro hmem
  obtain ⟨i, hi⟩ := hx hmem
  have h2i : x i (2 * i) = parityReal x (2 * i) := congrFun hi (2 * i)
  rw [parityReal_even] at h2i
  cases x i (2 * i) <;> simp at h2i

/-- The witness's canonical filter is not generic over `M`: it misses `oddTrue`, which `M`
sees. Uses only the visibility of `oddTrue` — no enumeration, no `Sees`. The proof is the
composition payoff of packaging the test as `oddTrueReq`: the generic requirement–visibility
bridge applies directly. -/
theorem not_genericOver_parityReal (hodd : M.Visible oddTrue) :
    ¬M.GenericOver (ofFunction (parityReal x)) :=
  fun hG ↦ (parity_separation x).2.2 (hG.meets_requirement (R := oddTrueReq) hodd)

/-- **Newness over `M` does not imply `M`-genericity.** The canonical filter of `parityReal x`
is total and its real avoids every designated ground real, yet it is not generic over `M`. A
witness-specific implication failure, derived from the two single-hypothesis declarations
above — which is how the incomparable budgets (enumeration for newness, `oddTrue` visibility
for non-genericity, no `Sees` anywhere) stay visible in signatures. -/
theorem parityReal_new_not_genericOver (hx : M.groundReals ⊆ Set.range x)
    (hodd : M.Visible oddTrue) :
    (∀ n, (genericFun (ofFunction (parityReal x)) n).isSome) ∧
      parityReal x ∉ M.groundReals ∧
      ¬M.GenericOver (ofFunction (parityReal x)) :=
  ⟨fun n ↦ isSome_genericFun (meets_coordReq_ofFunction _) n,
    parityReal_not_mem_groundReals hx, not_genericOver_parityReal hodd⟩

/-!
### Sanity example

Over the full context — which sees `oddTrue` outright — the separation applies to any
enumeration of any family of designated ground reals it covers.
-/

example (x : ℕ → ℕ → Bool) :
    ¬(CohenVisibilityContext.full (Set.range x)).GenericOver (ofFunction (parityReal x)) :=
  not_genericOver_parityReal VisibilityContext.visible_full

end Forcing.Cohen
