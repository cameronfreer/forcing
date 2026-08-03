/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Visibility

/-!
# The new-real theorem

Over a Cohen visibility context whose visibility obligations hold, an `M`-generic filter's real is
total and lies outside the designated ground reals; combined with external countability of the
visible family, such filters exist through every condition. The combined corollary is the
theorem that earns the phrase **adds a new real**.

The conclusion is against the *designated* ground reals: nothing here mentions `M[G]`, and
`c ∉ M` (as opposed to `c ∉ M.groundReals`) is the later material bridge. Adequacy and
existence stay separate — the adequacy statements use only `Sees` and genericity, and
countability appears only in the existence corollary. The M2 theorems are consumed unchanged:
this file adds no new density or diagonal content, only the observer.

## Main results

* `Forcing.Cohen.isSome_genericFun_of_genericOver`: adequacy, totality half.
* `Forcing.Cohen.not_mem_groundReals_of_genericOver`: adequacy, newness half.
* `Forcing.Cohen.exists_newReal_of_genericOver`: adequacy, packaged — the countability-free
  endpoint, extraction included.
* `Forcing.Cohen.exists_pfilter_genericOver_new`: **Cohen forcing adds a new real** — countable
  existence composed with the packaged adequacy theorem.
-/

namespace Forcing.Cohen

open Order FinitePartialFunction

variable {M : CohenVisibilityContext} {G : PFilter Cond}

/-- Adequacy, totality half: an `M`-generic filter's union is total. Uses only the visibility
obligations and genericity — no countability. -/
theorem isSome_genericFun_of_genericOver (hM : M.Sees) (hG : M.GenericOver G) (n : ℕ) :
    (genericFun G n).isSome :=
  isSome_genericFun (fun m ↦ hM.meets_coordReq hG m) n

/-- Adequacy, newness half: the extracted real of an `M`-generic filter is not a ground real.
The route is the M3 bridge: for each `x ∈ M.groundReals` the diagonal requirement `diagReq x`
is visible (`Sees.visible_diagReq`), genericity meets it, and meeting it forces disagreement.
Uses only the visibility obligations and genericity — no countability. -/
theorem not_mem_groundReals_of_genericOver (hM : M.Sees) (hG : M.GenericOver G)
    {c : ℕ → Bool} (hc : ∀ n, genericFun G n = some (c n)) :
    c ∉ M.groundReals := by
  intro hcM
  obtain ⟨n, b, hb, hne⟩ := exists_ne_of_meets_diagReq (hM.meets_diagReq hG hcM)
  rw [hc n] at hb
  exact hne (Option.some.inj hb).symm

/-- Adequacy, packaged: an `M`-generic filter yields a total real outside the designated ground
reals. Countability-free — this is the adequacy endpoint, with the total real extracted by the
generic `totalUnion`, so that the existence corollary below is literally "countable existence
composed with this theorem". -/
theorem exists_newReal_of_genericOver (hM : M.Sees) (hG : M.GenericOver G) :
    ∃ c : ℕ → Bool, (∀ n, genericFun G n = some (c n)) ∧ c ∉ M.groundReals := by
  have htotal : ∀ n, (genericFun G n).isSome := isSome_genericFun_of_genericOver hM hG
  exact ⟨totalUnion G htotal, unionFun_totalUnion htotal,
    not_mem_groundReals_of_genericOver hM hG (unionFun_totalUnion htotal)⟩

/-- **Cohen forcing adds a new real.** Through any condition there is an `M`-generic filter;
its union is total, and the extracted real avoids every designated ground real. The proof is
the adequacy/existence separation made literal: countable existence of a generic filter
(`exists_pfilter_genericOver`) composed with the countability-free adequacy endpoint
(`exists_newReal_of_genericOver`). External countability of the visible dense-open family lives
here and in no adequacy statement. -/
theorem exists_pfilter_genericOver_new (hM : M.Sees)
    (hcount : M.visibleDenseOpen.Countable) (p : Cond) :
    ∃ G : PFilter Cond, p ∈ G ∧ M.GenericOver G ∧
      ∃ c : ℕ → Bool, (∀ n, genericFun G n = some (c n)) ∧ c ∉ M.groundReals := by
  obtain ⟨G, hpG, hG⟩ := exists_pfilter_genericOver p hcount
  exact ⟨G, hpG, hG, exists_newReal_of_genericOver hM hG⟩

/-!
### Sanity example

The adequacy statements have no countability hypothesis; over the full context (which satisfies
the obligations for any designated reals) they apply to any generic filter directly.
-/

example {R : Set (ℕ → Bool)} (hG : (CohenVisibilityContext.full R).GenericOver G)
    {c : ℕ → Bool} (hc : ∀ n, genericFun G n = some (c n)) : c ∉ R :=
  not_mem_groundReals_of_genericOver (CohenVisibilityContext.sees_full R) hG hc

end Forcing.Cohen
