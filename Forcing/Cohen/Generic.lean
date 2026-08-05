/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Basic
import Forcing.GenericUnion

/-!
# The Cohen generic real

Cohen forcing instantiates the generic-union machinery at index type `ℕ` and value type `Bool`.
Everything substantive is proved generically in `Forcing/GenericUnion.lean`; this file fixes the
Cohen names and records what the instantiation gives.

At this milestone the statements are about a *supplied* family of tests: the coordinate
requirements make the generic real total, and Rasiowa–Sikorski provides such filters. Nothing
here says "avoids the designated reals" — that is the over-`M` theorem (M3), with "adds a new
real" reserved further still for the material `M[G]` (certified in
`Forcing/Cohen/NewReal.lean`) — and the diagonal requirements that separate this level from
the next come in the next file.

## Main definitions

* `Forcing.Cohen.coordReq`: the requirement to decide the `n`-th bit.
* `Forcing.Cohen.genericFun`: the generic real, as a partial function.
-/

namespace Forcing.Cohen

open Order FinitePartialFunction

variable {G : PFilter Cond}

/-- The coordinate requirement: decide the `n`-th bit. -/
abbrev coordReq (n : ℕ) : Requirement Cond :=
  FinitePartialFunction.coordReq n

/-- The generic real determined by a filter, as a partial function. -/
noncomputable abbrev genericFun (G : PFilter Cond) : ℕ → Option Bool :=
  FinitePartialFunction.unionFun G

theorem genericFun_eq_some_iff {n : ℕ} {b : Bool} :
    genericFun G n = some b ↔ ∃ p ∈ G, p.lookup n = some b :=
  unionFun_eq_some_iff

/-- **Meeting every coordinate requirement makes the generic real total.** -/
theorem isSome_genericFun (h : ∀ n, Meets G (coordReq n).support) (n : ℕ) :
    (genericFun G n).isSome :=
  isSome_unionFun h n

/-- Such filters exist: through any condition there is one whose generic real is total. -/
theorem exists_pfilter_total (p : Cond) :
    ∃ G : PFilter Cond, p ∈ G ∧ ∀ n, (genericFun G n).isSome :=
  FinitePartialFunction.exists_pfilter_total p

/-- **Faithful recovery**: a filter whose generic real is the total function `c` is the
canonical filter of `c`. Coordinate genericity is not an extra hypothesis — it is equivalent
evidence of totality (`meets_coordReq_iff`). -/
theorem eq_ofFunction {c : ℕ → Bool} (hc : ∀ n, genericFun G n = some (c n)) :
    G = ofFunction c :=
  eq_ofFunction_of_unionFun hc

/-!
### Sanity examples

The canonical filter of a real is coordinate-generic and returns that real, so the two
directions compose.
-/

example (c : ℕ → Bool) (n : ℕ) : genericFun (ofFunction c) n = some (c n) :=
  unionFun_ofFunction

example (c : ℕ → Bool) (n : ℕ) : Meets (ofFunction c) (coordReq n).support :=
  meets_coordReq_ofFunction c n

example (c : ℕ → Bool) : ofFunction c = ofFunction c :=
  eq_ofFunction fun _ ↦ unionFun_ofFunction

example {n : ℕ} : Meets G (coordReq n).support ↔ (genericFun G n).isSome :=
  meets_coordReq_iff_isSome_unionFun

end Forcing.Cohen
