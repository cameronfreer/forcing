/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.FinitePartialFunction

/-!
# Cohen forcing conditions

The Cohen forcing notion `Fn(ω, 2)`: finite partial functions `ℕ ⇀ Bool`, ordered by reverse
inclusion. This is the finite-partial-function carrier (`Forcing.FinitePartialFunction`) at
index type `ℕ` and value type `Bool`; everything representation-independent — the operations,
the order structure, compatibility as agreement, `insert_le_iff`, the union lemmas, and
fresh-coordinate existence — lives there and applies here by instantiation.

What is genuinely Cohen-specific begins in the next files: the coordinate and diagonal
requirements, and the generic real.

## Main definitions

* `Forcing.Cohen.Cond`: a Cohen condition.
-/

namespace Forcing.Cohen

/-- A *Cohen condition*: a finite partial function `ℕ ⇀ Bool`, thought of as a finite amount of
information about a real. -/
abbrev Cond : Type :=
  FinitePartialFunction (fun _ : ℕ => Bool)

/-!
### Sanity examples

Everything below is inherited from `FinitePartialFunction`; these examples pin down the two
facts that make Cohen forcing nontrivial — conditions can disagree, and disjoint coordinates
never conflict — and confirm that the generic API instantiates without friction.
-/

open FinitePartialFunction

example : (⊤ : Cond) = ∅ := top_eq_empty

example : ((∅ : Cond).insert 0 true).lookup 0 = some true := lookup_insert_self

/-- Two conditions deciding coordinate `0` differently are incompatible: the basic reason Cohen
forcing is nontrivial. -/
example : Incompatible ((∅ : Cond).insert 0 true) ((∅ : Cond).insert 0 false) := by
  rw [Incompatible, compatible_iff_agree]
  intro h
  exact Bool.noConfusion (h lookup_insert_self lookup_insert_self)

/-- Conditions deciding distinct coordinates are always compatible. -/
example : Compatible ((∅ : Cond).insert 0 true) ((∅ : Cond).insert 1 false) := by
  rw [compatible_iff_agree]
  intro n b b' hb hb'
  rcases eq_or_ne n 0 with rfl | h0
  · rw [lookup_insert_of_ne (by omega), lookup_empty] at hb'
    simp at hb'
  · rw [lookup_insert_of_ne h0, lookup_empty] at hb
    simp at hb

/-- Every condition leaves a coordinate undecided — the fresh-coordinate supply that diagonal
requirements will use. -/
example (p : Cond) : ∃ n, p.lookup n = none := exists_lookup_eq_none p

end Forcing.Cohen
