/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.FormulaCoding
import Forcing.Material.NameCoding

/-!
# Entries of the recursion graph

The first piece of the internal atomic recursion: the coding of a single **graph entry**, the
tagged tuple recording that a relation holds at a condition between two name codes.

One graph carries **both** atomic relations, distinguished by a tag — a *simultaneous* tagged
recursion, not two graphs plus a coherence theorem. `memWitnessTag` marks membership
witnesses and `eqTag` marks forced equality, and their disjointness
(`entry_inj`, plus `memWitnessTag ≠ eqTag`) is what keeps the two halves from interfering.

Coding, laws, and pricing follow the pattern of the earlier layers exactly: nested Kuratowski
pairs, one injectivity law from which decoding follows, and a membership theorem priced at
the finite closure axioms — empty set, pairing, and union, the last for the tag numerals.
Nothing here mentions the forcing relation, the recursion clauses, or any scheme: those
arrive with the graph itself.

## Main definitions

* `Forcing.AtomicRecursion.entry`: the tagged tuple.
* `Forcing.AtomicRecursion.memWitnessTag`, `Forcing.AtomicRecursion.eqTag`: the two relation tags.

## Main results

* `Forcing.AtomicRecursion.entry_inj`: entries determine tag, condition, and both name codes.
* `Forcing.MaterialGround.entry_mem`: entries lie in the ground, priced at finite closure.
-/

namespace Forcing

open FirstOrder

namespace AtomicRecursion

/-- The tag of a membership-witness entry. -/
def memWitnessTag : ℕ := 0

/-- The tag of a forced-equality entry. -/
def eqTag : ℕ := 1

theorem memWitnessTag_ne_eqTag : memWitnessTag ≠ eqTag := by
  decide

/-- A **graph entry**: at condition code `p`, the relation marked by `tag` holds between the
name codes `x` and `y`. -/
def entry (tag : ℕ) (p x y : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pair (natCode tag) (ZFSet.pair p (ZFSet.pair x y))

/-- **The entry law**: an entry determines its tag, its condition, and both name codes — so
the two tagged halves of the graph cannot interfere. -/
@[simp] theorem entry_inj {tag tag' : ℕ} {p x y p' x' y' : ZFSet.{0}} :
    entry tag p x y = entry tag' p' x' y' ↔ tag = tag' ∧ p = p' ∧ x = x' ∧ y = y' := by
  simp only [entry, ZFSet.pair_inj]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨natCode.injective h1, h2, h3, h4⟩,
    fun ⟨h1, h2, h3, h4⟩ ↦ ⟨congrArg _ h1, h2, h3, h4⟩⟩

/-- Membership-witness entries are never equality entries. -/
theorem entry_memWitness_ne_eq {p x y p' x' y' : ZFSet.{0}} :
    entry memWitnessTag p x y ≠ entry eqTag p' x' y' := by
  simp [entry_inj, memWitnessTag, eqTag]

end AtomicRecursion

namespace MaterialGround

open AtomicRecursion

variable {T : memLang.Theory} (M : MaterialGround.{0} T)
variable (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)

include he hp hu in
/-- **Entries lie in the ground**, priced at exactly the finite closure axioms: the tag is a
numeral and the tuple is nested Kuratowski pairs. -/
theorem entry_mem {tag : ℕ} {p x y : ZFSet.{0}} (hpm : p ∈ M) (hx : x ∈ M) (hy : y ∈ M) :
    entry tag p x y ∈ M :=
  M.pair_mem hp (M.natCode_mem he hp hu tag)
    (M.pair_mem hp hpm (M.pair_mem hp hx hy))

end MaterialGround

namespace AtomicRecursion

/-!
### Sanity examples

Entries at the two tags are distinguishable, and an entry determines its parts — the two
facts the simultaneous recursion needs in order to carry both relations in one graph.
-/

example {p x y : ZFSet.{0}} (h : entry memWitnessTag p x y = entry eqTag p x y) : False :=
  entry_memWitness_ne_eq h

example {tag : ℕ} {p x y p' x' y' : ZFSet.{0}}
    (h : entry tag p x y = entry tag p' x' y') : x = x' :=
  (entry_inj.1 h).2.2.1

end AtomicRecursion

end Forcing
