/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.CompilerBridge

/-!
# The test layout

A fixed parameter layout for compiled formulas read against a recognizer, `Fin (5 + Rec.arity)`:

```text
0 tagMem, 1 tagEq, 2 condSet, 3 orderCode, 4 a (the assignment), then Rec.params
```

with `n` bound variables. The connective tests (`Forcing/Material/ConnectiveTests.lean`) read
it at `n = 1`, the tested condition; the Collection witness relation
(`Forcing/Material/CollectionName.lean`) at `n = 2`, the index and the witness. Moved here
verbatim from `ConnectiveTests.lean` at that second consumer, with the bound-variable count
generalized from `1` to `n`; at `n = 1` the declarations, and so the test sentences, are
unchanged.

## Main definitions

* `Forcing.testParams`, `Forcing.testAssignment`, `Forcing.testVector`.

## Main results

* `Forcing.testParams_realizes`, `Forcing.realize_testAssignment`.
-/

universe u

namespace Forcing

open FirstOrder Language AtomicRecursion

variable {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} (Rec : InternalNameRecognition N) {n : ℕ}

/-- The parameter block at the test layout: `tagMem, tagEq, condSet, orderCode, a` at positions
`0`–`4`, the recognizer's parameters after. -/
def testParams : CompilerParams (Fin (5 + Rec.arity)) Rec.arity n where
  tagMem := var (Sum.inl (Fin.castAdd Rec.arity 0))
  tagEq := var (Sum.inl (Fin.castAdd Rec.arity 1))
  condSet := var (Sum.inl (Fin.castAdd Rec.arity 2))
  orderCode := var (Sum.inl (Fin.castAdd Rec.arity 3))
  recParams := fun i ↦ Sum.inl (Fin.natAdd 5 i)

/-- The assignment parameter at the test layout. -/
def testAssignment : memLang.Term (Fin (5 + Rec.arity) ⊕ Fin n) :=
  var (Sum.inl (Fin.castAdd Rec.arity 4))

/-- The parameter vector the tests are read at. -/
def testVector (tagMem tagEq condSet orderCode a : ↥M) : Fin (5 + Rec.arity) → ↥M :=
  Fin.append ![tagMem, tagEq, condSet, orderCode, a] Rec.params

/-- The layout realizes the invariant at its vector. -/
theorem testParams_realizes (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M)
    (hq : (natCode eqTag : ZFSet.{u}) ∈ M) (condSet orderCode a : ↥M) (xs : Fin n → M) :
    (testParams Rec).Realizes Rec condSet orderCode
      (testVector Rec ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩ condSet orderCode a) xs where
  tagMem_eq := by simp [testParams, testVector, Fin.append_left]
  tagEq_eq := by simp [testParams, testVector, Fin.append_left]
  condSet_eq := by simp [testParams, testVector, Fin.append_left]
  orderCode_eq := by simp [testParams, testVector, Fin.append_left]
  recParams_eq := fun i ↦ by simp [testParams, testVector, Fin.append_right]

/-- The assignment parameter realizes to the assignment. -/
theorem realize_testAssignment (tagMem tagEq condSet orderCode a : ↥M) (xs : Fin n → M) :
    Term.realize (Sum.elim (testVector Rec tagMem tagEq condSet orderCode a) xs)
      (testAssignment Rec) = a := by
  simp [testAssignment, testVector, Fin.append_left]

end Forcing
