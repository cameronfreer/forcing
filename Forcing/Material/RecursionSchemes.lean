/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes
import Forcing.Material.RecursionFormula

/-!
# The recursion's scheme instances

The point at which the atomic recursion begins to cost something. Every scheme instance the
construction uses is **named here, by its mathematical job**, together with the semantic
theorem it buys — so the ledger records the actual finite family of formulas rather than a
wholesale appeal to "Separation" or "Collection".

This module owns the first instance:

**The stage instance** — *carving a stage's valid tagged entries out of a bound.* Its formula
is literally `stageEntryDef`, the same formula the stage relation quantifies over, applied at
seven parameters. Nothing is contorted to make it fit: the separated condition **is** the
membership condition of `StageValue`, which is why `exists_stageValue_of_bound` below is the
internal counterpart of the external `stageValue_exists_of_bound` and is proved by the same
two-line argument with `ZFSet.sep` replaced by the instance.

## What this instance costs, and what it does not

`exists_stageValue_of_bound` charges **exactly one Separation sentence**. It charges no
Collection, no Foundation, no Infinity, and no Power Set, and it needs no finite-closure
axioms either: the bound is a carrier element, so the entries it contains are already in the
carrier by transitivity, and the separately priced `entry_mem` is not invoked. The bound
itself is a hypothesis, exactly as in the external version — constructing bounds is a later,
separately charged step.

Nothing here mentions `InternalNameCoding` or the external forcing relation.

## Main definitions

* `Forcing.AtomicRecursion.stageFormula`: the stage instance's formula, at its seven
  parameters.
* `Forcing.AtomicRecursion.stageSeparationSentence`: the named Separation instance.

## Main results

* `Forcing.MaterialGround.exists_stageValue_of_bound`: the stage exists inside the ground.
-/

universe u

namespace Forcing

open FirstOrder Language

namespace AtomicRecursion

/-- The stage instance's formula: `stageEntryDef` at seven parameters — the two tags, the
condition set, the order code, the history, and the two name codes — with the separated
variable naming the candidate entry.

The parameter order is fixed here once; `exists_stageValue_of_bound` supplies it in the same
order, so no consumer has to count `Sum.inl` indices. -/
def stageFormula : memLang.BoundedFormula (Fin 7) 1 :=
  stageEntryDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6)) (&0)

/-- **The stage instance**: the Separation sentence carving a stage's valid tagged entries out
of a bound. -/
def stageSeparationSentence : memLang.Sentence :=
  separationSentence stageFormula

theorem stageSeparationSentence_mem_scheme :
    stageSeparationSentence ∈ separationScheme :=
  separationSentence_mem_scheme stageFormula

end AtomicRecursion

namespace MaterialGround

open AtomicRecursion

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **The stage exists inside the ground**, given a bound. The internal counterpart of
`AtomicRecursion.stageValue_exists_of_bound`, and its exact analogue: the clause guards
discard malformed members, so **nothing is assumed about whether members of `x` or `y` are
coded branches** — the relation stays total on its whole indexing set, which is what
Collection will later require.

Charged to `T`: **one Separation sentence**, and nothing else. The entries are members of the
bound, hence carrier elements by transitivity, so no finite-closure axiom is consumed. -/
theorem exists_stageValue_of_bound (hsep : stageSeparationSentence ∈ T)
    (tagMem tagEq condSet orderCode history x y bound : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (he : (tagEq : ZFSet.{u}) = natCode eqTag)
    (hb : ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (bound : ZFSet.{u}) ∧
        entry eqTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (bound : ZFSet.{u})) :
    ∃ value : ↥M.toMaterialCarrier,
      StageValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
        (x : ZFSet.{u}) (y : ZFSet.{u}) (value : ZFSet.{u}) := by
  obtain ⟨b, hbdef⟩ := M.exists_separation (φ := stageFormula) hsep
    ![tagMem, tagEq, condSet, orderCode, history, x, y] bound
  -- The separated condition is exactly the stage-entry condition.
  have hbody : ∀ e : ↥M.toMaterialCarrier,
      stageFormula.Realize ![tagMem, tagEq, condSet, orderCode, history, x, y] ![e] ↔
        (∃ p ∈ (condSet : ZFSet.{u}), (e : ZFSet.{u}) =
            entry memWitnessTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∧
            MemClause (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u}) p
              (x : ZFSet.{u}) (y : ZFSet.{u})) ∨
          (∃ p ∈ (condSet : ZFSet.{u}), (e : ZFSet.{u}) =
            entry eqTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∧
            EqClause (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u}) p
              (x : ZFSet.{u}) (y : ZFSet.{u})) := by
    intro e
    rw [stageFormula, realize_stageEntryDef (by simpa using hm) (by simpa using he)]
    simp
  have hbM : (b : ZFSet.{u}) ∈ M.toMaterialCarrier := b.2
  have hboundM : (bound : ZFSet.{u}) ∈ M.toMaterialCarrier := bound.2
  refine ⟨b, fun e ↦ ⟨fun he' ↦ ?_, fun hd ↦ ?_⟩⟩
  · have heM : e ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans he' hbM
    exact (hbody ⟨e, heM⟩).1 ((hbdef ⟨e, heM⟩).1 he').2
  · -- The candidate entry lies in the bound, hence in the carrier.
    have heB : e ∈ (bound : ZFSet.{u}) := by
      rcases hd with ⟨p, hp, rfl, -⟩ | ⟨p, hp, rfl, -⟩
      · exact (hb p hp).1
      · exact (hb p hp).2
    have heM : e ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans heB hboundM
    exact (hbdef ⟨e, heM⟩).2 ⟨heB, (hbody ⟨e, heM⟩).2 hd⟩

end MaterialGround

end Forcing
