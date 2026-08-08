# ADR 0004 — the material ground interface is theory-indexed

**Status: decided** (M7 item 1, tracker #142; gates items 2–7).

## Context

M7 needs the model-bearing interface above `MaterialCarrier` — the name reserved for it since
the carrier layer landed. Two bad extremes had to be avoided: fixing every M7 construction to
full ZFC, or hiding an unspecified "adequate ground theory" behind a structure field. A pin
audit settled six questions before the interface was frozen.

## Decision

**The theory is an explicit parameter of the interface:**

```lean
structure MaterialGround (T : memLang.Theory) extends MaterialCarrier.{u} where
  models : ↥toMaterialCarrier ⊨ T
```

- `T` is a parameter — **never** a stored field, never silently ZFC.
- The membership *structure* is the scoped instance derived from `MaterialCarrier`
  (`Forcing/Material/Semantics.lean`); membership itself is `SetLike` through the carrier.
  Neither is duplicated.
- Nothing else is stored: no visibility context, no internal names, no forcing presentation,
  no countability, no closure operations.
- Downstream theorems state which axioms of `T` they consume, through
  `MaterialGround.realize_of_mem`; `MaterialGround.mono` records that consuming fewer axioms
  is the weaker hypothesis.
- A named ZFC theory or `ZFCGround` specialization appears **only** once the schemes are
  actually formalized — the pin has none (audit answer 5), so inventing one now would be
  vocabulary without content.

## The audit, answered

1. **Theory and satisfaction APIs.** `Language.Theory L` is `Set (L.Sentence)` (an abbrev);
   satisfaction is the `Prop`-valued class `Language.Theory.Model` with notation `M ⊨ T`, so
   it stores as a field. `Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ` and
   `Theory.realize_sentence_of_mem` make the per-axiom ledger of item 6 *literal*.
2. **Scoped structure, no global instance.** The carrier's `memLang.Structure` instance is
   `scoped`, and the field's type mentions it by unification on `↥toMaterialCarrier` — no
   global instance is installed, and none is needed.
3. **Nonemptiness is not required** by `Theory.Model`; mathlib needs `[Nonempty M]` only for
   particular realization lemmas. Since `model_nonemptyTheory_iff` exists, nonemptiness
   becomes an **axiom** (`memLang.nonemptyTheory ⊆ T`), recovered as
   `nonempty_of_nonemptyTheory` — the first dividend of theory-indexing, and the pattern
   every later requirement should follow.
4. **Universes are quiet.** `Language.Structure` is polymorphic in the carrier; `memLang`'s
   sentences live in `Type 0` (relations `memRel : ℕ → Type`, functions `Empty`), while the
   element type of a `MaterialCarrier.{u}` is `Type (u+1)`. Theories stay small while
   carriers live high; no lifting appears anywhere.
5. **No set-theory encodings at the pin.** `ModelTheory/` has `Arithmetic` but no set theory
   and no axiom schemes — confirming that a named ZFC theory is future work with real
   content, not a rename.
6. **Transport.** `Language.Equiv.theory_model_iff` transports satisfaction across
   isomorphic structures, and the `StrongHomClass` form exists; for *extensionally equal*
   carriers the membership-level `ext` already gives literal equality, so no bespoke
   transport API is owed.

## The standing guardrail

**Model satisfaction alone does not produce Lean-level internal codes.** Items 2–4 still owe
explicit coding and absoluteness theorems showing the relevant constructions exist inside the
carrier, each derived from **named axioms** of `T` — never added to `MaterialGround` as
convenience fields. This is the same discipline that kept `Sees` out of the carrier and out
of the visibility context: obligations are exposed and then earned, never assumed.

## Consequences

Item 2 (internal codes for conditions, names, assignments, and formulas) begins against this
interface and introduces axiom sentences of `memLang` as they are first consumed, naming each
one. Item 6's preservation ledger cites `realize_of_mem` per axiom. Item 7's Cohen endpoint
stays separate, with its non-tautology constraint intact.
