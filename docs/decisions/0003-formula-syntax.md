# ADR 0003 — formula syntax: mathlib `BoundedFormula`, exclusively

**Status: decided** (audit #135; gates M6 items 6–7 of #130).

## Context

M6's formula forcing needs a syntax for the membership language. The candidates: mathlib's
`FirstOrder.Language.BoundedFormula` versus a custom formula datatype. The audit compiled
seven pressure tests against the pin, with two genuine rejection criteria fixed in advance —
excessive dependent transports around the binary relation/terms, or a badly shaped
carrier-quantifier bridge. Import size alone was ruled out as a criterion: M7 needs
first-order semantics, substitution, and definability infrastructure regardless.

## Decision

**Mathlib syntax, exclusively — no parallel custom formula datatype.** `BoundedFormula`'s
primitive constructors (`falsum`, built-in `equal`, `rel`, `imp`, `all`) align exactly with
the intended direct forcing recursion; every pressure test passed, and neither rejection
criterion fired.

The membership language follows mathlib's graph-language pattern — an indexed inductive
relation type, so dependent matches are single-constructor and arity-forcing:

```lean
inductive memRel : ℕ → Type
  | mem : memRel 2

def memLang : FirstOrder.Language := ⟨fun _ ↦ Empty, memRel⟩
```

## The pressure tests, results

1. **Language**: defined as above; no `if`-shaped relation types, so no dependent transports
   anywhere downstream.
2. **Terms**: a bespoke `evalTerm : (β → PName P) → memLang.Term β → PName P` needs **no
   `Structure` instance** — the impossible function cases eliminate by `Empty.elim` — so
   term evaluation lives at the `ModelTheory.Syntax` level.
3. **The family-relative recursion** compiled structurally, at the intended clauses:
   `falsum ↦ False`; `equal ↦ ForcesEq`; `rel .mem ↦ ForcesMem` (the dot-pattern on `.mem`
   forces arity 2 with no case analysis on the arity); `imp` quantified over strengthenings;
   `all` quantified over `τ ∈ 𝒩`.
4. **Atomic reductions**: both reduction equations to `ForcesEq`/`ForcesMem` are
   **definitional** (`Iff.rfl`) — no bridging lemmas needed.
5. **Persistence** for the recursion skeleton: five one-line cases (atomic persistence,
   transitivity narrowing, pointwise for `all`).
6. **The decisive test**: `memLang.Structure` instantiates on any `MaterialCarrier`
   (membership as the `RelMap`), and the carrier-quantifier bridge is well shaped —
   `∀ x : extensionCarrier N S, Φ x ↔ ∀ τ ∈ N.names, Φ ⟨zval S τ, _⟩` follows from
   `mem_extensionCarrier_iff` in five lines, and `BoundedFormula.realize_all` composes with
   it in two. Quantification over the carrier **is** quantification over the internal names.
7. **Import boundaries**, recorded as normative for M6: the syntax/forcing module imports
   only `Mathlib.ModelTheory.Syntax` (whose chain reaches `Basic`, where `Structure` lives,
   but not `Semantics`); the semantic-truth module additionally imports
   `Mathlib.ModelTheory.Semantics` (for `Realize`); nothing imports the wider model-theory
   stack.

## Consequences

Both consumers have landed at the audited signatures: `ForcesFormula` over
`memLang.BoundedFormula` with Syntax-only imports (`Forcing/Name/FormulaForcing.lean`), and
the truth lemma stating realization over `extensionCarrier N G` through the audited bridge
(`Forcing/Material/TruthLemma.lean`, with the carrier semantics in
`Forcing/Material/Semantics.lean`). The spike prototypes were scratch material, superseded
by those implementations; this record is the durable output.
