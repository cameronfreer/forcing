# Roadmap

Milestones are outcome-based: each has explicit exit criteria and each later
milestone consumes only the public API of earlier ones. Design constraints that
apply across all milestones are recorded in
[docs/architecture.md](docs/architecture.md).

Status is tracked here, one line per milestone, and in the milestone tracking
issues; the README does not duplicate it.

## M1 — Forcing-oriented order kernel

**Status: complete** ([#1](https://github.com/cameronfreer/forcing/issues/1)).

Exit criteria:

- basic forcing vocabulary (`Compatible`, `Incompatible`, `IsDense`, `IsPredense`,
  `IsDenseOpen`);
- all `OrderDual` glue centralized in one module;
- `Order.PFilter`-based forcing filters, `Meets`, and `GenericFor`;
- forcing-oriented Rasiowa–Sikorski (no visible dualization in public statements);
- antichains and maximal-antichain equivalences;
- dense order embeddings with correctly qualified generic transport;
- separative preorder and quotient.

No `ZFSet`, names, Boolean-valued machinery, cardinal theory, or ccc.

## M2 — External Cohen generic real

**Status: complete** ([#20](https://github.com/cameronfreer/forcing/issues/20)).

Exit criteria:

- finite partial binary functions `Fn(ω, 2)` (representation chosen by spike);
- the generic union is well-defined;
- a filter meeting the coordinate dense sets has a total generic union;
- a filter meeting the diagonal requirements differs from every member of a
  supplied countable family.

This milestone is "Cohen generic diagonalizes a countable family" — not yet
the observer-relative avoidance theorem.

## M3 — Cohen forcing over a visibility context

**Status: complete** ([#35](https://github.com/cameronfreer/forcing/issues/35)).

Exit criterion: `G` is `M`-generic `→ c_G ∉ M.designatedReals`.

This is the **avoidance theorem**: the generic real avoids every designated
real. The ground model enters abstractly (a family of dense sets, a family of
designated reals, and a closure hypothesis), so the formal conclusion is stated
against the designated reals. "Adds a new real" is reserved for the material
theorem `realCode c_G ∈ M[G] ∧ realCode c_G ∉ M`, with `realCode` proved
faithful: the material presentation
([#62](https://github.com/cameronfreer/forcing/issues/62)) bridges carrier
membership to the designated reals, discharges the closure hypothesis, and
upgrades the conclusion to that material form.

## M4 — Names and external valuation semantics

**Status: complete** ([#54](https://github.com/cameronfreer/forcing/issues/54)).

Typed/intensional `P`-names, valuation, check and generic names, and valuation
images of selected name families. A material ground-model presentation is
required before the resulting object is called `M[G]` — that presentation is
M5.

## M5 — Material ground models and `M[G]`

**Status: in progress**
([#62](https://github.com/cameronfreer/forcing/issues/62), staged as
[#71](https://github.com/cameronfreer/forcing/issues/71)–[#75](https://github.com/cameronfreer/forcing/issues/75)).

Material carriers, the internal (no-junk) forcing presentation, the ground's
internal name family with its smallness evidence, and `M[G]` as an indexed
material set — ending at the material avoidance upgrade, the theorem that
finally earns "adds a new real".

## M6 — External forcing relation and truth lemma

**Status: planned.**

The forcing relation by direct recursion on formulas (never via Boolean
values), persistence under strengthening, and the semantic truth lemma
connecting stable local truth to generic evaluation. The atomic
membership/equality spike
([#93](https://github.com/cameronfreer/forcing/issues/93)) precedes the full
formula stack and need not wait for M5.

## M7 — Internal definability and ZFC in `M[G]`

**Status: planned.**

Definability of the forcing relation over the ground, and verification of the
ZFC axioms in `M[G]`.

## M8 — Preservation

**Status: planned.**

Closure and ccc preservation, cardinal arithmetic consequences.

## M9 — Boolean completion and Boolean-valued models

**Status: planned.**

The regular/Boolean completion of the already-existing separative quotient
(complete regular algebra via `Heyting.Regular` on lower sets), `B`-names, and
carefully scoped comparison theorems — distinguishing external completeness
from completeness internal to `M`.

## Later endpoint work

Flypitch port audit and concordance, proof theory, and CH independence are
endpoint work, not numbered near-term milestones. The Flypitch audit is a
parallel research task with no milestone dependency.
