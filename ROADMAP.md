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
"adds a new real."

## M3 — Cohen forcing over a ground model

**Status: complete** ([#35](https://github.com/cameronfreer/forcing/issues/35)).

Exit criterion: `G` is `M`-generic `→ c_G ∉ M.groundReals`.

This is the first genuine "Cohen forcing adds a real" theorem. The ground model
enters abstractly (a family of dense sets, a family of designated ground reals,
and a closure hypothesis), so the formal conclusion is stated against the
designated ground reals; the countable-transitive-model instantiation (M4+)
bridges carrier membership to the ground reals, discharges the closure
hypothesis, and upgrades the conclusion to `c_G ∉ M`.

## M4 — Names and generic extensions

**Status: in progress** ([#54](https://github.com/cameronfreer/forcing/issues/54)).

Typed/intensional `P`-names, valuation, check and generic names, and valuation
images of selected name families. A material ground-model presentation
([#62](https://github.com/cameronfreer/forcing/issues/62)) is required before
the resulting object is called `M[G]`, and is a named prerequisite for M5.

## M5 — Forcing theorem and preservation

**Status: planned.**

Prerequisite: the material ground/internal-name presentation
([#62](https://github.com/cameronfreer/forcing/issues/62)).

Internal forcing relation (defined by direct recursion on formulas, not via
Boolean values), definability, truth lemma, ZFC axioms in `M[G]`, closure and ccc
preservation.

## M6 — Boolean completion and Boolean-valued models

**Status: planned.**

Separative completion, complete regular algebra (via `Heyting.Regular` on lower
sets), `B`-names, and carefully scoped comparison theorems — distinguishing
external completeness from completeness internal to `M`.

## Later endpoint work

Flypitch port audit and concordance, proof theory, and CH independence are
endpoint work, not numbered near-term milestones. The Flypitch audit is a
parallel research task with no milestone dependency.
