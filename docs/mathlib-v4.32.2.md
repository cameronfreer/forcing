# Mathlib inventory at the pinned revision

Verified against the pin in [`lakefile.toml`](../lakefile.toml):
mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c` (the `v4.32.2` tag),
toolchain `leanprover/lean4:v4.32.2`.

**Staleness warning:** every claim below is specific to this revision and must be
re-audited on any toolchain/mathlib bump.

## What exists (and is directly usable)

| Ingredient | Location | Notes |
|---|---|---|
| `IsCoinitial` | `Mathlib/Order/Bounds/Defs.lean` | "for every `a`, there exists a member of `s` ≤ it" — literally forcing-density in forcing orientation; no dualization needed. |
| `Order.PFilter` | `Mathlib/Order/PFilter.lean` | Wraps `Ideal Pᵒᵈ`: nonempty, upward closed, downward directed — exactly the forcing-filter shape under smaller-is-stronger. |
| Rasiowa–Sikorski | `Mathlib/Order/Ideal.lean` | `Order.Cofinal`, `sequenceOfCofinals`, `idealOfCofinals`. Upward-oriented, indexed by `[Encodable ι]`; produces an `Ideal` containing a start point and meeting each cofinal set. Needs a one-time `OrderDual` bridge. |
| `IsAntichain` | `Mathlib/Order/Antichain.lean` | `IsAntichain r s := s.Pairwise rᶜ`, so `IsAntichain Compatible A` says distinct members are incompatible — a forcing antichain with no new definition. |
| `Heyting.Regular` | `Mathlib/Order/Heyting/Regular.lean` | Double-negation-stable elements of a Heyting algebra; `BooleanAlgebra (Regular α)` instance exists. **No completeness instance.** |
| `LowerSet` lattice structure | `Mathlib/Order/UpperLower/CompleteLattice.lean` | `CompletelyDistribLattice (LowerSet α)` instance; since `Order.Frame` extends `HeytingAlgebra` (`Mathlib/Order/CompleteBooleanAlgebra.lean`), `Heyting.Regular (LowerSet P)` type-checks today and is a `BooleanAlgebra` by the existing instance. |
| Material set theory | `Mathlib/SetTheory/ZFC/` | `PSet`, `ZFSet` (`Basic.lean`), `Class`, `Rank`, `VonNeumann`, ordinal/cardinal material. |
| First-order model theory | `Mathlib/ModelTheory/` | Syntax, semantics, satisfiability, ultraproducts, quotients. Semantic stack; no derivation calculus. |

## What is missing (ours to build, some upstreamable)

- **Completeness of regular elements.** No instance that the double-negation-stable
  elements of a frame form a *complete* Boolean algebra. This is the flagship
  upstream candidate; it instantiates at `LowerSet P` to give the forcing
  completion with no topology.
- **No `RegularOpens` API anywhere at this pin.** Mathlib PR
  [#10332](https://github.com/leanprover-community/mathlib4/pull/10332) remains
  open (as of 2026-07-30).
- **No separative preorders or separative quotients.** (The only "separative" hit
  in the source is an unrelated Scott-topology comment.)
- **No chain-condition (ccc) machinery** in a forcing-usable form.
- **No forcing-specific vocabulary**: compatibility, predensity, dense open sets,
  maximal antichains as predense sets, dense embeddings of forcing notions.

## Orientation notes

- Mathlib's cofinality/ideal machinery (`Cofinal`, `idealOfCofinals`) is
  upward-oriented; `PFilter` and `IsCoinitial` are already in forcing
  orientation. The kernel's bridge module is the *only* place these meet.
- `CompleteBooleanAlgebra` is the correct class for Boolean-valued work;
  `CompleteAtomicBooleanAlgebra` must never be required (forcing completions are
  generally atomless).
