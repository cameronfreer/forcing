# Forcing

[![CI](https://github.com/cameronfreer/forcing/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/cameronfreer/forcing/actions/workflows/lean_action_ci.yml)

A Lean 4 library for set-theoretic forcing, built against
[mathlib](https://github.com/leanprover-community/mathlib4).

The library is developed in layers, with **typed forcing posets as the spine**:
the order kernel and concrete forcing notions first, then observer-relative
genericity, typed names and external valuation semantics, material ground models
and `M[G]`, the forcing theorem and preservation, and only then Boolean
completions and Boolean-valued models.
Proof-theoretic independence results in the style of
[Flypitch](https://github.com/flypitch/flypitch) are a detachable endpoint, not a
foundation.

## Layout

The library is organized into independently reusable components; imports are kept
local, so users can stop at the layer they need. Use `import Forcing` for the
complete public surface, or import the component modules listed below for
narrower dependencies.

| Component | Modules | Provides |
|---|---|---|
| Order kernel | `Forcing/Order/` | conditions, compatibility, dense/predense/dense-open sets, forcing filters, family-relative genericity, Rasiowa–Sikorski, antichains, maximal antichains, dense embeddings, separative quotients, requirements |
| Finite conditions | `Forcing/FinitePartialFunction.lean`, `Forcing/GenericUnion.lean` | the shared carrier of finite-condition forcing notions; the correspondence between filters and partial functions; coordinate requirements and totality of the generic union |
| Names | `Forcing/Name/` | external name semantics: intensional `P`-names, valuation against condition sets, check and generic names, and selected-name valuation images with the certified collapse of the unrestricted image |
| Visibility contexts | `Forcing/Model/` | observer-relative genericity: visibility contexts (an interface, deliberately not yet a ground model), genericity over a context, existence from external countability, the requirement–visibility bridge |
| Material layer | `Forcing/Material/` | material carriers — transitive sets with a membership-only interface; the layer on which internal presentations, internal names, and `M[G]` are built |
| Cohen forcing | `Forcing/Cohen/` | `Fn(ω, 2)`; the generic real; diagonalization of a supplied countable family; the strict genericity spectrum; the avoidance theorem over a visibility context |

Milestones, their exit criteria, and their status live in [ROADMAP.md](ROADMAP.md);
active work is on
[the issue tracker](https://github.com/cameronfreer/forcing/issues).

## Conventions

Two orientation facts to know on arrival, and one policy:

- **Smaller is stronger**: `q ≤ p` means `q` carries at least as much information
  as `p`; a strongest condition (when one exists) is `⊥`.
- **Adequacy and existence are separate.** External countability enters
  Rasiowa–Sikorski existence statements, not the definitions of `GenericFor` or
  `GenericOver`.
- Mathlib's linters run with warnings-as-errors; project policy forbids `sorry`
  and custom axioms.

The full set of design constraints and layer boundaries is recorded in
[docs/architecture.md](docs/architecture.md).

## Building

Exact Lean and mathlib revisions are pinned in `lean-toolchain` and
`lakefile.toml`.

```sh
lake exe cache get
lake build
```

## Documentation

- [ROADMAP.md](ROADMAP.md) — outcome-based milestones, exit criteria, and status.
- [docs/conceptual-overview.md](docs/conceptual-overview.md) — theorem-first statement of the
  architecture: objects, tests, and descriptions relative to an observer; every claim certified
  or explicitly marked planned.
- [docs/architecture.md](docs/architecture.md) — stable design constraints and
  layer boundaries.
- [docs/mathlib-v4.32.2.md](docs/mathlib-v4.32.2.md) — verified inventory of what
  the pinned mathlib provides (and lacks) for forcing.
- [docs/why-genericity.md](docs/why-genericity.md) — genericity derived in discovery order,
  each definition introduced by the failure it repairs.
- [docs/names.md](docs/names.md) — external name semantics in the same discovery order, ending
  at the honest stopping point before `M[G]`.
- [docs/decisions/](docs/decisions/) — decision records for contested choices.

## Related work

- [Flypitch](https://github.com/flypitch/flypitch) (Lean 3): syntactic independence
  of CH via Boolean-valued models.
- [flypitch-lean4](https://github.com/zhangjunphy/flypitch-lean4): a direct Lean 4
  port of Flypitch (Lean 4.29).
- Isabelle/ZF AFP entries:
  [Forcing](https://isa-afp.org/entries/Forcing.html) and
  [Independence of CH](https://www.isa-afp.org/entries/Independence_CH.html) —
  modular countable-transitive-model forcing and generic extensions.

## License

Apache 2.0 — see [LICENSE](LICENSE).
