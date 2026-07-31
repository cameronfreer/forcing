# Forcing

A Lean 4 library for set-theoretic forcing, built against
[mathlib](https://github.com/leanprover-community/mathlib4).

The library is developed in layers, with **typed forcing posets as the spine**:
order-theoretic forcing combinatorics first, then genericity over a ground model,
`P`-names and generic extensions `M[G]`, the forcing theorem and preservation, and
only then separative quotients, Boolean completions, and Boolean-valued models.
Proof-theoretic independence results in the style of
[Flypitch](https://github.com/flypitch/flypitch) are a detachable endpoint, not a
foundation.

**Current milestone: M2 — external Cohen generic real** (M1, the forcing-oriented order
kernel, is complete).
See [ROADMAP.md](ROADMAP.md) for milestones and
[the issue tracker](https://github.com/cameronfreer/forcing/issues) for active work.

- Toolchain: `leanprover/lean4:v4.32.2`
- Mathlib: pinned to the `v4.32.2` tag (`905b9581`)

## Building

```sh
lake exe cache get
lake build
```

## Documentation

- [ROADMAP.md](ROADMAP.md) — outcome-based milestones and exit criteria.
- [docs/architecture.md](docs/architecture.md) — stable design constraints and
  layer boundaries.
- [docs/mathlib-v4.32.2.md](docs/mathlib-v4.32.2.md) — verified inventory of what
  the pinned mathlib provides (and lacks) for forcing.

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
