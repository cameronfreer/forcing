# 0001 — Cohen-condition carrier: `Finmap (fun _ : ℕ => Bool)`

**Status**: decided (2026-07-31). **Issue**: [#9](https://github.com/cameronfreer/forcing/issues/9).

## Context

M2 needs a carrier for `Fn(ω, 2)` — finite partial functions `ℕ ⇀ Bool` ordered by reverse
inclusion (smaller = more information). Per the spike protocol, the choice was made by
prototyping the same four operations for each candidate and attempting the generic-union
uniqueness lemma, not by abstract API comparison. The disposable prototypes are preserved
verbatim in [`0001-cohen-carrier/`](0001-cohen-carrier/); they compile against the M1 kernel
(`lake env lean`, pin v4.32.2) but are **not** library code and are not imported by the build.

## Method

Each prototype implements: empty condition; lookup; one-coordinate extension; compatibility /
common extension (as `Agree`, `agree_of_compatible`, `compatible_of_agree` with an explicit
join); the reverse-inclusion `Preorder` via lookup; and the target lemma

```
genericUnion_unique : pairwise-compatible S → p, q ∈ S → look p n = some b →
  look q n = some b' → b = b'
```

Evaluation criteria: ergonomics, proof complexity, extensionality, order reasoning, and the
uniqueness lemma. Failure points below are the literal compile errors hit during the spike.

## Candidates and findings

### A — `Finmap (fun _ : ℕ => Bool)` (chosen)

- **Compiled on the first attempt** — the only candidate to do so.
- The four operations are library calls: `∅`, `lookup`, `insert`, and the built-in left-biased
  `∪` serves as the common extension; `compatible_of_agree` needed only `Finmap.mem_lookup_union`
  and `Finmap.mem_iff`, with the one case split (`n ∈ p` or not) inherent to the mathematics.
- Extensionality is free: `Finmap.ext_lookup` (conditions equal iff lookups agree) already
  exists in mathlib.
- Domains are native `Finset`s (`Finmap.keys`), which is what the M5 combinatorics
  (Δ-systems, ccc) will want; fresh-coordinate existence for diagonal density is
  `Finset.exists_notMem`-shaped, a one-liner over an infinite index type.
- Costs accepted: the `Sigma`-encoded dependent value type is noise for a constant `Bool`
  target; the left-biased union's lemma shape (`b ∈ lookup a s₁ ∨ (a ∉ s₁ ∧ b ∈ lookup a s₂)`)
  carries a membership sidecar. Neither caused friction in practice.

### C — `{f : ℕ → Option Bool // {n | f n ≠ none}.Finite}` (close second, rejected)

- Conceptually cleanest: conditions *are* functions, so extensionality is
  `Subtype.ext ∘ funext`, and the eventual generic union is a function by construction. The
  pointwise `Option.or` join is pretty.
- **Concrete failure points** (all fixable, all recurring): the `▸`-motive failure on
  rewriting under the subtype coercion (`invalid ▸ notation, failed to compute motive`);
  `rw [Function.update_of_ne]` failing to find its pattern under `↑⟨Function.update …, _⟩ m`
  until a `show`-normalization was inserted; and a `push Not made no progress` dead end in the
  join's finiteness obligation, resolved only by restructuring around a `match` on the lookup.
- Diagnosis: every proof touching the representation pays a coercion-normalization tax
  (`show`/`simp only` preludes), and the library owns every lemma — there is no analogue of
  mathlib's several-hundred-line `Finmap` lemma base. Rejected on accumulated friction, not on
  any mathematical defect; revisit if `Finmap`'s `Sigma` noise ever dominates in M2+.

### B — `structure` with `Finset ℕ` domain + total `val` (rejected)

- Requires a normalization field (`val = false` off the domain) merely to make structure
  equality coincide with lookup equality; **without it, extensionality by lookup is false.**
- The normalization obligation then infects every constructor: `empty`, `extend`, and `join`
  each carry an extra proof, and `extend`/`join` need `Function.update`/if-then-else case
  analyses to discharge it.
- **Concrete failure points**: `ext_look` alone is ~15 lines (reassemble `dom` from lookups,
  then a generated-`ext` + `funext` + `norm` argument for `val`); a first attempt via
  `cases`/`mk.injEq` failed (`Unknown identifier mk.injEq` at the naive name) before switching
  to the `@[ext]`-generated lemma; if-then-else splits appear in every `look`-level proof.
- The dependent variant `val : {n // n ∈ dom} → Bool` was considered on paper and not
  prototyped: it trades the normalization field for `HEq`-extensionality, which is worse.

### Not prototyped

`Finsupp ℕ (Option Bool)` would need a nonstandard `Zero (Option Bool)` instance (`none`) and
drags in algebraic API that is irrelevant here; it is candidate C with extra steps. Plain
`List (ℕ × Bool)` requires quotienting by permutation/duplication — which is exactly what
`Finmap` already is.

## Decision

A **`Finmap`-backed carrier**. The wrapper is the *generic* finite-partial-function type — one
field, not a transparent abbreviation:

```lean
@[ext] structure FinitePartialFunction {ι : Type u} (β : ι → Type v) where
  toFinmap : Finmap β
```

An `abbrev` over mathlib's `Finmap` (as in the prototype) would make the forcing-order instance
an orphan instance on `Finmap` and leak the forcing orientation globally; the wrapper retains
every `Finmap` advantage, with operations and lemmas lifting through the single field.

Cohen conditions are then a *safe* abbreviation of that wrapper — safe precisely because the
instances belong to `FinitePartialFunction`, not to `Finmap`:

```lean
abbrev Cohen.Cond := FinitePartialFunction (fun _ : ℕ => Bool)
```

The order is reverse inclusion via lookup

```lean
q ≤ p ↔ ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b
```

(smaller = more information), the empty condition is weakest, `insert` is one-coordinate
extension, and the left-biased `∪` is the canonical common extension of compatible conditions.

## Consequences

- The representation-independent API lives on `FinitePartialFunction`
  (`Forcing/FinitePartialFunction.lean`): operations, order structure, `Agree`,
  `compatible_iff_agree`, `insert_le_iff`, the union bounds, and fresh-coordinate existence
  under `[Infinite ι]`. `Forcing/Cohen/` keeps only Cohen-specific content. The
  `Agree`/`compatible_iff_agree` bridge from the prototype became real library code there
  (re-proved properly, not copied).
- The actual order structure is provided, not just a `Preorder`: **`PartialOrder`**
  (antisymmetry of the lookup-extension order via `Finmap.ext_lookup`) and **`OrderTop`** (the
  empty condition is literally `⊤`). The kernel still never assumes a weakest condition; the
  Cohen poset simply has one.
- `union` gets **no lattice instance**: it is a common strengthening only under agreement, and
  globally it is left-biased, noncommutative, and not a forcing meet.
- Generalizing to `Fn(κ, λ)` needs no new carrier: `FinitePartialFunction` is already generic
  over a `DecidableEq` index type and a dependent value family, so `Add(ω, κ)` and collapse
  forcing instantiate it directly. The diagonal-density argument is what constrains the
  parameters: it needs both a fresh-coordinate supply (infinite `κ`) and the ability to choose a
  value differing from the ground function's value (typically `Nontrivial λ`).
