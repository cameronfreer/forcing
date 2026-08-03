# Architecture

Stable design constraints and layer boundaries. Changes to this document are
design decisions and should be justified in the commit message; genuinely
contested choices get a short decision record in `docs/decisions/`.

## Design constraints

1. **Smaller means stronger.** `q ≤ p` means `q` is a stronger condition.
   All public statements use this orientation; no theorem silently dualizes.
2. **Forcing notions require only `Preorder`.** No `PartialOrder` in the core;
   the separative quotient is where antisymmetry appears.
3. **No weakest condition in the core.** `[OrderTop P]` may appear in
   convenience lemmas only.
4. **Typed combinatorics before set coding.** All forcing combinatorics (density,
   antichains, closure, ccc) is proved on ordinary Lean types. `ZFSet` enters
   first as the *target* of external name valuation; set-coded presentations of
   the forcing notion itself arrive only at the material ground-model layer,
   with explicit absoluteness bridges.
5. **`GenericFor` is distinct from `GenericOver`.** `GenericFor 𝒟 G` (meeting a
   supplied family of dense sets) is pure order theory. `GenericOver M G` (meeting
   every dense-open test visible to `M`) is observer-relative: `M` is a
   `VisibilityContext` — a vocabulary of tests, not a model. The kernel knows only
   the former.
6. **Names remain intensional.** `P`-names and `B`-names are inductive trees; no
   quotient by (Boolean) extensional equality until the ultrafilter/model
   boundary.
7. **External complete Boolean algebras are distinct from algebras complete only
   inside `M`.** `[CompleteBooleanAlgebra B]` quantifies over Lean-indexed
   families; a completion coded in a ground model `M` is complete only for
   `M`-coded families and is generally not externally complete. Comparison
   theorems are restricted to `M`-names accordingly. Once both notions are in
   scope, always say "external Boolean completion" or "`M`-internal Boolean
   completion" — never the unqualified phrase.
8. **Proof theory is downstream and detachable.** The semantic library never
   depends on a derivation calculus.

## Layer boundaries

The spine is poset-first (see [ROADMAP.md](../ROADMAP.md)):

```text
order kernel → Cohen (external) → genericity over a visibility context
            → external name semantics → material grounds and M[G]
            → forcing relation and preservation → Boolean completion and BVM
```

Consequences of poset-first sequencing:

- **The forcing relation is defined by direct recursion on formulas** (density
  clauses), not as `e(p) ≤ ⟦φ⟧_B`. The Boolean-value characterization is a
  comparison theorem proved when the completion exists (M6), not a definition.
- `M[G]` is constructed without reference to any external regular-open algebra.
- The Boolean completion is planned order-natively as the regular
  (double-negation-stable) elements of `LowerSet P` — lower sets are the opens of
  the forcing Alexandrov topology. Expected (to be certified in Lean at M6): the
  Heyting complement of `D : LowerSet P` is the lower set of conditions
  incompatible with every member of `D`, and `Dᶜᶜ = {p | D is dense below p}`,
  recovering the classical regular-open completion. The topological
  presentation, if ever wanted, is to be proved isomorphic — not used as the
  definition.

## The two observer-relative vocabularies

The observer contributes two vocabularies, and they face opposite ways:

- **Tests.** A `VisibilityContext` fixes which dense-open tests count. More
  visible tests admit *fewer* generic filters — genericity is antitone in
  visibility (`GenericOver.anti`).
- **Descriptions.** A name family fixes which conditional descriptions are
  available. More names produce a *larger* valuation image — the image is
  monotone in the family (`valuationImage_mono`) — and the unrestricted family
  collapses to the ambient universe (`valuationImage_univ_eq_univ`).

Genericity constrains which worlds are admissible; valuation generates the sets
of a chosen world. A material ground must **derive both vocabularies coherently
from one carrier** — never accept them as independent fields (issue #62). The
forcing relation is the *persistent local judgment* on conditions; the **truth
lemma** (the forcing theorem) is the coherence statement connecting the two
vocabularies: the local conditions the ground recognizes as forcing a statement
are exactly those securing it when the ground's names are evaluated at its
generic worlds.

## Qualified claims (do not overstate)

- **"Adds a new real" is reserved for the material theorem**
  `realCode c ∈ M[G] ∧ realCode c ∉ M`, with `realCode` proved faithful
  (issue #62). The M3-layer theorem is **avoidance**: the abstract interface
  earns its over-`M` phrase exactly through its closure hypothesis (every
  designated real's diagonal dense set belongs to `M`'s dense family), and its
  formal conclusion is `c_G ∉ M.designatedReals` — a designated family, not the
  reals of a ground; the interface does not provide a model carrier, so it must
  not claim `c_G ∉ M`. The purely external statement is weaker still: "the
  generic diagonalizes a supplied countable family." The later material Cohen adapter (#75) discharges the pieces
  separately: it identifies the designated reals with coded carrier
  elements (the `realCode` bridge), proves visibility of the diagonal tests
  from the material presentation, and only then concludes the material form —
  with external countability entering only where generic existence is proved.
- **Generic-filter transport along dense embeddings is direction-asymmetric.**
  Given a dense order embedding `e : P → Q` and a generic `G : PFilter P`, the
  filter *generated by* `e '' G` meets transported dense sets. The literal
  preimage of a `Q`-filter need not be a filter, and the reverse transport
  direction needs stronger (typically model-relative) genericity hypotheses.
  Exact transport statements are a design deliverable, not an assumed
  unconditional theorem.

## Naming conventions

- Forcing vocabulary lives in `namespace Forcing`: `Compatible`, `Incompatible`,
  `IsDense`, `IsPredense`, `IsDenseOpen`.
- `Forcing.IsDense` is definitionally `IsCoinitial` (already forcing-oriented in
  mathlib); the alias keeps the library readable at zero cost.
- The embedding structure is `DenseOrderEmbedding` — explicit, and avoids
  collision with topology's dense embeddings. It extends `P ↪o Q` with a single
  `dense_range` field; monotonicity, order reflection, and compatibility
  reflection are theorems, not fields.
- All `OrderDual` conversions (to mathlib's upward-oriented cofinal/ideal
  machinery) are centralized in one bridge module; downstream files never
  manipulate `OrderDual` directly.
