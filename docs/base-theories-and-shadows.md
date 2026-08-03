# RFC: base theories and shadows

**Status: research RFC.** Nothing in this document is implemented, and nothing in it may be
implemented before the external forcing relation exists — the atomic membership/equality
spike (#93) is the designated first consumer of any shadow predicate. Until then "shadow" is
methodological vocabulary. Claims below are design heuristics or cited literature, never
certified statements; the certified/planned discipline of
[conceptual-overview.md](conceptual-overview.md) applies with everything here on the
*planned* side.

## The frame

A general forcing setup is indexed by more than a poset:

```text
𝔉 = (T, M, P, 𝒩, Γ, J, ⊩, val)
```

— base theory `T`, a model `M ⊨ T`, presentation `P`, name fragment `𝒩`, formula fragment
`Γ`, test family `J`, a forcing relation available perhaps only for `Γ`, and valuation. The
question "is `P` ccc / homogeneous / closed?" becomes: **which fragment of that property is
actually used** to obtain a specified consequence for `Γ`-formulas or `𝒩`-names over a model
of `T`?

A **shadow** is a theorem-local structural interface sufficient for one target observable.
The classical property is typically its *universal envelope* — the shadow quantified over all
relevant instances. In a weaker theory one quantifies only over the instances that exist, are
coded, or lie in the fragment. The eventual Lean design is therefore: **local predicates
first, classical properties as universal wrappers** — so dependency mining can discover that
a theorem needs one shadow, not a global property.

**The scope rule** (extends architecture constraint 9): once weak base theories are in
scope, every infinitary property also names its quantification universe — external,
`M`-internal, `Γ`-definable, or coded in the second-order part.

## Worked shadow 1: width (the ccc shadow), corrected

ccc does **not** bound the possible values of an arbitrary name — the generic Cohen real is
the counterexample: no countable set of checked ground reals covers it. The genuine width
shadow carries a **ground-valued codomain**:

```text
p ⊩ τ ∈ Ǎ   +   width certificate
    ⟹   a suitably small / suitably coded B ⊆ A covers the possible values of τ below p
```

(densely below `p`, `τ` is decided to equal a member of `B`). In ZFC, ccc makes `B`
countable; the theorem only ever uses the existence of a suitable `B`. This applies to
ordinal-valued names, names for members of a specified ground set, and witness names — it is
the actual mechanism of cardinal/cofinality preservation, and the reason ROADMAP M8's width
route is stated with the codomain qualification. Homogeneity is the width-one extreme: for an
invariant sentence, the truth-value spectrum is a singleton.

## Worked shadow 2: symmetry (the homogeneity shadow)

Equivariance, fixed parameters, and orbit compatibility are **not** sufficient; the argument
also needs the relevant decisions to exist. The local package for one formula `φ(τ⃗)`:

1. automorphisms `H` acting on conditions and on the names of `φ`;
2. `Γ`-equivariance: `p ⊩ φ(τ⃗) ↔ π p ⊩ φ(π τ⃗)`;
3. parameter invariance: `π τ⃗ = τ⃗` (or forced equal);
4. orbit compatibility: deciding conditions can be moved to compatibility;
5. **density of `Γ`-deciders** — or the fragmentary forcing theorem supplying it.

Together: the top condition decides this `Γ`-formula. Full weak homogeneity is the universal
wrapper over formulas and parameters. This `HomogeneousFor`-style interface is the intended
first shadow, over #93's atomic fragment.

## Worked shadow 3: collection (the KP shadow)

KP/KPU's fragile axiom is Collection. The direct shadow is witness collection: whenever
`p ⊩ ∀ x ∈ ǎ, ∃ y, ψ(x, y)` (bounded `ψ`), an `M`-set `B` of candidate witness names has
`p ⊩ ∀ x ∈ ǎ, ∃ y ∈ B, ψ`. An internal chain bound is one *certificate* for it. A recent
concrete instance: for an admissible premouse with a largest regular uncountable `δ` and
`M`-internally `δ`-cc forcing, KP is preserved
([Kruschewski–Schlutzenberg](https://arxiv.org/abs/2207.06136)) — the hypotheses are real
and must not be silently generalized to arbitrary KP/KPU. The reusable middle term is the
implication pattern

```text
M-internal width control ⟹ Σ₁-witness collection ⟹ KP preservation
```

with the middle notion (`Σ₁`-collecting forcing) the likely generalization target, not
`δ`-cc itself.

## The base-theory ladder

| Base | Forcing fragment | Preservation target |
|---|---|---|
| PROVI ([Mathias](https://eudml.org/doc/283381)) | `Δ₀`/rudimentary | providence |
| KPU/KP | `Δ₀`, `Σ₁` | admissibility / Collection |
| ZFC⁻ | larger first-order fragments | Replacement-like closure |
| ZFC | full first-order forcing | ZFC |
| second-order arithmetic | `Γ⁰ₙ`, `Γ¹ₙ` | induction/comprehension fragments |
| bounded arithmetic | bounded fragments | bounded induction/collection |

Supporting literature: forcing against weak arithmetic with partially definable forcing
relations ([Atserias–Müller](https://ucrisportal.univie.ac.at/en/publications/partially-definable-forcing-and-bounded-arithmetic/));
an axiomatic treatment of forcing over varied bases
([Freire–Holy](https://www.cambridge.org/core/journals/review-of-symbolic-logic));
Jensen-style forcing over weak bases replacing full ccc machinery by control of *definable*
antichains ([Kanovei](https://arxiv.org/abs/2305.12486)) — the clearest existing instance of
a ccc shadow in the wild.

**Arithmetic note.** External ccc is contentless over arithmetic (everything is externally
countable), and there is no useful external `ω₁`. The productive replacements are
**coded/definable control of the antichains or possibility sets the target proof uses**,
indexed by formula complexity and by the axiom scheme being preserved — the `BΣₙ` bounding
scheme is the most ccc-like row (bounded coded witness spectra). Correspondences of the form
"ccc ⇝ `BΣₙ`-witness bounds" are **research hypotheses**, not established theorems.

**Genericity note.** Computability-theoretic *n*-genericity
([Feferman](https://math.stanford.edu/~feferman/papers.html); Mathias-style genericity
hierarchies, e.g. [arXiv:1201.6084](https://arxiv.org/abs/1201.6084)) is already an instance
of this library's visibility grading: `Σ⁰ₙ`-visible test families are `VisibilityContext`s,
and weak/full *n*-genericity are `GenericOver` at graded contexts. Preservation of arithmetic
subsystems is forcing-specific — e.g. `F_σ`-Mathias forcing preserving theories ordinary
Mathias forcing does not ([Dorais](https://arxiv.org/abs/1110.6559)) — so arithmetic shadows
are indexed by the scheme being preserved, never by one "arithmetic ccc".

## What is deliberately deferred

- **Shadow predicates in Lean** (`PossibleValuesCovered`, `WitnessesCollected`,
  `EquivariantFor`, `DecisionsCoded`, `Resolves`): wait for #93; each is introduced only
  when a theorem uses it, with the classical property as a universal wrapper afterward.
- **A KPU urelement universe** (`USet U`): a second foundational set representation alongside
  `PSet`/`ZFSet` — not a small generalization of the material layer. Postponed until the
  ordinary material forcing theorem is complete, a concrete KPU theorem is selected, and it
  is clear which name/valuation APIs generalize; it may ultimately deserve a separate project
  sharing the typed order/genericity kernel.
- **Three later pilots, kept distinct** (not one tranche): arithmetic Cohen forcing
  (`Σ⁰ₙ`-visible families, weak/full *n*-genericity, fragment-relative decisions); KPU
  forcing over atoms; KP preservation by witness collection.

## The research program

For a base theory `T`, fragment `Γ`, and observable `Φ`: what is the weakest local shadow of
a familiar property sufficient for `Φ`, and which certificates prove it and survive the
desired composition? Sample questions: the weakest homogeneity shadow for `Σ₁`-generic
absoluteness over KPU; the weakest possibility-bounding shadow preserving `Δ₀`-Collection;
the exact arithmetic shadow preserving `BΣ⁰ₙ`; when definable-antichain control suffices in
place of ccc; which shadows are dense-embedding invariant. The strongest structural claim,
held as a working hypothesis: **properties control the action of `P` on name and formula
fragments, not `P` in isolation** — the eventual zoo is indexed by `(P, M, Γ, 𝒩, Φ)`.

---

Related: [property-zoo.md](property-zoo.md) fixes the property-level discipline this RFC
refines; [conceptual-overview.md](conceptual-overview.md) owns the certified/planned split;
issue #93 is the designated first consumer.
