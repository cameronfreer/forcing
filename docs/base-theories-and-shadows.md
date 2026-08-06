# RFC: base theories and shadows

**Status: research RFC.** The no-code trigger has **fired**: the external forcing relation
now exists (`ForcesMem`/`ForcesEq`/`ForcesFormula`, with the truth lemma certified), so
shadow predicates *may* now be implemented — but the shadows themselves remain research work
until a theorem consumes them, and each is still introduced only at its first consumer.
"Shadow" stays methodological vocabulary until then. Claims below are design heuristics or cited literature, never
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

**Definitional caution.** The primitive is the *predicate*
`PossibleAt p τ x := ∃ q ≤ p, q ⊩ τ = x̌`, not the spectrum `Poss_p(τ)` as an object: in a
weak theory the collection of all such `x` may not exist internally — the existence of a
coded cover is precisely what the shadow must provide. Do not assume Separation or Collection
in the definition of the very object whose coding is under investigation.

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

**Naming discipline.** Shadows are named by content — *fragment-relative,
parameter-relative homogeneity* — with KPU one instantiation, never baked into the name.

**The rigid-base caveat.** Over arithmetic the base structure is rigid: an arbitrary
coordinate permutation preserves neither `+`, `×`, order, nor named number parameters. An
arithmetic homogeneity shadow therefore applies only to parameter-free formulas, formulas
invariant under a specified definable group, a separate generic coordinate sort, or an
urelement presentation in which symmetry acts only on the forcing sort. Separating the
**rigid base structure** from the **symmetric generic coordinates** is the strongest argument
for eventually supporting urelements.

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
relations ([Atserias–Müller](https://ucrisportal.univie.ac.at/en/publications/partially-definable-forcing-and-bounded-arithmetic/)),
with random-variable forcing for bounded arithmetic compared to set-theoretic random forcing
in [arXiv:2603.10908](https://arxiv.org/abs/2603.10908);
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

## Axiom-by-axiom shadows for arithmetic

Indexed by the **target scheme** (the orthogonal lookup direction to the translation table
below). Every entry is a **candidate proof obligation or research hypothesis**, not an
established correspondence:

| Target scheme | Candidate forcing shadow |
|---|---|
| `IΣ⁰ₙ` | forcing relation for `Σ⁰ₙ`, persistence, and a least-counterexample or induction argument |
| `BΣ⁰ₙ` | a coded bound on possible witnesses — the most ccc-like row |
| `Δ⁰₁`-comprehension | uniform coding of two-sided decisions |
| arithmetical comprehension | a name family closed under arithmetical definitions/jumps — closure alone is **not** a preservation theorem; the full route is the obligation |
| `WKL₀` | a compactness/path/fusion shadow for internal infinite trees — a research direction, not yet a defined shadow |
| `Γ`-conservation | `Γ`-homogeneity plus a `Γ`-forcing theorem |
| standard-system preservation | every relevant newly definable set captured or controlled by an old code |

**Genericity note.** Computability-theoretic *n*-genericity
([Feferman](https://math.stanford.edu/~feferman/papers.html); Mathias-style genericity
hierarchies, e.g. [arXiv:1201.6084](https://arxiv.org/abs/1201.6084)) is already an instance
of this library's visibility grading: `Σ⁰ₙ`-visible test families are `VisibilityContext`s,
and weak/full *n*-genericity are `GenericOver` at graded contexts. Preservation of arithmetic
subsystems is forcing-specific — e.g. `F_σ`-Mathias forcing preserving theories ordinary
Mathias forcing does not ([Dorais](https://arxiv.org/abs/1110.6559)) — so arithmetic shadows
are indexed by the scheme being preserved, never by one "arithmetic ccc".

## What is deliberately deferred

- **Shadow predicates in Lean** (`PossibleAt`, `PossibleValuesCovered`,
  `ΓAntichainCoding`, `ΓDecisionCoding`, `WitnessesCollected`, `EquivariantFor`,
  `DecisionsCoded`, `Resolves`): the forcing relation now exists, so these are
  *implementable* — but each is still introduced only when a theorem uses it, with the
  classical property as a universal wrapper afterward.
- **A KPU urelement universe** (`USet U`): a second foundational set representation alongside
  `PSet`/`ZFSet` — not a small generalization of the material layer. Postponed until the
  ordinary material forcing theorem is complete, a concrete KPU theorem is selected, and it
  is clear which name/valuation APIs generalize; it may ultimately deserve a separate project
  sharing the typed order/genericity kernel.
- **Three later pilots, kept distinct** (not one tranche): arithmetic Cohen forcing
  (`Σ⁰ₙ`-visible families, weak/full *n*-genericity, fragment-relative decisions); KPU
  forcing over atoms; KP preservation by witness collection.

**The HYP bridge (candidate architecture, schematic).** For a structure `𝓜`, the least
admissible set above it gives `𝓜 → HYP(𝓜) → HYP(𝓜)[G]`: the arithmetic domain and its
relations live in the urelement sort; names, tests, and recursive constructions live in the
admissible set above it; forcing keeps the urelement structure fixed; the new sets project
back to a second-order arithmetic extension. This is a *candidate* architecture — not a
promise that every arithmetic model has a canonical `HYP` construction fitting the eventual
Lean interface. **Overshoot caveat:** `HYP(𝓜)` may be far stronger than `RCA₀` or bounded
arithmetic — the right bridge for admissible and hyperarithmetic phenomena, the wrong tool
for tight reverse-mathematical calibration, which routes through direct arithmetic forcing or
Mathias's provident sets. This caveat is why the arithmetic and KPU pilots remain separate.

## Translation table

Indexed by the **classical source property** (orthogonal to the axiom-by-axiom table's
target-scheme index). Every non-classical entry is a research hypothesis:

| Classical property | Local shadow | KPU/KP form | Arithmetic form |
|---|---|---|---|
| atomless | a relevant condition has a visible incompatible split | `A`-visible splitting | definable splitting giving a new predicate relative to old definable sets |
| separative | future compatibility distinguishes two conditions | visible/`Γ`-separativity | equivalence by the same `Γ`-forcing behavior |
| homogeneous | equivariance + parameter invariance + orbit compatibility + decider density, for one formula | `A`-coded action fixing urelements, `Γ = Δ₀` or `Σ₁` | definable action and `Σ⁰ₙ`-equivariance |
| ccc | a small possibility cover for a name with a ground-valued codomain | `A`-set of possible witnesses; internal `δ`-cc one certificate | coded/definable antichains or bounded witness spectra |
| `<κ`-distributive | one condition resolves a specified test family | resolves `A`-coded families | resolves coded families; adds no objects in a selected definability class |
| proper | master condition for a selected observer | master over an admissible substructure | master over a coded submodel/cut; standard-system or induction-fragment preservation |
| complete Boolean algebra | all relevant infinitary truth operations exist | complete for `A`-coded joins only | Boolean operations only for coded/formula-generated families |

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
