# Objects, tests, and descriptions

The theorem-first companion to [why-genericity.md](why-genericity.md) and [names.md](names.md):
those two documents derive the definitions in discovery order, failure by failure; this one
states the architecture they converge on.

**Status discipline.** Every claim below is either **certified** — linked to the Lean
declaration that proves it — or explicitly marked **planned** with the issue or milestone that
owns it. There is no third kind of claim.

---

## The thesis

A forcing presentation provides conditions carrying partial information. On the
finite-partial-function carrier, filters are exactly partial objects, represented by all of
their finite facts. Requirements are the persistent, locally attainable tests on conditions. A
visibility context determines which tests count, while external valuation evaluates a chosen
family of conditional descriptions along a condition set. The planned material bridge derives
both vocabularies — visible tests and available descriptions — from one carrier, and thereby
earns the construction `M[G]`; the planned truth lemma connects that evaluation semantics to
persistent local forcing judgments.

**The certified/planned split.** The external architecture is certified below: the two
equivalences, observer-relative genericity, the name semantics with its two certified
failures, and the two opposing monotonicities. So is the description side of the material
bridge: internal names and the **indexed `M[G]`** —
[`extensionCarrier`](../Forcing/Material/Extension.lean), a genuine transitive `ZFSet` whose
underlying set equals the valuation image of the internal family, with the ground-inclusion
and generic-code memberships proved. Two arrows remain planned: derived visibility and the
Cohen synchronization (#75), and the truth lemma (M6); the closing section states exactly
what each must provide.

## Objects: a filter is a partial object

On the finite-partial-function carrier, filters are **exactly** partial objects, presented by
all of their finite facts:

```text
PFilter (FinitePartialFunction β)  ≃  Π i, Option (β i)
```

([`pfilterEquivPartialFunction`](../Forcing/GenericUnion.lean)), with both inverse laws and no
genericity, totality, or fiber-nonemptiness hypotheses. Each filter axiom is the exact price of
one leg: directedness makes the union functional
([`unionGraph_unique`](../Forcing/GenericUnion.lean)), nonemptiness supplies an approximation
to recover, and upward closure makes the filter contain *every* finite fact its object
validates ([`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean)). Coordinate
genericity is exactly totality of the partial object
([`forall_meets_coordReq_iff_isSome_unionFun`](../Forcing/GenericUnion.lean)).

**Scope.** This equivalence is a theorem about the finite-partial-function carrier, not about
filters on an arbitrary order. For a general forcing notion the certified statement is just
the definition — a filter is a nonempty, downward-directed, weakening-closed collection of
conditions; conditions need not be finite, and the *object* a filter presents exists carrier
by carrier. Reading the correspondence as an ideal/domain completion is an informal gloss, not
a formalized theorem.

## Tests: a requirement is a dense-open set

Requirements — persistent, attainable tests — are **exactly** the dense-open sets:

```text
Requirement P  ≃  {D : Set P // IsDenseOpen D}
```

([`Requirement.equivDenseOpen`](../Forcing/Order/Requirement.lean)); arbitrary dense tests
normalize to persistent ones without changing which filters meet them
([`meets_normalize_iff`](../Forcing/Order/Requirement.lean)).

The observer enters as a vocabulary of tests, nothing more: a
[`VisibilityContext`](../Forcing/Model/Visibility.lean) is the family of sets of conditions the
observer can see, and genericity over it
([`GenericOver`](../Forcing/Model/GenericOver.lean)) means passing every visible dense-open
test. Existence of generic filters is the countable-satisfiability theorem for that vocabulary
([`exists_pfilter_genericOver`](../Forcing/Model/GenericOver.lean)), with countability an
external hypothesis, never a field.

The certified separation witnesses support the expository ordering of the test vocabularies:
coordinate tests recognize totality but not avoidance
([`totality_separation`](../Forcing/Cohen/Diagonal.lean)); adding diagonal tests recognizes
avoidance of the designated reals but not full genericity
([`parity_separation`](../Forcing/Cohen/Diagonal.lean),
[`parityReal_avoiding_not_genericOver`](../Forcing/Cohen/Spectrum.lean)). These spectra are
theorems about specific filters, not a formalized hierarchy of test languages.

## Descriptions: a name is a conditional expression

A [`PName`](../Forcing/Name/Basic.lean) is an order-free, intensional, well-founded
set-building expression whose branches are conditioned on an oracle question `p ∈ S`.
Valuation ([`val`, `zval`](../Forcing/Name/Valuation.lean)) is defined against an *arbitrary*
condition set, and the exact prices are part of the design: constant expressions
([`check`](../Forcing/Name/Check.lean)) cost `[Top P]` to build and `⊤ ∈ S` to evaluate
faithfully ([`zval_check`](../Forcing/Name/Check.lean)); the reflective expression
([`genName`](../Forcing/Name/GenName.lean)) values, under the same `⊤ ∈ S`, to a faithful
material code of its oracle — distinct filters have distinct codes
([`eq_of_zval_genName_eq_pfilter`](../Forcing/Name/GenName.lean)).

Two certified failures shape the layer:

- **Valuation is not monotone in the condition set**: enlarging `S` can recursively *change*
  an element rather than add one
  ([`exists_not_zval_subset_zval`](../Forcing/Name/Valuation.lean)).
- **The unrestricted family collapses**: every ambient set has a check name, so the valuation
  image of *all* names is the whole universe
  ([`valuationImage_univ_eq_univ`](../Forcing/Name/ValuationImage.lean)). Restricting which
  descriptions belong to the ground is the mathematical content of "extension".

## The vocabularies and their variances

**Today** — certified and external, with the two vocabularies as independent data:

```text
           THE OBSERVER  (today: external, independent data)

        tests it can ask              descriptions it can form
      visible dense-open sets            available names
              │                                │
   more tests ⇒ fewer generic       more names ⇒ larger image
      filters (antitone)                (monotone)
              │                                │
              ▼                                ▼
      admissible generic G   ────▶   evaluate the names at G
```

**Planned** — after the material bridge (#62, milestone M5), both sides are projections of
one carrier:

```text
     THE MATERIAL GROUND  (right side certified; left side is #75)

                   material presentation of P
                    │                      │
            derived visible tests   internal name family N_M
              (planned — #75)        (certified — Names.lean)
                    │                      │
                    ▼                      ▼
            admissible generic G  ──▶  M[G], an indexed material set
                                      (certified — extensionCarrier)
```

Three variances, kept apart — the first two certified, the third a certified *failure*:

| Enlarge… | Effect | Certificate |
|---|---|---|
| the visible tests | fewer generic filters (antitone) | [`GenericOver.anti`](../Forcing/Model/GenericOver.lean) |
| the name family | larger valuation image (monotone) | [`valuationImage_mono`](../Forcing/Name/ValuationImage.lean) |
| the condition oracle `S` | neither — an element can *change* | [`exists_not_zval_subset_zval`](../Forcing/Name/Valuation.lean) |

Genericity *constrains* which generic oracles are admissible; valuation *generates* the sets a
chosen oracle determines — "world" stays reserved until the two vocabularies are
synchronized through one material presentation (#75); the indexed `M[G]` itself is now
certified. The Cohen
visibility context already couples an embryonic form of the pair — a test vocabulary
(`visible`) with a designated-object vocabulary (`designatedReals`) — as independent data
([`CohenVisibilityContext`](../Forcing/Cohen/Visibility.lean)); the bridge's job is to replace
"independent data" with two projections of one material presentation.

## The remaining arrows

The description side of the material bridge is **certified**: material carriers
([`MaterialCarrier`](../Forcing/Material/Carrier.lean)), the no-junk internal presentation
([`InternalForcingPresentation`](../Forcing/Material/ForcingPresentation.lean)), the internal
name family with smallness kept
([`InternalNamePresentation`](../Forcing/Material/Names.lean)), and `M[G]` as an indexed
transitive carrier ([`extensionCarrier`](../Forcing/Material/Extension.lean)), with the
ground-inclusion and generic-code memberships proved from semantic representatives
([`HasCanonicalNames.mem_extensionCarrier_of_mem`,
`HasCanonicalNames.zval_genName_mem_extensionCarrier`](../Forcing/Material/Extension.lean)).
What is deliberately not yet a theorem:

1. **Derived visibility and the Cohen synchronization** *(planned — #75)*: the visibility
   context obtained as externalizations of internal test codes (a material presentation must
   *carry* those codes; they do not follow from transitivity), `designatedReals` derived as
   the materially coded reals, `Sees` proved from membership laws rather than assumed, and
   the material avoidance upgrade that earns "adds a new real". For Cohen forcing the
   eventual endpoint is `M[G] = M[c_G]` against an independently characterized extension,
   not one made true by definition.
2. **The truth lemma** *(planned — M6)*: the forcing relation as the persistent local judgment
   whose motivation is already certified — raw valuation is unstable under new information
   (`exists_not_zval_subset_zval`) — connecting stable local truth to actual generic
   evaluation, with the regular-open Boolean-value description a comparison theorem thereafter
   (M9).

These are precisely the coherence theorems between the two vocabularies: the tests `M` can ask
and the descriptions `M` can form, synchronized through one material carrier.

---

This document is the *horizontal* story — what forcing is. The classical forcing properties
(ccc, closure, properness, homogeneity, …) form a vertical control theory over it — what a
particular forcing does and why; their discipline lives in [property-zoo.md](property-zoo.md).

Related: [why-genericity.md](why-genericity.md) derives the test side in discovery order;
[names.md](names.md) derives the description side the same way;
[architecture.md](architecture.md) records the layer boundaries and the qualified claims;
[ROADMAP.md](../ROADMAP.md) records per-milestone status.
