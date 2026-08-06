# Why forcing?

The third discovery-order document: [why-genericity.md](why-genericity.md) derived the tests,
[names.md](names.md) the descriptions; this chapter derives the **forcing relation** — the
persistent local semantics connecting them — in the same format: each definition is
introduced by the specific failure it repairs, and every repair and every failure links to
the declaration that certifies it.

---

## 1. Raw valuation is unstable under new information

> **Attempt.** Reason about the extension directly from partial valuations: as the set of
> accepted conditions grows, name values should gradually accumulate.
> **Failure**, certified:
> [`exists_not_zval_subset_zval`](../Forcing/Name/Valuation.lean) exhibits `S ⊆ S'` whose
> values along a two-level name are `{∅}` and `{{∅}}` — enlarging the oracle recursively
> *changes* an existing element rather than adding one.
> **Repair.** Demand a **local judgment attached to a condition**, stable under
> strengthening, that speaks about every admissible future evaluation.

Be explicit about what this failure buys: it **motivates** the forcing relation — it does not
derive it. The relation must also deliver uniform truth across generic evaluations (§9), and
must eventually admit internal definability over the ground (M7). The nonmonotonicity is the
opening wound, not a characterization.

## 2. The persistent judgment

The atomic relations, by the standard density clauses
([`ForcesMem`, `ForcesEq`](../Forcing/Name/Atomic.lean)), and the formula relation by direct
recursion ([`ForcesFormula`](../Forcing/Name/FormulaForcing.lean)) — never via Boolean
values. Persistence is a theorem at every level:
[`ForcesMem.mono`, `ForcesEq.mono`](../Forcing/Name/Atomic.lean),
[`ForcesFormula.mono`](../Forcing/Name/FormulaForcing.lean).

**The first distinction worth protecting**: raw valuation is nonmonotone as the *oracle*
grows (§1); forcing is persistent as the *condition* strengthens. These are different axes —
the overview's variance table keeps them apart — and the whole design of the relation is that
the second axis behaves where the first does not.

## 3. The recursion is structural, not rank-based

Equality invokes membership in both orientations, so the recursion descends on the
**unordered pair** of names: the immediate-subname relation is well-founded
([`subname_wellFounded`](../Forcing/Name/Subname.lean)) and feeds `Sym2.GameAdd`, whose
swap constructor absorbs the orientation change with no separate left/right components. The
implementation mechanics stay subordinate to the mathematical dependency: names are
well-founded trees, and atomic truth descends along subnames.

## 4. Truth below a condition creates local tests, not global ones

The membership clause makes a set dense only *below* `p`, while genericity meets **global**
visible dense-open tests. The bridge is localization
([`localizeBelow`](../Forcing/Order/Localize.lean)): pad the downward closure with
everything incompatible with `p`. A locally dense test globalizes to a dense-open one
([`isDenseOpen_localizeBelow`](../Forcing/Order/Localize.lean)), and through `p` the padding
is invisible — meeting the localization is *equivalent* to meeting the original
([`meets_localizeBelow_iff`](../Forcing/Order/Localize.lean)).

## 5. Density-regularity: failure of forcing is persistent too

Forcing is equivalent to forcing being dense below
([`forcesFormula_iff_isDenseBelow`](../Forcing/Name/FormulaForcing.lean)). The reverse
direction is the engine of everything that follows: failure of forcing yields a
strengthening below which forcing is *impossible* — a persistent blocker
([`exists_blocker_of_not_forcesFormula`](../Forcing/Name/FormulaTests.lean)). The atomic
instances ride `IsDenseBelow.trans`, the coverage lemma in forcing-order form.

## 6. Atomic adequacy, and its asymmetric budgets

The mutual endpoint
([`forces_adequacy`](../Forcing/Name/AtomicAdequacy.lean)): along a filter meeting the right
tests, forced membership and equality coincide with actual membership and equality of the
valuations. The budgets are asymmetric, and each direction charges exactly its own family:

- **soundness** pays the localized membership witnesses —
  `localizeBelow (memWitness τ σ) p`;
- **completeness** pays the equality decision test —
  [`eqDecision`](../Forcing/Name/AtomicAdequacy.lean), the forcing-equality set padded with
  the two membership-obstruction families, globally dense open
  ([`isDenseOpen_eqDecision`](../Forcing/Name/AtomicAdequacy.lean)).

## 7. The connective tests

Each connective gets its own decision test — a uniform "forcers plus blockers" set is
avoided deliberately; its obstruction-soundness would be circular at the current formula.
A failed implication supplies a forced antecedent with a consequent blocker
([`impDecision`](../Forcing/Name/FormulaTests.lean)); a failed universal supplies a name with
an instance blocker ([`allDecision`](../Forcing/Name/FormulaTests.lean)). The recursively
required tests are packaged as a family
([`formulaTests`](../Forcing/Name/FormulaTests.lean)), every member dense open
*structurally* ([`isDenseOpen_of_mem_formulaTests`](../Forcing/Name/FormulaTests.lean)) —
and the atomic budgets remain separate: three budgets, no more.

## 8. Quantifiers are name-family-relative

The universal quantifier ranges over a **name family** `𝒩` — never over all of `PName P`,
which would reproduce the certified collapse
([`valuationImage_univ_eq_univ`](../Forcing/Name/ValuationImage.lean)): evaluating all names
yields the ambient universe, not an extension. For the material extension `𝒩 = N.names`, and
the carrier-quantifier bridge
([`forall_extensionCarrier_iff_names`](../Forcing/Material/Semantics.lean)) makes the
relativity exact: quantifying over `M[G]` *is* quantifying over the internal names.

## 9. The truth lemma

The observer-free endpoint
([`truth_lemma`](../Forcing/Material/TruthLemma.lean)):

```text
φ.Realize (extVal-valued assignments)  ↔  ∃ p ∈ G, ForcesFormula N.names v p φ xs
```

under exactly the three budgets — atomic membership, atomic equality, and the formula-test
family. Then the milestone theorem, the audited headline:
[`truth_lemma_of_genericOver`](../Forcing/Material/TruthLemma.lean) — observer-relative
genericity plus explicit visibility obligations yields truth in the extension carrier.
**Genericity's exact role is only to convert visible dense-open tests into meetings**; every
test's dense-openness is structural, so visibility is the observer's entire obligation.
Sentences specialize through the `⊩[𝒩]` notation
([`truth_lemma_sentence`](../Forcing/Material/TruthLemma.lean)).

## 10. The honest boundary

What this chapter deliberately does not provide: **no countability** anywhere in the truth
lemma (countability remains existence-side, as everywhere since M2); no definability of the
relation over the ground; no ZFC in `M[G]`; no preservation theory; no Boolean values (a
comparison theorem, milestones away).

**The second distinction worth protecting**: M6 proves an *external* semantic truth lemma
with **explicit** visibility obligations. M7's job is internality — prove those obligations
from the material presentation, internalize the relation, and establish definability and the
ZFC consequences. M6 explains forcing truth and exactly prices its visibility needs; M7 can
concentrate entirely on internality.

---

## What each ingredient costs

| Ingredient | Needs | Certificate |
|---|---|---|
| The persistent judgment | the order alone | [`ForcesFormula.mono`](../Forcing/Name/FormulaForcing.lean) |
| The recursion | well-founded subnames | [`subname_wellFounded`](../Forcing/Name/Subname.lean) |
| Globalizing local truth | lower closure + incompatibility padding | [`meets_localizeBelow_iff`](../Forcing/Order/Localize.lean) |
| Blocker extraction | density-regularity | [`forcesFormula_iff_isDenseBelow`](../Forcing/Name/FormulaForcing.lean) |
| Atomic adequacy | the two atomic budgets | [`forces_adequacy`](../Forcing/Name/AtomicAdequacy.lean) |
| Formula truth | + the formula-test family | [`truth_lemma`](../Forcing/Material/TruthLemma.lean) |
| Truth from genericity | visibility of the tests, nothing more | [`truth_lemma_of_genericOver`](../Forcing/Material/TruthLemma.lean) |

---

Related: [why-genericity.md](why-genericity.md) and [names.md](names.md) are the first two
chapters; [conceptual-overview.md](conceptual-overview.md) states the architecture all three
converge on; [architecture.md](architecture.md) carries the normative constraints. Internal
definability is the next chapter (M7); Boolean values are a comparison theorem two chapters
away (M9).
