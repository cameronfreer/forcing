# ADR 0006 — the internal name family is the maximal hereditarily valid one

**Status: decided** (spike 2026-09-04 on #219; gates M7 item 5, tracker #142).

## Context

M7 items 3 and 4 are complete: `MaterialGround.truth_lemma_of_genericOver` discharges every
M6 visibility budget from internal codes. The theorem is **parametric in an
`InternalNameRecognition`** — an internal unary formula recognizing exactly the range of a name
presentation's `code`. #218 showed such a recognizer cannot be derived from the name-coding laws:
they constrain known codes, not the *range* of `code`. So the sole remaining applicability gap is
one concrete object: a name presentation whose range is describable, together with its recognizer.

The 4b closure audit (#227, #230) found that items 3 and 4 impose **nothing on the family's
shape**. The compiler and the tests consume only exact recognition, `InternalNameCoding`, the
presentation's own fields, and pair closure. Richness is a requirement of the intended Cohen
development, not of the theorem pipeline.

## Decision

**The internal name family is the maximal natural one.**

```text
Code    := the carrier elements that are hereditarily valid name codes
code    := the underlying set
decode  := well-founded recursion on the coded branches
```

with hereditary validity the least fixed point

```lean
inductive IsNameCode (cs : ZFSet) : ZFSet → Prop
  | mk (x) (branch : ∀ y ∈ x, ∃ c e, y = ZFSet.pair c e ∧ c ∈ cs)
      (sub : ∀ y ∈ x, ∀ c e, y = ZFSet.pair c e → IsNameCode cs e) : IsNameCode cs x
```

Three reasons, in order of weight: the range is canonical and *describable*, rather than a family
selected to make recognition easy; subname closure and both `InternalNameCoding` laws follow from
the definition; and recognition is separated from Cohen richness — check names, the generic name,
and the Cohen-real name are later *proved to belong* to this family when their material codes are
constructed, rather than being built into it.

### Three binding clauses

1. **"Maximal" is a theorem, not a name.** The presentation must prove that every carrier element
   satisfying `IsNameCode` occurs in `Set.range N.code`. This is what makes the recognizer
   *exact* rather than merely sound: `realize_iff`'s completeness direction reduces to it.
2. **`Shrink` is strictly a universe bridge.** `PName`'s branch index lives in `Type u` while
   carrier elements live in `Type (u + 1)`, so `Code` is `Shrink.{u}` of the valid carrier
   subtype and each branch index is `Shrink.{u}` of a code's member type (mathlib's
   `ZFSet.small_coe`). That representation must not leak into downstream APIs: consumers see
   only `Code`, `code`, and `decode`, and no theorem outside the presentation's own module
   mentions `Shrink` or `equivShrink`.
3. **Do not yet generalize `UnionIteration`.** Certificate completeness (below) is a second
   consumer of ω-iteration, so the consumer-gating trigger has fired. But the decision is
   deferred to a bounded tranche-2 signature audit: generalize to a definable step **only if**
   the abstraction keeps every scheme cost formula-indexed and visible, and leaves the existing
   union iteration as a clean specialization. Otherwise implement a parallel descendant
   iteration and accept the duplication.

## The split

* **Tranche 1 — the external presentation.** `IsNameCode`, `decode`, `decode_injective`, the
  presentation, `subname_closed`, `InternalNameCoding`, the maximality theorem, and the
  certificate's soundness half. **Axiom-free**: no theory sentence is charged.
* **Tranche 2 — internal recognition.** The certificate as a formula, completeness, and the
  concrete `InternalNameRecognition`, with the descendant-closure ledger mined from the compiled
  proof.
* **Tranche 3 — richness pressure tests.** The empty name and a branch constructor are
  represented. Check, generic, and Cohen-real representatives are **item 7**, and must not enter
  #219 by accident.

## Spike findings

**`decode` typechecks and is injective.** The universe mismatch is real and `Shrink` resolves it
(clause 2). Injectivity is needed by `branch_mem_code_iff`'s backward direction — the law
produces a code whose *decode* matches a branch's subname and needs the *code* to match — and is
not immediate: equality of two `PName.mk` values yields only a type equality between index types.
The proof goes through a generalized index-matching lemma across that type equality, then rank
induction, recursing through the symmetric equation so the measure decreases on the right side.
Compiled in scratch on standard axioms.

**The certificate.** The recognizing formula is

```text
∃ D, x ∈ D ∧ ∀ z ∈ D, ∀ y ∈ z, ∃ c e, y = ⟨c, e⟩ ∧ c ∈ condSet ∧ e ∈ D
```

an existential, set-sized domain containing the candidate, closed under decoded subname edges,
every node locally branch-shaped. It is per-candidate, so there is no master name set.

* *Soundness* (certificate → `IsNameCode`) is rank induction. Compiled, axiom-free.
* *Completeness* (`IsNameCode x` → some `D` in the carrier) is where the cost is. The witness is
  the set of branch-descendants of `x`, `D = ⋃ₙ Dₙ` with `D₀ = {x}` and
  `Dₙ₊₁ = {e | ∃ z ∈ Dₙ, ∃ c, ⟨c, e⟩ ∈ z}`. Every descendant sits at finite depth, so an
  **ω-iteration suffices — of the descendant step, not `⋃₀`**. A transitive `A ∋ x` from
  `exists_transitiveDomain` bounds every `Dₙ`, so each step is a Separation over `A`. Expected
  ledger: the shape of `exists_transitiveDomain` — Infinity, `omegaSep`, one Collection instance,
  Separation instances for filter and approximation existence/uniqueness, Pairing, Binary Union,
  General Union.
* **No Power Set.** The routes that avoid ω — the greatest fixed point, or quantifying over
  subsets of `A` — are exactly the ones that need it, and are rejected. Power Set anywhere in
  tranche 2 is a stop-and-review signal.

## Consequences

Tranche 1 lands first as a code PR with no theory cost. Tranche 2 closes item 5 for every name
the maximal family contains, and item 7 then shows the Cohen names are in it. Until the
recognizer actually exists, #161, the ROADMAP, and the M7 status remain unchanged: a parametric
theorem with no instance is not yet a theorem about a name family.
