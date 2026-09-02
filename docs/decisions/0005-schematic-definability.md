# ADR 0005 — internal definability of forcing is schematic, not uniform

**Status: decided** (spike #154; gates M7 item 3, tracker #142).

## Context

Item 3 must define the forcing relation *inside* the ground. The tempting target is a single
internally definable predicate

```text
Force(p, formulaCode φ, assignmentCode a)
```

handling every formula code uniformly. Layer 4's coding makes that look available: formula
codes exist, `IsFormulaCode` parses them, and each code lies in the ground.

## Decision

**Do not define a uniform `Force`.** For trivial forcing such a predicate specializes to a
uniform truth predicate for the ground, which at the intended strength contradicts Tarski's
theorem. The definability theorem is **schematic**:

1. atomic membership and equality get fixed, uniform internal definitions on condition and
   name codes;
2. an **external compiler** `forcesDef : memLang.BoundedFormula (Fin k) n → memLang.BoundedFormula …`
   produces a defining formula for each external formula;
3. structural induction proves that `forcesDef φ` realizes exactly `ForcesFormula … φ`;
4. layer 4's finite-closure theorem shows each individual `forcesDef φ`'s code lies in the
   ground.

`formulaCode` and `IsFormulaCode` remain valuable — for parsing, coding transformations,
scheme indexing, and proving each defining formula internally available. **They must not be
turned into an internal full truth predicate.** The uniformity that Tarski forbids is
uniformity in `φ`; uniformity in the *name codes* (the atomic recursion) is fine, and is
exactly what 3b provides.

## The split

* **3a** — named Separation and Collection scheme infrastructure, plus the Foundation
  sentence. (**Corrected**: this originally said "Replacement/Collection". Replacement is
  absent from the implementation — `collectionSentence` asserts no functionality and has no
  reverse clause, so it is Collection, not Replacement or Strong Collection. The Foundation
  sentence exists for general semantics but is *free* for material carriers; see below.)
* **3b** — uniform definability of `ForcesMem`/`ForcesEq` by internal well-founded recursion
  on name codes.
* **3c** — the external compiler and its per-formula correctness theorem.

## Spike findings

The prototype compiled the compiler skeleton and the atomic recursion skeleton, with each
remaining obligation isolated as a sorry annotated by the axiom it needs.

**Where the costs actually are (3b).** The recursion is the usual "there is a coherent
computation covering this pair of name codes":

* ~~**Foundation** — uniqueness of the computation, by ∈-induction on the pair;~~
  **Falsified** — see the amendment below.
* **Separation + Collection** — existence: carving the computation out of the candidate
  partial computations and collecting the stage approximations;
* **Infinity — only for uniformity in the pair.** The existence statement takes a transitive
  set containing the two codes as a *parameter*; the recursion itself never needs Infinity.
  Supplying such a set for arbitrary codes is transitive closure, and *that* is what costs
  Infinity. The distinction is the spike's main result: **Infinity constructs uniformity, not
  the recursion.** 3b should therefore state the parameterized version first and charge
  Infinity only where the uniform version is actually wanted.
* **No Power Set.** The candidate computations are bounded by Collection over a fixed
  transitive set, not by a power set. Recorded as a negative finding — if an implementation
  reaches for Power Set, that is a signal the construction has drifted.

### Amendment: the Foundation prediction was falsified

The spike predicted **Foundation** for uniqueness of the computation. That prediction is
**wrong**, and PR #160 proved it so: Foundation is *free* for material carriers.

The reason is that uniqueness is established externally, by well-founded induction on the
ambient `ZFSet` membership relation, together with transitivity of the carrier. The metatheory
already supplies the well-foundedness; nothing needs to be assumed of the ground theory. The
implemented uniqueness results (`agreeAt_of_correctOn`, `correctOn_unique`) consume coherence,
descent-closure, and ambient rank, and cite no Foundation sentence.

Amended rather than rewritten, so that the record shows the spike made a prediction that the
implementation refuted. A decision record that quietly absorbs its own errors cannot be used
to calibrate the next spike.

### Amendment: the Infinity prediction was confirmed

The spike's main result — **"Infinity constructs uniformity, not the recursion"** — held
exactly. `MaterialGround.exists_atomicCoherentOn` takes the transitive domain as a parameter
and is priced without Infinity; `infinitySentence` occurs nowhere in `Recursion.lean`,
`RecursionSchemes.lean`, or `RecursionExistence.lean`, and this is checked rather than
asserted. Infinity was charged separately, and only for supplying a uniform ambient domain.

Recording a confirmed prediction alongside a falsified one is what makes the spike method
auditable: the same record shows which parts of the cost estimate were reliable.

### The implemented parameterized ledger

What `exists_atomicCoherentOn` actually charges, read off the compiled construction:

* **17 named Separation/Collection instances** — six for the aggregation layer, eleven for the
  fixed-point construction;
* **Pairing, Binary Union** — finite closure, for entries and the two-tag bound. **Not Empty
  Set**: `entry_mem` takes each tag's numeral as a hypothesis, and every consumer holds the tag
  as a carrier element with its defining equation. Empty Set enters only when the numerals are
  actually built, which happens once, at composition with the ambient domain;
* **General Union** — the flattening steps.

Absent: **no Foundation, no Infinity, no Power Set.** The Power Set negative finding recorded
above held; nothing in the construction reached for it.

The instance count was discovery-driven throughout — read off what compiled, not targeted. An
early estimate of four proved low by more than a factor of four, mostly because each
aggregation level needs its own gather/filter pair and the predecessor set needs three
instances of its own.

### Amendment: general Union is charged (row-wise prototype)

The original findings did not mention Union, and that was an omission. Implementation chose
the **row-wise** indexing for the recursion — for a fixed first coordinate, gather stage
values over the second — rather than indexing by coded pairs from `A × A`. Building `A × A`
inside the carrier would be material bookkeeping rather than mathematical content, and the
entries already retain both coordinates, so row aggregation loses no information.

A prototype carried that route through to its flattening step and isolated exactly one
obligation:

* **Per-state entry bounds are Union-free.** One Collection instance, used at *both* tags by
  varying its parameters, produces a bound at each tag; `binaryUnionSentence` combines them.
  The witnesses are individual entries, so nothing is flattened.
* **The row family is Union-free.** One Collection instance over the domain gathers the stage
  values.
* **The flattening is not.** Collection over the domain yields a set whose members are stage
  *sets*; the graph needs their entries. No bound on the members-of-members of an arbitrary
  collected family is available from the binary fragment, so **`unionSentence`, a genuine
  general Union axiom, is charged**. It is a named sentence with `MaterialGround.sUnion_mem`
  as its consequence, not an ambient `ZFSet` construction.

This is a dependency finding for the compiled row-wise construction, not an impossibility
theorem for every alternative construction. The ledger records the cost of the construction
actually being formalized; if a later proof avoids Union, the theorem is weakened and this
record amended.

General Union subsumes binary union given pairing (`union_mem_of_sUnion`), so this is one new
axiom of genuine strength, not two. Both sentences stay on the ledger so that each theorem
records the strength it actually uses.

**Still absent, and still load-bearing as negative findings**: no Power Set, and no Infinity
outside the final uniform-in-the-pair theorem.

**Constraints the row design must meet**, and against which the eventual construction is to be
checked: rows are an internal aggregation device only, with `rankPair` remaining the recursion
order; junk from nonfunctional Collection is filtered before it can enter the graph; and the
final object satisfies exact `AtomicCoherentOn`, not merely "contains a witness stage for
every pair". The instance count is to be read off the compiled construction — the working
estimate of four is not a target.

**The compiler is cheap (3c)**, as expected, with two findings:

* **Assignment lookup is finite.** Because the compiler runs per formula, the arity `n` and
  each index are fixed numerals, so reading the `i`-th entry of the reversed snoc-list is a
  *fixed finite block* of existentials. No internal recursion and no scheme is needed for
  assignments — layer 3's snoc law is the whole interface, and no syntactic substitution
  appears anywhere.
* **Projections are relational.** The language is function-free, so lookup and pairing are
  expressed by relations rather than terms: cheap, but syntactically bulky, and worth a
  helper (`pairDef`, `lookupDef`) rather than inline repetition.

The compiler's cases are otherwise light: falsum to falsum; equality and membership invoke
the two atomic definitions; implication quantifies over coded strengthenings; universal
quantification ranges over internally recognized name codes and extends the coded assignment
by pairing.

### Amendment: 3c's implemented shape

3c landed as `forcesDef` with `forcesDef_correct` (#224; tracker #158). Two findings that the
spike did not predict, recorded here so the ADR matches the code:

* **Correctness is one simultaneous induction, not two directional ones.** `ForcesFormula`'s
  implication clause is contravariant, so proving external forcing → compiled realization at
  `φ.imp ψ` needs compiled → external at `φ`, and conversely. The theorem proves the
  conjunction in a single structural induction, crossing projections at `.imp`; the two
  directional theorems are its components.
* **Pairing is reused at one site and charged to both directions.** The universal case
  introduces the extended assignment by a *guarded universal* (`∀' (pairDef c a a' ⟹ …)`), so
  the syntax asserts no existence. Compiled → external at `.all` must then build that
  assignment, as a single pair of two elements already in hand: pair closure is used exactly
  there, Empty Set is not charged, and — through the mutual recursion — pair closure is a
  hypothesis of both directions.

Two further points confirmed rather than amended: the `.imp` guard must assert condition-set
membership alongside the coded order (`order_iff` permits junk pairs; #223), and the universal
case is **parametric in an internally supplied name recognizer** (`InternalNameRecognition`),
which #218 showed is not derivable from the name-coding fields. The material corollary adds
**no theory cost beyond 3b's ledger**: Pairing was already there.

## Consequences

3a formalizes the schemes as *named, instance-indexed* sentence families, consistent with the
ledger discipline: an instance is cited where it is used, and a scheme is never assumed
wholesale. 3b states the parameterized recursion first. 3c consumes both and produces the
per-formula correctness theorem — the honest form of "the forcing relation is definable over
the ground". The spike prototypes are scratch and are not committed; this record is the
durable output.
