# Why genericity?

Chow's [*A beginner's guide to forcing*](https://arxiv.org/pdf/0712.1320) names genericity as the
weakest point of the standard exposition: dense sets and generic filters work beautifully once
introduced, but they seem to arrive from nowhere. This document is the library's answer, in
**discovery order** — each definition is introduced by the specific failure it repairs, and every
repair and every failure links to the declaration that certifies it.

The module dependency order is different, and deliberately so. Read `ROADMAP.md` for what is
built when; read this for why anything is built at all.

**Two conventions.** `q ≤ p` means `q` is a *stronger* condition (smaller is stronger). And
`J_total`, `J_new`, `J_full` below are **expository names for families of tests**, not Lean
structures — the library has no `GenericityDoctrine` type, and the comparisons between them are
theorems about specific filters, not about a formalized hierarchy.

---

## 1. Finite approximations must cohere: why filters

We want to build an infinite object — say a function `ℕ → Bool` — from finite approximations.
Conditions are finite partial functions ([`FinitePartialFunction`](../Forcing/FinitePartialFunction.lean)),
ordered by reverse inclusion.

> **Attempt.** Take an arbitrary set of finite approximations and glue them.
> **Failure.** Two approximations may disagree, and the glue is not a function.
> **Repair.** Require any two members to have a common strengthening **inside** the collection
> ([`exists_mem_le_le`](../Forcing/Order/Filter.lean)).

That single property — *directedness* — is exactly what makes the union well defined:
[`unionGraph_unique`](../Forcing/GenericUnion.lean). Note what the proof uses — only the common
strengthening — so it is independent of the index type, the value type, and the representation.

A *filter*
([`Order.PFilter`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/PFilter.html))
demands two further properties that this failure does **not** motivate: **nonemptiness**, and
**upward closure** — every weakening of a member is a member. Coherence uses neither, and a
discovery-order account should not smuggle them in. Both are bought later: upward closure by
normalization invariance (§8) and by recovery (§9), nonemptiness by recovery alone (§9). Until
then, everything proved about the union uses directedness alone.

## 2. A filter can still be partial: coordinate requirements

> **Attempt.** Take an arbitrary filter.
> **Failure.** Nothing forces it to decide any particular coordinate, and this is not a
> hypothetical: the principal filter at the weakest condition has a union that is *nowhere*
> defined — [`unionFun_principal_top`](../Forcing/GenericUnion.lean).
> **Repair.** Demand that the coordinate be decided:
> [`coordReq i`](../Forcing/GenericUnion.lean).

`coordReq i` is not an ad-hoc set. It is a *requirement*: a task that is **persistent** (once
achieved, more information cannot destroy it) and **attainable** (from any condition it can still
be achieved). Those two properties are the whole content of §8 below.

## 3. Coordinate requirements give totality — and existence is a separate theorem

Meeting every coordinate requirement makes the union total:
[`isSome_unionFun`](../Forcing/GenericUnion.lean), and in Cohen dress
[`isSome_genericFun`](../Forcing/Cohen/Generic.lean).

This is the first place where two different obligations are easy to conflate, so the library
keeps them apart:

| | **Adequacy** | **Existence** |
|---|---|---|
| Question | *If* a filter meets these tests, does the conclusion follow? | Does such a filter exist at all? |
| Cohen instance | [`isSome_unionFun`](../Forcing/GenericUnion.lean) | [`exists_pfilter_total`](../Forcing/GenericUnion.lean) |
| Depends on | nothing but the tests | attainability of every requirement, plus countability of the family |
| Proved by | unfolding the requirement | [Rasiowa–Sikorski](../Forcing/Order/RasiowaSikorski.lean) |

**Adequacy without existence is vacuous** — every statement of the form "every filter meeting
these tests satisfies `Φ`" is true when no such filter exists. The two are therefore separate
declarations, never bundled.

## 4. Totality is not enough: the first strict separation

> **Attempt.** Meet only the coordinate requirements.
> **Failure.** The union is total but may be a function we already had. Formally, for any real
> `x`, the canonical filter of `x` meets every coordinate requirement and *cannot* differ from
> `x`: [`totality_separation`](../Forcing/Cohen/Diagonal.lean).

Call the coordinate tests `J_total`. The failure is not a limitation of the proof; it is a
theorem that `J_total` is too weak for the next conclusion.

## 5. Diagonal requirements, added cumulatively

> **Repair.** Demand also that the object differ from each real in a supplied family:
> [`diagReq x`](../Forcing/Cohen/Diagonal.lean).

Attainability is where finiteness earns its keep: a condition decides only finitely many
coordinates ([`exists_lookup_eq_none`](../Forcing/FinitePartialFunction.lean)), so a fresh one is
free, and `Bool` supplies a different value to put there. (Generalizing to `Fn(κ, λ)`, these two
facts become "`κ` infinite" and "`λ` nontrivial" — see
[ADR 0001](decisions/0001-cohen-carrier.md).)

Write `J_new` for the coordinate tests **together with** the diagonal ones. The cumulativity is
not cosmetic: the diagonal tests alone would not make the union total, so `J_total < J_new` would
not even be the comparison being claimed.

## 6. Diagonalizing a countable family

Meeting a diagonal requirement forces disagreement
([`exists_ne_of_meets_diagReq`](../Forcing/Cohen/Diagonal.lean)), and Rasiowa–Sikorski supplies
the filter, because `J_new` is countable when the family is:
[`exists_pfilter_total_diagonalizing`](../Forcing/Cohen/Diagonal.lean). The accumulation is
literally a sum — the proof indexes `J_new` by `ℕ ⊕ ι` and applies Rasiowa–Sikorski once — so
cumulativity of doctrines rides on countability being closed under countable sums. That looks
like bookkeeping here; §10 shows how the same countability discipline reappears when the
observer's visible tests are enumerated.

**This is the M2 result, and it is not "adds a real."** The conclusion is about the *supplied*
family. There is no ground model in the statement, so there is nothing for "new" to mean. The
over-`M` theorem is [`exists_pfilter_genericOver_new`](../Forcing/Cohen/NewReal.lean) (§10).

## 7. Diagonalizing is still not genericity: the second strict separation

> **Attempt.** Meet every coordinate and every diagonal requirement.
> **Failure.** The result can still miss a dense open set.

The witness is explicit — no perfect sets, no cardinality argument. Let
[`parityReal x`](../Forcing/Cohen/Diagonal.lean) disagree with `x n` at coordinate `2n` and be
`false` at every odd coordinate. Its canonical filter meets every coordinate requirement and
every diagonal requirement, yet misses
[`oddTrue`](../Forcing/Cohen/Diagonal.lean) — the conditions putting `true` at some odd
coordinate: [`parity_separation`](../Forcing/Cohen/Diagonal.lean), restated with all three
conclusions in
[`parity_separation_total_diagonalizing`](../Forcing/Cohen/Diagonal.lean).

`oddTrue` is dense **open** ([`isDenseOpen_oddTrue`](../Forcing/Cohen/Diagonal.lean)), which is
what places it in `J_full` — the family of all dense open tests. Density alone would not have
sufficed, since `J_full` is a family of *persistent* tasks.

So the spectrum is strict at both steps, and both steps are proved:

```text
J_total  <  J_new  <  J_full
   │          │
   │          └── parity_separation
   └── totality_separation
```

Both separations were proved the same way, and the method deserves a name. Each witness filter
is the canonical filter of a real we *wrote down* — `x` itself in §4, `parityReal x` here — and
each is defeated by a test that detects a law its definition obeys. The library certifies two
instances: the law "equals this particular real `c`" always has the detector `diagReq c`, and
the parity witness additionally obeys "`false` on the odd coordinates", detected by the
parameter-free `oddTrue` — a stronger detector special to that construction. (No claim is made
that every informally described law has a dense-open violation test.) §10 turns this pattern
from a proof technique into the reason a ground model must enter.

## 8. Where "dense" comes from

Nothing in the formulation of the failures and repairs above required density as a primitive
notion. (The existence proof uses density internally; requirements supply it automatically from
local attainability.) What the repairs needed was **persistent, attainable tasks** — and those
are *exactly* the dense open sets:
[`Requirement.equivDenseOpen`](../Forcing/Order/Requirement.lean), an equivalence with both round
trips definitional.

And nothing is lost by insisting on persistence, because an arbitrary dense test has a canonical
persistent form — its downward closure — that the same filters meet:
[`meets_normalize_iff`](../Forcing/Order/Requirement.lean).

This is where the filter's *upward closure*, left deliberately unmotivated in §1, earns its
first keep. `meets_normalize_iff` is [`meets_lowerClosure`](../Forcing/Order/Filter.lean), and
its proof is one of exactly two places the story in this document uses closure under weakening
(`Order.PFilter.mem_of_le`): a filter containing a strengthening of a test element must contain
the test element itself. The two closures are dual and pay for each other — tests may be closed
**downward** at no cost precisely because filters are closed **upward**.

That is the answer to Chow's complaint. Dense open sets are not an inspired combinatorial trick;
they are the tasks one can impose on an object built by finite approximation, and the persistence
requirement costs nothing.

Genericity for requirements is not a new predicate either — it is
[`GenericFor`](../Forcing/Order/Filter.lean) of the supports
([`genericFor_support_iff`](../Forcing/Order/Requirement.lean)).

## 9. Faithful observability: the object determines the filter

A filter yields an object. Does the object yield the filter back?

Yes, and the two directions have different costs:

- **object → filter** needs no genericity whatsoever:
  [`ofFunction`](../Forcing/GenericUnion.lean) is defined for any total function.
- **filter → object → filter** holds with no genericity, totality, or fiber-nonemptiness
  hypothesis: every filter is the canonical
  filter of its own *partial* union
  ([`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean)), and the total case
  [`eq_ofFunction`](../Forcing/GenericUnion.lean) is its specialization along the union
  equation — carrying no genericity and no fiber-nonemptiness hypothesis.

So faithful recovery is genericity-free in both directions, and it is stated as its own theorem
rather than folded into any adequacy claim. Indeed the correspondence is exact:
[`pfilterEquivPartialFunction`](../Forcing/GenericUnion.lean) makes filters of finite partial
functions *equivalent* to partial objects, with both inverse laws
([`unionFun_ofPartialFunction`](../Forcing/GenericUnion.lean),
[`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean)) and no genericity, totality, or
fiber-nonemptiness hypotheses. Arbitrary
filters are partial objects; coordinate-generic filters are exactly the total ones
([`forall_meets_coordReq_iff_isSome_unionFun`](../Forcing/GenericUnion.lean), with extraction
by [`totalUnion`](../Forcing/GenericUnion.lean)); and `ofFunction` is the total inclusion.

Recovery is also upward closure's second — and decisive — appearance. The recovery inclusion
([`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean), through which `eq_ofFunction`
now factors) invokes closure under weakening exactly once, and that one step is the whole
difference between a filter and a merely directed set. Directedness alone cannot make the object
determine the collection: the chain of restrictions of `c` to `{0, …, n}` is directed and has
union `c`, yet is a proper subset of `ofFunction c`. (That counterexample is informal — the
library does not formalize directed non-filters.) Upward closure says the filter contains
*every* finite fact its object validates, and that maximality is exactly what recovery recovers.

Nonemptiness is bought by recovery too, more quietly. The empty collection is directed and has
the same nowhere-defined union as the principal filter at `⊤` — but only the latter is a filter,
and only a filter guarantees there is an approximation to recover: the base case of
[`exists_mem_le_of_forall_unionGraph`](../Forcing/GenericUnion.lean), the assembly step that
`ofPartialFunction_unionFun` consumes, opens with `G.nonempty`. Equivalently, a starting
condition supplies nonemptiness for free — which is why Rasiowa–Sikorski threads `p ∈ G`
through every existence statement.

The ledger opened in §1 is now balanced:

- **directedness** — the union is functional
  ([`unionGraph_unique`](../Forcing/GenericUnion.lean));
- **nonemptiness** — there is an approximation to recover, including for the empty partial
  function ([`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean));
- **upward closure** — meeting is invariant under normalization
  ([`meets_normalize_iff`](../Forcing/Order/Requirement.lean)), and every finite fact the object
  validates belongs to the filter
  ([`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean)).

No filter axiom is a convention: each is the exact price of a named theorem — and the three
prices together buy exactly the equivalence between filters and partial objects.

## 10. Fixing the observer: the ground context

The two separations instantiate one phenomenon. Each witness filter is `ofFunction` of a real
given by an explicit definition, and each is defeated by a detector for a law that definition
obeys. The library certifies two instances of the pattern: for any real `c`, the law "equals
`c`" has the detector `diagReq c`
([`totality_separation`](../Forcing/Cohen/Diagonal.lean)); and the parity witness — built from
the very family it diagonalizes — obeys the further law "`false` on the odd coordinates",
detected by `oddTrue` ([`parity_separation`](../Forcing/Cohen/Diagonal.lean)). The broader
reading suggested by the pattern — every explicitly constructed filter obeys *some* law with a
dense-open detector, so enlarging the supplied family merely restarts the game — is
**informal**: this document proves the two rounds above and asserts no general regress theorem.
But even the certified instances point at the right repair, and it is not "add tests one at a
time."

Fix the *observer* instead of the tests. The ground model enters the library as the minimal
interface that makes "visible to `M`" a hypothesis rather than a metaphor:
[`GroundContext`](../Forcing/Model/Ground.lean) is nothing but the family of sets of conditions
`M` can see. Genericity over it is not a new notion —
[`GenericOver`](../Forcing/Model/GenericOver.lean) is `GenericFor` of the visible dense-open
family, i.e. `J_full` relative to `M`, and at the all-seeing context it collapses back to the
absolute `J_full` ([`genericOver_full_iff`](../Forcing/Model/GenericOver.lean)). The passage
from visibility to meeting is generic, not Cohen-specific: a generic filter meets every visible
requirement ([`GenericOver.meets_requirement`](../Forcing/Model/Requirement.lean)).

The Cohen instance adds the designated ground reals
([`CohenGroundContext`](../Forcing/Cohen/Ground.lean)) and records — as an explicit interface
obligation, not a closure property hidden inside visibility — the bridge

```text
x ∈ M.groundReals   →   Visible M ((diagReq x).support)
```

formalized, with its coordinate companion, as
[`Sees.visible_diagReq`](../Forcing/Cohen/Ground.lean). The abstract context *exposes* this
obligation; a later material ground model must *prove* it. Granted the bridge, the certified
instance flips from limitation to theorem: a filter generic over `M` meets the visible detector
`diagReq x` for every ground real `x`, so its real differs from each of them
([`not_mem_groundReals_of_genericOver`](../Forcing/Cohen/NewReal.lean)). Newness is the special
case of lawbreaking in which the law is "equals this real of `M`" — a *consequence* of
genericity over `M` plus the bridge, not an extra demand. Adequacy is packaged
countability-free ([`exists_newReal_of_genericOver`](../Forcing/Cohen/NewReal.lean)), and
composing it with countable existence
([`exists_pfilter_genericOver`](../Forcing/Model/GenericOver.lean)) gives the theorem that
earns the phrase **adds a new real**:
[`exists_pfilter_genericOver_new`](../Forcing/Cohen/NewReal.lean).

The spectrum relativizes too, and the easy-to-forget obligation lands where it must: the
separating test `oddTrue` has to be *visible* to `M`, as a standalone hypothesis. Under it,
**newness over `M` does not imply `M`-genericity**
([`parityReal_new_not_genericOver`](../Forcing/Cohen/Spectrum.lean)), and the two legs are
separate declarations with *incomparable* hypothesis budgets:
[`parityReal_not_mem_groundReals`](../Forcing/Cohen/Spectrum.lean) uses only a covering
enumeration of the ground reals, while
[`not_genericOver_parityReal`](../Forcing/Cohen/Spectrum.lean) uses only the visibility of
`oddTrue` — no `Sees`, no enumeration. So the new-real theorem and the spectrum are independent
results, each blind to the other's hypotheses.

One quantitative remark, already visible in the Lean proofs — and one place where two textbook
adjectives do different jobs and should not travel as an unexplained package:

- **closure of countability under countable sums** is what let §6 combine the coordinate and
  diagonal families (`ℕ ⊕ ι`);
- **external countability of the visible dense-open family** is what existence consumes: the
  `Set.Countable` hypothesis of
  [`exists_pfilter_genericOver`](../Forcing/Model/GenericOver.lean), inherited by
  `exists_pfilter_genericOver_new` — enumerate the visible tests and run Rasiowa–Sikorski,
  exactly as in §6;
- **external countability of the designated ground reals**, supplied as a covering enumeration,
  is a *different* role: it constructs the spectrum witness
  ([`parityReal_not_mem_groundReals`](../Forcing/Cohen/Spectrum.lean)) and appears in no
  existence statement;
- external countability of `M` itself is one standard *sufficient* source of the visible-family
  fact — a countable observer sees countably many tests — not a requirement of the argument;
- **transitivity** plays no role in any of this. It becomes relevant later, for absoluteness,
  valuation, and interpreting `M[G]` — the material-model layer, not the existence of generics.

The countable transitive models of the textbook treatment bundle these jobs; the formal
development keeps them apart.

**What M3 does not claim.** The context is an interface, not a model: nothing above is a
countable transitive model or a model of ZFC, and `M.groundReals` is designated rather than
derived from any membership relation. Nothing constructs `M[G]`. And the conclusion is
`c ∉ M.groundReals` — upgrading it to `c ∉ M` is precisely the job of the later material
instantiation, which must prove the `Sees` obligations instead of assuming them.

---

## What each ingredient contributes

| Ingredient | Contributes | Declaration |
|---|---|---|
| Filter (directedness) | the union is a partial function | [`unionGraph_unique`](../Forcing/GenericUnion.lean) |
| Filter (nonemptiness) | there is an approximation to recover | [`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean) |
| Filter (upward closure) | the filter is *all* its object validates | [`ofPartialFunction_unionFun`](../Forcing/GenericUnion.lean) |
| All three axioms together | filters *are* partial objects | [`pfilterEquivPartialFunction`](../Forcing/GenericUnion.lean) |
| Coordinate requirements | the union is total | [`isSome_unionFun`](../Forcing/GenericUnion.lean) |
| Countability of the tests | such a filter exists | [`exists_pfilter_total`](../Forcing/GenericUnion.lean) |
| Diagonal requirements | differs from each supplied real | [`exists_ne_of_meets_diagReq`](../Forcing/Cohen/Diagonal.lean) |
| Finiteness of conditions | diagonal tests are attainable | [`exists_lookup_eq_none`](../Forcing/FinitePartialFunction.lean) |
| Persistence + attainability | *are* dense-openness | [`Requirement.equivDenseOpen`](../Forcing/Order/Requirement.lean) |
| Downward closure | persistence is free | [`meets_normalize_iff`](../Forcing/Order/Requirement.lean) |
| Union equation | the object determines the filter | [`eq_ofFunction`](../Forcing/GenericUnion.lean) |
| A ground context + the bridge | newness over `M` (adequacy) | [`exists_newReal_of_genericOver`](../Forcing/Cohen/NewReal.lean) |
| Countability of the visible tests | **adds a new real** (existence) | [`exists_pfilter_genericOver_new`](../Forcing/Cohen/NewReal.lean) |

And what each ingredient does **not** contribute:

| Not enough | Fails to give | Certificate |
|---|---|---|
| An arbitrary filter | totality | [`unionFun_principal_top`](../Forcing/GenericUnion.lean) |
| Coordinate tests | difference from a given real | [`totality_separation`](../Forcing/Cohen/Diagonal.lean) |
| Coordinate + diagonal tests | full genericity | [`parity_separation`](../Forcing/Cohen/Diagonal.lean) |
| Newness over `M` (even with `oddTrue` visible) | `M`-genericity | [`parityReal_new_not_genericOver`](../Forcing/Cohen/Spectrum.lean) |

---

Related: issue #17 owns this exposition; issue #27 owns the doctrine pilot that classifies these
facts. The coverage-generation and saturation questions those issues raise are **later work** —
nothing above formalizes a generated coverage or a saturation theorem.
