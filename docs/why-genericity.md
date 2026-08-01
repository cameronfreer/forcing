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
demands one further property that this failure does **not** motivate: upward closure — every
weakening of a member is a member. Coherence never uses it, and a discovery-order account should
not smuggle it in. It is bought later, by two different theorems: meeting a test must not depend
on how the test is normalized (§8), and the object must determine the filter (§9). Until then,
everything proved about the union uses directedness alone.

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
like bookkeeping here; §10 explains why it is the load-bearing cardinal fact of the whole
subject.

**This is the M2 result, and it is not "adds a real."** The conclusion is about the *supplied*
family. There is no ground model in the statement, so there is nothing for "new" to mean. The
over-`M` theorem is M3.

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
each is defeated by the test that detects the law its definition obeys: `diagReq x` detects
"agrees with `x`", and `oddTrue` detects "`false` on the odd coordinates". Note that `oddTrue`
takes no parameters at all: even the simplest laws already lie outside `J_new`. §10 turns this
pattern from a proof technique into the reason a ground model must enter.

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
- **filter → object → filter** needs only that the filter's union *be* that total function:
  [`eq_ofFunction`](../Forcing/GenericUnion.lean). Coordinate genericity is not an extra
  hypothesis here — it is equivalent evidence of totality
  ([`meets_coordReq_iff`](../Forcing/GenericUnion.lean)) and is derived inside the proof.

So faithful recovery is genericity-free in both directions, and it is stated as its own theorem
rather than folded into any adequacy claim. (The partial-function version, likely an equivalence
between filters and partial functions, is tracked as factoring work in issue #31.)

Recovery is also upward closure's second — and decisive — appearance. The proof of
`eq_ofFunction` invokes closure under weakening exactly once, and that one step is the whole
difference between a filter and a merely directed set. Directedness alone cannot make the object
determine the collection: the chain of restrictions of `c` to `{0, …, n}` is directed and has
union `c`, yet is a proper subset of `ofFunction c`. (That counterexample is informal — the
library does not formalize directed non-filters.) Upward closure says the filter contains
*every* finite fact its object validates, and that maximality is exactly what recovery recovers.

The ledger opened in §1 is now balanced. The gluing failure bought directedness
([`unionGraph_unique`](../Forcing/GenericUnion.lean)); upward closure is bought by §8 (meeting
is invariant under normalization) and by this section (the object determines the filter).
Neither filter axiom is a convention: each is the exact price of a named theorem.

## 10. What is still missing: the ground model

The two separations instantiate one phenomenon. Each witness filter is `ofFunction` of a real
given by an explicit definition; an explicitly defined real obeys some law visible in its
definition; and among the dense open tests is the detector for breaking exactly that law. So any supplied countable family of tests is defeated by a
construction from its own data — `parityReal` was built from the very family it diagonalizes.
Nor does enlarging the family help: add the detector, and the enlarged family has a new explicit
witness obeying a new law. Chasing tests one at a time is a regress.

The regress stops by fixing the *observer* instead of the tests. Quantify over every test
**visible to a ground model** `M`, and the pattern above flips from limitation to theorem: for
every real `x` that `M` contains, the detector `diagReq x` is itself `M`-visible, so a filter
generic over `M` meets it and its real differs from `x`. Newness is the special case of
lawbreaking in which the law is "equals this real of `M`" — which is why "adds a new real" is a
*consequence* of genericity over `M`, not an extra demand. That is what M3 adds:

- an explicit visibility context, so "`M`-coded" is a named field rather than something implicit
  in each test family;
- `J_full` relative to `M`, replacing "a supplied countable family";
- the obligation, easy to forget, that a separating test such as `oddTrue` is itself visible to
  `M`;
- and only then the theorem that deserves the phrase **adds a new real**.

One quantitative remark, already visible in the Lean proofs. §6 accumulated doctrines by summing
index types, and existence survived because countability is closed under countable sums.
Relative to a ground model, the family becomes "all dense open tests `M` can see", and *that* is
countable only when `M` is countable from the outside. The countable transitive models of the
textbook treatment are not a technicality grafted onto forcing — they are the same closure fact
that let `exists_pfilter_total_diagonalizing` absorb `ℕ ⊕ ι`, applied at the level of the
observer.

---

## What each ingredient contributes

| Ingredient | Contributes | Declaration |
|---|---|---|
| Filter (directedness) | the union is a partial function | [`unionGraph_unique`](../Forcing/GenericUnion.lean) |
| Filter (upward closure) | the filter is *all* its object validates | [`eq_ofFunction`](../Forcing/GenericUnion.lean) |
| Coordinate requirements | the union is total | [`isSome_unionFun`](../Forcing/GenericUnion.lean) |
| Countability of the tests | such a filter exists | [`exists_pfilter_total`](../Forcing/GenericUnion.lean) |
| Diagonal requirements | differs from each supplied real | [`exists_ne_of_meets_diagReq`](../Forcing/Cohen/Diagonal.lean) |
| Finiteness of conditions | diagonal tests are attainable | [`exists_lookup_eq_none`](../Forcing/FinitePartialFunction.lean) |
| Persistence + attainability | *are* dense-openness | [`Requirement.equivDenseOpen`](../Forcing/Order/Requirement.lean) |
| Downward closure | persistence is free | [`meets_normalize_iff`](../Forcing/Order/Requirement.lean) |
| Union equation | the object determines the filter | [`eq_ofFunction`](../Forcing/GenericUnion.lean) |
| A ground model | "new", and full genericity | M3 |

And what each ingredient does **not** contribute:

| Not enough | Fails to give | Certificate |
|---|---|---|
| An arbitrary filter | totality | [`unionFun_principal_top`](../Forcing/GenericUnion.lean) |
| Coordinate tests | difference from a given real | [`totality_separation`](../Forcing/Cohen/Diagonal.lean) |
| Coordinate + diagonal tests | full genericity | [`parity_separation`](../Forcing/Cohen/Diagonal.lean) |
| Any of the above | newness over a model | M3 (no ground model in scope yet) |

---

Related: issue #17 owns this exposition; issue #27 owns the doctrine pilot that classifies these
facts. The coverage-generation and saturation questions those issues raise are **later work** —
nothing above formalizes a generated coverage or a saturation theorem.
