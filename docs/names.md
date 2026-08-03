# Names: external valuation semantics

The companion to [why-genericity.md](why-genericity.md), continuing in the same **discovery
order**: each definition is introduced by the specific failure it repairs, every repair and
every failure links to the declaration that certifies it, and the chapter ends at an honest
stopping point rather than an overclaimed one.

The question this chapter answers: genericity built an object from a filter — what does the
*extension* contain before the filter is chosen?

---

## 1. Carrier-specific generic objects do not describe arbitrary future sets

M2 and M3 extract one object from a generic filter: a function, via
[`unionFun`](../Forcing/GenericUnion.lean) and [`totalUnion`](../Forcing/GenericUnion.lean) on
the finite-partial-function carrier. That machinery answers "what real does `G` determine?"
and nothing else.

> **Attempt.** Describe the sets of the extension the same way, one bespoke construction per
> kind of object.
> **Failure.** The extension contains *sets of sets of…* everything the ground can describe,
> uniformly — there is no carrier to bespoke-build against, because the object depends on a
> filter that has not been chosen yet.
> **Repair.** A **name**: a set-in-waiting, its elements conditioned on the filter to come.

## 2. Names are conditional, intensional trees

A [`PName P`](../Forcing/Name/Basic.lean) is an inductive tree mirroring mathlib's `PSet`, with
one addition: every branch carries the condition that admits it.

Two deliberate absences, both visible in the import graph (`Forcing/Name/Basic.lean` imports
only the prelude):

- **No order.** The tree structure never consults `≤`; even valuation will use only membership
  of conditions in a set.
- **No quotient.** Names are *intensional* — no `Setoid`, no extensional equality at this
  layer. Extensional identifications happen exactly once, at the `ZFSet` end of the valuation
  (§5).

## 3. Any condition set values a name

> **Attempt.** Define the value of a name along a generic filter.
> **Failure.** Nothing in the definition needs genericity — or the filter laws — or the order.
> Demanding them would be smuggling.
> **Repair.** Value against an **arbitrary set of conditions**:
> [`val (S : Set P)`](../Forcing/Name/Valuation.lean) keeps the admitted branches,
> recursively. A filter coerces to `Set P` at call sites; genericity earns its keep at the
> truth lemma, one milestone later.

The intensional/extensional boundary sits exactly here: `val` lands in `PSet`, and the public
laws are stated for [`zval`](../Forcing/Name/Valuation.lean), its composite with the quotient.
The principal law is the membership characterization
[`mem_zval_iff`](../Forcing/Name/Valuation.lean): a set belongs to the valuation exactly when
it is the valuation of an admitted branch.

## 4. Valuation is not monotone in the condition set

> **Attempt.** Expect `S ⊆ S' → zval S τ ⊆ zval S' τ` — more conditions, more elements.
> **Failure.** Growing the set admits more branches *recursively*, which can change an
> existing element rather than merely add one. The failure is certified, not just documented:
> [`exists_not_zval_subset_zval`](../Forcing/Name/Valuation.lean) exhibits a two-level name
> whose values along `S ⊆ S'` are `{∅}` and `{{∅}}` — and `∅ ∈ {∅}` while `∅ ∉ {{∅}}`.

This is a genuine trap: the corresponding statement about the *name family* is true (§7), and
the two axes must not be conflated. The table at the end keeps them apart.

## 5. Check names, and where intensional equality ends

The ambient universe embeds into names: [`check`](../Forcing/Name/Check.lean) tags every branch
with the distinguished element `⊤`. The exact prices are part of the design:

- constructing `x̌` needs only `[Top P]` — no order;
- valuation undoing it needs only `⊤ ∈ S`:
  [`val_check_equiv`](../Forcing/Name/Check.lean) intensionally,
  [`zval_check`](../Forcing/Name/Check.lean) extensionally;
- forcing filters pay via `[Preorder P] [OrderTop P]` and mathlib's `Order.PFilter.top_mem`,
  so the filter statements are corollaries
  ([`zval_check_pfilter`](../Forcing/Name/Check.lean)).

The two laws are not the same statement. Intensionally, `(check x).val S` is only
*extensionally equivalent* to `x` (`PSet.Equiv`); on-the-nose `PSet` equality is not expected
in general, because the valuation's index type is a subtype over a trivially-true condition.
The honest equality lives one quotient later, at `ZFSet` — which is precisely why the
extensional boundary of §3 was placed where it is.

## 6. The generic can name itself — once conditions have material codes

> **Attempt.** Write down a name whose value is the generic filter.
> **Failure.** A name values to a *set*; a filter is a set of *conditions*, and conditions are
> not sets. Nothing can be named until conditions are coded.
> **Repair.** An explicit, bundled coding:
> [`ConditionCode`](../Forcing/Name/GenName.lean) — a representation `repr : P → PSet` with
> injective extensional image. A structure, not a typeclass: different material grounds will
> code conditions differently, and nothing at this layer fixes a canonical one. (A concrete
> code for Cohen conditions — structural, with a full membership characterization — is
> [`cohenConditionCode`](../Forcing/Cohen/ConditionCode.lean).)

Then [`genName κ`](../Forcing/Name/GenName.lean) — one branch per condition, each tagged with
itself and carrying the condition's code, checked — needs only `[Top P]`, and its valuation
**faithfully codes any condition set containing `⊤`**:
[`mem_zval_genName_iff`](../Forcing/Name/GenName.lean) describes the members, and
[`eq_of_zval_genName_eq`](../Forcing/Name/GenName.lean) recovers the condition set from its
code. In particular distinct filters have distinct codes
([`eq_of_zval_genName_eq_pfilter`](../Forcing/Name/GenName.lean)).

The wording is deliberate: the valuation contains a *faithful material code* of `G` — a set
from which `G` is recoverable — never the Lean object `G` itself.

## 7. The extension must choose its names

> **Attempt.** Define the extension as the valuation image of *all* names.
> **Failure.** §8 — the image is the entire ambient universe.
> **Repair.** The valuation image of a **chosen family**:
> [`valuationImage N S`](../Forcing/Name/ValuationImage.lean). Membership facts carry explicit
> `∈ N` hypotheses: checked sets land in the image when their check names belong
> ([`mem_valuationImage_of_checkZF_mem`](../Forcing/Name/ValuationImage.lean)), and the
> generic's code lands when its name belongs
> ([`zval_genName_mem_valuationImage`](../Forcing/Name/ValuationImage.lean)) — the latter with
> **no** `⊤ ∈ S` hypothesis, because *belonging to the image* is a weaker claim than *being a
> faithful code*, and each theorem charges exactly what it uses.

Unlike valuation in the condition set (§4), the image **is** monotone in the family:
[`valuationImage_mono`](../Forcing/Name/ValuationImage.lean).

## 8. The certified collapse

> **Attempt.** Skip the choice of family anyway.
> **Failure**, certified: every ambient set has a check name, so along any condition set
> containing `⊤`,
>
> ```text
> valuationImage univ S = univ
> ```
>
> ([`valuationImage_univ_eq_univ`](../Forcing/Name/ValuationImage.lean), with the filter form
> [`valuationImage_univ_eq_univ_pfilter`](../Forcing/Name/ValuationImage.lean)).

Allowing every external name makes the valuation image the entire ambient `ZFSet`; "contains
the checked universe" degenerates into "contains everything". **Restricting which names belong
to the ground is what makes a genuine extension possible** — the restriction is not
bureaucracy, it is the mathematical content of "extension".

## 9. The honest stopping point

None of this is `M[G]`, and the library does not use the notation. What external name
semantics provides is: names, valuation against arbitrary condition sets, check names, the
generic's name over a supplied coding, and valuation images of chosen families — with the
collapse certifying why the family must be chosen. What it deliberately does not provide is
the *material* side: a ground whose internal name family makes the image a genuine extension,
with the checked-ground and generic-name memberships proved rather than hypothesized, and the
visibility obligations of the visibility context discharged. That is issue #62, the unique point
where external semantics becomes a material extension — and it is a named prerequisite for the
forcing theorem, not an optional refinement.

---

## The two axes, kept apart

| Change | Behavior |
|---|---|
| Enlarge the name family `N` | `valuationImage N S` grows monotonically ([`valuationImage_mono`](../Forcing/Name/ValuationImage.lean)) |
| Enlarge the condition set `S` | valuation need not be monotone ([`exists_not_zval_subset_zval`](../Forcing/Name/Valuation.lean)) |
| Allow all names | the image collapses to the ambient universe ([`valuationImage_univ_eq_univ`](../Forcing/Name/ValuationImage.lean)) |
| Restrict to material names | prerequisite for a genuine `M[G]` (issue #62) |

## What each ingredient costs

| Ingredient | Needs | Certificate |
|---|---|---|
| Building a name | nothing (prelude-only module) | [`PName`](../Forcing/Name/Basic.lean) |
| Valuing a name | membership in a `Set P` | [`val`](../Forcing/Name/Valuation.lean) |
| Building `x̌` | a distinguished `⊤` | [`check`](../Forcing/Name/Check.lean) |
| Valuation undoing `x̌` | `⊤ ∈ S` | [`zval_check`](../Forcing/Name/Check.lean) |
| Coding conditions | an injective `repr`, no order | [`ConditionCode`](../Forcing/Name/GenName.lean) |
| The generic naming itself | `[Top P]` + a coding | [`genName`](../Forcing/Name/GenName.lean) |
| Faithfulness of the code | `⊤ ∈ S` | [`eq_of_zval_genName_eq`](../Forcing/Name/GenName.lean) |
| Filters paying `⊤ ∈ S` | the order + filter laws | [`zval_check_pfilter`](../Forcing/Name/Check.lean) |
| A genuine extension | a material name family | issue #62 |

---

Related: [why-genericity.md](why-genericity.md) tells the genericity story this chapter
continues; [conceptual-overview.md](conceptual-overview.md) states the architecture both
documents converge on; issue #62 owns the material restriction; the Cohen condition code lives
in [`Forcing/Cohen/ConditionCode.lean`](../Forcing/Cohen/ConditionCode.lean).
The forcing relation, by direct recursion on formulas, is the next chapter; Boolean values are
a comparison theorem two chapters away.
