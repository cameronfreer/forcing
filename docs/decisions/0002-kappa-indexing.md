# ADR 0002 — κ-indexing conventions for closure and distributivity

**Status: decided** (spike #107; gates Wave C of the property track, #104).

## Context

Depth-axis properties quantify over "small" chains and test families, and the indexing
convention affects every statement: ordinal-indexed descending sequences versus arbitrary
index types bounded by `Cardinal.mk ι < κ`; where regularity assumptions enter; and the
formulation of small dense-open intersections. The spike protocol demanded tiny Lean
prototypes and a skeletal closure-to-distributivity proof as the deciding experiment, with
three explicit questions: the empty chain, regularity, and universe/lift costs.

## Decision

**Dual normal form, bridged — neither formulation is bent to serve both jobs.**

1. **Closure** quantifies over **nonempty well-ordered index types**, cardinal-bounded, with
   the order data explicit so constructed orders can be supplied:

   ```lean
   def IsChainClosed (κ : Cardinal.{u}) (P : Type u) [Preorder P] : Prop :=
     ∀ (ι : Type u) (_ : LinearOrder ι) (_ : WellFoundedLT ι), Nonempty ι →
       Cardinal.mk ι < κ → ∀ f : ι → P, Antitone f → ∃ r, ∀ i, r ≤ f i
   ```

2. **Distributivity** quantifies over **arbitrary index types**, cardinal-bounded, with *no*
   nonemptiness (the empty intersection is `univ`, dense trivially):

   ```lean
   def IsDistributive (κ : Cardinal.{u}) (P : Type u) [Preorder P] : Prop :=
     ∀ (ι : Type u), Cardinal.mk ι < κ → ∀ D : ι → Set P, (∀ i, IsDenseOpen (D i)) →
       IsDense (⋂ i, D i)
   ```

3. The **ordinal-length form** (`∀ lam < κ.ord`, …) is a derived presentation connected by an
   explicit bridge theorem using a canonical well-order — not a second primitive. The two
   bounds coincide because the ordinals of cardinality `< κ` are exactly the ordinals
   `< κ.ord`.

## The three questions, answered by the prototypes

1. **Empty chain**: closure quantifies only over **nonempty** chains. The compiled vacuity
   example certifies that no `Nonempty P` requirement leaks in — the empty preorder satisfies
   `IsChainClosed` for every `κ`.
2. **Regularity**: **not needed** for closure ⟹ distributivity. In the skeletal proof, every
   chain handed to closure (each predecessor stage, and the final full chain) has cardinality
   `≤ Cardinal.mk ι < κ` outright; no cofinality computation occurs. Regularity is deferred
   to the preservation-side theorems (M8), where it genuinely belongs; the prototype adds no
   reflexive `Fact κ.IsRegular`.
3. **Universes/lift**: everything lives in one universe — `P : Type u`, `ι : Type u`,
   `κ : Cardinal.{u}` — and no `Cardinal.lift` appears anywhere. Cross-universe generality is
   declined until a consumer demands it.

## Costs exposed by the deciding experiment

The skeletal closure-to-distributivity proof compiles with exactly three sorried
obligations, which are Wave C's implementation costs in order of weight:

1. *(light, choice)* a canonical well-order on the index type (`WellOrderingRel`);
2. *(the main cost)* the transfinite recursion carrying its invariant: construct `g : ι → P`
   with `g i ∈ D i`, `g i ≤ p`, and `Antitone g`, where stage `i` applies closure to the
   nonempty chain `{p} ∪ (predecessor values)` and then density of `D i`;
3. *(light)* one final closure application to the whole constructed chain.

One structural finding worth recording: **openness is load-bearing** in the last step — the
lower bound lands in each `D i` precisely because `D i` is a lower set below `g i`; for
dense-only families the argument fails at exactly that point, matching the classical
statement.

## Consequences

Wave C implements `Forcing/Property/Closure.lean` (`IsChainClosed`, directed variant,
implications) and `Forcing/Property/Distributive.lean` (`IsDistributive`, closure ⟹
distributivity) at these signatures; the ordinal bridge lands with them or immediately after.
The spike prototypes are scratch material and are not committed; this record and the settled
signatures in the Wave C issue are the durable output.
