# The property zoo: structural certificates over the semantic spine

The library's horizontal spine explains **what forcing is**; the classical forcing properties
form a **vertical control theory** over it, saying what a particular forcing does and why:

```text
                    SEMANTIC SPINE

conditions → generic filters → names → M[G] → forcing truth
     │              │            │       │          │
     ├─ branching ──┘            │       │          │
     ├─ depth / resolution ──────┴───────┘          │
     ├─ width / antichain control ───────┴──────────┘
     ├─ observer lifting ────────────────────────────┘
     └─ symmetry ────────────────────────────────────┘
```

This document fixes the discipline for the vertical dimension. The valuable Lean design is a
family of explicit certificate theorems of the shape

```text
core forcing semantics + typed structural certificate ⟹ extension observable
```

— never a universal `Certificate`, `Shadow`, or property-zoo structure.

## The five levels (normative — see architecture.md)

Properties live on different objects, and the difference is essential:

| Level | Typical entries |
|---|---|
| Raw presentation `P` | closed, directed closed, linked, centered |
| Separative quotient | separative, atomless (presentation-independent form) |
| Boolean completion | complete, distributive, Boolean homogeneous |
| Dense-presentation / equivalence class | "has a dense closed suborder", proper, semiproper |
| Ground-internal notion | `M ⊨ "P is ccc/closed/distributive"` |
| Generic extension | adds no reals, preserves `ω₁`, preserves stationary sets |

Raw presentation ≠ dense presentation ≠ Boolean invariant ≠ `M`-internal property ≠ semantic
extension effect. Presentation-dependence is made explicit property by property ("has a dense
closed suborder"); a generic `Densely` wrapper is extracted only when concrete duplication
demands it. **Every infinitary property declares its quantification universe** — external,
`M`-internal, or observer/coding-relative. External ccc is nearly vacuous for externally
countable posets (the decoded forcing of a countable material model is externally σ-centered
by singleton decomposition), so it cannot explain preservation inside the model — and genuine
internal ccc is *not* "visible antichains only": it involves the model's cardinality
computation and eventually its satisfaction relation.

## The five axes — documentation tags, not a classification

The axes organize exposition; they are never a Lean sum type, and a property may occupy
several at once (fusion is depth with name-reading data; properness is observer lifting with
resolution data).

- **Normalization (above the axes).** Separativity is observational extensionality — identify
  conditions no future compatibility test distinguishes; the separative quotient (M1) is that
  observational quotient, and it makes the map to the Boolean completion faithful rather than
  possible. Completeness belongs to `RO(P)` (M9), not the condition poset: forcing uses the
  positive cone, which is not complete.
- **Branching.** Atomlessness: every condition leaves two incompatible futures. The correct
  abstract "adds a new generic" is a pair — atomlessness makes the complement of every
  forcing filter dense open; visibility of that complement refutes genericity. Branching
  supplies the material; observer-relative genericity turns it into newness.
- **Depth / resolution.** Closure, directed closure, strategic closure, distributivity;
  later fusion and Prikry properties. Chain: lower-bound certificate ⟹ simultaneous
  resolution of dense tests ⟹ control of names for short sequences. Distributivity is stated
  natively in the test vocabulary (small intersections of dense-open tests are dense); "adds
  no new `<κ`-sequences" is its semantic consequence, never its definition. Closure implies
  strategic closure, **not** conversely; game conventions must be frozen before that
  implication is formalized.
- **Width / incompatibility control.** (σ-)linked, (σ-)centered, κ-cc, Knaster, precaliber,
  caliber. These bound the width of incompatible possibilities. The proof pattern they feed:
  a deciding antichain for a name *with a ground-valued codomain* is a family of incompatible
  possible values; a chain condition bounds it. Strictness claims enter Lean only with
  certified separating examples.
- **Observer lifting.** Proper, semiproper, subcomplete; stationary-set preservation is the
  semantic outcome class they certify. Properness is a local genericity-compression theorem
  for countable visibility contexts; semiproperness genuinely weakens what the master
  condition preserves; subcompleteness is a distinct embedding-lifting technology, not a
  point on a linear scale. Deferred until material and elementary-submodel layers exist.
- **Symmetry.** Homogeneity's consequence is generic-choice independence (top decides
  suitable invariant sentences). No certifiable content before the forcing relation; its
  first Lean deliverable is tied to the atomic-forcing spike (#93).

## Effects, invariants, certificates

"The fact" versus "the route proving the fact":

- **Semantic effect**: no new `<κ`-sequences; preserves a cardinal; adds no reals.
- **Forcing-equivalence invariant**: distributivity; chain condition of the completion;
  stationary-set preservation.
- **Presentation-specific certificate**: a closure operation; a winning strategy; a
  σ-centered decomposition; a fusion ordering; a master-condition construction.

Canonical chains: `<κ`-closed ⟹ `<κ`-distributive ⟹ no new `<κ`-sequences; σ-centered ⟹
σ-linked ⟹ ccc ⟹ (with `M`-internal scope and regularity qualifications)
cardinal/cofinality preservation. Refactoring should progressively replace strong
presentation-specific hypotheses by their weaker invariant shadows.

## The property card (issue/documentation template, not a Lean structure)

Every property added to the library fills in all eight fields at issue time:

| Field | Question |
|---|---|
| **Lives on** | Raw preorder, dense presentation, separative quotient, completion, extension? |
| **Scope** | External, `M`-internal, or observer/coding-relative? |
| **Certificate** | What data or proposition witnesses it? |
| **Test/name action** | Which requirements or names does it control? |
| **Observable** | What exact extension-theoretic conclusion follows? |
| **Transport** | Behavior under order iso, dense embedding, separativization, completion — *a field to fill honestly, not a theorem quota*: "dense embedding: false / one direction / repaired by a dense-presentation form" is a legitimate answer, and counterexamples are as valuable as transport lemmas |
| **Composition** | Products? Which iteration support (finite / countable / revised countable / `<κ`)? |
| **Strictness** | Which reverse implications fail, by what example? |

## The doctrine connection

Issue #27's pilot `(M, P, J, Res, O)` extends in the future to `(M, P, J_M, N_M; C; Φ)`,
with the resolver slot broadened to typed structural certificates tagged by axis. That is the
*planned* shape of the doctrine, not a structure that exists; the certified M2/M3 artifacts
of the pilot stand unchanged.

## Implemented property modules

- [`Forcing/Property/Atomless.lean`](../Forcing/Property/Atomless.lean) — branching:
  `IsAtomless`, the dense-open complement of every forcing filter
  (`isDenseOpen_compl_pfilter`), and the visibility refutation
  (`not_genericOver_of_visible_compl`).

(Rows are added as modules land; a module row is the only place this document makes
implementation claims.)

---

Related: [conceptual-overview.md](conceptual-overview.md) is the horizontal spine;
[base-theories-and-shadows.md](base-theories-and-shadows.md) refines properties into
theorem-local shadows indexed by base theory and formula fragment (research RFC);
[architecture.md](architecture.md) carries the normative constraints.
