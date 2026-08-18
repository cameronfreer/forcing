/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes
import Forcing.Material.RecursionFormula

/-!
# The recursion's scheme instances

The point at which the atomic recursion begins to cost something. Every scheme instance the
construction uses is **named here, by its mathematical job**, together with the semantic
theorem it buys — so the ledger records the actual finite family of formulas rather than a
wholesale appeal to "Separation" or "Collection".

The instances, each named by its job:

| Instance | Scheme | Job |
| --- | --- | --- |
| `entryBoundFormula` | Collection | the tagged entries at one state, as a bound |
| `stageFormula` | Separation | carve a stage out of that bound |
| `stageGatherFormula` | Collection | gather the stages along a row |
| `stageFilterFormula` | Separation | discard Collection's junk, *before* flattening |
| `rowGatherFormula` | Collection | gather the rows of a graph |
| `rowFilterFormula` | Separation | discard Collection's junk, again before flattening |
| `packageGatherFormula` | Collection | one covering ⟨D, R⟩ package per predecessor state |
| `packageFilterFormula` | Separation | keep only packages certified at a predecessor |
| `domainFamilyFormula` | Separation | the domains occurring in a package family |
| `graphFamilyFormula` | Separation | the graphs occurring in a package family |
| `predBoundRightFormula` | Collection | right-oriented predecessor witnesses |
| `predBoundLeftFormula` | Collection | left-oriented predecessor witnesses |
| `predSepFormula` | Separation | the exact predecessor set |
| `rowStateGatherFormula` | Collection | a package per state along a row |
| `rowStateFilterFormula` | Separation | keep only packages certified along that row |

The count is **discovery-driven**: it is read off the construction that compiled, not chosen
in advance. It came to **thirteen** — two Collection/Separation pairs for the aggregation
levels, the bound and stage instances, one more pair for the recursion's package family, two
provenance-preserving projections, three for the predecessor set, and one pair for the row
aggregation.
`entryBoundFormula` takes the tag as a parameter, so one sentence serves both tags rather
than two.

## Aggregation is not coherence

Everything here builds a graph **relative to a history**: `exists_graphValue` says exactly
which entries the graph has, with every clause evaluated against `history`. `AtomicCoherentOn`
requires the clauses evaluated against the graph *itself*. The two are joined by
`atomicCoherentOn_of_graphValue` only under observational agreement between the two, and
producing that agreement is the fixed-point problem — it belongs to the `rankPair` recursion,
not to any set construction. `exists_graphValue_coherent_of_agree` states that boundary
explicitly rather than blurring it.

## Filter before flatten

Collection is not functional, so its output may carry members that are not stages at all.
Those must be removed **before** `sUnion`: after flattening, a junk member's provenance is
gone and cannot be recovered. `exists_rowValue` therefore runs gather → filter → flatten, in
that order, and concludes with an **exact membership characterization** (`RowValue`) rather
than a containment. That is what keeps the eventual coherence theorem an extensional
consequence instead of a witness-containment argument.

**The stage instance** — *carving a stage's valid tagged entries out of a bound.* Its formula
is literally `stageEntryDef`, the same formula the stage relation quantifies over, applied at
seven parameters. Nothing is contorted to make it fit: the separated condition **is** the
membership condition of `StageValue`, which is why `exists_stageValue_of_bound` below is the
internal counterpart of the external `stageValue_exists_of_bound` and is proved by the same
two-line argument with `ZFSet.sep` replaced by the instance.

## What this module costs

The full ledger for the constructions here, so that the per-theorem prices below are read
against a stated whole:

* the finite-closure axioms — `emptySetSentence`, `pairingSentence`, `binaryUnionSentence`
  — for entries and for the two-tag bound;
* `unionSentence`, general Union, at each of the two flattening steps;
* the fifteen scheme instances named above.

Absent, and load-bearing as negative findings: **no Foundation, no Infinity, no Power Set**.
Nothing here mentions `InternalNameCoding` or the external forcing relation.

The individual theorems are cheaper than the module, and are priced separately.
`exists_stageValue_of_bound` in particular charges **exactly one Separation sentence** — no
Collection, and no finite-closure axioms either: the bound is a carrier element, so the
entries it contains are already in the carrier by transitivity, and the separately priced
`entry_mem` is not invoked. Its bound is a hypothesis, exactly as in the external version;
constructing bounds is `exists_stageBound`'s job and is charged there.

## Main definitions

* `Forcing.AtomicRecursion.entryBoundFormula`, `Forcing.AtomicRecursion.stageFormula`,
  `Forcing.AtomicRecursion.stageGatherFormula`, `Forcing.AtomicRecursion.stageFilterFormula`,
  `Forcing.AtomicRecursion.rowGatherFormula`, `Forcing.AtomicRecursion.rowFilterFormula`,
  `Forcing.AtomicRecursion.packageGatherFormula`,
  `Forcing.AtomicRecursion.packageFilterFormula`,
  `Forcing.AtomicRecursion.domainFamilyFormula`,
  `Forcing.AtomicRecursion.graphFamilyFormula`,
  `Forcing.AtomicRecursion.predBoundRightFormula`,
  `Forcing.AtomicRecursion.predBoundLeftFormula`,
  `Forcing.AtomicRecursion.predSepFormula`,
  `Forcing.AtomicRecursion.rowStateGatherFormula`,
  `Forcing.AtomicRecursion.rowStateFilterFormula`: the fifteen instance formulas.
* the corresponding `…Sentence` definitions: the named instances.

## Main results

* `Forcing.MaterialGround.exists_stageValue_of_bound`: the stage exists inside the ground.
* `Forcing.MaterialGround.exists_stageValue`: the same with the bound constructed.
* `Forcing.MaterialGround.exists_rowValue`, `Forcing.MaterialGround.exists_graphValue`: the
  row and the graph exist, each with an exact membership characterization.
* `Forcing.MaterialGround.exists_graphValue_coherent_of_agree`: aggregation plus the bridge,
  with the remaining fixed-point obligation stated rather than discharged.
* `Forcing.MaterialGround.exists_packageFamily`: the recursion's predecessor packages —
  every retained one valid, and every predecessor covered by a retained one.
* `Forcing.MaterialGround.exists_projections`: the component families, selected by
  provenance and flattened to exactly the merge's hypotheses.
* `Forcing.MaterialGround.exists_materialApproximation_step`: the carrier-valued case split.
* `Forcing.MaterialGround.exists_materialApproximation_at`: parameterized existence of an
  approximation at each state, given the predecessor sets.
* `Forcing.MaterialGround.exists_predValue`: the exact predecessor set.
* `Forcing.MaterialGround.exists_approximation_at_state`: per-state existence with every
  hypothesis discharged.
* `Forcing.MaterialGround.exists_rowApproximation`: the row approximation, carrying universal
  row coverage.
-/

universe u v

namespace Forcing

open FirstOrder Language

namespace AtomicRecursion

/-- The stage instance's formula: `stageEntryDef` at seven parameters — the two tags, the
condition set, the order code, the history, and the two name codes — with the separated
variable naming the candidate entry.

The parameter order is fixed here once; `exists_stageValue_of_bound` supplies it in the same
order, so no consumer has to count `Sum.inl` indices. -/
def stageFormula : memLang.BoundedFormula (Fin 7) 1 :=
  stageEntryDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (var (Sum.inl 6)) (&0)

/-- **The stage instance**: the Separation sentence carving a stage's valid tagged entries out
of a bound. -/
def stageSeparationSentence : memLang.Sentence :=
  separationSentence stageFormula

theorem stageSeparationSentence_mem_scheme :
    stageSeparationSentence ∈ separationScheme :=
  separationSentence_mem_scheme stageFormula

/-- **The entry-bound instance**: the Collection sentence producing a set that contains the
tagged entries at a state. The tag is a **parameter**, so this single sentence serves *both*
tags — used once at `memWitnessTag` and once at `eqTag`. Its witnesses are individual
entries, not sets of entries, so nothing needs flattening. -/
def entryBoundFormula : memLang.BoundedFormula (Fin 3) 2 :=
  entryDef (var (Sum.inl 0)) (&0) (var (Sum.inl 1)) (var (Sum.inl 2)) (&1)

/-- **The stage-gathering instance**: the Collection sentence gathering the stage values
along a row, indexed by the second coordinate. -/
def stageGatherFormula : memLang.BoundedFormula (Fin 6) 2 :=
  stageValueDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (&0) (&1)

/-- **The stage-filter instance**: the Separation sentence keeping exactly the genuine stage
values of a row. Collection is not functional, so its output may carry junk; this filter runs
**before** the union, because after flattening the provenance of a junk member is gone and
cannot be recovered. -/
def stageFilterFormula : memLang.BoundedFormula (Fin 7) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 6))) ⊓
    stageValueDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
      (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3))) (liftTerm (var (Sum.inl 4)))
      (liftTerm (var (Sum.inl 5))) (&(Fin.last 1)) (liftTerm (&0)))

/-- **The row-gathering instance**: the Collection sentence gathering the rows of a graph,
indexed by the first coordinate. -/
def rowGatherFormula : memLang.BoundedFormula (Fin 6) 2 :=
  rowValueDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (&0) (&1)

/-- **The row-filter instance**: the Separation sentence keeping exactly the genuine rows,
run **before** the second flattening for the same reason as the stage filter. -/
def rowFilterFormula : memLang.BoundedFormula (Fin 6) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 5))) ⊓
    rowValueDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
      (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3))) (liftTerm (var (Sum.inl 4)))
      (liftTerm (var (Sum.inl 5))) (&(Fin.last 1)) (liftTerm (&0)))

/-- **The package-gathering instance**: the Collection sentence gathering, for each
predecessor state, a package certified at it. -/
def packageGatherFormula : memLang.BoundedFormula (Fin 5) 2 :=
  packageAtDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (&0) (&1)

/-- **The package-filter instance**: the Separation sentence keeping exactly those packages
that are certified at some member of the *exact* predecessor set. Collection is not
functional, so its output may carry unrelated or malformed witnesses; this removes them
before any projection. -/
def packageFilterFormula : memLang.BoundedFormula (Fin 6) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 5))) ⊓
    packageAtDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
      (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3))) (liftTerm (var (Sum.inl 4)))
      (&(Fin.last 1)) (liftTerm (&0)))

/-- **The domain-projection instance**: keep the sets occurring as a package's first
coordinate. Selection is by **provenance** — occurrence in a pair of `F` — never by a property
of the component alone, which would forget the pairing. -/
def domainFamilyFormula : memLang.BoundedFormula (Fin 1) 1 :=
  domainFamilyDef (var (Sum.inl 0)) (&0)

/-- **The graph-projection instance**, dually. -/
def graphFamilyFormula : memLang.BoundedFormula (Fin 1) 1 :=
  graphFamilyDef (var (Sum.inl 0)) (&0)

/-- **The right predecessor-bound instance** (Collection). Gives **coverage only** — a raw
Collection output may contain junk, so exactness waits for the separation below. -/
def predBoundRightFormula : memLang.BoundedFormula (Fin 1) 2 :=
  predBoundRightDef (var (Sum.inl 0)) (&0) (&1)

/-- **The left predecessor-bound instance** (Collection), used at two parameter settings. -/
def predBoundLeftFormula : memLang.BoundedFormula (Fin 1) 2 :=
  predBoundLeftDef (var (Sum.inl 0)) (&0) (&1)

/-- **The predecessor instance** (Separation): carves the exact predecessor set out of the
combined bound. This is where the condition-set guard and the orientation constraints are
applied, and where `PredValue` becomes exact. -/
def predSepFormula : memLang.BoundedFormula (Fin 3) 1 :=
  predSpecDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (&0)

/-- **The row-gathering instance** (Collection): for a fixed first coordinate, a package
covering the state `⟨x, y⟩` for each `y ∈ A`. -/
def rowStateGatherFormula : memLang.BoundedFormula (Fin 6) 2 :=
  statePackageAtDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (var (Sum.inl 5)) (&0) (&1)

/-- **The row-filter instance** (Separation): keep only packages certified at a state
`⟨x, y⟩` with `y ∈ A`. -/
def rowStateFilterFormula : memLang.BoundedFormula (Fin 6) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 4))) ⊓
    statePackageAtDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
      (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3))) (liftTerm (var (Sum.inl 4)))
      (liftTerm (var (Sum.inl 5))) (&(Fin.last 1)) (liftTerm (&0)))

def entryBoundSentence : memLang.Sentence := collectionSentence entryBoundFormula

def rowStateGatherSentence : memLang.Sentence := collectionSentence rowStateGatherFormula

def rowStateFilterSentence : memLang.Sentence := separationSentence rowStateFilterFormula

theorem rowStateGatherSentence_mem_scheme : rowStateGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme rowStateGatherFormula

theorem rowStateFilterSentence_mem_scheme : rowStateFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme rowStateFilterFormula

def predBoundRightSentence : memLang.Sentence := collectionSentence predBoundRightFormula

def predBoundLeftSentence : memLang.Sentence := collectionSentence predBoundLeftFormula

def predSepSentence : memLang.Sentence := separationSentence predSepFormula

theorem predBoundRightSentence_mem_scheme : predBoundRightSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme predBoundRightFormula

theorem predBoundLeftSentence_mem_scheme : predBoundLeftSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme predBoundLeftFormula

theorem predSepSentence_mem_scheme : predSepSentence ∈ separationScheme :=
  separationSentence_mem_scheme predSepFormula

def domainFamilySentence : memLang.Sentence := separationSentence domainFamilyFormula

def graphFamilySentence : memLang.Sentence := separationSentence graphFamilyFormula

theorem domainFamilySentence_mem_scheme : domainFamilySentence ∈ separationScheme :=
  separationSentence_mem_scheme domainFamilyFormula

theorem graphFamilySentence_mem_scheme : graphFamilySentence ∈ separationScheme :=
  separationSentence_mem_scheme graphFamilyFormula

def packageGatherSentence : memLang.Sentence := collectionSentence packageGatherFormula

def packageFilterSentence : memLang.Sentence := separationSentence packageFilterFormula

theorem packageGatherSentence_mem_scheme : packageGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme packageGatherFormula

theorem packageFilterSentence_mem_scheme : packageFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme packageFilterFormula

def rowGatherSentence : memLang.Sentence := collectionSentence rowGatherFormula

def rowFilterSentence : memLang.Sentence := separationSentence rowFilterFormula

theorem rowGatherSentence_mem_scheme : rowGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme rowGatherFormula

theorem rowFilterSentence_mem_scheme : rowFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme rowFilterFormula

def stageGatherSentence : memLang.Sentence := collectionSentence stageGatherFormula

def stageFilterSentence : memLang.Sentence := separationSentence stageFilterFormula

theorem entryBoundSentence_mem_scheme : entryBoundSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme entryBoundFormula

theorem stageGatherSentence_mem_scheme : stageGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme stageGatherFormula

theorem stageFilterSentence_mem_scheme : stageFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme stageFilterFormula

end AtomicRecursion

namespace MaterialGround

open AtomicRecursion

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **The stage exists inside the ground**, given a bound. The internal counterpart of
`AtomicRecursion.stageValue_exists_of_bound`, and its exact analogue: the clause guards
discard malformed members, so **nothing is assumed about whether members of `x` or `y` are
coded branches** — the relation stays total on its whole indexing set, which is what
Collection will later require.

Charged to `T`: **one Separation sentence**, and nothing else. The entries are members of the
bound, hence carrier elements by transitivity, so no finite-closure axiom is consumed. -/
theorem exists_stageValue_of_bound (hsep : stageSeparationSentence ∈ T)
    (tagMem tagEq condSet orderCode history x y bound : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (he : (tagEq : ZFSet.{u}) = natCode eqTag)
    (hb : ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (bound : ZFSet.{u}) ∧
        entry eqTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (bound : ZFSet.{u})) :
    ∃ value : ↥M.toMaterialCarrier,
      StageValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
        (x : ZFSet.{u}) (y : ZFSet.{u}) (value : ZFSet.{u}) := by
  obtain ⟨b, hbdef⟩ := M.exists_separation (φ := stageFormula) hsep
    ![tagMem, tagEq, condSet, orderCode, history, x, y] bound
  -- The separated condition is exactly the stage-entry condition.
  have hbody : ∀ e : ↥M.toMaterialCarrier,
      stageFormula.Realize ![tagMem, tagEq, condSet, orderCode, history, x, y] ![e] ↔
        StageEntry (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (x : ZFSet.{u}) (y : ZFSet.{u}) (e : ZFSet.{u}) := by
    intro e
    rw [stageFormula, realize_stageEntryDef (by simpa using hm) (by simpa using he)]
    simp
  have hbM : (b : ZFSet.{u}) ∈ M.toMaterialCarrier := b.2
  have hboundM : (bound : ZFSet.{u}) ∈ M.toMaterialCarrier := bound.2
  refine ⟨b, fun e ↦ ⟨fun he' ↦ ?_, fun hd ↦ ?_⟩⟩
  · have heM : e ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans he' hbM
    exact (hbody ⟨e, heM⟩).1 ((hbdef ⟨e, heM⟩).1 he').2
  · -- The candidate entry lies in the bound, hence in the carrier.
    have heB : e ∈ (bound : ZFSet.{u}) := by
      rcases (hd : StageEntry _ _ _ _ _ _) with ⟨p, hp, rfl, -⟩ | ⟨p, hp, rfl, -⟩
      · exact (hb p hp).1
      · exact (hb p hp).2
    have heM : e ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans heB hboundM
    exact (hbdef ⟨e, heM⟩).2 ⟨heB, (hbody ⟨e, heM⟩).2 hd⟩

/-! ### The row construction

Collection, then **filter**, then flatten. The filter is not optional bookkeeping: Collection
is not functional, so its output may carry junk, and after `sUnion` a junk member's
provenance is gone. Filtering first is what makes the final statement an exact membership
characterization rather than a containment. -/

/-- The per-state entry bound at one tag, from the entry-bound instance. **No general
Union**: the witnesses are individual entries. -/
theorem exists_entryBound (hcol : entryBoundSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tag : ℕ) (tagCode condSet x y : ↥M.toMaterialCarrier)
    (htag : (tagCode : ZFSet.{u}) = natCode tag) :
    ∃ E : ↥M.toMaterialCarrier, ∀ p ∈ (condSet : ZFSet.{u}),
      entry tag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (E : ZFSet.{u}) := by
  have hbody : ∀ p e : ↥M.toMaterialCarrier,
      entryBoundFormula.Realize ![tagCode, x, y] ![p, e] ↔
        (e : ZFSet.{u}) = entry tag (p : ZFSet.{u}) (x : ZFSet.{u}) (y : ZFSet.{u}) := by
    intro p e
    rw [entryBoundFormula, realize_entryDef_natCode (by simpa using htag)]
    simp
  obtain ⟨E, hE⟩ := M.exists_collection (φ := entryBoundFormula) hcol ![tagCode, x, y] condSet
    (fun p hp' ↦ ⟨⟨_, M.entry_mem he hp hu (M.toMaterialCarrier.mem_trans hp' condSet.2)
      x.2 y.2⟩, (hbody p _).2 rfl⟩)
  refine ⟨E, fun p hp' ↦ ?_⟩
  obtain ⟨e, heE, hval⟩ := hE ⟨p, M.toMaterialCarrier.mem_trans hp' condSet.2⟩ hp'
  rw [(hbody _ e).1 hval] at heE
  exact heE

/-- The per-state bound at both tags — the same instance twice, combined by **binary** union.
This is what discharges the bound hypothesis of `exists_stageValue_of_bound`. -/
theorem exists_stageBound (hcol : entryBoundSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet x y : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∃ bound : ↥M.toMaterialCarrier, ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (bound : ZFSet.{u}) ∧
        entry eqTag p (x : ZFSet.{u}) (y : ZFSet.{u}) ∈ (bound : ZFSet.{u}) := by
  obtain ⟨E₁, hE₁⟩ := M.exists_entryBound hcol he hp hu memWitnessTag tagMem condSet x y hm
  obtain ⟨E₂, hE₂⟩ := M.exists_entryBound hcol he hp hu eqTag tagEq condSet x y hq
  exact ⟨⟨(E₁ : ZFSet.{u}) ∪ (E₂ : ZFSet.{u}), M.union_mem hu E₁.2 E₂.2⟩, fun p hp' ↦
    ⟨ZFSet.mem_union.2 (Or.inl (hE₁ p hp')), ZFSet.mem_union.2 (Or.inr (hE₂ p hp'))⟩⟩

/-- **The stage exists outright**, with the bound now constructed rather than assumed. -/
theorem exists_stageValue (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode history x y : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∃ value : ↥M.toMaterialCarrier,
      StageValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
        (x : ZFSet.{u}) (y : ZFSet.{u}) (value : ZFSet.{u}) := by
  obtain ⟨bound, hbd⟩ := M.exists_stageBound hbnd he hp hu tagMem tagEq condSet x y hm hq
  exact M.exists_stageValue_of_bound hsep tagMem tagEq condSet orderCode history x y bound
    hm hq hbd

/-- The stage-filter instance reads as "some `y` in the domain has this stage". -/
theorem realize_stageFilterFormula
    (tagMem tagEq condSet orderCode history x A value : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag)
    (hentM : ∀ y ∈ (A : ZFSet.{u}), ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p (x : ZFSet.{u}) y ∈ M.toMaterialCarrier ∧
        entry eqTag p (x : ZFSet.{u}) y ∈ M.toMaterialCarrier) :
    stageFilterFormula.Realize ![tagMem, tagEq, condSet, orderCode, history, x, A] ![value] ↔
      ∃ y ∈ (A : ZFSet.{u}),
        StageValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (x : ZFSet.{u}) y (value : ZFSet.{u}) := by
  have hsv : ∀ w : ↥M.toMaterialCarrier, (w : ZFSet.{u}) ∈ (A : ZFSet.{u}) →
      ((stageValueDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
          (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3)))
          (liftTerm (var (Sum.inl 4))) (liftTerm (var (Sum.inl 5))) (&(Fin.last 1))
          (liftTerm (&0))).Realize
        ![tagMem, tagEq, condSet, orderCode, history, x, A] (Fin.snoc ![value] w) ↔
        StageValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (x : ZFSet.{u}) (w : ZFSet.{u}) (value : ZFSet.{u})) := by
    intro w hw
    rw [realize_stageValueDef (by simpa [liftTerm, Term.realize_relabel] using hm)
      (by simpa [liftTerm, Term.realize_relabel] using hq)
      (by simpa [liftTerm, Term.realize_relabel] using hentM (w : ZFSet.{u}) hw)]
    simp [liftTerm]
  have hAM : (A : ZFSet.{u}) ∈ M.toMaterialCarrier := A.2
  simp only [stageFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  constructor
  · rintro ⟨w, hw, hs⟩
    exact ⟨(w : ZFSet.{u}), hw, (hsv w hw).1 hs⟩
  · rintro ⟨w, hw, hs⟩
    exact ⟨⟨w, M.toMaterialCarrier.mem_trans hw hAM⟩, hw, (hsv ⟨w, _⟩ hw).2 hs⟩

/-- **The row exists inside the ground, with an exact membership characterization.**

Collection gathers the stages along the row, the filter instance discards junk **before** any
flattening, and general Union assembles the entries. The conclusion says precisely which
entries the row has — not merely that it contains a stage for every `y`. -/
theorem exists_rowValue (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : stageGatherSentence ∈ T) (hfil : stageFilterSentence ∈ T)
    (huni : unionSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode history A x : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∃ row : ↥M.toMaterialCarrier,
      RowValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
        (A : ZFSet.{u}) (x : ZFSet.{u}) (row : ZFSet.{u}) := by
  have hAM : (A : ZFSet.{u}) ∈ M.toMaterialCarrier := A.2
  have hcM : (condSet : ZFSet.{u}) ∈ M.toMaterialCarrier := condSet.2
  -- Entries along the row are carrier elements, by finite closure.
  have hentM : ∀ y ∈ (A : ZFSet.{u}), ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p (x : ZFSet.{u}) y ∈ M.toMaterialCarrier ∧
        entry eqTag p (x : ZFSet.{u}) y ∈ M.toMaterialCarrier := by
    intro y hy p hp'
    exact ⟨M.entry_mem he hp hu (M.toMaterialCarrier.mem_trans hp' hcM) x.2
        (M.toMaterialCarrier.mem_trans hy hAM),
      M.entry_mem he hp hu (M.toMaterialCarrier.mem_trans hp' hcM) x.2
        (M.toMaterialCarrier.mem_trans hy hAM)⟩
  -- Step 1: gather the stages along the row.
  have hstageR : ∀ y value : ↥M.toMaterialCarrier,
      (y : ZFSet.{u}) ∈ (A : ZFSet.{u}) →
      (stageGatherFormula.Realize ![tagMem, tagEq, condSet, orderCode, history, x]
          ![y, value] ↔
        StageValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (x : ZFSet.{u}) (y : ZFSet.{u}) (value : ZFSet.{u})) := by
    intro y value hy
    rw [stageGatherFormula, realize_stageValueDef (by simpa using hm) (by simpa using hq)
      (by simpa using hentM (y : ZFSet.{u}) hy)]
    simp
  obtain ⟨B, hB⟩ := M.exists_collection (φ := stageGatherFormula) hgat
    ![tagMem, tagEq, condSet, orderCode, history, x] A
    (fun y hy ↦ by
      obtain ⟨value, hv⟩ := M.exists_stageValue hbnd hsep he hp hu tagMem tagEq condSet
        orderCode history x y hm hq
      exact ⟨value, (hstageR y value hy).2 hv⟩)
  -- Step 2: filter, BEFORE flattening.
  obtain ⟨B', hB'⟩ := M.exists_separation (φ := stageFilterFormula) hfil
    ![tagMem, tagEq, condSet, orderCode, history, x, A] B
  -- Step 3: flatten.
  refine ⟨⟨ZFSet.sUnion (B' : ZFSet.{u}), M.sUnion_mem huni B'.2⟩,
    rowValue_of_sUnion ?_ ?_⟩
  · -- every `y ∈ A` has its stage present in the filtered family
    intro y hy
    obtain ⟨value, hvB, hval⟩ := hB ⟨y, M.toMaterialCarrier.mem_trans hy hAM⟩ hy
    have hsv := (hstageR ⟨y, _⟩ value hy).1 hval
    refine ⟨(value : ZFSet.{u}), (hB' value).2 ⟨hvB, ?_⟩, hsv⟩
    exact (M.realize_stageFilterFormula tagMem tagEq condSet orderCode history x A value
      hm hq hentM).2 ⟨y, hy, hsv⟩
  · -- every member of the filtered family is a stage along the row
    intro w hw
    have hwM : w ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hw B'.2
    exact (M.realize_stageFilterFormula tagMem tagEq condSet orderCode history x A ⟨w, hwM⟩
      hm hq hentM).1 ((hB' ⟨w, hwM⟩).1 hw).2

/-! ### The graph construction

The same three moves one level up — gather rows, filter, flatten — and then the **bridge**.
Aggregation and coherence are kept apart deliberately: `exists_graphValue` fixes exactly which
entries the graph has *relative to `history`*, and `atomicCoherentOn_of_graphValue` converts
that into coherence only under observational agreement. Producing the agreement is the
fixed-point problem, where `rankPair` belongs. -/

/-- The row-filter instance reads as "some `x` in the domain has this row". -/
theorem realize_rowFilterFormula
    (tagMem tagEq condSet orderCode history A row : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag)
    (hentM : ∀ x ∈ (A : ZFSet.{u}), ∀ y ∈ (A : ZFSet.{u}), ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p x y ∈ M.toMaterialCarrier ∧
        entry eqTag p x y ∈ M.toMaterialCarrier) :
    rowFilterFormula.Realize ![tagMem, tagEq, condSet, orderCode, history, A] ![row] ↔
      ∃ x ∈ (A : ZFSet.{u}),
        RowValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (A : ZFSet.{u}) x (row : ZFSet.{u}) := by
  have hrv : ∀ w : ↥M.toMaterialCarrier, (w : ZFSet.{u}) ∈ (A : ZFSet.{u}) →
      ((rowValueDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
          (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3)))
          (liftTerm (var (Sum.inl 4))) (liftTerm (var (Sum.inl 5))) (&(Fin.last 1))
          (liftTerm (&0))).Realize
        ![tagMem, tagEq, condSet, orderCode, history, A] (Fin.snoc ![row] w) ↔
        RowValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (A : ZFSet.{u}) (w : ZFSet.{u}) (row : ZFSet.{u})) := by
    intro w hw
    rw [realize_rowValueDef (by simpa [liftTerm, Term.realize_relabel] using hm)
      (by simpa [liftTerm, Term.realize_relabel] using hq)
      (by simpa [liftTerm, Term.realize_relabel] using hentM (w : ZFSet.{u}) hw)]
    simp [liftTerm]
  have hAM : (A : ZFSet.{u}) ∈ M.toMaterialCarrier := A.2
  simp only [rowFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  constructor
  · rintro ⟨w, hw, hs⟩
    exact ⟨(w : ZFSet.{u}), hw, (hrv w hw).1 hs⟩
  · rintro ⟨w, hw, hs⟩
    exact ⟨⟨w, M.toMaterialCarrier.mem_trans hw hAM⟩, hw, (hrv ⟨w, _⟩ hw).2 hs⟩

/-- **The graph exists inside the ground, with an exact membership characterization.**

Gather the rows, filter, flatten. The conclusion says precisely which entries the graph has
**relative to `history`** — it is aggregation, not yet coherence. -/
theorem exists_graphValue (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : stageGatherSentence ∈ T) (hfil : stageFilterSentence ∈ T)
    (hrgat : rowGatherSentence ∈ T) (hrfil : rowFilterSentence ∈ T)
    (huni : unionSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode history A : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∃ graph : ↥M.toMaterialCarrier,
      GraphValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
        (A : ZFSet.{u}) (graph : ZFSet.{u}) := by
  have hAM : (A : ZFSet.{u}) ∈ M.toMaterialCarrier := A.2
  have hcM : (condSet : ZFSet.{u}) ∈ M.toMaterialCarrier := condSet.2
  have hentM : ∀ x ∈ (A : ZFSet.{u}), ∀ y ∈ (A : ZFSet.{u}), ∀ p ∈ (condSet : ZFSet.{u}),
      entry memWitnessTag p x y ∈ M.toMaterialCarrier ∧
        entry eqTag p x y ∈ M.toMaterialCarrier := by
    intro x hx y hy p hp'
    have hpM := M.toMaterialCarrier.mem_trans hp' hcM
    have hxM := M.toMaterialCarrier.mem_trans hx hAM
    have hyM := M.toMaterialCarrier.mem_trans hy hAM
    exact ⟨M.entry_mem he hp hu hpM hxM hyM, M.entry_mem he hp hu hpM hxM hyM⟩
  have hrowR : ∀ x row : ↥M.toMaterialCarrier, (x : ZFSet.{u}) ∈ (A : ZFSet.{u}) →
      (rowGatherFormula.Realize ![tagMem, tagEq, condSet, orderCode, history, A]
          ![x, row] ↔
        RowValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (A : ZFSet.{u}) (x : ZFSet.{u}) (row : ZFSet.{u})) := by
    intro x row hx
    rw [rowGatherFormula, realize_rowValueDef (by simpa using hm) (by simpa using hq)
      (by simpa using hentM (x : ZFSet.{u}) hx)]
    simp
  -- Step 1: gather the rows.
  obtain ⟨B, hB⟩ := M.exists_collection (φ := rowGatherFormula) hrgat
    ![tagMem, tagEq, condSet, orderCode, history, A] A
    (fun x hx ↦ by
      obtain ⟨row, hrow⟩ := M.exists_rowValue hbnd hsep hgat hfil huni he hp hu
        tagMem tagEq condSet orderCode history A x hm hq
      exact ⟨row, (hrowR x row hx).2 hrow⟩)
  -- Step 2: filter, BEFORE flattening.
  obtain ⟨B', hB'⟩ := M.exists_separation (φ := rowFilterFormula) hrfil
    ![tagMem, tagEq, condSet, orderCode, history, A] B
  -- Step 3: flatten.
  refine ⟨⟨ZFSet.sUnion (B' : ZFSet.{u}), M.sUnion_mem huni B'.2⟩,
    graphValue_of_sUnion ?_ ?_⟩
  · intro x hx
    obtain ⟨row, hrB, hrval⟩ := hB ⟨x, M.toMaterialCarrier.mem_trans hx hAM⟩ hx
    have hrv := (hrowR ⟨x, _⟩ row hx).1 hrval
    refine ⟨(row : ZFSet.{u}), (hB' row).2 ⟨hrB, ?_⟩, hrv⟩
    exact (M.realize_rowFilterFormula tagMem tagEq condSet orderCode history A row
      hm hq hentM).2 ⟨x, hx, hrv⟩
  · intro w hw
    have hwM := M.toMaterialCarrier.mem_trans hw B'.2
    exact (M.realize_rowFilterFormula tagMem tagEq condSet orderCode history A ⟨w, hwM⟩
      hm hq hentM).1 ((hB' ⟨w, hwM⟩).1 hw).2

/-- **Aggregation and the bridge, combined.** The graph exists inside the ground, and is
coherent **whenever** it observes the same slices as the history did — an implication, not an
equivalence. The remaining
obligation is stated, not discharged: producing that agreement is the fixed-point problem,
and it belongs to the `rankPair` recursion rather than to any set construction. -/
theorem exists_graphValue_coherent_of_agree
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : stageGatherSentence ∈ T) (hfil : stageFilterSentence ∈ T)
    (hrgat : rowGatherSentence ∈ T) (hrfil : rowFilterSentence ∈ T)
    (huni : unionSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode history A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∃ graph : ↥M.toMaterialCarrier,
      GraphValue (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (history : ZFSet.{u})
          (A : ZFSet.{u}) (graph : ZFSet.{u}) ∧
        ((∀ x ∈ (A : ZFSet.{u}), ∀ y ∈ (A : ZFSet.{u}),
            AgreeAt (condSet : ZFSet.{u}) (history : ZFSet.{u}) (graph : ZFSet.{u}) x y) →
          AtomicCoherentOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
            (graph : ZFSet.{u})) := by
  obtain ⟨graph, hgv⟩ := M.exists_graphValue hbnd hsep hgat hfil hrgat hrfil huni he hp hu
    tagMem tagEq condSet orderCode history A hm hq
  exact ⟨graph, hgv, fun hagree ↦ atomicCoherentOn_of_graphValue hA hgv hagree⟩

/-! ### The package family

Collection supplies at least one covering package per predecessor; Separation removes the
unrelated and malformed witnesses; every retained package is valid *and* records which
predecessor it covers. That last part is what lets projection and flattening recover the
exact `hpred` hypothesis `exists_approximation_step` demands. -/

/-- Entries at any coded state of a carrier element lie in the carrier. The bridge is
structural for the coordinates and `entry_mem` for the entry itself, so this is priced at
finite closure and nothing more. -/
theorem entry_mem_of_state (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T)
    (hu : binaryUnionSentence ∈ T) (condSet D : ↥M.toMaterialCarrier) :
    ∀ a b : ZFSet.{u}, ZFSet.pair a b ∈ (D : ZFSet.{u}) →
      ∀ q ∈ (condSet : ZFSet.{u}),
        entry memWitnessTag q a b ∈ M.toMaterialCarrier ∧
          entry eqTag q a b ∈ M.toMaterialCarrier := by
  intro a b hab q hq
  have hpM : ZFSet.pair a b ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hab D.2
  have haM : a ∈ M.toMaterialCarrier :=
    M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inl rfl))
      (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
  have hbM : b ∈ M.toMaterialCarrier :=
    M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
      (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
  have hqM : q ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hq condSet.2
  exact ⟨M.entry_mem he hp hu hqM haM hbM, M.entry_mem he hp hu hqM haM hbM⟩

section PackageRealization

variable {β : Type v} {k : ℕ} {w : β → ↥M.toMaterialCarrier} {xs : Fin k → ↥M.toMaterialCarrier}

/-- **The package law**: the formula realizes exactly `PackageAt`. Its hypotheses are the two
tag equations plus finite closure — the latter supplying `realize_approximationDef`'s entry
obligation *uniformly in the bound domain*, which is possible precisely because that
obligation is structural in `D` apart from the entry construction itself.

Stated for an arbitrary assignment so that it can be used under the filter's binder. -/
theorem realize_packageAtDef (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T)
    (hu : binaryUnionSentence ∈ T)
    {tagMem tagEq condSet orderCode A s a : memLang.Term (β ⊕ Fin k)}
    (hm : ((Term.realize (Sum.elim w xs) tagMem : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim w xs) tagEq : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      natCode eqTag) :
    (packageAtDef tagMem tagEq condSet orderCode A s a).Realize w xs ↔
      PackageAt ((Term.realize (Sum.elim w xs) condSet : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) orderCode : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) s : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier) : ZFSet.{u}) := by
  have haM : ((Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier) : ZFSet.{u}) ∈
      M.toMaterialCarrier := (Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier).2
  have happ : ∀ D R : ↥M.toMaterialCarrier,
      (approximationDef (liftTerm (liftTerm tagMem)) (liftTerm (liftTerm tagEq))
          (liftTerm (liftTerm condSet)) (liftTerm (liftTerm orderCode))
          (liftTerm (liftTerm A)) (&(Fin.castSucc (Fin.last k)))
          (&(Fin.last (k + 1)))).Realize w (Fin.snoc (Fin.snoc xs D) R) ↔
        (DescentClosed
            ((Term.realize (Sum.elim w xs) condSet : ↥M.toMaterialCarrier) : ZFSet.{u})
            ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u})
            (D : ZFSet.{u}) ∧
          CorrectOn ((Term.realize (Sum.elim w xs) condSet : ↥M.toMaterialCarrier) : ZFSet.{u})
            ((Term.realize (Sum.elim w xs) orderCode : ↥M.toMaterialCarrier) : ZFSet.{u})
            (D : ZFSet.{u}) (R : ZFSet.{u})) := by
    intro D R
    rw [realize_approximationDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)
      (by simpa [realize_liftTerm] using
        M.entry_mem_of_state he hp hu (Term.realize (Sum.elim w xs) condSet) D)]
    simp [realize_liftTerm]
  simp only [packageAtDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairDef]
  constructor
  · rintro ⟨D, R, hpair, happ', hsD⟩
    exact ⟨(D : ZFSet.{u}), (R : ZFSet.{u}), hpair, ((happ D R).1 happ').1,
      ((happ D R).1 happ').2, hsD⟩
  · rintro ⟨D, R, hpair, hdc, hco, hsD⟩
    have hp2 : ZFSet.pair D R ∈ M.toMaterialCarrier := hpair ▸ haM
    have hDM : D ∈ M.toMaterialCarrier :=
      M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inl rfl))
        (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hp2)
    have hRM : R ∈ M.toMaterialCarrier :=
      M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
        (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hp2)
    exact ⟨⟨D, hDM⟩, ⟨R, hRM⟩, hpair, (happ ⟨D, hDM⟩ ⟨R, hRM⟩).2 ⟨hdc, hco⟩, hsD⟩

end PackageRealization

/-- **The package family**: Collection supplies at least one covering package per predecessor,
Separation removes the unrelated and malformed witnesses, and every retained package is both
valid *and* certified at a member of the exact predecessor set.

The second conclusion is the one that matters downstream: after projection and flattening it
becomes exactly the `hpred` hypothesis of `exists_approximation_step`. Filtering on
`Approximation` alone would not give it, because a retained package would carry no record of
which predecessor it covers. -/
theorem exists_packageFamily (hgat : packageGatherSentence ∈ T)
    (hfil : packageFilterSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A P : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag)
    (hcov : ∀ s : ↥M.toMaterialCarrier, (s : ZFSet.{u}) ∈ (P : ZFSet.{u}) →
      ∃ a : ↥M.toMaterialCarrier,
        PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
          (s : ZFSet.{u}) (a : ZFSet.{u})) :
    ∃ F : ↥M.toMaterialCarrier,
      (∀ a ∈ (F : ZFSet.{u}),
        Approximation (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u}) a) ∧
      ∀ s ∈ (P : ZFSet.{u}), ∃ a ∈ (F : ZFSet.{u}),
        PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u}) s a := by
  have hPM : (P : ZFSet.{u}) ∈ M.toMaterialCarrier := P.2
  -- Step 1: gather a package for each predecessor state.
  have hgather : ∀ s a : ↥M.toMaterialCarrier,
      (packageGatherFormula.Realize ![tagMem, tagEq, condSet, orderCode, A] ![s, a] ↔
        PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
          (s : ZFSet.{u}) (a : ZFSet.{u})) := by
    intro s a
    rw [packageGatherFormula, M.realize_packageAtDef he hp hu (by simpa using hm)
      (by simpa using hq)]
    simp
  obtain ⟨B, hB⟩ := M.exists_collection (φ := packageGatherFormula) hgat
    ![tagMem, tagEq, condSet, orderCode, A] P
    (fun s hs ↦ (hcov s hs).imp fun a ha ↦ (hgather s a).2 ha)
  -- Step 2: filter, keeping only packages certified at a member of `P`.
  obtain ⟨F, hF⟩ := M.exists_separation (φ := packageFilterFormula) hfil
    ![tagMem, tagEq, condSet, orderCode, A, P] B
  have hfilter : ∀ a : ↥M.toMaterialCarrier,
      (packageFilterFormula.Realize ![tagMem, tagEq, condSet, orderCode, A, P] ![a] ↔
        ∃ s ∈ (P : ZFSet.{u}), PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u})
          (A : ZFSet.{u}) s (a : ZFSet.{u})) := by
    intro a
    have hpk : ∀ t : ↥M.toMaterialCarrier,
        ((packageAtDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
            (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3)))
            (liftTerm (var (Sum.inl 4))) (&(Fin.last 1)) (liftTerm (&0))).Realize
          ![tagMem, tagEq, condSet, orderCode, A, P] (Fin.snoc ![a] t) ↔
          PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
            (t : ZFSet.{u}) (a : ZFSet.{u})) := by
      intro t
      rw [M.realize_packageAtDef he hp hu (by simpa [liftTerm, Term.realize_relabel] using hm)
        (by simpa [liftTerm, Term.realize_relabel] using hq)]
      simp [liftTerm]
    simp only [packageFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
      realize_liftTerm]
    exact ⟨fun ⟨t, ht, hpa⟩ ↦ ⟨(t : ZFSet.{u}), ht, (hpk t).1 hpa⟩,
      fun ⟨t, ht, hpa⟩ ↦ ⟨⟨t, M.toMaterialCarrier.mem_trans ht hPM⟩, ht,
        (hpk ⟨t, _⟩).2 hpa⟩⟩
  refine ⟨F, fun a ha ↦ ?_, fun s hs ↦ ?_⟩
  · -- every retained package is a valid approximation
    have haM := M.toMaterialCarrier.mem_trans ha F.2
    obtain ⟨-, hcert⟩ := (hF ⟨a, haM⟩).1 ha
    obtain ⟨t, -, hpa⟩ := (hfilter ⟨a, haM⟩).1 hcert
    exact approximation_of_packageAt hpa
  · -- every predecessor is covered by a retained package
    obtain ⟨a, haB, hpa⟩ := hB ⟨s, M.toMaterialCarrier.mem_trans hs hPM⟩ hs
    have hpa' := (hgather ⟨s, _⟩ a).1 hpa
    exact ⟨(a : ZFSet.{u}), (hF a).2 ⟨haB, (hfilter a).2 ⟨s, hs, hpa'⟩⟩, hpa'⟩

/-! ### The material induction

`exists_approximation_of_step` cannot serve here: its witnesses are plain `ZFSet`s, so its
induction hypothesis proves no carrier membership, and `exists_packageFamily` needs a coverage
witness that is a carrier element coding `⟨D, R⟩`. The fix is to instantiate the generic
`predSpec_induction` with a **carrier-valued motive** — the states stay `ZFSet`s, since the
descent is on them, while the approximation components are carrier elements throughout. -/

/-- **The material induction.** The predecessor hypothesis supplies *internal* `D` and `R`,
so a package can be constructed from them at finite closure, and `predSpec_mem_domain` is the
sole bridge supplying the `u, v ∈ A` side conditions — the step never has to establish them
itself. -/
theorem exists_materialApproximation (condSet orderCode A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (step : ∀ x y : ZFSet.{u}, x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      (∀ u v : ZFSet.{u}, PredSpec (condSet : ZFSet.{u}) x y (ZFSet.pair u v) →
        ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair u v ∈ (D : ZFSet.{u}) ∧
          DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
          CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
            (R : ZFSet.{u})) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u})) :
    ∀ x y : ZFSet.{u}, x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u}) := by
  refine predSpec_induction (condSet := (condSet : ZFSet.{u}))
    (motive := fun x y ↦ x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u}))
    fun x y ih hx hy ↦ step x y hx hy fun u v hpred ↦ ?_
  obtain ⟨u', hu', v', hv', heq⟩ := predSpec_mem_domain hA hx hy hpred
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 heq
  exact ih u v hpred hu' hv'

/-- The predecessor packages are carrier elements, at pairing: this is the step that turns the
material induction hypothesis into `exists_packageFamily`'s coverage hypothesis. -/
theorem packageAt_mem (hp : pairingSentence ∈ T) {condSet orderCode A s : ZFSet.{u}}
    {D R : ↥M.toMaterialCarrier} (hsD : s ∈ (D : ZFSet.{u}))
    (hdc : DescentClosed condSet A (D : ZFSet.{u}))
    (hco : CorrectOn condSet orderCode (D : ZFSet.{u}) (R : ZFSet.{u})) :
    ∃ a : ↥M.toMaterialCarrier, PackageAt condSet orderCode A s (a : ZFSet.{u}) :=
  ⟨⟨ZFSet.pair (D : ZFSet.{u}) (R : ZFSet.{u}), M.pair_mem hp D.2 R.2⟩,
    (D : ZFSet.{u}), (R : ZFSet.{u}), rfl, hdc, hco, hsD⟩

/-- **The interface**: the material induction hypothesis is exactly what
`exists_packageFamily` needs. Decoding a member of the exact predecessor set back into a
coded state is `exists_pair_of_predSpec`, a structural fact — **no rank enters the material
package construction** — and pairing turns the internal `D`, `R` into the internal package. -/
theorem exists_packageCoverage (hp : pairingSentence ∈ T)
    {condSet orderCode A P : ↥M.toMaterialCarrier} {x y : ZFSet.{u}}
    (hP : PredValue (condSet : ZFSet.{u}) x y (P : ZFSet.{u}))
    (ih : ∀ u v : ZFSet.{u}, PredSpec (condSet : ZFSet.{u}) x y (ZFSet.pair u v) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair u v ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u})) :
    ∀ s : ↥M.toMaterialCarrier, (s : ZFSet.{u}) ∈ (P : ZFSet.{u}) →
      ∃ a : ↥M.toMaterialCarrier,
        PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
          (s : ZFSet.{u}) (a : ZFSet.{u}) := by
  intro s hs
  have hpred : PredSpec (condSet : ZFSet.{u}) x y (s : ZFSet.{u}) := (hP _).1 hs
  obtain ⟨u, v, hsuv⟩ := exists_pair_of_predSpec hpred
  obtain ⟨D, R, hsD, hdc, hco⟩ := ih u v (by rw [← hsuv]; exact hpred)
  refine M.packageAt_mem hp ?_ hdc hco
  rw [hsuv]; exact hsD

/-! ### The projections

Select each component family by provenance, then flatten. The results are literally
`approximation_union`'s `hDc` and `hRc`. **No functionality of the Collection output is
assumed**: packages may share a domain, or a domain may occur with several graphs, and the
laws are unaffected because they quantify over the *pair* being in `F`. -/

/-- Both components of a package in `F` lie in `⋃⋃F`, which is the bound the two Separation
instances carve from. Structural. -/
private theorem components_mem_sUnion_sUnion {F a b : ZFSet.{u}} (h : ZFSet.pair a b ∈ F) :
    a ∈ ZFSet.sUnion (ZFSet.sUnion F) ∧ b ∈ ZFSet.sUnion (ZFSet.sUnion F) := by
  have hmid : ({a, b} : ZFSet.{u}) ∈ ZFSet.sUnion F :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair a b, h, ZFSet.mem_pair.2 (Or.inr rfl)⟩
  exact ⟨ZFSet.mem_sUnion.2 ⟨_, hmid, ZFSet.mem_pair.2 (Or.inl rfl)⟩,
    ZFSet.mem_sUnion.2 ⟨_, hmid, ZFSet.mem_pair.2 (Or.inr rfl)⟩⟩

/-- **The projections exist inside the ground, with exactly the laws the merge needs.**

Charged: two Separation instances and general Union. The bound `⋃⋃F` is where the packages'
components live, and provenance is what the separated conditions test. -/
theorem exists_projections (hdom : domainFamilySentence ∈ T)
    (hgra : graphFamilySentence ∈ T) (huni : unionSentence ∈ T)
    (F : ↥M.toMaterialCarrier) :
    ∃ D₀ R₀ : ↥M.toMaterialCarrier,
      (∀ s, s ∈ (D₀ : ZFSet.{u}) ↔
        ∃ D R, ZFSet.pair D R ∈ (F : ZFSet.{u}) ∧ s ∈ D) ∧
      ∀ e, e ∈ (R₀ : ZFSet.{u}) ↔
        ∃ D R, ZFSet.pair D R ∈ (F : ZFSet.{u}) ∧ e ∈ R := by
  have hb : ZFSet.sUnion (ZFSet.sUnion (F : ZFSet.{u})) ∈ M.toMaterialCarrier :=
    M.sUnion_mem huni (M.sUnion_mem huni F.2)
  set bound : ↥M.toMaterialCarrier := ⟨_, hb⟩ with hbound
  obtain ⟨Dfam, hDfam⟩ := M.exists_separation (φ := domainFamilyFormula) hdom ![F] bound
  obtain ⟨Rfam, hRfam⟩ := M.exists_separation (φ := graphFamilyFormula) hgra ![F] bound
  have hdomBody : ∀ d : ↥M.toMaterialCarrier,
      (domainFamilyFormula.Realize ![F] ![d] ↔
        ∃ R, ZFSet.pair (d : ZFSet.{u}) R ∈ (F : ZFSet.{u})) := by
    intro d
    rw [domainFamilyFormula, realize_domainFamilyDef]
    simp
  have hgraBody : ∀ r : ↥M.toMaterialCarrier,
      (graphFamilyFormula.Realize ![F] ![r] ↔
        ∃ D, ZFSet.pair D (r : ZFSet.{u}) ∈ (F : ZFSet.{u})) := by
    intro r
    rw [graphFamilyFormula, realize_graphFamilyDef]
    simp
  -- The selections are exact: the bound already contains every component.
  have hDsel : DomainFamily (F : ZFSet.{u}) (Dfam : ZFSet.{u}) := by
    intro d
    constructor
    · intro hd
      exact (hdomBody ⟨d, M.toMaterialCarrier.mem_trans hd Dfam.2⟩).1
        ((hDfam ⟨d, M.toMaterialCarrier.mem_trans hd Dfam.2⟩).1 hd).2
    · rintro ⟨R, hR⟩
      have hdM : d ∈ M.toMaterialCarrier :=
        M.toMaterialCarrier.mem_trans (components_mem_sUnion_sUnion hR).1 hb
      exact (hDfam ⟨d, hdM⟩).2 ⟨(components_mem_sUnion_sUnion hR).1,
        (hdomBody ⟨d, hdM⟩).2 ⟨R, hR⟩⟩
  have hRsel : GraphFamily (F : ZFSet.{u}) (Rfam : ZFSet.{u}) := by
    intro r
    constructor
    · intro hr
      exact (hgraBody ⟨r, M.toMaterialCarrier.mem_trans hr Rfam.2⟩).1
        ((hRfam ⟨r, M.toMaterialCarrier.mem_trans hr Rfam.2⟩).1 hr).2
    · rintro ⟨D, hD⟩
      have hrM : r ∈ M.toMaterialCarrier :=
        M.toMaterialCarrier.mem_trans (components_mem_sUnion_sUnion hD).2 hb
      exact (hRfam ⟨r, hrM⟩).2 ⟨(components_mem_sUnion_sUnion hD).2,
        (hgraBody ⟨r, hrM⟩).2 ⟨D, hD⟩⟩
  exact ⟨⟨_, M.sUnion_mem huni Dfam.2⟩, ⟨_, M.sUnion_mem huni Rfam.2⟩,
    sUnion_domainFamily hDsel, sUnion_graphFamily hRsel⟩

/-! ### The material case split, and the composite step

`exists_approximation_step` cannot be used here for the same reason
`exists_approximation_of_step` could not: its witnesses are plain `ZFSet`s. The carrier-valued
counterpart is named below rather than buried in the composite, so its finite-closure ledger
stays inspectable — it charges **pairing and binary union**, and nothing else beyond what
`exists_stageValue` already charges. -/

/-- **The material case split** — the carrier-valued counterpart of
`exists_approximation_step`.

Every construction is internal and priced: transitivity puts `x` and `y` in the carrier,
pairing builds the coded state, pairing with binary union builds the extended domain,
`exists_stageValue` supplies the stage against `R₀`, and binary union builds the extended
graph. No scheme instance beyond those `exists_stageValue` already uses. -/
theorem exists_materialApproximation_step (hbnd : entryBoundSentence ∈ T)
    (hsep : stageSeparationSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A : ↥M.toMaterialCarrier)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag)
    {x y : ZFSet.{u}} (hx : x ∈ (A : ZFSet.{u})) (hy : y ∈ (A : ZFSet.{u}))
    {D₀ R₀ : ↥M.toMaterialCarrier}
    (hDC₀ : DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D₀ : ZFSet.{u}))
    (hCO₀ : CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D₀ : ZFSet.{u})
      (R₀ : ZFSet.{u}))
    (hpred : ∀ s, PredSpec (condSet : ZFSet.{u}) x y s → s ∈ (D₀ : ZFSet.{u})) :
    ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
      DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
      CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
        (R : ZFSet.{u}) := by
  have hxM : x ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hx A.2
  have hyM : y ∈ M.toMaterialCarrier := M.toMaterialCarrier.mem_trans hy A.2
  by_cases hmem : ZFSet.pair x y ∈ (D₀ : ZFSet.{u})
  · -- Already covered; nothing is constructed and nothing is charged.
    exact ⟨D₀, R₀, hmem, hDC₀, hCO₀⟩
  · obtain ⟨stage, hst⟩ := M.exists_stageValue hbnd hsep he hp hu tagMem tagEq condSet
      orderCode R₀ ⟨x, hxM⟩ ⟨y, hyM⟩ hm hq
    have hext := approximation_extend (D₁ := insert (ZFSet.pair x y) (D₀ : ZFSet.{u}))
      (R₁ := (R₀ : ZFSet.{u}) ∪ (stage : ZFSet.{u})) hDC₀ hCO₀ hx hy hpred hmem hst
      (fun t ↦ by rw [ZFSet.mem_insert_iff]; exact or_comm) (fun e ↦ ZFSet.mem_union)
    exact ⟨⟨_, M.insert_mem hp hu (M.pair_mem hp hxM hyM) D₀.2⟩,
      ⟨_, M.union_mem hu R₀.2 stage.2⟩, ZFSet.mem_insert_iff.2 (Or.inl rfl),
      hext.1, hext.2⟩

/-- **The composite step, and the parameterized existence at a state.**

Gather the predecessors' packages, filter, project by provenance, flatten, merge, then case
split — each move a named theorem. The predecessor set is a hypothesis: constructing it
internally is a separate obligation, and stating it here keeps this theorem's ledger exact.

Nothing here mentions `InternalNameCoding` or the external forcing relation, and no Infinity,
Foundation, or Power Set is charged. -/
theorem exists_materialApproximation_at (hbnd : entryBoundSentence ∈ T)
    (hsep : stageSeparationSentence ∈ T) (hgat : packageGatherSentence ∈ T)
    (hfil : packageFilterSentence ∈ T) (hdom : domainFamilySentence ∈ T)
    (hgra : graphFamilySentence ∈ T) (huni : unionSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag)
    (hPred : ∀ x y : ZFSet.{u}, x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      ∃ P : ↥M.toMaterialCarrier,
        PredValue (condSet : ZFSet.{u}) x y (P : ZFSet.{u})) :
    ∀ x y : ZFSet.{u}, x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u}) := by
  refine M.exists_materialApproximation condSet orderCode A hA fun x y hx hy ih ↦ ?_
  obtain ⟨P, hP⟩ := hPred x y hx hy
  -- gather → filter
  obtain ⟨F, hvalid, hcover⟩ := M.exists_packageFamily hgat hfil he hp hu tagMem tagEq
    condSet orderCode A P hm hq (M.exists_packageCoverage hp hP ih)
  -- project by provenance → flatten
  obtain ⟨D₀, R₀, hDc, hRc⟩ := M.exists_projections hdom hgra huni F
  -- merge
  obtain ⟨hDC₀, hCO₀⟩ := approximation_union hvalid hDc hRc
  -- the predecessors landed in the merged domain
  have hpred : ∀ s, PredSpec (condSet : ZFSet.{u}) x y s → s ∈ (D₀ : ZFSet.{u}) := by
    intro s hs
    obtain ⟨a, haF, D, R, rfl, -, -, hsD⟩ := hcover s ((hP s).2 hs)
    exact (hDc s).2 ⟨D, R, haF, hsD⟩
  exact M.exists_materialApproximation_step hbnd hsep he hp hu tagMem tagEq condSet orderCode
    A hm hq hx hy hDC₀ hCO₀ hpred

/-! ### The predecessor set

Gather, union, then separate — and **only after separating** is membership exact. A raw
Collection output supplies coverage and nothing more: it may contain junk, and the two bound
formulas deliberately impose no condition-set guard, since a bound need only *contain* the
witnesses. The guard, the orientations, and exactness all arrive with `predSepFormula`. -/

/-- Right-oriented coverage. Not exactness: `E` may contain anything else besides. -/
theorem exists_predBoundRight (hcol : predBoundRightSentence ∈ T) (hp : pairingSentence ∈ T)
    (fixed source : ↥M.toMaterialCarrier) :
    ∃ E : ↥M.toMaterialCarrier, ∀ c z, ZFSet.pair c z ∈ (source : ZFSet.{u}) →
      ZFSet.pair (fixed : ZFSet.{u}) z ∈ (E : ZFSet.{u}) := by
  have hbody : ∀ w s : ↥M.toMaterialCarrier,
      (predBoundRightFormula.Realize ![fixed] ![w, s] ↔
        ∀ c z, (w : ZFSet.{u}) = ZFSet.pair c z →
          (s : ZFSet.{u}) = ZFSet.pair (fixed : ZFSet.{u}) z) := by
    intro w s
    rw [predBoundRightFormula, realize_predBoundRightDef]
    simp
  obtain ⟨E, hE⟩ := M.exists_collection (φ := predBoundRightFormula) hcol ![fixed] source
    (fun w hw ↦ by
      classical
      by_cases hpair : ∃ c z, (w : ZFSet.{u}) = ZFSet.pair c z
      · obtain ⟨c, z, hcz⟩ := hpair
        have hpM : ZFSet.pair c z ∈ M.toMaterialCarrier := hcz ▸ w.2
        have hzM : z ∈ M.toMaterialCarrier :=
          M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
            (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
        refine ⟨⟨ZFSet.pair (fixed : ZFSet.{u}) z, M.pair_mem hp fixed.2 hzM⟩, ?_⟩
        refine (hbody w _).2 fun c' z' hcz' ↦ ?_
        obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 (hcz.symm.trans hcz')
        rfl
      · exact ⟨w, (hbody w w).2 fun c z hcz ↦ absurd ⟨c, z, hcz⟩ hpair⟩)
  refine ⟨E, fun c z hcz ↦ ?_⟩
  have hwM : ZFSet.pair c z ∈ M.toMaterialCarrier :=
    M.toMaterialCarrier.mem_trans hcz source.2
  obtain ⟨s, hsE, hval⟩ := hE ⟨ZFSet.pair c z, hwM⟩ hcz
  rw [← (hbody ⟨_, hwM⟩ s).1 hval c z rfl]
  exact hsE

/-- Left-oriented coverage. -/
theorem exists_predBoundLeft (hcol : predBoundLeftSentence ∈ T) (hp : pairingSentence ∈ T)
    (fixed source : ↥M.toMaterialCarrier) :
    ∃ E : ↥M.toMaterialCarrier, ∀ c z, ZFSet.pair c z ∈ (source : ZFSet.{u}) →
      ZFSet.pair z (fixed : ZFSet.{u}) ∈ (E : ZFSet.{u}) := by
  have hbody : ∀ w s : ↥M.toMaterialCarrier,
      (predBoundLeftFormula.Realize ![fixed] ![w, s] ↔
        ∀ c z, (w : ZFSet.{u}) = ZFSet.pair c z →
          (s : ZFSet.{u}) = ZFSet.pair z (fixed : ZFSet.{u})) := by
    intro w s
    rw [predBoundLeftFormula, realize_predBoundLeftDef]
    simp
  obtain ⟨E, hE⟩ := M.exists_collection (φ := predBoundLeftFormula) hcol ![fixed] source
    (fun w hw ↦ by
      classical
      by_cases hpair : ∃ c z, (w : ZFSet.{u}) = ZFSet.pair c z
      · obtain ⟨c, z, hcz⟩ := hpair
        have hpM : ZFSet.pair c z ∈ M.toMaterialCarrier := hcz ▸ w.2
        have hzM : z ∈ M.toMaterialCarrier :=
          M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
            (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
        refine ⟨⟨ZFSet.pair z (fixed : ZFSet.{u}), M.pair_mem hp hzM fixed.2⟩, ?_⟩
        refine (hbody w _).2 fun c' z' hcz' ↦ ?_
        obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 (hcz.symm.trans hcz')
        rfl
      · exact ⟨w, (hbody w w).2 fun c z hcz ↦ absurd ⟨c, z, hcz⟩ hpair⟩)
  refine ⟨E, fun c z hcz ↦ ?_⟩
  have hwM : ZFSet.pair c z ∈ M.toMaterialCarrier :=
    M.toMaterialCarrier.mem_trans hcz source.2
  obtain ⟨s, hsE, hval⟩ := hE ⟨ZFSet.pair c z, hwM⟩ hcz
  rw [← (hbody ⟨_, hwM⟩ s).1 hval c z rfl]
  exact hsE

/-- **The predecessor set exists inside the ground, exactly.**

The three instantiated bounds cover the three shapes, binary union combines them, and the
separation makes membership exact — applying the condition-set guard and the orientation
constraints that the bounds deliberately omitted. Charged: two Collection instances (the left
one twice), one Separation, pairing, and binary union. -/
theorem exists_predValue (hbr : predBoundRightSentence ∈ T)
    (hbl : predBoundLeftSentence ∈ T) (hsep : predSepSentence ∈ T)
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (condSet x y : ↥M.toMaterialCarrier) :
    ∃ P : ↥M.toMaterialCarrier,
      PredValue (condSet : ZFSet.{u}) (x : ZFSet.{u}) (y : ZFSet.{u}) (P : ZFSet.{u}) := by
  obtain ⟨E₁, hE₁⟩ := M.exists_predBoundRight hbr hp x y
  obtain ⟨E₂, hE₂⟩ := M.exists_predBoundLeft hbl hp y x
  obtain ⟨E₃, hE₃⟩ := M.exists_predBoundLeft hbl hp x y
  set bound : ↥M.toMaterialCarrier :=
    ⟨(E₁ : ZFSet.{u}) ∪ ((E₂ : ZFSet.{u}) ∪ (E₃ : ZFSet.{u})),
      M.union_mem hu E₁.2 (M.union_mem hu E₂.2 E₃.2)⟩ with hbdef
  -- Coverage of the combined bound, still not exactness.
  have hcover : ∀ s, PredSpec (condSet : ZFSet.{u}) (x : ZFSet.{u}) (y : ZFSet.{u}) s →
      s ∈ (bound : ZFSet.{u}) := by
    rintro s (⟨c, z, hb, -, rfl⟩ | ⟨c, z, hb, -, rfl⟩ | ⟨c, z, hb, -, rfl⟩)
    · exact ZFSet.mem_union.2 (Or.inl (hE₁ c z hb))
    · exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl (hE₂ c z hb))))
    · exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (hE₃ c z hb))))
  obtain ⟨P, hP⟩ := M.exists_separation (φ := predSepFormula) hsep ![condSet, x, y] bound
  have hbody : ∀ s : ↥M.toMaterialCarrier,
      (predSepFormula.Realize ![condSet, x, y] ![s] ↔
        PredSpec (condSet : ZFSet.{u}) (x : ZFSet.{u}) (y : ZFSet.{u}) (s : ZFSet.{u})) := by
    intro s
    rw [predSepFormula, realize_predSpecDef]
    simp
  refine ⟨P, fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩⟩
  · have hsM := M.toMaterialCarrier.mem_trans hs P.2
    exact (hbody ⟨s, hsM⟩).1 ((hP ⟨s, hsM⟩).1 hs).2
  · have hsb := hcover s hs
    have hsM := M.toMaterialCarrier.mem_trans hsb bound.2
    exact (hP ⟨s, hsM⟩).2 ⟨hsb, (hbody ⟨s, hsM⟩).2 hs⟩

/-- **Per-state existence, with every hypothesis discharged.**

The last hypothesis of `exists_materialApproximation_at` was the predecessor set; the tranche
above builds it. What remains are only named scheme-instance memberships and the finite
closure axioms — no `InternalNameCoding`, no external forcing relation, **no Foundation, no
Infinity, and no Power Set**. -/
theorem exists_approximation_at_state (hbnd : entryBoundSentence ∈ T)
    (hsep : stageSeparationSentence ∈ T) (hgat : packageGatherSentence ∈ T)
    (hfil : packageFilterSentence ∈ T) (hdom : domainFamilySentence ∈ T)
    (hgra : graphFamilySentence ∈ T) (hbr : predBoundRightSentence ∈ T)
    (hbl : predBoundLeftSentence ∈ T) (hpsep : predSepSentence ∈ T)
    (huni : unionSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∀ x y : ZFSet.{u}, x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u}) :=
  M.exists_materialApproximation_at hbnd hsep hgat hfil hdom hgra huni he hp hu
    tagMem tagEq condSet orderCode A hA hm hq
    (fun x y hx hy ↦ M.exists_predValue hbr hbl hpsep hp hu condSet
      ⟨x, M.toMaterialCarrier.mem_trans hx A.2⟩ ⟨y, M.toMaterialCarrier.mem_trans hy A.2⟩)

/-! ### The row aggregation

The first of the two final levels. For a fixed first coordinate, gather a package for every
`y ∈ A`, filter, project by provenance, and merge — reusing `exists_projections` and
`approximation_union` unchanged. The result carries **universal row coverage**, which is the
certificate the second level will filter on. `A × A` is never formed. -/

section RowAggregation

variable {β : Type v} {k : ℕ} {w : β → ↥M.toMaterialCarrier} {xs : Fin k → ↥M.toMaterialCarrier}

/-- The state-package law, at an arbitrary assignment. -/
theorem realize_statePackageAtDef (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T)
    (hu : binaryUnionSentence ∈ T)
    {tagMem tagEq condSet orderCode A x y a : memLang.Term (β ⊕ Fin k)}
    (hm : ((Term.realize (Sum.elim w xs) tagMem : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim w xs) tagEq : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      natCode eqTag) :
    (statePackageAtDef tagMem tagEq condSet orderCode A x y a).Realize w xs ↔
      PackageAt ((Term.realize (Sum.elim w xs) condSet : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) orderCode : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u})
        (ZFSet.pair ((Term.realize (Sum.elim w xs) x : ↥M.toMaterialCarrier) : ZFSet.{u})
          ((Term.realize (Sum.elim w xs) y : ↥M.toMaterialCarrier) : ZFSet.{u}))
        ((Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier) : ZFSet.{u}) := by
  have hpk : ∀ s : ↥M.toMaterialCarrier,
      (packageAtDef (liftTerm tagMem) (liftTerm tagEq) (liftTerm condSet)
          (liftTerm orderCode) (liftTerm A) (&(Fin.last k)) (liftTerm a)).Realize w
        (Fin.snoc xs s) ↔
        PackageAt ((Term.realize (Sum.elim w xs) condSet : ↥M.toMaterialCarrier) : ZFSet.{u})
          ((Term.realize (Sum.elim w xs) orderCode : ↥M.toMaterialCarrier) : ZFSet.{u})
          ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u})
          (s : ZFSet.{u})
          ((Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier) : ZFSet.{u}) := by
    intro s
    rw [M.realize_packageAtDef he hp hu (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)]
    simp [realize_liftTerm]
  simp only [statePackageAtDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    realize_liftTerm]
  constructor
  · rintro ⟨s, hs, hpa⟩
    rw [← hs]
    exact (hpk s).1 hpa
  · intro hpa
    have hxyM : ZFSet.pair
        ((Term.realize (Sum.elim w xs) x : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) y : ↥M.toMaterialCarrier) : ZFSet.{u}) ∈
          M.toMaterialCarrier :=
      M.pair_mem hp (Term.realize (Sum.elim w xs) x : ↥M.toMaterialCarrier).2
        (Term.realize (Sum.elim w xs) y : ↥M.toMaterialCarrier).2
    exact ⟨⟨_, hxyM⟩, rfl, (hpk ⟨_, hxyM⟩).2 hpa⟩

end RowAggregation

/-- **The row approximation, with universal row coverage.**

Gather a package for every `y ∈ A`, filter, project by provenance, merge. The coverage
conclusion — `∀ y ∈ A, ⟨x, y⟩ ∈ D` — is what the second aggregation level filters on; it is
recovered from the retained packages exactly as `hpred` was, through the filter's coverage
field and the provenance projection. -/
theorem exists_rowApproximation (hbnd : entryBoundSentence ∈ T)
    (hsep : stageSeparationSentence ∈ T) (hgat : packageGatherSentence ∈ T)
    (hfil : packageFilterSentence ∈ T) (hdom : domainFamilySentence ∈ T)
    (hgra : graphFamilySentence ∈ T) (hbr : predBoundRightSentence ∈ T)
    (hbl : predBoundLeftSentence ∈ T) (hpsep : predSepSentence ∈ T)
    (hrgat : rowStateGatherSentence ∈ T) (hrfil : rowStateFilterSentence ∈ T)
    (huni : unionSentence ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag)
    (x : ↥M.toMaterialCarrier) (hx : (x : ZFSet.{u}) ∈ (A : ZFSet.{u})) :
    ∃ D R : ↥M.toMaterialCarrier,
      DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u}) ∧
        ∀ y ∈ (A : ZFSet.{u}), ZFSet.pair (x : ZFSet.{u}) y ∈ (D : ZFSet.{u}) := by
  have hAM : (A : ZFSet.{u}) ∈ M.toMaterialCarrier := A.2
  have hgatherBody : ∀ y a : ↥M.toMaterialCarrier,
      (rowStateGatherFormula.Realize ![tagMem, tagEq, condSet, orderCode, A, x] ![y, a] ↔
        PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
          (ZFSet.pair (x : ZFSet.{u}) (y : ZFSet.{u})) (a : ZFSet.{u})) := by
    intro y a
    rw [rowStateGatherFormula, M.realize_statePackageAtDef he hp hu (by simpa using hm)
      (by simpa using hq)]
    simp
  -- Step 1: gather a package for each `y ∈ A`.
  obtain ⟨B, hB⟩ := M.exists_collection (φ := rowStateGatherFormula) hrgat
    ![tagMem, tagEq, condSet, orderCode, A, x] A
    (fun y hy ↦ by
      obtain ⟨D, R, hstate, hdc, hco⟩ := M.exists_approximation_at_state hbnd hsep hgat hfil
        hdom hgra hbr hbl hpsep huni he hp hu tagMem tagEq condSet orderCode A hA hm hq
        (x : ZFSet.{u}) (y : ZFSet.{u}) hx hy
      obtain ⟨a, ha⟩ := M.packageAt_mem hp hstate hdc hco
      exact ⟨a, (hgatherBody y a).2 ha⟩)
  -- Step 2: filter.
  obtain ⟨F, hF⟩ := M.exists_separation (φ := rowStateFilterFormula) hrfil
    ![tagMem, tagEq, condSet, orderCode, A, x] B
  have hfilterBody : ∀ a : ↥M.toMaterialCarrier,
      (rowStateFilterFormula.Realize ![tagMem, tagEq, condSet, orderCode, A, x] ![a] ↔
        ∃ y ∈ (A : ZFSet.{u}), PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u})
          (A : ZFSet.{u}) (ZFSet.pair (x : ZFSet.{u}) y) (a : ZFSet.{u})) := by
    intro a
    have hsp : ∀ t : ↥M.toMaterialCarrier,
        ((statePackageAtDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
            (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3)))
            (liftTerm (var (Sum.inl 4))) (liftTerm (var (Sum.inl 5))) (&(Fin.last 1))
            (liftTerm (&0))).Realize
          ![tagMem, tagEq, condSet, orderCode, A, x] (Fin.snoc ![a] t) ↔
          PackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
            (ZFSet.pair (x : ZFSet.{u}) (t : ZFSet.{u})) (a : ZFSet.{u})) := by
      intro t
      rw [M.realize_statePackageAtDef he hp hu
        (by simpa [liftTerm, Term.realize_relabel] using hm)
        (by simpa [liftTerm, Term.realize_relabel] using hq)]
      simp [liftTerm]
    simp only [rowStateFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
      realize_liftTerm]
    exact ⟨fun ⟨t, ht, hpa⟩ ↦ ⟨(t : ZFSet.{u}), ht, (hsp t).1 hpa⟩,
      fun ⟨t, ht, hpa⟩ ↦ ⟨⟨t, M.toMaterialCarrier.mem_trans ht hAM⟩, ht,
        (hsp ⟨t, _⟩).2 hpa⟩⟩
  -- Step 3: project by provenance, then merge.
  obtain ⟨D₀, R₀, hDc, hRc⟩ := M.exists_projections hdom hgra huni F
  have hvalid : ∀ a ∈ (F : ZFSet.{u}),
      Approximation (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u}) a := by
    intro a ha
    have haM := M.toMaterialCarrier.mem_trans ha F.2
    obtain ⟨-, hcert⟩ := (hF ⟨a, haM⟩).1 ha
    obtain ⟨t, -, hpa⟩ := (hfilterBody ⟨a, haM⟩).1 hcert
    exact approximation_of_packageAt hpa
  obtain ⟨hDC₀, hCO₀⟩ := approximation_union hvalid hDc hRc
  refine ⟨D₀, R₀, hDC₀, hCO₀, fun y hy ↦ ?_⟩
  -- Universal row coverage, recovered through the filter's coverage field.
  obtain ⟨a, haB, hpa⟩ := hB ⟨y, M.toMaterialCarrier.mem_trans hy hAM⟩ hy
  have hpa' := (hgatherBody ⟨y, _⟩ a).1 hpa
  have haF : (a : ZFSet.{u}) ∈ (F : ZFSet.{u}) :=
    (hF a).2 ⟨haB, (hfilterBody a).2 ⟨y, hy, hpa'⟩⟩
  obtain ⟨D, R, haeq, -, -, hsD⟩ := hpa'
  exact (hDc _).2 ⟨D, R, haeq ▸ haF, hsD⟩

end MaterialGround

end Forcing
