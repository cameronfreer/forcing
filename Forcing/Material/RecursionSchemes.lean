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

The count is **discovery-driven**: it is read off the construction that compiled, not chosen
in advance. It came to **six** — two Collection/Separation pairs, one per aggregation level,
plus the bound and stage instances. `entryBoundFormula` takes the tag as a parameter, so one
sentence serves both tags rather than two.

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
* the six scheme instances named above.

Absent, and load-bearing as negative findings: **no Foundation, no Infinity, no Power Set**.
Nothing here mentions `InternalNameCoding` or the external forcing relation.

The individual theorems are cheaper than the module, and are priced separately.
`exists_stageValue_of_bound` in particular charges **exactly one Separation sentence** — no
Collection, and no finite-closure axioms either: the bound is a carrier element, so the
entries it contains are already in the carrier by transitivity, and the separately priced
`entry_mem` is not invoked. Its bound is a hypothesis, exactly as in the external version;
constructing bounds is `exists_stageBound`'s job and is charged there.

## Main definitions

* `Forcing.AtomicRecursion.stageFormula`, `Forcing.AtomicRecursion.entryBoundFormula`,
  `Forcing.AtomicRecursion.stageGatherFormula`, `Forcing.AtomicRecursion.stageFilterFormula`:
  the instance formulas.
* the corresponding `…Sentence` definitions: the named instances.

## Main results

* `Forcing.MaterialGround.exists_stageValue_of_bound`: the stage exists inside the ground.
* `Forcing.MaterialGround.exists_stageValue`: the same with the bound constructed.
* `Forcing.MaterialGround.exists_rowValue`, `Forcing.MaterialGround.exists_graphValue`: the
  row and the graph exist, each with an exact membership characterization.
* `Forcing.MaterialGround.exists_graphValue_coherent_of_agree`: aggregation plus the bridge,
  with the remaining fixed-point obligation stated rather than discharged.
-/

universe u

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

def entryBoundSentence : memLang.Sentence := collectionSentence entryBoundFormula

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

end MaterialGround

end Forcing
