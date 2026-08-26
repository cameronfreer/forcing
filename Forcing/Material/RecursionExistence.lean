/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.RecursionSchemes

/-!
# Existence of the atomic recursion

The construction itself. `Forcing/Material/RecursionSchemes.lean` supplies the aggregation
layer — stages, rows, and graphs relative to a *history*. This module builds the fixed point:
a graph whose clauses are evaluated against itself.

The shape is the one frozen in the design record: a well-founded induction along `PredSpec`,
whose step gathers the predecessors' approximation packages, filters them, projects the two
component families by provenance, flattens, merges, and extends by one state. Each move is a
named theorem, so the assembly reads as its own audit trail.

## Two disciplines run throughout

**Filter before flatten, and filter on the certificate you will need.** Collection is not
functional, so its output carries junk; and a filter that checks only `Approximation` retains
packages with no record of *which* state they cover, leaving no route to the coverage
hypotheses downstream. Every filter here therefore certifies both.

**Provenance survives projection.** The two component families are selected by occurrence in
a package — `∃ R, ⟨D, R⟩ ∈ F` — never by a property of the component alone, which would allow
one package's domain to be paired with another's graph.

## Where rank appears

Nowhere in this module. `rankPair` licenses `predSpec_induction` and nothing else in the
descent-closed layer; the material construction and its formulas never mention it.

## Main results

* `Forcing.MaterialGround.exists_packageFamily`: the predecessor packages.
* `Forcing.MaterialGround.exists_projections`: the component families, by provenance.
* `Forcing.MaterialGround.exists_approximation_at_state`: per-state existence.
* `Forcing.MaterialGround.exists_rowApproximation`: the row, with universal row coverage.
* `Forcing.MaterialGround.exists_atomicCoherentOn`: **3b's parameterized endpoint**.
-/

universe u v

namespace Forcing

open FirstOrder Language

namespace AtomicRecursion

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

/-- **The final gather instance** (Collection): a row package for each first coordinate. -/
def rowFinalGatherFormula : memLang.BoundedFormula (Fin 5) 2 :=
  rowPackageAtDef (var (Sum.inl 0)) (var (Sum.inl 1)) (var (Sum.inl 2)) (var (Sum.inl 3))
    (var (Sum.inl 4)) (&0) (&1)

/-- **The final filter instance** (Separation): keep only packages that are row packages at
some `x ∈ A` — retaining **both** the approximation conditions and universal row coverage. -/
def rowFinalFilterFormula : memLang.BoundedFormula (Fin 5) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 4))) ⊓
    rowPackageAtDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
      (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3))) (liftTerm (var (Sum.inl 4)))
      (&(Fin.last 1)) (liftTerm (&0)))

def rowFinalGatherSentence : memLang.Sentence := collectionSentence rowFinalGatherFormula

def rowFinalFilterSentence : memLang.Sentence := separationSentence rowFinalFilterFormula

theorem rowFinalGatherSentence_mem_scheme : rowFinalGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme rowFinalGatherFormula

theorem rowFinalFilterSentence_mem_scheme : rowFinalFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme rowFinalFilterFormula

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

end AtomicRecursion

namespace MaterialGround

open AtomicRecursion

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-! ### The package family

Collection supplies at least one covering package per predecessor; Separation removes the
unrelated and malformed witnesses; every retained package is valid *and* records which
predecessor it covers. That last part is what lets projection and flattening recover the
exact `hpred` hypothesis `exists_approximation_step` demands. -/

/-- Entries at any coded state of a carrier element lie in the carrier. The bridge is
structural for the coordinates and `entry_mem` for the entry itself, so this is priced at
finite closure and nothing more. -/
theorem entry_mem_of_state (hp : pairingSentence ∈ T)
    (htm : natCode memWitnessTag ∈ M.toMaterialCarrier)
    (hte : natCode eqTag ∈ M.toMaterialCarrier) (condSet D : ↥M.toMaterialCarrier) :
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
  exact ⟨M.entry_mem hp htm hqM haM hbM, M.entry_mem hp hte hqM haM hbM⟩

section PackageRealization

variable {β : Type v} {k : ℕ} {w : β → ↥M.toMaterialCarrier} {xs : Fin k → ↥M.toMaterialCarrier}

/-- **The package law**: the formula realizes exactly `PackageAt`. Its hypotheses are the two
tag equations plus finite closure — the latter supplying `realize_approximationDef`'s entry
obligation *uniformly in the bound domain*, which is possible precisely because that
obligation is structural in `D` apart from the entry construction itself.

Stated for an arbitrary assignment so that it can be used under the filter's binder. -/
theorem realize_packageAtDef (hp : pairingSentence ∈ T)
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
    have htm : natCode memWitnessTag ∈ M.toMaterialCarrier :=
      hm ▸ (Term.realize (Sum.elim w xs) tagMem : ↥M.toMaterialCarrier).2
    have hte : natCode eqTag ∈ M.toMaterialCarrier :=
      hq ▸ (Term.realize (Sum.elim w xs) tagEq : ↥M.toMaterialCarrier).2
    rw [realize_approximationDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)
      (by simpa [realize_liftTerm] using
        M.entry_mem_of_state hp htm hte (Term.realize (Sum.elim w xs) condSet) D)]
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
    (hfil : packageFilterSentence ∈ T) (hp : pairingSentence ∈ T)
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
    rw [packageGatherFormula, M.realize_packageAtDef hp (by simpa using hm)
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
      rw [M.realize_packageAtDef hp (by simpa [liftTerm, Term.realize_relabel] using hm)
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
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
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
  · obtain ⟨stage, hst⟩ := M.exists_stageValue hbnd hsep hp hu tagMem tagEq condSet
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
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
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
  obtain ⟨F, hvalid, hcover⟩ := M.exists_packageFamily hgat hfil hp tagMem tagEq
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
  exact M.exists_materialApproximation_step hbnd hsep hp hu tagMem tagEq condSet orderCode
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
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∀ x y : ZFSet.{u}, x ∈ (A : ZFSet.{u}) → y ∈ (A : ZFSet.{u}) →
      ∃ D R : ↥M.toMaterialCarrier, ZFSet.pair x y ∈ (D : ZFSet.{u}) ∧
        DescentClosed (condSet : ZFSet.{u}) (A : ZFSet.{u}) (D : ZFSet.{u}) ∧
        CorrectOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (D : ZFSet.{u})
          (R : ZFSet.{u}) :=
  M.exists_materialApproximation_at hbnd hsep hgat hfil hdom hgra huni hp hu
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
theorem realize_statePackageAtDef (hp : pairingSentence ∈ T)
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
    rw [M.realize_packageAtDef hp (by simpa [realize_liftTerm] using hm)
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
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
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
    rw [rowStateGatherFormula, M.realize_statePackageAtDef hp (by simpa using hm)
      (by simpa using hq)]
    simp
  -- Step 1: gather a package for each `y ∈ A`.
  obtain ⟨B, hB⟩ := M.exists_collection (φ := rowStateGatherFormula) hrgat
    ![tagMem, tagEq, condSet, orderCode, A, x] A
    (fun y hy ↦ by
      obtain ⟨D, R, hstate, hdc, hco⟩ := M.exists_approximation_at_state hbnd hsep hgat hfil
        hdom hgra hbr hbl hpsep huni hp hu tagMem tagEq condSet orderCode A hA hm hq
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
      rw [M.realize_statePackageAtDef hp
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

/-! ### The endpoint

Level 2, and 3b's parameterized conclusion. Gather a row package for each `x ∈ A`, filter on
`RowPackageAt` so that **both** the approximation conditions and universal row coverage
survive, project by provenance, merge, and read off global coverage. -/

section FinalAggregation

variable {β : Type v} {k : ℕ} {w : β → ↥M.toMaterialCarrier} {xs : Fin k → ↥M.toMaterialCarrier}

/-- The row-package law, at an arbitrary assignment. -/
theorem realize_rowPackageAtDef (hp : pairingSentence ∈ T)
    {tagMem tagEq condSet orderCode A x a : memLang.Term (β ⊕ Fin k)}
    (hm : ((Term.realize (Sum.elim w xs) tagMem : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim w xs) tagEq : ↥M.toMaterialCarrier) : ZFSet.{u}) =
      natCode eqTag) :
    (rowPackageAtDef tagMem tagEq condSet orderCode A x a).Realize w xs ↔
      RowPackageAt ((Term.realize (Sum.elim w xs) condSet : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) orderCode : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) x : ↥M.toMaterialCarrier) : ZFSet.{u})
        ((Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier) : ZFSet.{u}) := by
  have haM : ((Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier) : ZFSet.{u}) ∈
      M.toMaterialCarrier := (Term.realize (Sum.elim w xs) a : ↥M.toMaterialCarrier).2
  have hAM : ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u}) ∈
      M.toMaterialCarrier := (Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier).2
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
    have htm : natCode memWitnessTag ∈ M.toMaterialCarrier :=
      hm ▸ (Term.realize (Sum.elim w xs) tagMem : ↥M.toMaterialCarrier).2
    have hte : natCode eqTag ∈ M.toMaterialCarrier :=
      hq ▸ (Term.realize (Sum.elim w xs) tagEq : ↥M.toMaterialCarrier).2
    rw [realize_approximationDef (by simpa [realize_liftTerm] using hm)
      (by simpa [realize_liftTerm] using hq)
      (by simpa [realize_liftTerm] using
        M.entry_mem_of_state hp htm hte (Term.realize (Sum.elim w xs) condSet) D)]
    simp [realize_liftTerm]
  simp only [rowPackageAtDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    realize_liftTerm, realize_pairDef]
  have hcovL : ∀ D R : ↥M.toMaterialCarrier,
      (rowCoverageDef (liftTerm (liftTerm A)) (liftTerm (liftTerm x))
          (&(Fin.castSucc (Fin.last k)))).Realize w (Fin.snoc (Fin.snoc xs D) R) ↔
        ∀ y ∈ ((Term.realize (Sum.elim w xs) A : ↥M.toMaterialCarrier) : ZFSet.{u}),
          ZFSet.pair ((Term.realize (Sum.elim w xs) x : ↥M.toMaterialCarrier) : ZFSet.{u}) y ∈
            (D : ZFSet.{u}) := by
    intro D R
    rw [realize_rowCoverageDef]
    simp [realize_liftTerm]
  constructor
  · rintro ⟨D, R, hpair, happ', hcov⟩
    exact ⟨(D : ZFSet.{u}), (R : ZFSet.{u}), hpair, ((happ D R).1 happ').1,
      ((happ D R).1 happ').2, (hcovL D R).1 hcov⟩
  · rintro ⟨D, R, hpair, hdc, hco, hcov⟩
    have hp2 : ZFSet.pair D R ∈ M.toMaterialCarrier := hpair ▸ haM
    have hDM : D ∈ M.toMaterialCarrier :=
      M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inl rfl))
        (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hp2)
    have hRM : R ∈ M.toMaterialCarrier :=
      M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
        (M.toMaterialCarrier.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hp2)
    exact ⟨⟨D, hDM⟩, ⟨R, hRM⟩, hpair, (happ ⟨D, hDM⟩ ⟨R, hRM⟩).2 ⟨hdc, hco⟩,
      (hcovL ⟨D, hDM⟩ ⟨R, hRM⟩).2 hcov⟩

end FinalAggregation

/-- The row package is a carrier element, at pairing. -/
theorem rowPackageAt_mem (hp : pairingSentence ∈ T) {condSet orderCode A x : ZFSet.{u}}
    {D R : ↥M.toMaterialCarrier}
    (hdc : DescentClosed condSet A (D : ZFSet.{u}))
    (hco : CorrectOn condSet orderCode (D : ZFSet.{u}) (R : ZFSet.{u}))
    (hcov : ∀ y ∈ A, ZFSet.pair x y ∈ (D : ZFSet.{u})) :
    ∃ a : ↥M.toMaterialCarrier, RowPackageAt condSet orderCode A x (a : ZFSet.{u}) :=
  ⟨⟨ZFSet.pair (D : ZFSet.{u}) (R : ZFSet.{u}), M.pair_mem hp D.2 R.2⟩,
    (D : ZFSet.{u}), (R : ZFSet.{u}), rfl, hdc, hco, hcov⟩

/-- **3b's parameterized endpoint: the atomic recursion exists inside the ground.**

Gather a row package for each `x ∈ A`, filter on `RowPackageAt` so that both the
approximation conditions *and* universal row coverage survive, project by provenance, merge,
and read off global coverage. `atomicCoherentOn_of_correctOn` converts that into coherence.

Charged to `T`: the named scheme instances and the finite-closure axioms, plus general Union.
**No Foundation, no Infinity, no Power Set.** `A × A` is never formed, no
`InternalNameCoding` appears, and the external forcing relation is not mentioned. -/
theorem exists_atomicCoherentOn (hbnd : entryBoundSentence ∈ T)
    (hsep : stageSeparationSentence ∈ T) (hgat : packageGatherSentence ∈ T)
    (hfil : packageFilterSentence ∈ T) (hdom : domainFamilySentence ∈ T)
    (hgra : graphFamilySentence ∈ T) (hbr : predBoundRightSentence ∈ T)
    (hbl : predBoundLeftSentence ∈ T) (hpsep : predSepSentence ∈ T)
    (hrgat : rowStateGatherSentence ∈ T) (hrfil : rowStateFilterSentence ∈ T)
    (hfgat : rowFinalGatherSentence ∈ T) (hffil : rowFinalFilterSentence ∈ T)
    (huni : unionSentence ∈ T)
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (tagMem tagEq condSet orderCode A : ↥M.toMaterialCarrier)
    (hA : (A : ZFSet.{u}).IsTransitive)
    (hm : (tagMem : ZFSet.{u}) = natCode memWitnessTag)
    (hq : (tagEq : ZFSet.{u}) = natCode eqTag) :
    ∃ R : ↥M.toMaterialCarrier,
      AtomicCoherentOn (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
        (R : ZFSet.{u}) := by
  have hAM : (A : ZFSet.{u}) ∈ M.toMaterialCarrier := A.2
  have hgatherBody : ∀ x a : ↥M.toMaterialCarrier,
      (rowFinalGatherFormula.Realize ![tagMem, tagEq, condSet, orderCode, A] ![x, a] ↔
        RowPackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
          (x : ZFSet.{u}) (a : ZFSet.{u})) := by
    intro x a
    rw [rowFinalGatherFormula, M.realize_rowPackageAtDef hp (by simpa using hm)
      (by simpa using hq)]
    simp
  -- Step 1: a row package for each `x ∈ A`.
  obtain ⟨B, hB⟩ := M.exists_collection (φ := rowFinalGatherFormula) hfgat
    ![tagMem, tagEq, condSet, orderCode, A] A
    (fun x hx ↦ by
      obtain ⟨D, R, hdc, hco, hcov⟩ := M.exists_rowApproximation hbnd hsep hgat hfil hdom
        hgra hbr hbl hpsep hrgat hrfil huni hp hu tagMem tagEq condSet orderCode A hA
        hm hq x hx
      obtain ⟨a, ha⟩ := M.rowPackageAt_mem hp hdc hco hcov
      exact ⟨a, (hgatherBody x a).2 ha⟩)
  -- Step 2: filter, retaining BOTH conditions.
  obtain ⟨F, hF⟩ := M.exists_separation (φ := rowFinalFilterFormula) hffil
    ![tagMem, tagEq, condSet, orderCode, A] B
  have hfilterBody : ∀ a : ↥M.toMaterialCarrier,
      (rowFinalFilterFormula.Realize ![tagMem, tagEq, condSet, orderCode, A] ![a] ↔
        ∃ x ∈ (A : ZFSet.{u}), RowPackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u})
          (A : ZFSet.{u}) x (a : ZFSet.{u})) := by
    intro a
    have hrp : ∀ t : ↥M.toMaterialCarrier,
        ((rowPackageAtDef (liftTerm (var (Sum.inl 0))) (liftTerm (var (Sum.inl 1)))
            (liftTerm (var (Sum.inl 2))) (liftTerm (var (Sum.inl 3)))
            (liftTerm (var (Sum.inl 4))) (&(Fin.last 1)) (liftTerm (&0))).Realize
          ![tagMem, tagEq, condSet, orderCode, A] (Fin.snoc ![a] t) ↔
          RowPackageAt (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u})
            (t : ZFSet.{u}) (a : ZFSet.{u})) := by
      intro t
      rw [M.realize_rowPackageAtDef hp
        (by simpa [liftTerm, Term.realize_relabel] using hm)
        (by simpa [liftTerm, Term.realize_relabel] using hq)]
      simp [liftTerm]
    simp only [rowFinalFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
      Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
      realize_liftTerm]
    exact ⟨fun ⟨t, ht, hpa⟩ ↦ ⟨(t : ZFSet.{u}), ht, (hrp t).1 hpa⟩,
      fun ⟨t, ht, hpa⟩ ↦ ⟨⟨t, M.toMaterialCarrier.mem_trans ht hAM⟩, ht,
        (hrp ⟨t, _⟩).2 hpa⟩⟩
  -- Step 3: project by provenance, then merge.
  obtain ⟨D₀, R₀, hDc, hRc⟩ := M.exists_projections hdom hgra huni F
  have hvalid : ∀ a ∈ (F : ZFSet.{u}),
      Approximation (condSet : ZFSet.{u}) (orderCode : ZFSet.{u}) (A : ZFSet.{u}) a := by
    intro a ha
    have haM := M.toMaterialCarrier.mem_trans ha F.2
    obtain ⟨-, hcert⟩ := (hF ⟨a, haM⟩).1 ha
    obtain ⟨t, -, hpa⟩ := (hfilterBody ⟨a, haM⟩).1 hcert
    exact approximation_of_rowPackageAt hpa
  obtain ⟨-, hCO₀⟩ := approximation_union hvalid hDc hRc
  -- Step 4: global coverage, then coherence.
  refine ⟨R₀, atomicCoherentOn_of_correctOn (fun x hx y hy ↦ ?_) hCO₀⟩
  obtain ⟨a, haB, hpa⟩ := hB ⟨x, M.toMaterialCarrier.mem_trans hx hAM⟩ hx
  have hpa' := (hgatherBody ⟨x, _⟩ a).1 hpa
  have haF : (a : ZFSet.{u}) ∈ (F : ZFSet.{u}) :=
    (hF a).2 ⟨haB, (hfilterBody a).2 ⟨x, hx, hpa'⟩⟩
  obtain ⟨D, R, haeq, -, -, hcov⟩ := hpa'
  exact (hDc _).2 ⟨D, R, haeq ▸ haF, hcov y hy⟩

end MaterialGround

end Forcing
