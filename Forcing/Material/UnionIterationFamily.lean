/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.UnionIterationInternal

/-!
# The ambient transitive domain

The end of the union-iteration tranche: gather the iterates of a seed over internal `ω`,
flatten them, and read off a transitive set containing whatever the seed contained.

This is what closes the parameterized gap in `MaterialGround.exists_atomicCoherentOn`, which
takes its transitive domain as a hypothesis.

## The exact family

```text
IterateFamily M seed ω F  :=  ∀ S, S ∈ F ↔ ∃ n ∈ ω, UnionIterate M seed n S
```

A biconditional, not coverage. Collection alone gives only the `←` direction, since its output
may carry junk and its witness at each index is arbitrary. The `→` direction comes from the
Separation filter, and the *upgrade* from coverage to exactness comes from
`unionIterate_unique`: a genuine iterate at `n` must equal whichever witness Collection chose
there, hence lies in the collected set.

## Where Infinity enters, and where it stops

Infinity is charged here and only here, to obtain internal `ω`. It reaches
`exists_atomicCoherentOn` only as the *supplied* domain — that theorem remains priced without
it, which is the separation ADR 0005 predicted and this module preserves.

No Cartesian product is formed, and no Power Set is used.
-/

universe u

namespace Forcing

open FirstOrder Language UnionIteration

/-- The **exact** family of iterates of `seed` along `ω`. -/
def IterateFamily (M : MaterialCarrier.{u}) (seed omega F : ZFSet.{u}) : Prop :=
  ∀ S, S ∈ F ↔ ∃ n ∈ omega, UnionIterate M seed n S

/-- **The iterate-gathering instance** (Collection): one iterate per index of `ω`. -/
def iterateGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  unionIterateDef (var (Sum.inl 0)) (&0) (&1)

/-- **The iterate-filter instance** (Separation): keep exactly the sets that *are* iterates at
some index of `ω`. This is what turns Collection's coverage into the biconditional. -/
def iterateFilterFormula : memLang.BoundedFormula (Fin 2) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 1))) ⊓
    unionIterateDef (liftTerm (var (Sum.inl 0))) (&(Fin.last 1))
      (liftTerm (&(0 : Fin 1))))

def iterateGatherSentence : memLang.Sentence := collectionSentence iterateGatherFormula

def iterateFilterSentence : memLang.Sentence := separationSentence iterateFilterFormula

theorem iterateGatherSentence_mem_scheme : iterateGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme iterateGatherFormula

theorem iterateFilterSentence_mem_scheme : iterateFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme iterateFilterFormula

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **The exact family exists inside the ground.**

Gather, filter, and upgrade. The upgrade is where `unionIterate_unique` is consumed: a genuine
iterate at `n` equals whichever witness Collection chose there, so it lies in the collected
set and survives the filter. -/
theorem exists_iterateFamily (hgat : iterateGatherSentence ∈ T)
    (hfil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmem : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T) (huni : unionSentence ∈ T)
    {w : ZFSet.{u}} {omega : ↥M.toMaterialCarrier}
    (hw : IsInductive w)
    (hom : OmegaValue M.toMaterialCarrier w (omega : ZFSet.{u}))
    (seed : ↥M.toMaterialCarrier) :
    ∃ F : ↥M.toMaterialCarrier,
      IterateFamily M.toMaterialCarrier (seed : ZFSet.{u}) (omega : ZFSet.{u})
        (F : ZFSet.{u}) := by
  have homM : (omega : ZFSet.{u}) ∈ M.toMaterialCarrier := omega.2
  -- an iterate is a carrier element, through its witnessing trace
  have hiterM : ∀ n S : ZFSet.{u},
      UnionIterate M.toMaterialCarrier (seed : ZFSet.{u}) n S → S ∈ M.toMaterialCarrier := by
    rintro n S ⟨t, htM, -, hS⟩
    exact (MaterialCarrier.pair_components_mem_of_mem htM hS).2
  have hgather : ∀ n S : ↥M.toMaterialCarrier,
      (iterateGatherFormula.Realize ![seed] ![n, S] ↔
        UnionIterate M.toMaterialCarrier (seed : ZFSet.{u}) (n : ZFSet.{u})
          (S : ZFSet.{u})) := by
    intro n S
    rw [iterateGatherFormula, realize_unionIterateDef]
    simp
  -- Step 1: gather.
  obtain ⟨B, hB⟩ := M.exists_collection (φ := iterateGatherFormula) hgat ![seed] omega
    (fun n hn ↦ by
      obtain ⟨S, hSM, hS⟩ := M.exists_unionIterate hex hp hu huni hw hom seed n hn
      exact ⟨⟨S, hSM⟩, (hgather n ⟨S, hSM⟩).2 hS⟩)
  -- Step 2: filter.
  obtain ⟨F, hF⟩ := M.exists_separation (φ := iterateFilterFormula) hfil ![seed, omega] B
  have hfilter : ∀ S : ↥M.toMaterialCarrier,
      (iterateFilterFormula.Realize ![seed, omega] ![S] ↔
        ∃ n ∈ (omega : ZFSet.{u}), UnionIterate M.toMaterialCarrier (seed : ZFSet.{u}) n
          (S : ZFSet.{u})) := by
    intro S
    have hui : ∀ t : ↥M.toMaterialCarrier,
        ((unionIterateDef (liftTerm (var (Sum.inl 0))) (&(Fin.last 1))
            (liftTerm (&(0 : Fin 1)))).Realize ![seed, omega] (Fin.snoc ![S] t) ↔
          UnionIterate M.toMaterialCarrier (seed : ZFSet.{u}) (t : ZFSet.{u})
            (S : ZFSet.{u})) := by
      intro t
      rw [realize_unionIterateDef]
      simp [liftTerm]
    simp only [iterateFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
      memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
      Sum.elim_inl, Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero,
      Matrix.cons_val_one, realize_liftTerm]
    exact ⟨fun ⟨t, ht, hui'⟩ ↦ ⟨(t : ZFSet.{u}), ht, (hui t).1 hui'⟩,
      fun ⟨t, ht, hui'⟩ ↦ ⟨⟨t, M.toMaterialCarrier.mem_trans ht homM⟩, ht,
        (hui ⟨t, _⟩).2 hui'⟩⟩
  refine ⟨F, fun S ↦ ⟨fun hS ↦ ?_, fun hS ↦ ?_⟩⟩
  · have hSM := M.toMaterialCarrier.mem_trans hS F.2
    exact (hfilter ⟨S, hSM⟩).1 ((hF ⟨S, hSM⟩).1 hS).2
  · -- the upgrade: uniqueness identifies `S` with Collection's chosen witness
    obtain ⟨n, hn, hiter⟩ := hS
    have hSM := hiterM n S hiter
    have hnM := M.toMaterialCarrier.mem_trans hn homM
    obtain ⟨S', hS'B, hS'⟩ := hB ⟨n, hnM⟩ hn
    have hSS' : S = (S' : ZFSet.{u}) :=
      M.unionIterate_unique hmem hagree hw hom seed ⟨n, hnM⟩ hn hiter
        ((hgather ⟨n, hnM⟩ S').1 hS')
    exact (hF ⟨S, hSM⟩).2 ⟨hSS' ▸ hS'B, (hfilter ⟨S, hSM⟩).2 ⟨n, hn, hiter⟩⟩

/-- **The ambient transitive domain.** For any two carrier elements there is a transitive
carrier element containing both — the hypothesis `exists_atomicCoherentOn` takes as given.

Transitivity is the successor law read through the family: a member of a member lies in the
*next* iterate, which the family also contains.

Charged: Infinity and `omegaSepSentence` for internal `ω`; the gather and filter instances;
the already-named approximation existence and uniqueness instances; Pairing, Binary Union, and
General Union. **No Empty Set** — `∅` arrives as a member of `ω`. No Foundation, no Power Set,
and no Cartesian product. -/
theorem exists_transitiveDomain (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (hgat : iterateGatherSentence ∈ T) (hfil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmem : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T) (huni : unionSentence ∈ T)
    (x y : ↥M.toMaterialCarrier) :
    ∃ A : ↥M.toMaterialCarrier, (A : ZFSet.{u}).IsTransitive ∧
      (x : ZFSet.{u}) ∈ (A : ZFSet.{u}) ∧ (y : ZFSet.{u}) ∈ (A : ZFSet.{u}) := by
  obtain ⟨w, omega, hw, hom⟩ := M.exists_omega hinf hosep
  have homM : (omega : ZFSet.{u}) ∈ M.toMaterialCarrier := omega.2
  have hind : IsInductive (omega : ZFSet.{u}) := omegaValue_isInductive hw hom
  set seed : ↥M.toMaterialCarrier :=
    ⟨({(x : ZFSet.{u}), (y : ZFSet.{u})} : ZFSet.{u}), M.insert_pair_mem hp x.2 y.2⟩
    with hseed
  obtain ⟨F, hF⟩ := M.exists_iterateFamily hgat hfil hex hmem hagree hp hu huni hw hom seed
  -- `∅` arrives as a member of `ω`, so no Empty Set axiom is charged.
  have h0M : (∅ : ZFSet.{u}) ∈ M.toMaterialCarrier :=
    M.toMaterialCarrier.mem_trans hind.1 homM
  have hseedF : (seed : ZFSet.{u}) ∈ (F : ZFSet.{u}) :=
    (hF _).2 ⟨∅, hind.1, M.unionIterate_base hp seed ⟨∅, h0M⟩ rfl⟩
  refine ⟨⟨ZFSet.sUnion (F : ZFSet.{u}), M.sUnion_mem huni F.2⟩, fun a ha z hz ↦ ?_, ?_, ?_⟩
  · -- transitivity: a member of a member lies in the next iterate
    obtain ⟨S, hSF, haS⟩ := ZFSet.mem_sUnion.1 ha
    obtain ⟨n, hn, hiter⟩ := (hF S).1 hSF
    have hnM := M.toMaterialCarrier.mem_trans hn homM
    have hsuccOmega : insert n n ∈ (omega : ZFSet.{u}) := hind.2 n hn
    have hsuccM := M.toMaterialCarrier.mem_trans hsuccOmega homM
    have hnext : ZFSet.sUnion S ∈ (F : ZFSet.{u}) :=
      (hF _).2 ⟨insert n n, hsuccOmega,
        M.unionIterate_succ hp hu huni ⟨insert n n, hsuccM⟩ rfl hiter⟩
    exact ZFSet.mem_sUnion.2 ⟨ZFSet.sUnion S, hnext, ZFSet.mem_sUnion.2 ⟨a, haS, hz⟩⟩
  · exact ZFSet.mem_sUnion.2 ⟨(seed : ZFSet.{u}), hseedF,
      ZFSet.mem_insert_iff.2 (Or.inl rfl)⟩
  · exact ZFSet.mem_sUnion.2 ⟨(seed : ZFSet.{u}), hseedF,
      ZFSet.mem_insert_iff.2 (Or.inr (ZFSet.mem_singleton.2 rfl))⟩

end MaterialGround

end Forcing
