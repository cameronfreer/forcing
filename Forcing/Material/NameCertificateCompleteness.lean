/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.NameCertificate
import Forcing.Material.AxiomSchemes
import Forcing.Material.Axioms

/-!
# Certificate completeness

ADR 0006, tranche 2: every hereditarily valid carrier element has a certificate **in the
ground**:

```text
IsNameCode cs x → x ∈ M → ∃ D ∈ M, x ∈ D ∧ IsNameDomain cs D
```

## Direct induction, not ω-iteration

The proof is an external induction on `IsNameCode`. At a valid code `x`, the induction
hypothesis supplies an internal certificate for the subname of each branch; the named schemes
gather and filter those certificates into a family `F`; and `isNameDomain_assemble` closes the
step with `{x} ∪ ⋃₀ F`. There is no unrestricted internal induction, no least fixed point, and
no iteration along `ω` — because `IsNameDomain` accepts *any* closed domain and closed domains
are preserved by union.

## Coverage, not exhaustiveness

Collection supplies one certificate per branch, and the filter keeps exactly the collected sets
that certify *some* branch of `x`:

```text
D ∈ F ↔ D ∈ B ∧ ∃ b ∈ x, BranchCertificate cs b D
```

`F` is **not** claimed to contain every certificate — certificates are not unique — and the
assembly step asks only for closure of each retained domain and coverage of each branch, which
is exactly what the filter delivers.

## Ledger

One Collection instance (`certificateGatherSentence`), one Separation instance
(`certificateFilterSentence`), Pairing, and General Union — the last two for `{x} ∪ ⋃₀ F`,
through `singleton_mem`, `sUnion_mem`, and `union_mem_of_sUnion` (so no separate Binary Union).
**No Infinity, no Empty Set, no Power Set.** Carrier membership of each subname comes from
`pair_components_mem_of_mem`, so `x ∈ M` is the only membership carried through the induction.

## Main results

* `Forcing.MaterialGround.exists_certificateFamily`: the gather/filter step.
* `Forcing.MaterialGround.exists_nameDomain_of_isNameCode`: certificate completeness.
-/

universe u

namespace Forcing

open FirstOrder Language

/-! ### The two instances -/

/-- **The certificate-gathering instance** (Collection): parameter `cs`, indexed by a branch `b`,
witnessed by a certificate domain `D`. Its condition-set parameter lets the one sentence serve
every recursive call. -/
def certificateGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  branchCertificateDef (var (Sum.inl 0)) (&0) (&1)

/-- **The certificate-filter instance** (Separation): parameters `x` and `cs`; keep the sets that
certify some branch of `x`. -/
def certificateFilterFormula : memLang.BoundedFormula (Fin 2) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 0))) ⊓
    branchCertificateDef (liftTerm (var (Sum.inl 1))) (&(Fin.last 1)) (liftTerm (&(0 : Fin 1))))

def certificateGatherSentence : memLang.Sentence := collectionSentence certificateGatherFormula

def certificateFilterSentence : memLang.Sentence := separationSentence certificateFilterFormula

theorem certificateGatherSentence_mem_scheme : certificateGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme certificateGatherFormula

theorem certificateFilterSentence_mem_scheme : certificateFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme certificateFilterFormula

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

theorem realize_certificateGatherFormula (cs b D : ↥M.toMaterialCarrier) :
    certificateGatherFormula.Realize ![cs] ![b, D] ↔
      BranchCertificate (cs : ZFSet.{u}) (b : ZFSet.{u}) (D : ZFSet.{u}) := by
  rw [certificateGatherFormula, realize_branchCertificateDef]
  simp

theorem realize_certificateFilterFormula (x cs D : ↥M.toMaterialCarrier) :
    certificateFilterFormula.Realize ![x, cs] ![D] ↔
      ∃ b ∈ (x : ZFSet.{u}), BranchCertificate (cs : ZFSet.{u}) b (D : ZFSet.{u}) := by
  have hw : ∀ b : ↥M.toMaterialCarrier,
      (branchCertificateDef (liftTerm (var (Sum.inl 1))) (&(Fin.last 1))
        (liftTerm (&(0 : Fin 1)))).Realize ![x, cs] (Fin.snoc ![D] b) ↔
      BranchCertificate (cs : ZFSet.{u}) (b : ZFSet.{u}) (D : ZFSet.{u}) := by
    intro b
    rw [realize_branchCertificateDef]
    simp [liftTerm]
  simp only [certificateFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Sum.elim_inl, Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  exact ⟨fun ⟨b, hb, h⟩ ↦ ⟨(b : ZFSet.{u}), hb, (hw b).1 h⟩,
    fun ⟨b, hb, h⟩ ↦ ⟨⟨b, M.toMaterialCarrier.mem_trans hb x.2⟩, hb, (hw _).2 h⟩⟩

/-! ### Gather and filter -/

/-- **The certificate family.** If every branch of `x` has a certificate in the ground, then some
member `F` of the ground consists of name domains and covers every branch of `x`. Coverage only:
`F` is filtered from Collection's bound and need not contain every certificate. -/
theorem exists_certificateFamily (hgat : certificateGatherSentence ∈ T)
    (hfil : certificateFilterSentence ∈ T) {cs x : ZFSet.{u}} (hcs : cs ∈ M) (hx : x ∈ M)
    (hwit : ∀ b ∈ x, ∃ D ∈ M, BranchCertificate cs b D) :
    ∃ F ∈ M, (∀ D ∈ F, IsNameDomain cs D) ∧ ∀ b ∈ x, ∃ D ∈ F, BranchCertificate cs b D := by
  -- gather
  obtain ⟨B, hB⟩ := M.exists_collection (φ := certificateGatherFormula) hgat ![⟨cs, hcs⟩] ⟨x, hx⟩
    (fun b hb ↦ by
      obtain ⟨D, hDM, hD⟩ := hwit b hb
      exact ⟨⟨D, hDM⟩, (M.realize_certificateGatherFormula ⟨cs, hcs⟩ b ⟨D, hDM⟩).2 hD⟩)
  -- filter
  obtain ⟨F, hF⟩ := M.exists_separation (φ := certificateFilterFormula) hfil ![⟨x, hx⟩, ⟨cs, hcs⟩] B
  refine ⟨F, F.2, fun D hDF ↦ ?_, fun b hb ↦ ?_⟩
  · have hDM := M.toMaterialCarrier.mem_trans hDF F.2
    obtain ⟨-, hcert⟩ := (hF ⟨D, hDM⟩).1 hDF
    obtain ⟨b, -, -, -, -, -, -, hD⟩ := (M.realize_certificateFilterFormula _ _ ⟨D, hDM⟩).1 hcert
    exact hD
  · obtain ⟨D, hDB, hD⟩ := hB ⟨b, M.toMaterialCarrier.mem_trans hb hx⟩ hb
    rw [M.realize_certificateGatherFormula] at hD
    refine ⟨D, (hF D).2 ⟨hDB, ?_⟩, hD⟩
    exact (M.realize_certificateFilterFormula _ _ D).2 ⟨b, hb, hD⟩

/-! ### Completeness -/

/-- **Certificate completeness**: every hereditarily valid element of the ground lies in a name
domain that is itself in the ground. Induction on `IsNameCode`, gather and filter at each node,
assemble with `{x} ∪ ⋃₀ F`. Ledger: one Collection instance, one Separation instance, Pairing,
General Union. -/
theorem exists_nameDomain_of_isNameCode (hgat : certificateGatherSentence ∈ T)
    (hfil : certificateFilterSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {cs : ZFSet.{u}} (hcs : cs ∈ M) {x : ZFSet.{u}} (h : IsNameCode cs x) :
    x ∈ M → ∃ D ∈ M, x ∈ D ∧ IsNameDomain cs D := by
  induction h with
  | mk x branch _ ih =>
    intro hx
    obtain ⟨F, hFM, hFdom, hcov⟩ := M.exists_certificateFamily hgat hfil hcs hx
      (fun b hb ↦ by
        obtain ⟨c, e, rfl, hc⟩ := branch b hb
        have heM := (MaterialCarrier.pair_components_mem_of_mem hx hb).2
        obtain ⟨D, hDM, heD, hD⟩ := ih _ hb c e rfl heM
        exact ⟨D, hDM, c, e, rfl, hc, heD, hD⟩)
    obtain ⟨hxD, hD⟩ := isNameDomain_assemble hFdom hcov
    exact ⟨_, M.union_mem_of_sUnion huni hp (M.singleton_mem hp hx) (M.sUnion_mem huni hFM),
      hxD, hD⟩

end MaterialGround

end Forcing
