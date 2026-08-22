/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes

/-!
# The least internal inductive set

`ω`, for the ambient-domain construction. Infinity supplies *some* inductive set; this module
cuts out the least one and gives the iteration exactly the three facts it needs.

## The scope of "least" is internal, and deliberately so

**`ω` is least among the inductive sets belonging to the material carrier, not among all
ambient `ZFSet`s.** The leastness condition quantifies over carrier elements, because that is
what a Separation instance can express and what the ground can verify. `OmegaValue` states
this explicitly rather than leaving it to be read off the formula, so nothing here advertises
an external second-order leastness claim.

The distinction matters for what may be concluded. Internal leastness suffices for everything
downstream — the iteration is indexed by `ω` and justified by induction — but it is strictly
weaker than external minimality, and a later consumer that wanted the latter would have to
earn it.

## Induction is formula-relative

`omega_induction` takes the induction predicate as **the realization of a named formula at
named parameters**, never as an arbitrary `ZFSet → Prop`. An unrestricted version would assert
a scheme the ground does not have. Each consumer therefore names and pays for its own
Separation instance, exactly as elsewhere in this development.

## Deliberately absent

No claim that the members of `ω` are the finite ordinals. Nothing here or downstream needs it,
and proving it would pull in a von Neumann ordinal development the repository does not
otherwise have. If a consumer ever wants it, it should be a separately named theorem rather
than folded into this interface.

Two related facts are also *not* declared here, for different reasons. `∅ ∈ n ∨ ∅ = n` for
`n ∈ ω` is a **consequence** of an approximation existing — exact support applied to the base
entry gives it — so it is left to the iteration to declare if the compiled proof turns out to
want it. And `n ∉ n` is **free** from ambient well-foundedness (`ZFSet.mem_irrefl`), for the
same reason Foundation is free for material carriers; charging an induction instance for it
would be paying twice.

## Main definitions

* `Forcing.OmegaValue`: the exact contract — membership in the supplied inductive set, plus
  membership in every *internal* inductive set.
* `Forcing.omegaSepFormula`: the Separation instance carving it out.
* `Forcing.omegaTransFormula`: the one named induction instance this module charges.

## Main results

* `Forcing.MaterialGround.exists_omega`: `ω` exists inside the ground.
* `Forcing.omegaValue_isInductive`, `Forcing.omegaValue_least`: the two structural facts.
* `Forcing.MaterialGround.omega_induction`: formula-relative induction, separately priced.
* `Forcing.MaterialGround.omegaValue_isTransitive`: `ω` is transitive — the load-bearing fact
  for the iteration, since bounded approximation indices must return to `ω`.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-- **The `ω` contract.** Membership in the supplied inductive set `w`, together with
membership in every inductive set *belonging to the carrier* — internal leastness, not
external minimality. -/
def OmegaValue (M : MaterialCarrier.{u}) (w omega : ZFSet.{u}) : Prop :=
  ∀ n, n ∈ omega ↔ n ∈ w ∧ ∀ u : ↥M, IsInductive (u : ZFSet.{u}) → n ∈ (u : ZFSet.{u})

/-- **The `ω` instance**: the Separation sentence carving the least internal inductive set out
of an inductive one. Its condition is stated against the shared `inductiveDef`. -/
def omegaSepFormula : memLang.BoundedFormula (Fin 0) 1 :=
  ∀' (inductiveDef (&(Fin.last 1)) ⟹
    memFormula (liftTerm (&(0 : Fin 1))) (&(Fin.last 1)))

def omegaSepSentence : memLang.Sentence := separationSentence omegaSepFormula

theorem omegaSepSentence_mem_scheme : omegaSepSentence ∈ separationScheme :=
  separationSentence_mem_scheme omegaSepFormula

/-- The leastness condition realizes to quantification over **carrier** elements. No
hypotheses and no theory axioms. -/
theorem realize_omegaSepFormula {M : MaterialCarrier.{u}} (n : ↥M) :
    omegaSepFormula.Realize (default : Fin 0 → ↥M) ![n] ↔
      ∀ u : ↥M, IsInductive (u : ZFSet.{u}) → (n : ZFSet.{u}) ∈ (u : ZFSet.{u}) := by
  simp only [omegaSepFormula, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm, realize_inductiveDef]

/-- **`ω` is inductive.** -/
theorem omegaValue_isInductive {M : MaterialCarrier.{u}} {w omega : ZFSet.{u}}
    (hw : IsInductive w) (hom : OmegaValue M w omega) : IsInductive omega := by
  constructor
  · exact (hom _).2 ⟨hw.1, fun u hu ↦ hu.1⟩
  · intro x hx
    obtain ⟨hxw, hxu⟩ := (hom x).1 hx
    exact (hom _).2 ⟨hw.2 x hxw, fun u hu ↦ hu.2 x (hxu u hu)⟩

/-- **Internal leastness**: `ω` is contained in every inductive set belonging to the carrier.
This is the whole of the leastness claim — nothing is asserted about ambient inductive sets
outside the carrier. -/
theorem omegaValue_least {M : MaterialCarrier.{u}} {w omega : ZFSet.{u}}
    (hom : OmegaValue M w omega) (u : ↥M) (hu : IsInductive (u : ZFSet.{u})) :
    ∀ n ∈ omega, n ∈ (u : ZFSet.{u}) :=
  fun n hn ↦ ((hom n).1 hn).2 u hu

/-- **The transitivity instance**: `n ⊆ ω`, with `ω` as the parameter and `n` the separated
variable. One named formula-relative induction instance, and the only one this module
charges. -/
def omegaTransFormula : memLang.BoundedFormula (Fin 1) 1 :=
  ∀' (memFormula (&(Fin.last 1)) (liftTerm (&(0 : Fin 1))) ⟹
    memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 0))))

/-- The transitivity instance reads as containment in `ω`. No hypotheses, no theory axioms. -/
theorem realize_omegaTransFormula {M : MaterialCarrier.{u}} (omega n : ↥M) :
    omegaTransFormula.Realize ![omega] ![n] ↔
      ∀ z ∈ (n : ZFSet.{u}), z ∈ (omega : ZFSet.{u}) := by
  have hnM : (n : ZFSet.{u}) ∈ M := n.2
  simp only [omegaTransFormula, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Sum.elim_inl, Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm]
  exact ⟨fun h z hz ↦ h ⟨z, M.mem_trans hz hnM⟩ hz, fun h z ↦ h (z : ZFSet.{u})⟩

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **`ω` exists inside the ground.** Charged: Infinity and one Separation instance. -/
theorem exists_omega (hinf : infinitySentence ∈ T) (hsep : omegaSepSentence ∈ T) :
    ∃ w : ZFSet.{u}, ∃ omega : ↥M.toMaterialCarrier,
      IsInductive w ∧ OmegaValue M.toMaterialCarrier w (omega : ZFSet.{u}) := by
  obtain ⟨w, hwM, hw⟩ := M.exists_inductive hinf
  obtain ⟨omega, hom⟩ := M.exists_separation (φ := omegaSepFormula) hsep default ⟨w, hwM⟩
  refine ⟨w, omega, hw, fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩⟩
  · have hnM := M.toMaterialCarrier.mem_trans hn omega.2
    obtain ⟨hnw, hcond⟩ := (hom ⟨n, hnM⟩).1 hn
    exact ⟨hnw, (realize_omegaSepFormula ⟨n, hnM⟩).1 hcond⟩
  · have hnM := M.toMaterialCarrier.mem_trans hn.1 hwM
    exact (hom ⟨n, hnM⟩).2 ⟨hn.1, (realize_omegaSepFormula ⟨n, hnM⟩).2 hn.2⟩

/-- **Formula-relative induction on `ω`.**

The induction predicate is the realization of `φ` at `params` — never an arbitrary
`ZFSet → Prop`, which would assert a scheme the ground does not have. Each use names and pays
for its own Separation instance.

The base and successor hypotheses are stated up to the *representative*: the caller supplies
them for any carrier element whose underlying set is `∅`, respectively `insert n n`, which
avoids threading membership proofs through the interface. -/
theorem omega_induction {k : ℕ} {φ : memLang.BoundedFormula (Fin k) 1}
    (hsep : separationSentence φ ∈ T) (params : Fin k → ↥M.toMaterialCarrier)
    {w : ZFSet.{u}} {omega : ↥M.toMaterialCarrier}
    (hw : IsInductive w)
    (hom : OmegaValue M.toMaterialCarrier w (omega : ZFSet.{u}))
    (hzero : ∀ z : ↥M.toMaterialCarrier, (z : ZFSet.{u}) = ∅ → φ.Realize params ![z])
    (hsucc : ∀ n : ↥M.toMaterialCarrier, (n : ZFSet.{u}) ∈ (omega : ZFSet.{u}) →
      φ.Realize params ![n] → ∀ s : ↥M.toMaterialCarrier,
        (s : ZFSet.{u}) = insert (n : ZFSet.{u}) (n : ZFSet.{u}) → φ.Realize params ![s]) :
    ∀ n : ↥M.toMaterialCarrier, (n : ZFSet.{u}) ∈ (omega : ZFSet.{u}) →
      φ.Realize params ![n] := by
  have hindΩ : IsInductive (omega : ZFSet.{u}) := omegaValue_isInductive hw hom
  obtain ⟨S, hS⟩ := M.exists_separation (φ := φ) hsep params omega
  -- The separated set is inductive, so internal leastness places `ω` inside it.
  have hindS : IsInductive (S : ZFSet.{u}) := by
    constructor
    · have h0M : (∅ : ZFSet.{u}) ∈ M.toMaterialCarrier :=
        M.toMaterialCarrier.mem_trans hindΩ.1 omega.2
      exact (hS ⟨∅, h0M⟩).2 ⟨hindΩ.1, hzero ⟨∅, h0M⟩ rfl⟩
    · intro x hx
      have hxM := M.toMaterialCarrier.mem_trans hx S.2
      obtain ⟨hxΩ, hφ⟩ := (hS ⟨x, hxM⟩).1 hx
      have hsΩ : insert x x ∈ (omega : ZFSet.{u}) := hindΩ.2 x hxΩ
      have hsM := M.toMaterialCarrier.mem_trans hsΩ omega.2
      exact (hS ⟨insert x x, hsM⟩).2 ⟨hsΩ, hsucc ⟨x, hxM⟩ hxΩ hφ ⟨insert x x, hsM⟩ rfl⟩
  intro n hn
  exact ((hS n).1 (omegaValue_least hom S hindS (n : ZFSet.{u}) hn)).2

/-- **`ω` is transitive.**

This is the load-bearing `ω`-fact for the iteration: an approximation's indices satisfy
`k ∈ n ∨ k = n` with `n ∈ ω`, and it is transitivity that returns `k` to `ω` so that the
recurrence and the induction hypotheses apply to it. Without it the bounded indices would
escape the set the induction is over.

Charged: one named induction instance, `omegaTransFormula`. -/
theorem omegaValue_isTransitive (hsep : separationSentence omegaTransFormula ∈ T)
    {w : ZFSet.{u}} {omega : ↥M.toMaterialCarrier}
    (hw : IsInductive w)
    (hom : OmegaValue M.toMaterialCarrier w (omega : ZFSet.{u})) :
    (omega : ZFSet.{u}).IsTransitive := by
  have key : ∀ n : ↥M.toMaterialCarrier, (n : ZFSet.{u}) ∈ (omega : ZFSet.{u}) →
      omegaTransFormula.Realize ![omega] ![n] := by
    refine M.omega_induction hsep ![omega] hw hom (fun z hz ↦ ?_) (fun n hn hφ s hs ↦ ?_)
    · rw [realize_omegaTransFormula, hz]
      exact fun y hy ↦ absurd hy (ZFSet.notMem_empty _)
    · rw [realize_omegaTransFormula, hs]
      have hindΩ : IsInductive (omega : ZFSet.{u}) := omegaValue_isInductive hw hom
      intro y hy
      rcases ZFSet.mem_insert_iff.1 hy with rfl | hy'
      · exact hn
      · exact (realize_omegaTransFormula omega n).1 hφ y hy'
  intro x hx
  have hxM := M.toMaterialCarrier.mem_trans hx omega.2
  exact (realize_omegaTransFormula omega ⟨x, hxM⟩).1 (key ⟨x, hxM⟩ hx)

end MaterialGround

end Forcing
