/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.ZFC.Rank
import Forcing.Material.NameCoding

/-!
# The maximal name presentation

ADR 0006, tranche 1. The internal name family is the **maximal** hereditarily valid one:

```text
Code    := the carrier elements that are hereditarily valid name codes
code    := the underlying set
decode  := well-founded recursion on the coded branches
```

Everything here is **axiom-free**: no theory sentence is charged. What is proved:

* `IsNameCode`, hereditary validity as a least fixed point, with the branch accessors;
* `decode`, by rank recursion, and its unfolding law;
* `decode_injective` — needed by `branch_mem_code_iff`'s backward direction, and not immediate:
  equality of two `PName.mk` values gives only a *type equality* between index types, so the
  proof matches indices across that equality and recurses through the symmetric equation;
* the presentation `maximal`, with `subname_closed`;
* **maximality as a theorem** (`exists_code_of_isNameCode`): every hereditarily valid carrier
  element is in the range of `code`. This is what will make recognition exact, not merely sound;
* the coding laws `maximal_coding`;
* the certificate's soundness half (`isNameCode_of_mem_nameDomain`): a set-sized domain
  containing the candidate, closed under branch second components, every node locally
  branch-shaped, certifies hereditary validity. Rank induction.

## `Shrink` is a universe bridge, nothing more

`PName`'s branch index lives in `Type u`; carrier elements live in `Type (u + 1)`. So `Code` is
`Shrink.{u}` of the valid carrier subtype, and a code's branch index is `Shrink.{u}` of its member
type (mathlib's `ZFSet.small_coe`). Per ADR 0006 this representation **must not leak**: consumers
see `Code`, `code`, `decode`, and the theorems below, and no module outside this one mentions
`Shrink` or `equivShrink`.

## Main definitions

* `Forcing.IsNameCode`, `Forcing.MaximalNames.decode`, `Forcing.MaximalNames.maximal`.
* `Forcing.IsNameDomain`: the certificate's domain condition, on sets.

## Main results

* `Forcing.MaximalNames.decode_injective`.
* `Forcing.MaximalNames.exists_code_of_isNameCode`: maximality.
* `Forcing.MaximalNames.maximal_coding`: the coding laws.
* `Forcing.isNameCode_of_mem_nameDomain`: certificate soundness.
-/

universe u

namespace Forcing

open PName

/-! ### Hereditary validity -/

/-- **Hereditary name-code validity**, relative to a condition-code set `cs`: every member is a
branch `⟨c, e⟩` with `c ∈ cs` and `e` hereditarily valid. An inductive predicate, hence the least
fixed point, and it carries the induction principle the well-founded arguments need. -/
inductive IsNameCode (cs : ZFSet.{u}) : ZFSet.{u} → Prop
  | mk (x : ZFSet.{u}) (branch : ∀ y ∈ x, ∃ c e, y = ZFSet.pair c e ∧ c ∈ cs)
      (sub : ∀ y ∈ x, ∀ c e, y = ZFSet.pair c e → IsNameCode cs e) : IsNameCode cs x

namespace IsNameCode

variable {cs x : ZFSet.{u}}

theorem branch (h : IsNameCode cs x) : ∀ y ∈ x, ∃ c e, y = ZFSet.pair c e ∧ c ∈ cs := by
  cases h; assumption

theorem sub (h : IsNameCode cs x) : ∀ y ∈ x, ∀ c e, y = ZFSet.pair c e → IsNameCode cs e := by
  cases h; assumption

end IsNameCode

/-- A branch code sits three Kuratowski levels above the subname code it carries. -/
theorem rank_lt_of_pair_mem {c z w : ZFSet.{u}} (h : ZFSet.pair c z ∈ w) : z.rank < w.rank := by
  have h₁ : z.rank < ({c, z} : ZFSet.{u}).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  have h₂ : ({c, z} : ZFSet.{u}).rank < (ZFSet.pair c z).rank :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
  exact (h₁.trans h₂).trans (ZFSet.rank_lt_of_mem h)

/-! ### The certificate's soundness half -/

/-- **The certificate's domain condition**: closed under branch second components, every member
locally branch-shaped. Per-candidate — this is not a master name set. -/
def IsNameDomain (cs D : ZFSet.{u}) : Prop :=
  ∀ z ∈ D, ∀ y ∈ z, ∃ c e, y = ZFSet.pair c e ∧ c ∈ cs ∧ e ∈ D

/-- **Soundness**: membership in a name domain certifies hereditary validity. Rank induction;
axiom-free. -/
theorem isNameCode_of_mem_nameDomain {cs D : ZFSet.{u}} (hD : IsNameDomain cs D) :
    ∀ x ∈ D, IsNameCode cs x := by
  intro x
  induction x using (InvImage.wf ZFSet.rank Ordinal.lt_wf).induction with
  | _ x ih =>
    intro hx
    refine IsNameCode.mk x (fun y hy ↦ ?_) (fun y hy c e hye ↦ ?_)
    · obtain ⟨c, e, hye, hc, -⟩ := hD x hx y hy
      exact ⟨c, e, hye, hc⟩
    · obtain ⟨c', e', hye', -, he'⟩ := hD x hx y hy
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (hye.symm.trans hye')
      exact ih e (rank_lt_of_pair_mem (hye ▸ hy)) he'

namespace MaximalNames

/-! ### Branch accessors -/

section Branch

variable {cs x y : ZFSet.{u}}

/-- The condition code of a branch. -/
noncomputable def branchCond (h : IsNameCode cs x) (hy : y ∈ x) : ZFSet.{u} :=
  Classical.choose (h.branch y hy)

/-- The subname code of a branch. -/
noncomputable def branchSub (h : IsNameCode cs x) (hy : y ∈ x) : ZFSet.{u} :=
  Classical.choose (Classical.choose_spec (h.branch y hy))

theorem branch_eq (h : IsNameCode cs x) (hy : y ∈ x) :
    y = ZFSet.pair (branchCond h hy) (branchSub h hy) :=
  (Classical.choose_spec (Classical.choose_spec (h.branch y hy))).1

theorem branchCond_mem (h : IsNameCode cs x) (hy : y ∈ x) : branchCond h hy ∈ cs :=
  (Classical.choose_spec (Classical.choose_spec (h.branch y hy))).2

theorem branchSub_isNameCode (h : IsNameCode cs x) (hy : y ∈ x) :
    IsNameCode cs (branchSub h hy) :=
  h.sub y hy _ _ (branch_eq h hy)

theorem branchSub_rank_lt (h : IsNameCode cs x) (hy : y ∈ x) :
    (branchSub h hy).rank < x.rank :=
  rank_lt_of_pair_mem (branch_eq h hy ▸ hy)

end Branch

/-! ### Decoding -/

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- The typed condition of a condition code. -/
noncomputable def condOf {c : ZFSet.{u}} (hc : c ∈ (Pres.conditionSet : ZFSet.{u})) : P :=
  Classical.choose (Pres.code_surjective c hc)

theorem condCode_condOf {c : ZFSet.{u}} (hc : c ∈ (Pres.conditionSet : ZFSet.{u})) :
    c = ZFSet.mk (Pres.conditionCode.repr (condOf Pres hc)) :=
  Classical.choose_spec (Pres.code_surjective c hc)

/-- **Decode**, by rank recursion. The branch index is the code's member type, shrunk to
`Type u`; each branch decodes its subname code and reads its condition. -/
noncomputable def decode :
    (x : ZFSet.{u}) → IsNameCode (Pres.conditionSet : ZFSet.{u}) x → PName P
  | x, h =>
    PName.mk (Shrink.{u} x)
      (fun i ↦ decode (branchSub h ((equivShrink x).symm i).2) (branchSub_isNameCode h _))
      (fun i ↦ condOf Pres (branchCond_mem h ((equivShrink x).symm i).2))
termination_by x => x.rank
decreasing_by exact branchSub_rank_lt h _

theorem decode_eq (x : ZFSet.{u}) (h : IsNameCode (Pres.conditionSet : ZFSet.{u}) x) :
    decode Pres x h =
      PName.mk (Shrink.{u} x)
        (fun i ↦ decode Pres (branchSub h ((equivShrink x).symm i).2)
          (branchSub_isNameCode h _))
        (fun i ↦ condOf Pres (branchCond_mem h ((equivShrink x).symm i).2)) := by
  rw [decode]

omit [Preorder P] in
/-- Equal names have matching branches, index by index across the type equality that
`PName.mk` injectivity yields. -/
theorem mk_eq_mk_imp {ι ι' : Type u} {e : ι → PName P} {e' : ι' → PName P} {c : ι → P}
    {c' : ι' → P} (h : PName.mk ι e c = PName.mk ι' e' c') :
    ∀ i, ∃ i', e i = e' i' ∧ c i = c' i' := by
  injection h with hι he hc
  subst hι
  intro i
  exact ⟨i, congrFun (eq_of_heq he) i, congrFun (eq_of_heq hc) i⟩

/-- **Decode is injective** on hereditarily valid codes. Rank induction, recursing through the
symmetric equation in the second containment so the measure decreases on the right side. -/
theorem decode_injective :
    ∀ (x : ZFSet.{u}) (h : IsNameCode (Pres.conditionSet : ZFSet.{u}) x)
      (x' : ZFSet.{u}) (h' : IsNameCode (Pres.conditionSet : ZFSet.{u}) x'),
      decode Pres x h = decode Pres x' h' → x = x'
  | x, h, x', h', heq => by
    have key : ∀ (a : ZFSet.{u}) (ha : IsNameCode _ a) (b : ZFSet.{u}) (hb : IsNameCode _ b),
        decode Pres a ha = decode Pres b hb →
        ∀ i : Shrink.{u} a, ∃ i' : Shrink.{u} b,
          decode Pres (branchSub ha ((equivShrink a).symm i).2) (branchSub_isNameCode ha _) =
            decode Pres (branchSub hb ((equivShrink b).symm i').2)
              (branchSub_isNameCode hb _) ∧
          condOf Pres (branchCond_mem ha ((equivShrink a).symm i).2) =
            condOf Pres (branchCond_mem hb ((equivShrink b).symm i').2) := by
      intro a ha b hb hab
      rw [decode_eq, decode_eq] at hab
      exact mk_eq_mk_imp hab
    apply ZFSet.ext
    intro y
    constructor
    · intro hy
      obtain ⟨i', hsub, hcond⟩ := key x h x' h' heq (equivShrink x ⟨y, hy⟩)
      have hy' := ((equivShrink x').symm i').2
      have hsub' := decode_injective _ _ _ _ hsub
      have hc : branchCond h hy = branchCond h' hy' := by
        have := congrArg (fun p ↦ ZFSet.mk (Pres.conditionCode.repr p)) hcond
        simp only [Equiv.symm_apply_apply] at this
        rwa [← condCode_condOf, ← condCode_condOf] at this
      simp only [Equiv.symm_apply_apply] at hsub'
      rw [branch_eq h hy, hc, hsub']
      exact (branch_eq h' hy') ▸ hy'
    · intro hy
      obtain ⟨i', hsub, hcond⟩ := key x' h' x h heq.symm (equivShrink x' ⟨y, hy⟩)
      have hy' := ((equivShrink x).symm i').2
      have hsub' := (decode_injective _ _ _ _ hsub.symm).symm
      have hc : branchCond h' hy = branchCond h hy' := by
        have := congrArg (fun p ↦ ZFSet.mk (Pres.conditionCode.repr p)) hcond
        simp only [Equiv.symm_apply_apply] at this
        rwa [← condCode_condOf, ← condCode_condOf] at this
      simp only [Equiv.symm_apply_apply] at hsub'
      rw [branch_eq h' hy, hc, hsub']
      exact (branch_eq h hy') ▸ hy'
termination_by x => x.rank
decreasing_by all_goals apply branchSub_rank_lt

/-! ### The presentation -/

/-- A material carrier is small: it is the member type of a set. -/
instance smallCarrier : Small.{u} ↥M :=
  small_of_injective (f := fun x : ↥M ↦ (⟨x.1, x.2⟩ : ↥M.carrier))
    (fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h))

/-- Codes: hereditarily valid carrier elements, shrunk to `Type u`. -/
abbrev MaxCode : Type u := Shrink.{u} {x : ↥M // IsNameCode (Pres.conditionSet : ZFSet.{u}) x}

theorem branchSub_mem_carrier {x y : ZFSet.{u}}
    (hx : IsNameCode (Pres.conditionSet : ZFSet.{u}) x) (hxM : x ∈ M) (hy : y ∈ x) :
    branchSub hx hy ∈ M := by
  have h1 : branchSub hx hy ∈ ({branchCond hx hy, branchSub hx hy} : ZFSet.{u}) :=
    ZFSet.mem_pair.2 (Or.inr rfl)
  have h2 : ({branchCond hx hy, branchSub hx hy} : ZFSet.{u}) ∈
      ZFSet.pair (branchCond hx hy) (branchSub hx hy) := ZFSet.mem_pair.2 (Or.inr rfl)
  exact M.mem_trans h1 (M.mem_trans h2 (M.mem_trans (branch_eq hx hy ▸ hy) hxM))

/-- The code of a branch's subname. -/
noncomputable def subCode {x y : ZFSet.{u}} (hx : IsNameCode (Pres.conditionSet : ZFSet.{u}) x)
    (hxM : x ∈ M) (hy : y ∈ x) : MaxCode Pres :=
  equivShrink _ ⟨⟨_, branchSub_mem_carrier Pres hx hxM hy⟩, branchSub_isNameCode hx hy⟩

/-- **The maximal name presentation.** -/
noncomputable def maximal : InternalNamePresentation M P where
  Code := MaxCode Pres
  code i := ((equivShrink _).symm i).1.1
  code_mem i := ((equivShrink _).symm i).1.2
  decode i := decode Pres _ ((equivShrink _).symm i).2
  subname_closed i j := by
    revert j
    generalize (equivShrink _).symm i = s
    obtain ⟨⟨x, hxM⟩, hx⟩ := s
    rw [decode_eq]
    intro j
    refine ⟨subCode Pres hx hxM ((equivShrink x).symm j).2, ?_⟩
    simp only [subCode, Equiv.symm_apply_apply, PName.elems_mk]

/-- Codes are injective: faithfulness for free. -/
theorem maximal_code_injective : Function.Injective (maximal Pres).code := by
  intro i j h
  exact (equivShrink _).symm.injective (Subtype.ext (Subtype.ext h))

/-- **Maximality, as a theorem.** Every hereditarily valid carrier element is a code. This is
what will make recognition exact rather than merely sound. -/
theorem exists_code_of_isNameCode {x : ZFSet.{u}} (hxM : x ∈ M)
    (hx : IsNameCode (Pres.conditionSet : ZFSet.{u}) x) :
    ∃ i : (maximal Pres).Code, (maximal Pres).code i = x :=
  ⟨equivShrink _ ⟨⟨x, hxM⟩, hx⟩, by simp [maximal]⟩

/-- The range of `code` is exactly the hereditarily valid carrier elements. -/
theorem mem_range_code_iff {x : ZFSet.{u}} :
    x ∈ Set.range (maximal Pres).code ↔ x ∈ M ∧ IsNameCode (Pres.conditionSet : ZFSet.{u}) x :=
  ⟨fun ⟨i, hi⟩ ↦ hi ▸ ⟨(maximal Pres).code_mem i, ((equivShrink _).symm i).2⟩,
    fun ⟨hxM, hx⟩ ↦ exists_code_of_isNameCode Pres hxM hx⟩

/-- The representation law, at an explicit code. -/
theorem branch_mem_iff (x : ZFSet.{u}) (hxM : x ∈ M)
    (hx : IsNameCode (Pres.conditionSet : ZFSet.{u}) x) (y : ZFSet.{u}) :
    y ∈ x ↔ ∃ (k : (decode Pres x hx).Idx) (j : MaxCode Pres),
      decode Pres _ ((equivShrink _).symm j).2 = (decode Pres x hx).elems k ∧
      y = ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr ((decode Pres x hx).conds k)))
        ((equivShrink _).symm j).1.1 := by
  rw [decode_eq Pres x hx]
  simp only [PName.elems_mk, PName.conds_mk]
  constructor
  · intro hy
    refine ⟨equivShrink x ⟨y, hy⟩, subCode Pres hx hxM hy, ?_, ?_⟩
    · simp only [subCode, Equiv.symm_apply_apply]
    · simp only [subCode, Equiv.symm_apply_apply]
      rw [← condCode_condOf]
      exact branch_eq hx hy
  · rintro ⟨k, j, hdec, rfl⟩
    have hyk := ((equivShrink x).symm k).2
    have hj := decode_injective Pres _ _ _ _ hdec
    rw [← condCode_condOf, hj]
    exact branch_eq hx hyk ▸ hyk

/-- **The coding laws hold** for the maximal presentation: representation from
`branch_mem_iff`, faithfulness from injectivity of `code`. -/
theorem maximal_coding : InternalNameCoding Pres (maximal Pres) where
  branch_mem_code_iff i y := branch_mem_iff Pres _ ((equivShrink _).symm i).1.2
    ((equivShrink _).symm i).2 y
  decode_eq_of_code_eq i j h := by rw [maximal_code_injective Pres h]

end MaximalNames

end Forcing
