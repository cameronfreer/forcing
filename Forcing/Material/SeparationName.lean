/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.CompilerCorrectness
import Forcing.Material.TestCoding
import Forcing.Material.UnionName

/-!
# The separation name: semantic laws and exact formula laws

M7 item 6 (#241), Separation, first of two PRs. For a name code `t = code i`, parameter codes
`free`, and `φ : BoundedFormula (Fin k) 1`, the **separation code** is the set of `⟨⌜q⌝, σ⟩` such
that some branch `⟨⌜p⌝, σ⟩` of `t` has `q ≤ p` and `q` forces `φ` at the parameters and `σ`:

```text
sepBranchDef Rec φ Γ A t m :=
  ∃ q σ, m = ⟨q, σ⟩ ∧ q ∈ condSet ∧
    (∃ p, ⟨p, σ⟩ ∈ t ∧ p ∈ condSet ∧ ⟨q, p⟩ ∈ orderCode) ∧
    ∀ a', a' = ⟨σ, A⟩ → forcesDef Rec.formula φ Γ q a'
```

The orientation is `order_iff`'s: `⟨⌜q⌝, ⌜p⌝⟩ ∈ ord ↔ q ≤ p`. **Both internally quantified
conditions carry their `condSet` guard** (#223). The middle conjunct is `unionInnerDef`, reused
with its realization law.

## The parameter layout

`sepParams`, `sepVector`: the connective tests' layout plus one slot, `Fin (6 + Rec.arity)`:

```text
0 tagMem, 1 tagEq, 2 condSet, 3 orderCode, 4 A (the parameter assignment), 5 t, then Rec.params
```

so recognizer parameter `i` moves from `5 + i` (`testParams`) to `6 + i` (`sepVector_natAdd`,
and `recParams_eq` in `sepParams_realizes`). `A` codes the parameters alone,
`assignmentCode (combinedCodes free ![])`, and the compiled formula at `σ = code j` reads
`⟨code j, A⟩`, which is `assignmentCode (combinedCodes free ![j])`: the new name first
(`assignmentCode_combinedCodes_single`).

## Two layers of laws

1. **The formula law** (`realize_sepBranchDef`) is exact, with no validity and no theory
   hypothesis: the compiled forcing stays a realization, and the extended assignment stays a
   **guarded universal over internal `a'`**, so the syntax asserts no existence.
2. **The typed characterization** (`MaximalNames.realize_sepBranchDef_iff`) reads it as
   `MaximalNames.IsSepBranch`, a full biconditional with `∃ p : P`. It takes compiler
   correctness's inputs (pair closure and the two atomic equivalences) and `t = code i`. Pair
   closure is used at exactly one site: the forward direction must construct `⟨code j, A⟩` to
   instantiate the guarded universal; without it the guard could hold vacuously.

## Contract

Validity and valuation are stated against a **supplied exact characterization**
`∀ m, m ∈ code b ↔ IsSepBranch Pres free φ i m`, so they do not depend on how the internal bound
is built (the second PR):

* `MaximalNames.isNameCode_of_isSepBranch`: the characterized set is a valid code;
* `MaximalNames.mem_zval_decode_of_isSepBranch`: **membership over the extension carrier**,
  `x ∈ val b ↔ x ∈ val i ∧ φ.Realize ps ![x]` for every `x` in `(maximal Pres).extensionCarrier S`,
  where `ps` are the `extVal`s of the parameters. It holds along every `S` that is **upward
  closed** and **downward directed**, given a supplied truth-lemma equivalence `htl` at `φ`.
  Upward closure takes an admitted `q ≤ p` back to the branch condition; directedness and
  persistence (`ForcesFormula.mono`) combine the branch witness with the forcing witness. No
  theory sentence and no genericity: genericity enters only in discharging `htl`.

## The carrier unfolding

The sentence bridge this proof needs is `MaterialCarrier.realize_separationSentence_iff`
(`AxiomSchemes.lean`), the bare unfolding of a Separation instance on any carrier, not an
`Empty`/`Fin 0` relabel.

## Main results

* `Forcing.sepParams`, `Forcing.sepVector`, `Forcing.sepParams_realizes`,
  `Forcing.sepVector_natAdd`, `Forcing.assignmentCode_combinedCodes_single`.
* `Forcing.sepBranchDef`, `Forcing.realize_sepBranchDef`; the instance
  `Forcing.sepNameFormula` and its sentence `Forcing.sepNameSentence`.
* `Forcing.MaximalNames.IsSepBranch`, `Forcing.MaximalNames.realize_sepBranchDef_iff`,
  `Forcing.MaximalNames.realize_sepNameFormula_iff`.
* `Forcing.MaximalNames.isNameCode_of_isSepBranch`,
  `Forcing.MaximalNames.mem_zval_decode_of_isSepBranch`.
-/

universe u v

namespace Forcing

open FirstOrder Language PName AtomicRecursion

/-! ### The assignment at the separated variable -/

section Assignment

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P} {k : ℕ}

/-- **The assignment equation, new name first**: the separated variable's code `j` is paired onto
the code of the parameters alone. -/
theorem assignmentCode_combinedCodes_single (free : Fin k → N.Code) (j : N.Code) :
    N.assignmentCode (combinedCodes free ![j]) =
      ZFSet.pair (N.code j) (N.assignmentCode (combinedCodes free ![])) := by
  have h : (![j] : Fin 1 → N.Code) = Fin.snoc (![] : Fin 0 → N.Code) j := by
    funext x
    rw [Fin.fin_one_eq_zero x]
    rfl
  rw [h, combinedCodes_snoc, InternalNamePresentation.assignmentCode_snoc]

end Assignment

/-! ### The parameter layout -/

section Layout

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P}
variable (Rec : InternalNameRecognition N)

/-- The parameter block at the separation layout: `tagMem, tagEq, condSet, orderCode` at `0`–`3`
as in `testParams`, the assignment `A` at `4`, the separated set's code `t` at `5`, and the
recognizer's parameters after, at `6 + i`. -/
def sepParams : CompilerParams (Fin (6 + Rec.arity)) Rec.arity 1 where
  tagMem := var (Sum.inl (Fin.castAdd Rec.arity 0))
  tagEq := var (Sum.inl (Fin.castAdd Rec.arity 1))
  condSet := var (Sum.inl (Fin.castAdd Rec.arity 2))
  orderCode := var (Sum.inl (Fin.castAdd Rec.arity 3))
  recParams := fun i ↦ Sum.inl (Fin.natAdd 6 i)

/-- The parameter-assignment slot `A`, at `4`. -/
def sepAssignment : memLang.Term (Fin (6 + Rec.arity) ⊕ Fin 1) :=
  var (Sum.inl (Fin.castAdd Rec.arity 4))

/-- The separated set's slot `t`, at `5`. -/
def sepTarget : memLang.Term (Fin (6 + Rec.arity) ⊕ Fin 1) :=
  var (Sum.inl (Fin.castAdd Rec.arity 5))

/-- The parameter vector the separation formula is read at. -/
def sepVector (tagMem tagEq condSet orderCode A t : ↥M) : Fin (6 + Rec.arity) → ↥M :=
  Fin.append ![tagMem, tagEq, condSet, orderCode, A, t] Rec.params

/-- **The recognizer block moves by one slot**: recognizer parameter `i` is read at `6 + i`, past
the new `t` slot (`testVector` reads it at `5 + i`). -/
@[simp] theorem sepVector_natAdd (tagMem tagEq condSet orderCode A t : ↥M) (i : Fin Rec.arity) :
    sepVector Rec tagMem tagEq condSet orderCode A t (Fin.natAdd 6 i) = Rec.params i := by
  simp [sepVector, Fin.append_right]

/-- The layout realizes the compiler invariant at its vector. -/
theorem sepParams_realizes (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M)
    (hq : (natCode eqTag : ZFSet.{u}) ∈ M) (condSet orderCode A t : ↥M) (xs : Fin 1 → M) :
    (sepParams Rec).Realizes Rec condSet orderCode
      (sepVector Rec ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩ condSet orderCode A t)
      xs where
  tagMem_eq := by simp [sepParams, sepVector, Fin.append_left]
  tagEq_eq := by simp [sepParams, sepVector, Fin.append_left]
  condSet_eq := by simp [sepParams, sepVector, Fin.append_left]
  orderCode_eq := by simp [sepParams, sepVector, Fin.append_left]
  recParams_eq := fun i ↦ by simp [sepParams]

/-- The assignment slot realizes to `A`. -/
theorem realize_sepAssignment (tagMem tagEq condSet orderCode A t : ↥M) (xs : Fin 1 → M) :
    Term.realize (Sum.elim (sepVector Rec tagMem tagEq condSet orderCode A t) xs)
      (sepAssignment Rec) = A := by
  simp [sepAssignment, sepVector, Fin.append_left]

/-- The target slot realizes to `t`. -/
theorem realize_sepTarget (tagMem tagEq condSet orderCode A t : ↥M) (xs : Fin 1 → M) :
    Term.realize (Sum.elim (sepVector Rec tagMem tagEq condSet orderCode A t) xs)
      (sepTarget Rec) = t := by
  simp [sepTarget, sepVector, Fin.append_left]

end Layout

/-! ### The formula -/

section Syntax

variable {α : Type v} {k n : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P}

/-- **The guarded separation-branch formula**:
`∃ q σ, m = ⟨q, σ⟩ ∧ q ∈ condSet ∧ (∃ p, ⟨p, σ⟩ ∈ t ∧ p ∈ condSet ∧ ⟨q, p⟩ ∈ orderCode) ∧
∀ a', a' = ⟨σ, A⟩ → forcesDef φ q a'`. The extended assignment is a guarded universal, as in
`forcesDef_all` and `allTestDef`. -/
def sepBranchDef (Rec : InternalNameRecognition N) (φ : memLang.BoundedFormula (Fin k) 1)
    (Γ : CompilerParams α Rec.arity n) (A t m : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) (liftTerm (liftTerm m)) ⊓
    (memFormula (&(Fin.castSucc (Fin.last n))) Γ.lift.lift.condSet ⊓
      (unionInnerDef Γ.lift.lift.condSet Γ.lift.lift.orderCode (&(Fin.castSucc (Fin.last n)))
          (&(Fin.last (n + 1))) (liftTerm (liftTerm t)) ⊓
        ∀' (pairDef (&(Fin.castSucc (Fin.last (n + 1)))) (liftTerm (liftTerm (liftTerm A)))
              (&(Fin.last (n + 2))) ⟹
          forcesDef Rec.formula φ Γ.lift.lift.lift (&(Fin.castSucc (Fin.castSucc (Fin.last n))))
            (&(Fin.last (n + 2)))))))

variable (Rec : InternalNameRecognition N)

/-- **The separation filter** (Separation; the parameters at the separation layout). -/
def sepNameFormula (φ : memLang.BoundedFormula (Fin k) 1) :
    memLang.BoundedFormula (Fin (6 + Rec.arity)) 1 :=
  sepBranchDef Rec φ (sepParams Rec) (sepAssignment Rec) (sepTarget Rec) &0

/-- The Separation instance for `φ`: one per formula. -/
def sepNameSentence (φ : memLang.BoundedFormula (Fin k) 1) : memLang.Sentence :=
  separationSentence (sepNameFormula Rec φ)

theorem sepNameSentence_mem_scheme (φ : memLang.BoundedFormula (Fin k) 1) :
    sepNameSentence Rec φ ∈ separationScheme :=
  separationSentence_mem_scheme _

end Syntax

/-! ### The formula law -/

section Realization

variable {α : Type v} {k n : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} {Rec : InternalNameRecognition N}
variable {v : α → M} {xs : Fin n → M} {condSet orderCode : ZFSet.{u}}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

/-- **The separation-branch law**: exact, with no validity or theory hypothesis. The compiled
forcing stays a realization, and the extended assignment a guarded universal over internal
`a'`. -/
theorem realize_sepBranchDef {φ : memLang.BoundedFormula (Fin k) 1}
    {Γ : CompilerParams α Rec.arity n} {A t m : memLang.Term (α ⊕ Fin n)}
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (sepBranchDef Rec φ Γ A t m).Realize v xs ↔
      ∃ q σ : ↥M, ⟪m⟫ = ZFSet.pair (q : ZFSet.{u}) (σ : ZFSet.{u}) ∧
        (q : ZFSet.{u}) ∈ condSet ∧
        (∃ p, ZFSet.pair p (σ : ZFSet.{u}) ∈ ⟪t⟫ ∧ p ∈ condSet ∧
          ZFSet.pair (q : ZFSet.{u}) p ∈ orderCode) ∧
        ∀ a' : ↥M, (a' : ZFSet.{u}) = ZFSet.pair (σ : ZFSet.{u}) ⟪A⟫ →
          (forcesDef Rec.formula φ Γ.lift.lift.lift
            (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.last (n + 2)))).Realize v
              (Fin.snoc (Fin.snoc (Fin.snoc xs q) σ) a') := by
  simp only [sepBranchDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairDef, realize_unionInnerDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm]
  refine exists_congr fun q ↦ exists_congr fun σ ↦ ?_
  rw [((hΓ.lift q).lift σ).condSet_eq, ((hΓ.lift q).lift σ).orderCode_eq]

end Realization

/-! ### The typed layer -/

namespace MaximalNames

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- **A branch of the separation code**, typed: `⟨⌜q⌝, code j⟩`, where `q` strengthens the
condition `p` of a branch `⟨⌜p⌝, code j⟩` of `code i` and forces `φ` at the parameters and
`decode j`. -/
def IsSepBranch {k : ℕ} (free : Fin k → (maximal Pres).Code)
    (φ : memLang.BoundedFormula (Fin k) 1) (i : (maximal Pres).Code) (m : ZFSet.{u}) : Prop :=
  ∃ (q : P) (j : (maximal Pres).Code), m = ZFSet.pair (condCode Pres q) ((maximal Pres).code j) ∧
    (∃ p : P, ZFSet.pair (condCode Pres p) ((maximal Pres).code j) ∈ (maximal Pres).code i ∧
      q ≤ p) ∧
    ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
      ![(maximal Pres).decode j]

/-- **Validity**: a set characterized exactly by `IsSepBranch` is a valid code. Each member's
right coordinate is a code. -/
theorem isNameCode_of_isSepBranch {k : ℕ} {free : Fin k → (maximal Pres).Code}
    {φ : memLang.BoundedFormula (Fin k) 1} {i : (maximal Pres).Code} {B : ZFSet.{u}}
    (hB : ∀ m, m ∈ B ↔ IsSepBranch Pres free φ i m) :
    IsNameCode (Pres.conditionSet : ZFSet.{u}) B := by
  refine IsNameCode.mk _ (fun m hm ↦ ?_) (fun m hm c e hm' ↦ ?_)
  · obtain ⟨q, j, rfl, -⟩ := (hB m).1 hm
    exact ⟨_, _, rfl, Pres.code_mem q⟩
  · obtain ⟨q, j, rfl, -⟩ := (hB m).1 hm
    obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 hm'
    exact ((mem_range_code_iff Pres).1 ⟨j, rfl⟩).2

variable {Pres}

/-- **Valuation of the separation name, over the extension carrier.** For a maximal name whose
code is exactly the separation code of `code i` at `φ` and `free`, membership of an element `x` of
the extension carrier in its value is membership in the value of `i` together with `φ` at the
parameters' `extVal`s and `x`. Along every upward-closed, downward-directed `S`, given the
truth-lemma equivalence `htl` at `φ`. Upward closure gives the forward branch, directedness and
persistence the reverse. Axiom-free; no genericity, which enters only in discharging `htl`. -/
theorem mem_zval_decode_of_isSepBranch {S : Set P} (hup : IsUpperSet S)
    (hdir : DirectedOn (· ≥ ·) S) {k : ℕ} {free : Fin k → (maximal Pres).Code}
    {φ : memLang.BoundedFormula (Fin k) 1} {i b : (maximal Pres).Code}
    (hb : ∀ m, m ∈ (maximal Pres).code b ↔ IsSepBranch Pres free φ i m)
    (htl : ∀ j : (maximal Pres).Code,
      φ.Realize (fun l ↦ (maximal Pres).extVal S ((maximal Pres).decode (free l))
          ((maximal Pres).decode_mem_names _))
        ![(maximal Pres).extVal S ((maximal Pres).decode j) ((maximal Pres).decode_mem_names _)] ↔
      ∃ r ∈ S, ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) r φ
        ![(maximal Pres).decode j])
    (x : (maximal Pres).extensionCarrier S) :
    (x : ZFSet.{u}) ∈ zval S ((maximal Pres).decode b) ↔
      (x : ZFSet.{u}) ∈ zval S ((maximal Pres).decode i) ∧
        φ.Realize (fun l ↦ (maximal Pres).extVal S ((maximal Pres).decode (free l))
          ((maximal Pres).decode_mem_names _)) ![x] := by
  have hx : ∀ j, (x : ZFSet.{u}) = zval S ((maximal Pres).decode j) →
      x = (maximal Pres).extVal S ((maximal Pres).decode j) ((maximal Pres).decode_mem_names _) :=
    fun _ h ↦ Subtype.ext h
  rw [mem_zval_decode_iff, mem_zval_decode_iff]
  constructor
  · rintro ⟨q, hq, j, hqj, hxj⟩
    obtain ⟨q', j', hpair, ⟨p, hpj, hqp⟩, hf⟩ := (hb _).1 hqj
    obtain ⟨hqq, hjj⟩ := ZFSet.pair_inj.1 hpair
    obtain rfl := Pres.conditionCode.injective_mk hqq
    obtain rfl := maximal_code_injective Pres hjj
    refine ⟨⟨p, hup hqp hq, j, hpj, hxj⟩, ?_⟩
    rw [hx j hxj]
    exact (htl j).2 ⟨q, hq, hf⟩
  · rintro ⟨⟨p, hp, j, hpj, hxj⟩, hφ⟩
    rw [hx j hxj] at hφ
    obtain ⟨r, hr, hf⟩ := (htl j).1 hφ
    obtain ⟨q, hq, hpq, hrq⟩ := hdir p hp r hr
    exact ⟨q, hq, j, (hb _).2 ⟨q, j, rfl, ⟨p, hpj, hpq⟩, ForcesFormula.mono φ hf hrq⟩, hxj⟩

/-! ### The typed characterization -/

section Typed

variable {α : Type v} {k n : ℕ} {Rec : InternalNameRecognition (maximal Pres)}
variable {v : α → M} {xs : Fin n → M} {free : Fin k → (maximal Pres).Code}
variable (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
variable (hEq : ∀ (r : P) (i j : (maximal Pres).Code),
  AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) ((maximal Pres).code i)
      ((maximal Pres).code j) ↔
    ForcesEq r ((maximal Pres).decode i) ((maximal Pres).decode j))
variable (hMem : ∀ (r : P) (i j : (maximal Pres).Code),
  AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) ((maximal Pres).code i)
      ((maximal Pres).code j) ↔
    ForcesMem r ((maximal Pres).decode i) ((maximal Pres).decode j))

include hpair hEq hMem

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

/-- **The typed characterization**: at `t = code i` and `A` coding the parameters alone, the
separation-branch formula holds of `m` exactly when `m` is a typed separation branch. Compiler
correctness reads the forcing; `code_surjective` types `q` and `p`, validity of `code i` and
`mem_range_code_iff` make `σ` a code, and `order_iff` reads the order fact. Pair closure is used
once, forward, to construct `⟨code j, A⟩` for the guarded universal. -/
theorem realize_sepBranchDef_iff {φ : memLang.BoundedFormula (Fin k) 1}
    {Γ : CompilerParams α Rec.arity n} {A t m : memLang.Term (α ⊕ Fin n)}
    {i : (maximal Pres).Code} (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (ht : ⟪t⟫ = (maximal Pres).code i)
    (hA : ⟪A⟫ = (maximal Pres).assignmentCode (combinedCodes free ![])) :
    (sepBranchDef Rec φ Γ A t m).Realize v xs ↔ IsSepBranch Pres free φ i ⟪m⟫ := by
  have hcorr : ∀ (q σ a' : ↥M) (q' : P) (j : (maximal Pres).Code),
      (q : ZFSet.{u}) = condCode Pres q' →
      (a' : ZFSet.{u}) =
        ZFSet.pair ((maximal Pres).code j) ((maximal Pres).assignmentCode (combinedCodes free ![]))
        → ((forcesDef Rec.formula φ Γ.lift.lift.lift
            (&(Fin.castSucc (Fin.castSucc (Fin.last n)))) (&(Fin.last (n + 2)))).Realize v
              (Fin.snoc (Fin.snoc (Fin.snoc xs q) σ) a') ↔
          ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q' φ
            ![(maximal Pres).decode j]) := by
    intro q σ a' q' j hq ha'
    have hbound : ((maximal Pres).decode ∘ ![j]) = ![(maximal Pres).decode j] := by
      funext x
      rw [Fin.fin_one_eq_zero x]
      rfl
    rw [← hbound]
    refine realize_forcesDef_iff_forcesFormula hpair hEq hMem (((hΓ.lift q).lift σ).lift a') ?_ ?_
    · simpa using hq
    · simpa [assignmentCode_combinedCodes_single] using ha'
  rw [realize_sepBranchDef hΓ, ht, hA]
  constructor
  · rintro ⟨q, σ, hm, hq, ⟨p, hpσ, hp, hqp⟩, hf⟩
    obtain ⟨q', hq'⟩ := Pres.code_surjective q hq
    obtain ⟨p', rfl⟩ := Pres.code_surjective p hp
    obtain ⟨-, htv⟩ := (mem_range_code_iff Pres).1 ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := (mem_range_code_iff Pres).2 ⟨σ.2, htv.sub _ hpσ _ _ rfl⟩
    have hAM : (maximal Pres).assignmentCode (combinedCodes free ![]) ∈ M :=
      hA ▸ (Term.realize (Sum.elim v xs) A : ↥M).2
    let a' : ↥M := ⟨ZFSet.pair ((maximal Pres).code j)
      ((maximal Pres).assignmentCode (combinedCodes free ![])),
      hpair ((maximal Pres).code_mem j) hAM⟩
    refine ⟨q', j, ?_, ⟨p', ?_, (Pres.order_iff p' q').1 (hq' ▸ hqp)⟩, ?_⟩
    · rw [hm, hq', hj]
      rfl
    · rw [hj]
      exact hpσ
    · exact (hcorr q σ a' q' j hq' rfl).1 (hf a' (congrArg (fun z ↦ ZFSet.pair z _) hj))
  · rintro ⟨q', j, hm, ⟨p', hpj, hqp⟩, hf⟩
    exact ⟨condElem Pres q', ⟨_, (maximal Pres).code_mem j⟩, hm, Pres.code_mem q',
      ⟨condCode Pres p', hpj, Pres.code_mem p', (Pres.order_iff p' q').2 hqp⟩,
      fun a' ha' ↦ (hcorr _ _ a' q' j rfl ha').2 hf⟩

/-- **The instance, typed**: the separation filter at the separation layout, with `t = code i`
and `A` coding the parameters alone, holds of `m` exactly when `m` is a typed separation
branch. -/
theorem realize_sepNameFormula_iff (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M)
    (hq : (natCode eqTag : ZFSet.{u}) ∈ M) (φ : memLang.BoundedFormula (Fin k) 1)
    (i : (maximal Pres).Code) (A : ↥M)
    (hA : (A : ZFSet.{u}) = (maximal Pres).assignmentCode (combinedCodes free ![])) (m : ↥M) :
    (sepNameFormula Rec φ).Realize
        (sepVector Rec ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩ Pres.conditionSet
          Pres.orderCode A ⟨(maximal Pres).code i, (maximal Pres).code_mem i⟩) ![m] ↔
      IsSepBranch Pres free φ i (m : ZFSet.{u}) := by
  rw [sepNameFormula, realize_sepBranchDef_iff hpair hEq hMem
    (sepParams_realizes Rec hm hq _ _ _ _ _) (by rw [realize_sepTarget])
    (by rw [realize_sepAssignment, hA])]
  rfl

end Typed

end MaximalNames

end Forcing
