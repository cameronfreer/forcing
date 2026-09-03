/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicTests
import Forcing.Material.CompilerCorrectness
import Forcing.Name.FormulaTests

/-!
# The connective test codes

M7 item 4b: the formula-test visibility hypothesis of `truth_lemma_of_genericOver`, discharged
member by member. Every member of `formulaTests N.names v φ xs` is an `impDecision` or an
`allDecision` at a subformula and an extended bound assignment, and each of those is coded by
**one** Separation instance whose formula is the compiled test.

```text
impDecision 𝒩 v φ ψ xs  ↦  impTestDef  …  ↦  impTest Rec φ ψ
allDecision 𝒩 v φ xs    ↦  allTestDef  …  ↦  allTest Rec φ
```

## Parametric in a recognizer, exactly as the compiler is

The universal obstruction ranges over the name family. Internally that is the recognizer
`Rec.formula`, spliced under the binder by `relabel` as in `forcesDef_all`, and its only use is
`Rec.realize_iff`: to range over **exactly** `N.names`. No master name-code set appears.

## The guardrail, again

Every internal condition quantifier the tests introduce — the blocker in `impObstruction`, the
blocker in `allObstruction` — carries condition-set membership alongside its order-code fact
(`blockerDef`). The compiled formulas guard their own binders (#223); this is for the ones the
*tests* add around them.

## The one Pairing site, again

`allTestDef` introduces the extended assignment by a guarded universal, as the compiler does, so
the syntax asserts no existence. Reading the obstruction externally must then build that
assignment — one `pair` of two elements in hand — and that is the single site pair closure is
used. Empty Set is charged only where a **root** assignment is genuinely constructed: the
material code theorems, which must exhibit the parameter `a` as a carrier element.

## The compiled list of costs

`formulaTestSentences Rec φ` is the set of Separation instances the family for `φ` needs: one
per implication and per universal subformula, independent of the assignment (the assignment is a
*parameter* of each test, not part of its formula). `exists_code_of_mem_formulaTests` takes
exactly `formulaTestSentences Rec φ ⊆ T`.

**For #219**: no closure operation on the name family beyond the presentation's own fields is
demanded here. The universal case consumes `Rec.realize_iff`, `N.subname_closed` through the
bound-assignment extension, and pair closure. That is the whole list.

## Main results

* `Forcing.impTestDef`, `Forcing.allTestDef`: the two test formulas, term-parameterized.
* `Forcing.externalize_impTest`, `Forcing.externalize_allTest`: the externalization laws.
* `Forcing.formulaTestSentences`: the compiled list of Separation instances.
* `Forcing.MaterialGround.exists_impDecisionCode`, `…exists_allDecisionCode`,
  `…exists_code_of_mem_formulaTests`: the codes, materially.
-/

universe u v

namespace Forcing

open FirstOrder Language AtomicRecursion

/-! ### The formulas -/

section Syntax

variable {α : Type v} {k sn m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P}

/-- `∀ q ∈ condSet, ⟨q, r⟩ ∈ orderCode → ¬ body q`: no strengthening of `r` satisfies `body`,
with the strengthening guarded. The blocker shape both connective tests share. -/
def blockerDef (condSet orderCode r : memLang.Term (α ⊕ Fin m))
    (body : memLang.BoundedFormula α (m + 1)) : memLang.BoundedFormula α m :=
  ∀' (memFormula (&(Fin.last m)) (liftTerm condSet) ⟹
    (pairMemDef (&(Fin.last m)) (liftTerm r) (liftTerm orderCode) ⟹ ∼body))

/-- **The implication decision test**: `r` forces `φ → ψ`, or `r` forces `φ` and blocks `ψ`. -/
def impTestDef (Rec : InternalNameRecognition N) (φ ψ : memLang.BoundedFormula (Fin k) sn)
    (Γ : CompilerParams α Rec.arity m) (r a : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  forcesDef Rec.formula (φ.imp ψ) Γ r a ⊔
    (forcesDef Rec.formula φ Γ r a ⊓
      blockerDef Γ.condSet Γ.orderCode r
        (forcesDef Rec.formula ψ Γ.lift (&(Fin.last m)) (liftTerm a)))

/-- **The universal decision test**: `r` forces `∀ φ`, or some recognized name has its instance
blocked below `r`. The extended assignment is introduced by a guarded universal, as in
`forcesDef_all`. -/
def allTestDef (Rec : InternalNameRecognition N) (φ : memLang.BoundedFormula (Fin k) (sn + 1))
    (Γ : CompilerParams α Rec.arity m) (r a : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  forcesDef Rec.formula φ.all Γ r a ⊔
    ∃' (Rec.formula.relabel Γ.recParams ⊓
      ∀' (pairDef (&(Fin.castSucc (Fin.last m))) (liftTerm (liftTerm a)) (&(Fin.last (m + 1))) ⟹
        blockerDef Γ.lift.lift.condSet Γ.lift.lift.orderCode (liftTerm (liftTerm r))
          (forcesDef Rec.formula φ Γ.lift.lift.lift (&(Fin.last (m + 2)))
            (&(Fin.castSucc (Fin.last (m + 1)))))))

end Syntax

/-! ### Realization -/

section Realization

variable {α : Type v} {k sn m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} {Rec : InternalNameRecognition N}
variable {v : α → M} {xs : Fin m → M}

theorem realize_blockerDef {condSet orderCode r : memLang.Term (α ⊕ Fin m)}
    {body : memLang.BoundedFormula α (m + 1)} :
    (blockerDef condSet orderCode r body).Realize v xs ↔
      ∀ q : ↥M, (q : ZFSet.{u}) ∈ ((Term.realize (Sum.elim v xs) condSet : ↥M) : ZFSet.{u}) →
        ZFSet.pair (q : ZFSet.{u}) ((Term.realize (Sum.elim v xs) r : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) orderCode : ↥M) : ZFSet.{u}) →
        ¬ body.Realize v (Fin.snoc xs q) := by
  simp only [blockerDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_not, memFormula, BoundedFormula.realize_rel₂, relMap_mem,
    Matrix.cons_val_zero, Matrix.cons_val_one, realize_pairMemDef, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Fin.snoc_last, realize_liftTerm]

variable {condSet orderCode : ZFSet.{u}}

theorem realize_impTestDef {φ ψ : memLang.BoundedFormula (Fin k) sn}
    {Γ : CompilerParams α Rec.arity m} {r a : memLang.Term (α ⊕ Fin m)}
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (impTestDef Rec φ ψ Γ r a).Realize v xs ↔
      (forcesDef Rec.formula (φ.imp ψ) Γ r a).Realize v xs ∨
      ((forcesDef Rec.formula φ Γ r a).Realize v xs ∧
        ∀ q : ↥M, (q : ZFSet.{u}) ∈ condSet →
          ZFSet.pair (q : ZFSet.{u}) ((Term.realize (Sum.elim v xs) r : ↥M) : ZFSet.{u}) ∈
            orderCode →
          ¬ (forcesDef Rec.formula ψ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v
            (Fin.snoc xs q)) := by
  rw [impTestDef, BoundedFormula.realize_sup, BoundedFormula.realize_inf, realize_blockerDef,
    hΓ.condSet_eq, hΓ.orderCode_eq]

theorem realize_allTestDef {φ : memLang.BoundedFormula (Fin k) (sn + 1)}
    {Γ : CompilerParams α Rec.arity m} {r a : memLang.Term (α ⊕ Fin m)}
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (allTestDef Rec φ Γ r a).Realize v xs ↔
      (forcesDef Rec.formula φ.all Γ r a).Realize v xs ∨
      ∃ c : ↥M, (∃ i : N.Code, (c : ZFSet.{u}) = N.code i) ∧
        ∀ a' : ↥M, (a' : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) →
          ∀ q : ↥M, (q : ZFSet.{u}) ∈ condSet →
            ZFSet.pair (q : ZFSet.{u}) ((Term.realize (Sum.elim v xs) r : ↥M) : ZFSet.{u}) ∈
              orderCode →
            ¬ (forcesDef Rec.formula φ Γ.lift.lift.lift (&(Fin.last (m + 2)))
              (&(Fin.castSucc (Fin.last (m + 1))))).Realize v
                (Fin.snoc (Fin.snoc (Fin.snoc xs c) a') q) := by
  have hrec : ∀ c : ↥M, (Rec.formula.relabel Γ.recParams).Realize v (Fin.snoc xs c) ↔
      ∃ i : N.Code, (c : ZFSet.{u}) = N.code i := by
    intro c
    rw [realize_relabel_snoc, show (fun i ↦ Sum.elim v xs (Γ.recParams i)) = Rec.params from
      funext hΓ.recParams_eq]
    exact Rec.realize_iff c
  have hblk : ∀ c a' : ↥M,
      (blockerDef Γ.lift.lift.condSet Γ.lift.lift.orderCode (liftTerm (liftTerm r))
        (forcesDef Rec.formula φ Γ.lift.lift.lift (&(Fin.last (m + 2)))
          (&(Fin.castSucc (Fin.last (m + 1)))))).Realize v (Fin.snoc (Fin.snoc xs c) a') ↔
      ∀ q : ↥M, (q : ZFSet.{u}) ∈ condSet →
        ZFSet.pair (q : ZFSet.{u}) ((Term.realize (Sum.elim v xs) r : ↥M) : ZFSet.{u}) ∈
          orderCode →
        ¬ (forcesDef Rec.formula φ Γ.lift.lift.lift (&(Fin.last (m + 2)))
          (&(Fin.castSucc (Fin.last (m + 1))))).Realize v
            (Fin.snoc (Fin.snoc (Fin.snoc xs c) a') q) := by
    intro c a'
    rw [realize_blockerDef, ((hΓ.lift c).lift a').condSet_eq, ((hΓ.lift c).lift a').orderCode_eq]
    simp only [realize_liftTerm]
  simp only [allTestDef, BoundedFormula.realize_sup, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]
  exact or_congr_right (exists_congr fun c ↦ and_congr (hrec c)
    (forall_congr' fun a' ↦ imp_congr_right fun _ ↦ hblk c a'))

end Realization

/-! ### Externalization, typed

Each compiled formula is read through `forcesDef_correct`; each blocker quantifier is decoded
through `code_surjective` on its condition-set conjunct and `order_iff` on its order fact. -/

section Externalize

variable {α : Type v} {k sn m : ℕ} {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}
variable {Rec : InternalNameRecognition N} {v : α → M} {free : Fin k → N.Code}
variable (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
variable (hEq : ∀ (r : P) (i j : N.Code),
  AtomicEqRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i) (N.code j) ↔
    ForcesEq r (N.decode i) (N.decode j))
variable (hMem : ∀ (r : P) (i j : N.Code),
  AtomicMemRealized M Pres.conditionSet Pres.orderCode (condCode Pres r) (N.code i) (N.code j) ↔
    ForcesMem r (N.decode i) (N.decode j))

include hpair hEq hMem

/-- A blocker quantifier, decoded: the guarded internal strengthenings of `r` on which a compiled
formula fails are exactly the typed strengthenings on which the external one fails. -/
theorem blocker_iff {sn' : ℕ} {φ : memLang.BoundedFormula (Fin k) sn'}
    {Γ : CompilerParams α Rec.arity m} {xs : Fin m → M} {a : memLang.Term (α ⊕ Fin m)}
    {r : P} {bound : Fin sn' → N.Code}
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound)) :
    (∀ q : ↥M, (q : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) →
        ZFSet.pair (q : ZFSet.{u}) (condCode Pres r) ∈ (Pres.orderCode : ZFSet.{u}) →
        ¬ (forcesDef Rec.formula φ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v
          (Fin.snoc xs q)) ↔
      ∀ q : P, q ≤ r → ¬ ForcesFormula N.names (N.decode ∘ free) q φ (N.decode ∘ bound) := by
  have hcorr : ∀ (q : ↥M) (q' : P), (q : ZFSet.{u}) = condCode Pres q' →
      ((forcesDef Rec.formula φ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v
        (Fin.snoc xs q) ↔
      ForcesFormula N.names (N.decode ∘ free) q' φ (N.decode ∘ bound)) := by
    intro q q' hq
    refine realize_forcesDef_iff_forcesFormula hpair hEq hMem (hΓ.lift q) ?_ ?_
    · simpa using hq
    · rw [realize_liftTerm]; exact ha
  constructor
  · intro h q' hle hf
    exact h (condElem Pres q') (Pres.code_mem q') ((Pres.order_iff r q').2 hle)
      ((hcorr _ q' rfl).2 hf)
  · intro h q hq hqr hf
    obtain ⟨q', hq'⟩ := Pres.code_surjective q hq
    exact h q' ((Pres.order_iff r q').1 (hq' ▸ hqr)) ((hcorr q q' hq').1 hf)

/-- **The implication test externalizes.** -/
theorem externalize_impTest {φ ψ : memLang.BoundedFormula (Fin k) sn}
    {Γ : CompilerParams α Rec.arity m} {rt a : memLang.Term (α ⊕ Fin m)} {xs : Fin m → M}
    {r : P} {bound : Fin sn → N.Code}
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hr : ((Term.realize (Sum.elim v xs) rt : ↥M) : ZFSet.{u}) = condCode Pres r)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound)) :
    (impTestDef Rec φ ψ Γ rt a).Realize v xs ↔
      r ∈ impDecision N.names (N.decode ∘ free) φ ψ (N.decode ∘ bound) := by
  rw [realize_impTestDef hΓ, hr, realize_forcesDef_iff_forcesFormula hpair hEq hMem hΓ hr ha,
    realize_forcesDef_iff_forcesFormula hpair hEq hMem hΓ hr ha,
    blocker_iff hpair hEq hMem hΓ ha]
  rfl

/-- **The universal test externalizes.** The recognizer is used exactly once, to identify the
internally quantified name with a member of `N.names`; pair closure is used exactly once, to
build the extended assignment the guarded universal is instantiated at. -/
theorem externalize_allTest {φ : memLang.BoundedFormula (Fin k) (sn + 1)}
    {Γ : CompilerParams α Rec.arity m} {rt a : memLang.Term (α ⊕ Fin m)} {xs : Fin m → M}
    {r : P} {bound : Fin sn → N.Code}
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hr : ((Term.realize (Sum.elim v xs) rt : ↥M) : ZFSet.{u}) = condCode Pres r)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound)) :
    (allTestDef Rec φ Γ rt a).Realize v xs ↔
      r ∈ allDecision N.names (N.decode ∘ free) φ (N.decode ∘ bound) := by
  rw [realize_allTestDef hΓ, hr, realize_forcesDef_iff_forcesFormula hpair hEq hMem hΓ hr ha]
  refine or_congr_right ?_
  have hblk : ∀ (i : N.Code) (c a' : ↥M), (c : ZFSet.{u}) = N.code i →
      (a' : ZFSet.{u}) = N.assignmentCode (combinedCodes free (Fin.snoc bound i)) →
      ((∀ q : ↥M, (q : ZFSet.{u}) ∈ (Pres.conditionSet : ZFSet.{u}) →
          ZFSet.pair (q : ZFSet.{u}) (condCode Pres r) ∈ (Pres.orderCode : ZFSet.{u}) →
          ¬ (forcesDef Rec.formula φ Γ.lift.lift.lift (&(Fin.last (m + 2)))
            (&(Fin.castSucc (Fin.last (m + 1))))).Realize v
              (Fin.snoc (Fin.snoc (Fin.snoc xs c) a') q)) ↔
        ∀ q : P, q ≤ r →
          ¬ ForcesFormula N.names (N.decode ∘ free) q φ (Fin.snoc (N.decode ∘ bound)
            (N.decode i))) := by
    intro i c a' hc ha'
    rw [← Fin.comp_snoc]
    exact blocker_iff hpair hEq hMem (free := free) (bound := Fin.snoc bound i)
      (xs := Fin.snoc (Fin.snoc xs c) a') (a := &(Fin.last (m + 1)))
      ((hΓ.lift c).lift a') (by simpa using ha')
  constructor
  · -- internal → external: recognition names the code; the extension is built by one pair
    rintro ⟨c, ⟨i, hc⟩, h⟩
    have haM : N.assignmentCode (combinedCodes free bound) ∈ M :=
      ha ▸ (Term.realize (Sum.elim v xs) a : ↥M).2
    let a' : ↥M := ⟨ZFSet.pair (N.code i) (N.assignmentCode (combinedCodes free bound)),
      hpair (N.code_mem i) haM⟩
    have ha' : ((a' : ↥M) : ZFSet.{u}) =
        N.assignmentCode (combinedCodes free (Fin.snoc bound i)) := by
      rw [combinedCodes_snoc, InternalNamePresentation.assignmentCode_snoc]
    refine ⟨N.decode i, N.decode_mem_names i, (hblk i c a' hc ha').1 (h a' ?_)⟩
    rw [hc, ha]
  · -- external → internal: the extension is handed to us
    rintro ⟨τ, ⟨i, rfl⟩, h⟩
    refine ⟨⟨N.code i, N.code_mem i⟩, ⟨i, rfl⟩, fun a' ha' ↦ (hblk i _ a' rfl ?_).2 h⟩
    rw [ha', combinedCodes_snoc, InternalNamePresentation.assignmentCode_snoc, ha]

end Externalize

/-! ### The Separation instances

A fixed parameter layout for every test: the four fixed codes, the assignment, then the
recognizer's parameters; the tested condition is the single bound variable. -/

section Tests

variable {k sn : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} (Rec : InternalNameRecognition N)

/-- The parameter block at the test layout: `tagMem, tagEq, condSet, orderCode, a` at positions
`0`–`4`, the recognizer's parameters after. -/
def testParams : CompilerParams (Fin (5 + Rec.arity)) Rec.arity 1 where
  tagMem := var (Sum.inl (Fin.castAdd Rec.arity 0))
  tagEq := var (Sum.inl (Fin.castAdd Rec.arity 1))
  condSet := var (Sum.inl (Fin.castAdd Rec.arity 2))
  orderCode := var (Sum.inl (Fin.castAdd Rec.arity 3))
  recParams := fun i ↦ Sum.inl (Fin.natAdd 5 i)

/-- The assignment parameter at the test layout. -/
def testAssignment : memLang.Term (Fin (5 + Rec.arity) ⊕ Fin 1) :=
  var (Sum.inl (Fin.castAdd Rec.arity 4))

/-- The implication decision test, as a Separation instance. -/
def impTest (φ ψ : memLang.BoundedFormula (Fin k) sn) :
    memLang.BoundedFormula (Fin (5 + Rec.arity)) 1 :=
  impTestDef Rec φ ψ (testParams Rec) &0 (testAssignment Rec)

/-- The universal decision test, as a Separation instance. -/
def allTest (φ : memLang.BoundedFormula (Fin k) (sn + 1)) :
    memLang.BoundedFormula (Fin (5 + Rec.arity)) 1 :=
  allTestDef Rec φ (testParams Rec) &0 (testAssignment Rec)

/-- The parameter vector the tests are read at. -/
def testVector (tagMem tagEq condSet orderCode a : ↥M) : Fin (5 + Rec.arity) → ↥M :=
  Fin.append ![tagMem, tagEq, condSet, orderCode, a] Rec.params

/-- The layout realizes the invariant at its vector. -/
theorem testParams_realizes (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M)
    (hq : (natCode eqTag : ZFSet.{u}) ∈ M) (condSet orderCode a : ↥M) (xs : Fin 1 → M) :
    (testParams Rec).Realizes Rec condSet orderCode
      (testVector Rec ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩ condSet orderCode a) xs where
  tagMem_eq := by simp [testParams, testVector, Fin.append_left]
  tagEq_eq := by simp [testParams, testVector, Fin.append_left]
  condSet_eq := by simp [testParams, testVector, Fin.append_left]
  orderCode_eq := by simp [testParams, testVector, Fin.append_left]
  recParams_eq := fun i ↦ by simp [testParams, testVector, Fin.append_right]

/-- The assignment parameter realizes to the assignment. -/
theorem realize_testAssignment (tagMem tagEq condSet orderCode a : ↥M) (xs : Fin 1 → M) :
    Term.realize (Sum.elim (testVector Rec tagMem tagEq condSet orderCode a) xs)
      (testAssignment Rec) = a := by
  simp [testAssignment, testVector, Fin.append_left]

/-- **The compiled list of Separation instances** the formula-test family for `φ` needs: one
per implication subformula, one per universal subformula, none at the atomics. Independent of
the assignment, which is a parameter of each test rather than part of its formula. -/
def formulaTestSentences : ∀ {n : ℕ}, memLang.BoundedFormula (Fin k) n → Set memLang.Sentence
  | _, .falsum => ∅
  | _, .equal _ _ => ∅
  | _, .rel _ _ => ∅
  | _, .imp φ ψ =>
      insert (separationSentence (impTest Rec φ ψ))
        (formulaTestSentences φ ∪ formulaTestSentences ψ)
  | _, .all φ => insert (separationSentence (allTest Rec φ)) (formulaTestSentences φ)

end Tests

/-! ### The codes, materially -/

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] {Pres : InternalForcingPresentation M.toMaterialCarrier P}
variable {N : InternalNamePresentation M.toMaterialCarrier P} {Rec : InternalNameRecognition N}
variable {k sn : ℕ} {free : Fin k → N.Code}

/-- The shared material step: the typed atomic equivalences, pair closure, and a root
assignment as a carrier element. Empty Set is charged **here**, for the root assignment, and
nowhere else in this file. -/
private theorem test_context
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T) (hc : InternalNameCoding Pres N) :
    (∀ {x y : ZFSet.{u}}, x ∈ M.toMaterialCarrier → y ∈ M.toMaterialCarrier →
      ZFSet.pair x y ∈ M.toMaterialCarrier) ∧
    (∀ (r : P) (i j : N.Code),
      AtomicEqRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode (condCode Pres r)
        (N.code i) (N.code j) ↔ ForcesEq r (N.decode i) (N.decode j)) ∧
    (∀ (r : P) (i j : N.Code),
      AtomicMemRealized M.toMaterialCarrier Pres.conditionSet Pres.orderCode (condCode Pres r)
        (N.code i) (N.code j) ↔ ForcesMem r (N.decode i) (N.decode j)) ∧
    ∀ {n : ℕ} (a : Fin n → N.Code), N.assignmentCode a ∈ M.toMaterialCarrier :=
  ⟨fun hx hy ↦ M.pair_mem hp hx hy,
    fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).2.1,
    fun r i j ↦ (M.atomicRealized_iff hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
      hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc i j r).2.2,
    fun a ↦ InternalNamePresentation.assignmentCode_mem he hp a⟩

/-- **The implication decision test is coded**, on `atomicDefinability`'s ledger plus one
Separation instance. -/
theorem exists_impDecisionCode
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T) (hc : InternalNameCoding Pres N)
    (φ ψ : memLang.BoundedFormula (Fin k) sn) (htest : separationSentence (impTest Rec φ ψ) ∈ T)
    (bound : Fin sn → N.Code) :
    ∃ d : Pres.InternalSubset,
      d.externalize = impDecision N.names (N.decode ∘ free) φ ψ (N.decode ∘ bound) := by
  obtain ⟨hpair, hEq, hMem, hasg⟩ := M.test_context hbnd hsep hgat hfil hdom hgra hbr hbl hpsep
    hrgat hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc
  obtain ⟨d, hd⟩ := M.exists_internalSubset_of_separation (Pres := Pres) htest
    (testVector Rec ⟨_, M.natCode_mem he hp hu memWitnessTag⟩ ⟨_, M.natCode_mem he hp hu eqTag⟩
      Pres.conditionSet Pres.orderCode ⟨_, hasg (combinedCodes free bound)⟩)
  refine ⟨d, Set.ext fun r ↦ (hd r).trans ?_⟩
  exact externalize_impTest hpair hEq hMem (testParams_realizes Rec _ _ _ _ _ _)
    (by simp [condElem]) (by rw [realize_testAssignment])

/-- **The universal decision test is coded**, likewise. -/
theorem exists_allDecisionCode
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T) (hc : InternalNameCoding Pres N)
    (φ : memLang.BoundedFormula (Fin k) (sn + 1)) (htest : separationSentence (allTest Rec φ) ∈ T)
    (bound : Fin sn → N.Code) :
    ∃ d : Pres.InternalSubset,
      d.externalize = allDecision N.names (N.decode ∘ free) φ (N.decode ∘ bound) := by
  obtain ⟨hpair, hEq, hMem, hasg⟩ := M.test_context hbnd hsep hgat hfil hdom hgra hbr hbl hpsep
    hrgat hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc
  obtain ⟨d, hd⟩ := M.exists_internalSubset_of_separation (Pres := Pres) htest
    (testVector Rec ⟨_, M.natCode_mem he hp hu memWitnessTag⟩ ⟨_, M.natCode_mem he hp hu eqTag⟩
      Pres.conditionSet Pres.orderCode ⟨_, hasg (combinedCodes free bound)⟩)
  refine ⟨d, Set.ext fun r ↦ (hd r).trans ?_⟩
  exact externalize_allTest hpair hEq hMem (testParams_realizes Rec _ _ _ _ _ _)
    (by simp [condElem]) (by rw [realize_testAssignment])

/-- **Every member of the formula-test family is coded**, given exactly the Separation
instances in `formulaTestSentences`. By induction on the formula, generalizing the bound
assignment: the universal case's members live at extended assignments, which are again of the
form `N.decode ∘ bound'`. -/
theorem exists_code_of_mem_formulaTests
    (hbnd : entryBoundSentence ∈ T) (hsep : stageSeparationSentence ∈ T)
    (hgat : packageGatherSentence ∈ T) (hfil : packageFilterSentence ∈ T)
    (hdom : domainFamilySentence ∈ T) (hgra : graphFamilySentence ∈ T)
    (hbr : predBoundRightSentence ∈ T) (hbl : predBoundLeftSentence ∈ T)
    (hpsep : predSepSentence ∈ T) (hrgat : rowStateGatherSentence ∈ T)
    (hrfil : rowStateFilterSentence ∈ T) (hfgat : rowFinalGatherSentence ∈ T)
    (hffil : rowFinalFilterSentence ∈ T)
    (hinf : infinitySentence ∈ T) (hosep : omegaSepSentence ∈ T)
    (higat : iterateGatherSentence ∈ T) (hifil : iterateFilterSentence ∈ T)
    (hex : separationSentence approxExistsFormula ∈ T)
    (hmemi : separationSentence omegaMemTransFormula ∈ T)
    (hagree : separationSentence approxAgreeFormula ∈ T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    (huni : unionSentence ∈ T) (hc : InternalNameCoding Pres N) :
    ∀ {n : ℕ} (φ : memLang.BoundedFormula (Fin k) n), formulaTestSentences Rec φ ⊆ T →
      ∀ (bound : Fin n → N.Code),
        ∀ D ∈ formulaTests N.names (N.decode ∘ free) φ (N.decode ∘ bound),
          ∃ d : Pres.InternalSubset, d.externalize = D
  | _, .falsum, _, _, _, hD => absurd hD (Set.notMem_empty _)
  | _, .equal _ _, _, _, _, hD => absurd hD (Set.notMem_empty _)
  | _, .rel _ _, _, _, _, hD => absurd hD (Set.notMem_empty _)
  | _, .imp φ ψ, hT, bound, D, hD => by
    rw [formulaTests] at hD
    rcases Set.mem_insert_iff.1 hD with rfl | hD
    · exact M.exists_impDecisionCode hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
        hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc φ ψ
        (hT (Set.mem_insert _ _)) bound
    · have hT' : formulaTestSentences Rec φ ∪ formulaTestSentences Rec ψ ⊆ T :=
        fun s hs ↦ hT (Set.mem_insert_of_mem _ hs)
      rcases hD with hD | hD
      · exact exists_code_of_mem_formulaTests hbnd hsep hgat hfil hdom hgra hbr hbl hpsep
          hrgat hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc φ
          (fun s hs ↦ hT' (Set.mem_union_left _ hs)) bound D hD
      · exact exists_code_of_mem_formulaTests hbnd hsep hgat hfil hdom hgra hbr hbl hpsep
          hrgat hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc ψ
          (fun s hs ↦ hT' (Set.mem_union_right _ hs)) bound D hD
  | _, .all φ, hT, bound, D, hD => by
    rw [formulaTests] at hD
    rcases Set.mem_insert_iff.1 hD with rfl | hD
    · exact M.exists_allDecisionCode hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat hrfil
        hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc φ
        (hT (Set.mem_insert _ _)) bound
    · obtain ⟨τ, ⟨i, rfl⟩, hD⟩ := Set.mem_iUnion₂.1 hD
      rw [← Fin.comp_snoc] at hD
      exact exists_code_of_mem_formulaTests hbnd hsep hgat hfil hdom hgra hbr hbl hpsep hrgat
        hrfil hfgat hffil hinf hosep higat hifil hex hmemi hagree he hp hu huni hc φ
        (fun s hs ↦ hT (Set.mem_insert_of_mem _ hs)) (Fin.snoc bound i) D hD

end MaterialGround

end Forcing
