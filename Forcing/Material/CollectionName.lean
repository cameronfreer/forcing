/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.CompilerCorrectness
import Forcing.Material.TestCoding
import Forcing.Material.TestLayout
import Forcing.Material.AxiomSchemes
import Forcing.Material.MaximalNames

/-!
# The collection name: semantic laws and exact formula laws

M7 item 6 (#241), Collection, first of two PRs. For a name code `t = code i`, parameter codes
`free`, and `φ : BoundedFormula (Fin k) 2`, the witnesses are collected **per (condition, input)
pair**: for every condition code `c ∈ cs` and input `σ`, a witness `w` that `c` forces to satisfy
`φ(σ, w)` whenever some recognized witness exists, kept as the package `⟨c, w⟩`:

```text
collWitnessDef Rec φ Γ A idx y :=
  ∀ c σ, idx = ⟨c, σ⟩ → c ∈ condSet → Rec(σ) →
    ∃ w, Rec(w) ∧ y = ⟨c, w⟩ ∧
      ((∃ w', Rec(w') ∧ c ⊩ φ(σ, w')) → c ⊩ φ(σ, w))
```

`Rec(·)` is the recognizer formula, a **formula guard: no master name-code set**. `c ⊩ φ(σ, w)` is
`collForcesDef`: the compiled forcing at condition `c` and the extended assignment `⟨w, ⟨σ, A⟩⟩`
(the witness outermost, as `assignmentCode_snoc` puts the last bound name), reached by two nested
guarded universals, so the syntax asserts no existence.

**Why condition-indexed.** A witness is usable along `G` only under a condition in `G` that
forces it, and `G` is external. Indexing by every `c ∈ cs` lets the preservation proof use the
exact `r ∈ G` that the truth lemma returns for a concrete witness, with no relation to the
condition of the input's branch and no density argument of its own.

## The parameter layout

The test layout (`Forcing/Material/TestLayout.lean`), at two bound variables: the index `idx`
and the witness `y`. `t` is not a parameter.

## Layers, kept separate

1. **Raw formula laws**, carrier-relative, with no validity and no theory hypothesis:
   `realize_collForcesDef`, `realize_collWitnessDef` (recognition stays
   `Rec.formula.Realize Rec.params`), `realize_collPairFilterFormula`.
2. **Typed equivalences** (`MaximalNames`): `realize_collForcesDef_iff` through compiler
   correctness, and `realize_collWitnessDef_iff` reading the relation as `IsCollWitness`, which
   decodes through `Rec.realize_iff` only here.
3. **Totality** (`exists_isCollWitness`), split on whether a witnessing decomposition exists:
   if one does, `y := ⟨⌜q⌝, code j'⟩`, the only branch that constructs anything (Pairing);
   otherwise `y := idx`. At a good index that is `⟨c, σ⟩` with `w := σ`, and the implication is
   vacuous; at a bad index the guard is.
4. **The filter** (`collPairFilterFormula`, φ-independent; parameters `condSet` and
   `Rec.params` only): keeps the members `⟨⌜q⌝, code j⟩` of the collected set. Validity
   (`isNameCode_of_isCodePair`) and **coverage preservation** (`exists_mem_of_isCollWitness`:
   the package obtained for `(r, j)` survives filtering with that same `r`). The filter
   certifies neither forcing nor provenance; extra valid branches are harmless, since Collection
   asks for witness coverage, not an exact image.
5. **The witness lemma** (`exists_mem_zval_of_isCollWitness`): axiom-free given a supplied
   truth-lemma equivalence `htl`, used twice (truth to forcing, forcing to truth). Extracting
   the input's branch uses the forward direction of `mem_zval_decode_iff`; output membership
   needs only its reverse direction, from a filtered package under `r ∈ S`. No upward closure
   or directedness.

## Main definitions

* `Forcing.collForcesDef`, `Forcing.collWitnessDef`: the formulas, term-parameterized.
* `Forcing.collWitnessFormula`, `Forcing.collWitnessGatherSentence`: the Collection instance,
  one per `φ`.
* `Forcing.collPairFilterFormula`, `Forcing.collPairFilterSentence`: the Separation instance,
  one per recognizer.
* `Forcing.MaximalNames.IsCollWitness`, `Forcing.MaximalNames.IsCodePair`: the typed readings.

## Main results

* `Forcing.realize_collForcesDef`, `Forcing.realize_collWitnessDef`,
  `Forcing.realize_collPairFilterFormula`: the raw laws.
* `Forcing.MaximalNames.realize_collWitnessDef_iff`,
  `Forcing.MaximalNames.realize_collWitnessFormula_iff`,
  `Forcing.MaximalNames.realize_collPairFilterFormula_iff`: the typed equivalences.
* `Forcing.MaximalNames.exists_isCollWitness`: totality.
* `Forcing.MaximalNames.isNameCode_of_isCodePair`,
  `Forcing.MaximalNames.exists_mem_of_isCollWitness`: validity and coverage preservation.
* `Forcing.MaximalNames.exists_mem_zval_of_isCollWitness`: the witness lemma.
-/

universe u v

namespace Forcing

open FirstOrder Language AtomicRecursion PName

/-! ### The formulas -/

section Syntax

variable {α : Type v} {k m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P}

/-- **Compiled forcing at a two-name extension**: `∀ a₁, a₁ = ⟨σ, A⟩ → ∀ a₂, a₂ = ⟨w, a₁⟩ →
forcesDef φ c a₂`. Two guarded universals, as in `forcesDef_all`; the witness `w` is outermost. -/
def collForcesDef (Rec : InternalNameRecognition N) (φ : memLang.BoundedFormula (Fin k) 2)
    (Γ : CompilerParams α Rec.arity m) (c σ w A : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (pairDef (liftTerm σ) (liftTerm A) (&(Fin.last m)) ⟹
    ∀' (pairDef (liftTerm (liftTerm w)) (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1))) ⟹
      forcesDef Rec.formula φ Γ.lift.lift (liftTerm (liftTerm c)) (&(Fin.last (m + 1)))))

/-- **The total Collection relation**:
`∀ c σ, idx = ⟨c, σ⟩ → c ∈ condSet → Rec(σ) →
  ∃ w, Rec(w) ∧ y = ⟨c, w⟩ ∧ ((∃ w', Rec(w') ∧ c ⊩ φ(σ, w')) → c ⊩ φ(σ, w))`.
Each recognition guard is the recognizer spliced at the binder it guards. -/
def collWitnessDef (Rec : InternalNameRecognition N) (φ : memLang.BoundedFormula (Fin k) 2)
    (Γ : CompilerParams α Rec.arity m) (A idx y : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' ∀' (pairDef (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1))) (liftTerm (liftTerm idx)) ⟹
    (memFormula (&(Fin.castSucc (Fin.last m))) Γ.lift.lift.condSet ⟹
      (Rec.formula.relabel Γ.lift.recParams ⟹
        ∃' (Rec.formula.relabel Γ.lift.lift.recParams ⊓
          (pairDef (&(Fin.castSucc (Fin.castSucc (Fin.last m)))) (&(Fin.last (m + 2)))
              (liftTerm (liftTerm (liftTerm y))) ⊓
            ((∃' (Rec.formula.relabel Γ.lift.lift.lift.recParams ⊓
                collForcesDef Rec φ Γ.lift.lift.lift.lift
                  (&(Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last m)))))
                  (&(Fin.castSucc (Fin.castSucc (Fin.last (m + 1)))))
                  (&(Fin.last (m + 3))) (liftTerm (liftTerm (liftTerm (liftTerm A)))))) ⟹
              collForcesDef Rec φ Γ.lift.lift.lift
                (&(Fin.castSucc (Fin.castSucc (Fin.last m))))
                (&(Fin.castSucc (Fin.last (m + 1)))) (&(Fin.last (m + 2)))
                (liftTerm (liftTerm (liftTerm A)))))))))

end Syntax

/-! ### The raw formula laws -/

section Realization

variable {α : Type v} {k m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} {Rec : InternalNameRecognition N}
variable {v : α → M} {xs : Fin m → M} {condSet orderCode : ZFSet.{u}}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

/-- The recognizer spliced at the newest binder reads as recognition of that binder. -/
theorem CompilerParams.Realizes.realize_recognizer {Γ : CompilerParams α Rec.arity m}
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) (c : ↥M) :
    (Rec.formula.relabel Γ.recParams).Realize v (Fin.snoc xs c) ↔
      Rec.formula.Realize Rec.params ![c] := by
  rw [realize_relabel_snoc, show (fun i ↦ Sum.elim v xs (Γ.recParams i)) = Rec.params from
    funext hΓ.recParams_eq]

/-- **The extension law**, exact: the two guarded universals over internal `a₁`, `a₂`. -/
theorem realize_collForcesDef {φ : memLang.BoundedFormula (Fin k) 2}
    {Γ : CompilerParams α Rec.arity m} {c σ w A : memLang.Term (α ⊕ Fin m)} :
    (collForcesDef Rec φ Γ c σ w A).Realize v xs ↔
      ∀ a₁ : ↥M, (a₁ : ZFSet.{u}) = ZFSet.pair ⟪σ⟫ ⟪A⟫ →
        ∀ a₂ : ↥M, (a₂ : ZFSet.{u}) = ZFSet.pair ⟪w⟫ (a₁ : ZFSet.{u}) →
          (forcesDef Rec.formula φ Γ.lift.lift (liftTerm (liftTerm c))
            (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs a₁) a₂) := by
  simp only [collForcesDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_pairDef, Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]

/-- **The relation law**, exact and carrier-relative: recognition stays a realization of the
recognizer, and the compiled forcing stays `collForcesDef`. -/
theorem realize_collWitnessDef {φ : memLang.BoundedFormula (Fin k) 2}
    {Γ : CompilerParams α Rec.arity m} {A idx y : memLang.Term (α ⊕ Fin m)}
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (collWitnessDef Rec φ Γ A idx y).Realize v xs ↔
      ∀ c σ : ↥M, ⟪idx⟫ = ZFSet.pair (c : ZFSet.{u}) (σ : ZFSet.{u}) →
        (c : ZFSet.{u}) ∈ condSet → Rec.formula.Realize Rec.params ![σ] →
        ∃ w : ↥M, Rec.formula.Realize Rec.params ![w] ∧
          ⟪y⟫ = ZFSet.pair (c : ZFSet.{u}) (w : ZFSet.{u}) ∧
          ((∃ w' : ↥M, Rec.formula.Realize Rec.params ![w'] ∧
              (collForcesDef Rec φ Γ.lift.lift.lift.lift
                (&(Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last m)))))
                (&(Fin.castSucc (Fin.castSucc (Fin.last (m + 1)))))
                (&(Fin.last (m + 3))) (liftTerm (liftTerm (liftTerm (liftTerm A))))).Realize v
                  (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs c) σ) w) w')) →
            (collForcesDef Rec φ Γ.lift.lift.lift
              (&(Fin.castSucc (Fin.castSucc (Fin.last m))))
              (&(Fin.castSucc (Fin.last (m + 1)))) (&(Fin.last (m + 2)))
              (liftTerm (liftTerm (liftTerm A)))).Realize v
                (Fin.snoc (Fin.snoc (Fin.snoc xs c) σ) w)) := by
  simp only [collWitnessDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]
  refine forall_congr' fun c ↦ forall_congr' fun σ ↦ ?_
  rw [((hΓ.lift c).lift σ).condSet_eq, (hΓ.lift c).realize_recognizer σ]
  refine imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
    exists_congr fun w ↦ ?_
  rw [((hΓ.lift c).lift σ).realize_recognizer w]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ imp_congr_left (exists_congr fun w' ↦ ?_)
  rw [(((hΓ.lift c).lift σ).lift w).realize_recognizer w']

end Realization

/-! ### The Collection instance -/

section Instance

variable {k : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} (Rec : InternalNameRecognition N)

/-- **The witness relation** at the test layout: the index `&0`, the witness `&1`. -/
def collWitnessFormula (φ : memLang.BoundedFormula (Fin k) 2) :
    memLang.BoundedFormula (Fin (5 + Rec.arity)) 2 :=
  collWitnessDef Rec φ (testParams Rec) (testAssignment Rec) &0 &1

/-- The Collection instance for `φ`: one per formula. -/
def collWitnessGatherSentence (φ : memLang.BoundedFormula (Fin k) 2) : memLang.Sentence :=
  collectionSentence (collWitnessFormula Rec φ)

theorem collWitnessGatherSentence_mem_scheme (φ : memLang.BoundedFormula (Fin k) 2) :
    collWitnessGatherSentence Rec φ ∈ collectionScheme :=
  collectionSentence_mem_scheme _

/-! ### The filter -/

/-- **The package filter**, φ-independent: `∃ c w, c ∈ condSet ∧ m = ⟨c, w⟩ ∧ Rec(w)`, with
`condSet` at `0` and the recognizer's parameters after. -/
def collPairFilterFormula : memLang.BoundedFormula (Fin (1 + Rec.arity)) 1 :=
  ∃' ∃' (memFormula (&1) (var (Sum.inl (Fin.castAdd Rec.arity 0))) ⊓
    (pairDef (&1) (&2) (&0) ⊓ Rec.formula.relabel fun i ↦ Sum.inl (Fin.natAdd 1 i)))

/-- The Separation instance for the filter: one per recognizer, independent of `φ`. -/
def collPairFilterSentence : memLang.Sentence :=
  separationSentence (collPairFilterFormula Rec)

theorem collPairFilterSentence_mem_scheme : collPairFilterSentence Rec ∈ separationScheme :=
  separationSentence_mem_scheme _

/-- The parameter vector the filter is read at. -/
def collFilterVector (condSet : ↥M) : Fin (1 + Rec.arity) → ↥M :=
  Fin.append ![condSet] Rec.params

/-- **The filter law**, exact and carrier-relative. -/
theorem realize_collPairFilterFormula (condSet m : ↥M) :
    (collPairFilterFormula Rec).Realize (collFilterVector Rec condSet) ![m] ↔
      ∃ c w : ↥M, (c : ZFSet.{u}) ∈ (condSet : ZFSet.{u}) ∧
        (m : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (w : ZFSet.{u}) ∧
        Rec.formula.Realize Rec.params ![w] := by
  have hrec : ∀ c w : ↥M, (Rec.formula.relabel fun i ↦ Sum.inl (Fin.natAdd 1 i)).Realize
      (collFilterVector Rec condSet) (Fin.snoc (Fin.snoc ![m] c) w) ↔
        Rec.formula.Realize Rec.params ![w] := by
    intro c w
    rw [realize_relabel_snoc]
    simp [collFilterVector, Fin.append_right]
  simp only [collPairFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf, hrec]
  simp [memFormula, realize_pairDef, collFilterVector, Fin.append_left]

end Instance

/-! ### The typed layer -/

namespace MaximalNames

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- **The witness relation, typed**: at every typed decomposition `idx = ⟨⌜q⌝, code j⟩`, `y` is a
package `⟨⌜q⌝, code j''⟩` whose witness `q` forces to satisfy `φ` whenever some witness does.
Vacuous at indices with no typed decomposition. -/
def IsCollWitness {k : ℕ} (free : Fin k → (maximal Pres).Code)
    (φ : memLang.BoundedFormula (Fin k) 2) (idx y : ZFSet.{u}) : Prop :=
  ∀ (q : P) (j : (maximal Pres).Code),
    idx = ZFSet.pair (condCode Pres q) ((maximal Pres).code j) →
    ∃ j'' : (maximal Pres).Code, y = ZFSet.pair (condCode Pres q) ((maximal Pres).code j'') ∧
      ((∃ j' : (maximal Pres).Code, ForcesFormula (maximal Pres).names
          ((maximal Pres).decode ∘ free) q φ ![(maximal Pres).decode j, (maximal Pres).decode j'])
        → ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
            ![(maximal Pres).decode j, (maximal Pres).decode j''])

/-- **A package**, typed: a typed condition paired with a code. -/
def IsCodePair (m : ZFSet.{u}) : Prop :=
  ∃ (q : P) (j : (maximal Pres).Code), m = ZFSet.pair (condCode Pres q) ((maximal Pres).code j)

variable {Pres}

/-- **Totality.** Split on whether a typed witnessing decomposition exists: if so, the package
`⟨⌜q⌝, code j'⟩` (the only construction, by pair closure); if not, `idx` itself. -/
theorem exists_isCollWitness (hpair : ∀ {x y : ZFSet.{u}}, x ∈ M → y ∈ M → ZFSet.pair x y ∈ M)
    {k : ℕ} (free : Fin k → (maximal Pres).Code) (φ : memLang.BoundedFormula (Fin k) 2)
    (idx : ↥M) : ∃ y : ↥M, IsCollWitness Pres free φ idx y := by
  by_cases h : ∃ (q : P) (j j' : (maximal Pres).Code),
      (idx : ZFSet.{u}) = ZFSet.pair (condCode Pres q) ((maximal Pres).code j) ∧
        ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
          ![(maximal Pres).decode j, (maximal Pres).decode j']
  · obtain ⟨q, j, j', hidx, hf⟩ := h
    refine ⟨⟨_, hpair (condElem Pres q).2 ((maximal Pres).code_mem j')⟩, fun q₀ j₀ h₀ ↦ ?_⟩
    obtain ⟨hq, hj⟩ := ZFSet.pair_inj.1 (hidx.symm.trans h₀)
    obtain rfl := Pres.conditionCode.injective_mk hq
    obtain rfl := maximal_code_injective Pres hj
    exact ⟨j', rfl, fun _ ↦ hf⟩
  · refine ⟨idx, fun q j hidx ↦ ⟨j, hidx, fun ⟨j', hf⟩ ↦ (h ⟨q, j, j', hidx, hf⟩).elim⟩⟩

/-- **Validity**: a set whose members are exactly the packages of some `Y` is a valid code. -/
theorem isNameCode_of_isCodePair {Y B : ZFSet.{u}}
    (hB : ∀ m, m ∈ B ↔ m ∈ Y ∧ IsCodePair Pres m) :
    IsNameCode (Pres.conditionSet : ZFSet.{u}) B := by
  refine IsNameCode.mk _ (fun m hm ↦ ?_) (fun m hm c e hm' ↦ ?_)
  · obtain ⟨q, j, rfl⟩ := ((hB m).1 hm).2
    exact ⟨_, _, rfl, Pres.code_mem q⟩
  · obtain ⟨q, j, rfl⟩ := ((hB m).1 hm).2
    obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 hm'
    exact ((mem_range_code_iff Pres).1 ⟨j, rfl⟩).2

/-- **Coverage survives filtering, at the same condition.** If `y₀ ∈ Y` witnesses the index
`⟨⌜r⌝, code j⟩` and some witness is forced by `r`, then a package `⟨⌜r⌝, code j''⟩` with
`r ⊩ φ(j, j'')` lies in the filtered set. -/
theorem exists_mem_of_isCollWitness {k : ℕ} {free : Fin k → (maximal Pres).Code}
    {φ : memLang.BoundedFormula (Fin k) 2} {Y B y₀ : ZFSet.{u}}
    (hB : ∀ m, m ∈ B ↔ m ∈ Y ∧ IsCodePair Pres m) (hy₀ : y₀ ∈ Y) {r : P}
    {j : (maximal Pres).Code}
    (hw : IsCollWitness Pres free φ (ZFSet.pair (condCode Pres r) ((maximal Pres).code j)) y₀)
    (hex : ∃ j' : (maximal Pres).Code, ForcesFormula (maximal Pres).names
      ((maximal Pres).decode ∘ free) r φ ![(maximal Pres).decode j, (maximal Pres).decode j']) :
    ∃ j'' : (maximal Pres).Code,
      ZFSet.pair (condCode Pres r) ((maximal Pres).code j'') ∈ B ∧
      ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) r φ
        ![(maximal Pres).decode j, (maximal Pres).decode j''] := by
  obtain ⟨j'', rfl, himp⟩ := hw r j rfl
  exact ⟨j'', (hB _).2 ⟨hy₀, r, j'', rfl⟩, himp hex⟩

/-- **The witness lemma, over the extension carrier.** Given an index set covering
`cs × ⋃⋃ (code i)`, a collected set witnessing every index, its filtered packages exactly
`code b`, and the truth-lemma equivalence `htl` at `φ`: every `x` in the value of `i` with a
`φ`-witness in the extension carrier has one in the value of `b`. `htl` is used twice, truth to
forcing and back, at the exact `r ∈ S` it returns; no relation between `r` and the condition of
`x`'s branch is needed. Axiom-free, for every `S`; genericity enters only in discharging `htl`. -/
theorem exists_mem_zval_of_isCollWitness {S : Set P} {k : ℕ}
    {free : Fin k → (maximal Pres).Code} {φ : memLang.BoundedFormula (Fin k) 2}
    {i b : (maximal Pres).Code} {I Y : ZFSet.{u}}
    (hI : ∀ s ∈ (Pres.conditionSet : ZFSet.{u}),
      ∀ ρ ∈ ZFSet.sUnion (ZFSet.sUnion ((maximal Pres).code i)), ZFSet.pair s ρ ∈ I)
    (hY : ∀ idx ∈ I, ∃ y ∈ Y, IsCollWitness Pres free φ idx y)
    (hb : ∀ m, m ∈ (maximal Pres).code b ↔ m ∈ Y ∧ IsCodePair Pres m)
    (htl : ∀ j j' : (maximal Pres).Code,
      φ.Realize (fun l ↦ (maximal Pres).extVal S ((maximal Pres).decode (free l))
          ((maximal Pres).decode_mem_names _))
        ![(maximal Pres).extVal S ((maximal Pres).decode j) ((maximal Pres).decode_mem_names _),
          (maximal Pres).extVal S ((maximal Pres).decode j') ((maximal Pres).decode_mem_names _)]
        ↔ ∃ r ∈ S, ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) r φ
          ![(maximal Pres).decode j, (maximal Pres).decode j'])
    (x : (maximal Pres).extensionCarrier S)
    (hx : (x : ZFSet.{u}) ∈ zval S ((maximal Pres).decode i))
    (y : (maximal Pres).extensionCarrier S)
    (hφ : φ.Realize (fun l ↦ (maximal Pres).extVal S ((maximal Pres).decode (free l))
      ((maximal Pres).decode_mem_names _)) ![x, y]) :
    ∃ y' : (maximal Pres).extensionCarrier S,
      (y' : ZFSet.{u}) ∈ zval S ((maximal Pres).decode b) ∧
      φ.Realize (fun l ↦ (maximal Pres).extVal S ((maximal Pres).decode (free l))
        ((maximal Pres).decode_mem_names _)) ![x, y'] := by
  obtain ⟨p, -, j, hpj, hxj⟩ := (mem_zval_decode_iff Pres i).1 hx
  obtain ⟨j', hyj⟩ := (maximal Pres).mem_extensionCarrier_iff.1 y.2
  obtain rfl : x = (maximal Pres).extVal S ((maximal Pres).decode j)
      ((maximal Pres).decode_mem_names _) := Subtype.ext hxj
  obtain rfl : y = (maximal Pres).extVal S ((maximal Pres).decode j')
      ((maximal Pres).decode_mem_names _) := Subtype.ext hyj
  obtain ⟨r, hr, hf⟩ := (htl j j').1 hφ
  obtain ⟨y₀, hy₀, hw⟩ := hY _ (hI _ (Pres.code_mem r) _ (components_mem_sUnion_sUnion hpj).2)
  obtain ⟨j'', hmem, hf''⟩ := exists_mem_of_isCollWitness hb hy₀ hw ⟨j', hf⟩
  exact ⟨(maximal Pres).extVal S ((maximal Pres).decode j'') _,
    (mem_zval_decode_iff Pres b).2 ⟨r, hr, j'', hmem, rfl⟩, (htl j j'').2 ⟨r, hr, hf''⟩⟩

/-! ### The typed equivalences -/

section Typed

variable {α : Type v} {k m : ℕ} {Rec : InternalNameRecognition (maximal Pres)}
variable {v : α → M} {xs : Fin m → M} {free : Fin k → (maximal Pres).Code}
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

omit hpair hEq hMem in
/-- The two-name assignment: the witness outermost, then the input, then the parameters. -/
theorem assignmentCode_combinedCodes_pair (j j' : (maximal Pres).Code) :
    (maximal Pres).assignmentCode (combinedCodes free ![j, j']) =
      ZFSet.pair ((maximal Pres).code j') (ZFSet.pair ((maximal Pres).code j)
        ((maximal Pres).assignmentCode (combinedCodes free ![]))) := by
  have h : (![j, j'] : Fin 2 → (maximal Pres).Code) =
      Fin.snoc (Fin.snoc (![] : Fin 0 → (maximal Pres).Code) j) j' := by
    funext x
    match x with
    | 0 => rfl
    | 1 => rfl
  rw [h, combinedCodes_snoc, InternalNamePresentation.assignmentCode_snoc, combinedCodes_snoc,
    InternalNamePresentation.assignmentCode_snoc]

/-- **The extension, typed**: at a typed condition, two codes, and `A` coding the parameters
alone, the compiled two-name forcing is external forcing at `![decode j, decode j']`. Pair
closure builds the two guarded assignments in the forward direction, beyond compiler
correctness's own use. -/
theorem realize_collForcesDef_iff {φ : memLang.BoundedFormula (Fin k) 2}
    {Γ : CompilerParams α Rec.arity m} {c σ w A : memLang.Term (α ⊕ Fin m)} {q : P}
    {j j' : (maximal Pres).Code} (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hc : ⟪c⟫ = condCode Pres q) (hσ : ⟪σ⟫ = (maximal Pres).code j)
    (hw : ⟪w⟫ = (maximal Pres).code j')
    (hA : ⟪A⟫ = (maximal Pres).assignmentCode (combinedCodes free ![])) :
    (collForcesDef Rec φ Γ c σ w A).Realize v xs ↔
      ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
        ![(maximal Pres).decode j, (maximal Pres).decode j'] := by
  have hbound : ((maximal Pres).decode ∘ ![j, j']) =
      ![(maximal Pres).decode j, (maximal Pres).decode j'] := by
    funext x
    match x with
    | 0 => rfl
    | 1 => rfl
  have hcorr : ∀ a₁ a₂ : ↥M, (a₁ : ZFSet.{u}) = ZFSet.pair ⟪σ⟫ ⟪A⟫ →
      (a₂ : ZFSet.{u}) = ZFSet.pair ⟪w⟫ (a₁ : ZFSet.{u}) →
      ((forcesDef Rec.formula φ Γ.lift.lift (liftTerm (liftTerm c))
          (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs a₁) a₂) ↔
        ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
          ![(maximal Pres).decode j, (maximal Pres).decode j']) := by
    intro a₁ a₂ h₁ h₂
    rw [← hbound]
    refine realize_forcesDef_iff_forcesFormula hpair hEq hMem ((hΓ.lift a₁).lift a₂) ?_ ?_
    · simpa [realize_liftTerm] using hc
    · simp only [Function.comp_apply, Term.realize_var, Sum.elim_inr, Fin.snoc_last]
      rw [h₂, h₁, hσ, hw, hA, assignmentCode_combinedCodes_pair]
  rw [realize_collForcesDef]
  constructor
  · intro h
    have hAM : ⟪A⟫ ∈ M := (Term.realize (Sum.elim v xs) A : ↥M).2
    have hσM : ⟪σ⟫ ∈ M := (Term.realize (Sum.elim v xs) σ : ↥M).2
    have hwM : ⟪w⟫ ∈ M := (Term.realize (Sum.elim v xs) w : ↥M).2
    let a₁ : ↥M := ⟨ZFSet.pair ⟪σ⟫ ⟪A⟫, hpair hσM hAM⟩
    let a₂ : ↥M := ⟨ZFSet.pair ⟪w⟫ (a₁ : ZFSet.{u}), hpair hwM a₁.2⟩
    exact (hcorr a₁ a₂ rfl rfl).1 (h a₁ rfl a₂ rfl)
  · intro hf a₁ h₁ a₂ h₂
    exact (hcorr a₁ a₂ h₁ h₂).2 hf

/-- **The relation, typed**: at `A` coding the parameters alone, the witness relation holds of
`(idx, y)` exactly when `y` is a typed witness for `idx`. `code_surjective` types the condition,
`Rec.realize_iff` makes `σ`, `w`, `w'` codes, and compiler correctness reads the forcing. -/
theorem realize_collWitnessDef_iff {φ : memLang.BoundedFormula (Fin k) 2}
    {Γ : CompilerParams α Rec.arity m} {A idx y : memLang.Term (α ⊕ Fin m)}
    (hΓ : Γ.Realizes Rec Pres.conditionSet Pres.orderCode v xs)
    (hA : ⟪A⟫ = (maximal Pres).assignmentCode (combinedCodes free ![])) :
    (collWitnessDef Rec φ Γ A idx y).Realize v xs ↔ IsCollWitness Pres free φ ⟪idx⟫ ⟪y⟫ := by
  -- the two compiled forcings, typed at their contexts
  have hF3 : ∀ (c σ w : ↥M) (q : P) (j j' : (maximal Pres).Code),
      (c : ZFSet.{u}) = condCode Pres q → (σ : ZFSet.{u}) = (maximal Pres).code j →
      (w : ZFSet.{u}) = (maximal Pres).code j' →
      ((collForcesDef Rec φ Γ.lift.lift.lift
          (&(Fin.castSucc (Fin.castSucc (Fin.last m))))
          (&(Fin.castSucc (Fin.last (m + 1)))) (&(Fin.last (m + 2)))
          (liftTerm (liftTerm (liftTerm A)))).Realize v
            (Fin.snoc (Fin.snoc (Fin.snoc xs c) σ) w) ↔
        ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
          ![(maximal Pres).decode j, (maximal Pres).decode j']) := by
    intro c σ w q j j' hc hσ hw
    exact realize_collForcesDef_iff hpair hEq hMem (((hΓ.lift c).lift σ).lift w)
      (by simpa using hc) (by simpa using hσ) (by simpa using hw)
      (by simpa [realize_liftTerm] using hA)
  have hF4 : ∀ (c σ w w' : ↥M) (q : P) (j j' : (maximal Pres).Code),
      (c : ZFSet.{u}) = condCode Pres q → (σ : ZFSet.{u}) = (maximal Pres).code j →
      (w' : ZFSet.{u}) = (maximal Pres).code j' →
      ((collForcesDef Rec φ Γ.lift.lift.lift.lift
          (&(Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last m)))))
          (&(Fin.castSucc (Fin.castSucc (Fin.last (m + 1)))))
          (&(Fin.last (m + 3))) (liftTerm (liftTerm (liftTerm (liftTerm A))))).Realize v
            (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs c) σ) w) w') ↔
        ForcesFormula (maximal Pres).names ((maximal Pres).decode ∘ free) q φ
          ![(maximal Pres).decode j, (maximal Pres).decode j']) := by
    intro c σ w w' q j j' hc hσ hw'
    exact realize_collForcesDef_iff hpair hEq hMem ((((hΓ.lift c).lift σ).lift w).lift w')
      (by simpa using hc) (by simpa using hσ) (by simpa using hw')
      (by simpa [realize_liftTerm] using hA)
  rw [realize_collWitnessDef hΓ]
  constructor
  · intro h q j hidx
    obtain ⟨w, hwR, hy, himp⟩ := h (condElem Pres q) ⟨_, (maximal Pres).code_mem j⟩ hidx
      (Pres.code_mem q) (Rec.realize_code j)
    obtain ⟨j'', hj''⟩ := Rec.exists_code_of_realize hwR
    refine ⟨j'', hy.trans (by rw [hj'']; rfl), fun ⟨j', hf⟩ ↦ ?_⟩
    refine (hF3 _ _ w q j j'' rfl rfl hj'').1 (himp ⟨⟨_, (maximal Pres).code_mem j'⟩,
      Rec.realize_code j', (hF4 _ _ w _ q j j' rfl rfl rfl).2 hf⟩)
  · intro h c σ hidx hc hσR
    obtain ⟨q, hq⟩ := Pres.code_surjective c hc
    obtain ⟨j, hj⟩ := Rec.exists_code_of_realize hσR
    obtain ⟨j'', hy, himp⟩ := h q j (by rw [hidx, hq, hj]; rfl)
    refine ⟨⟨_, (maximal Pres).code_mem j''⟩, Rec.realize_code j'', by rw [hy, hq]; rfl,
      fun ⟨w', hw'R, hf⟩ ↦ ?_⟩
    obtain ⟨j', hj'⟩ := Rec.exists_code_of_realize hw'R
    exact (hF3 c σ _ q j j'' hq hj rfl).2
      (himp ⟨j', (hF4 c σ _ w' q j j' hq hj hj').1 hf⟩)

/-- **The instance, typed**: the witness relation at the test layout, with `A` coding the
parameters alone, holds of `(idx, y)` exactly when `y` is a typed witness for `idx`. -/
theorem realize_collWitnessFormula_iff (hm : (natCode memWitnessTag : ZFSet.{u}) ∈ M)
    (hq : (natCode eqTag : ZFSet.{u}) ∈ M) (φ : memLang.BoundedFormula (Fin k) 2) (A : ↥M)
    (hA : (A : ZFSet.{u}) = (maximal Pres).assignmentCode (combinedCodes free ![]))
    (idx y : ↥M) :
    (collWitnessFormula Rec φ).Realize
        (testVector Rec ⟨natCode memWitnessTag, hm⟩ ⟨natCode eqTag, hq⟩ Pres.conditionSet
          Pres.orderCode A) ![idx, y] ↔
      IsCollWitness Pres free φ (idx : ZFSet.{u}) (y : ZFSet.{u}) := by
  rw [collWitnessFormula, realize_collWitnessDef_iff hpair hEq hMem
    (testParams_realizes Rec hm hq _ _ _ _) (by rw [realize_testAssignment, hA])]
  rfl

end Typed

/-- **The filter, typed**: at the condition set, the filter keeps exactly the packages. -/
theorem realize_collPairFilterFormula_iff (Rec : InternalNameRecognition (maximal Pres))
    (m : ↥M) :
    (collPairFilterFormula Rec).Realize (collFilterVector Rec Pres.conditionSet) ![m] ↔
      IsCodePair Pres (m : ZFSet.{u}) := by
  rw [realize_collPairFilterFormula]
  constructor
  · rintro ⟨c, w, hc, hm, hwR⟩
    obtain ⟨q, hq⟩ := Pres.code_surjective c hc
    obtain ⟨j, hj⟩ := Rec.exists_code_of_realize hwR
    exact ⟨q, j, by rw [hm, hq, hj]; rfl⟩
  · rintro ⟨q, j, hm⟩
    exact ⟨condElem Pres q, ⟨_, (maximal Pres).code_mem j⟩, Pres.code_mem q, hm,
      Rec.realize_code j⟩

end MaximalNames

end Forcing
