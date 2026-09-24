/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes
import Forcing.Material.Semantics

/-!
# Check graphs: the certificate for check-name codes

M7 item 6 (#241), check-name representation, first PR. The code of the check name of `x` at a
condition code `c` is

```text
checkCode c x = {⟨c, checkCode c y⟩ : y ∈ x}
```

an external ∈-recursion. "`g = checkCode c z`" is not first-order, so the internal construction
cannot index a scheme by it. This module replaces it, exactly as `IsNameDomain` replaced
descendant closure for #219, by a **local closure property** any set can be checked against:

```text
IsCheckGraph c H :=
  ∀ ⟨z, g⟩ ∈ H,
    (∀ w ∈ z, ∃ g', ⟨w, g'⟩ ∈ H) ∧                          -- z's members are in the domain
    (∀ b ∈ g, ∃ w ∈ z, ∃ g', ⟨w, g'⟩ ∈ H ∧ b = ⟨c, g'⟩) ∧    -- g has only the right branches
    (∀ w ∈ z, ∀ g', ⟨w, g'⟩ ∈ H → ⟨c, g'⟩ ∈ g)              -- and all of them
```

## Junk is ignored, not excluded

Members of `H` that are not pairs impose nothing, and `IsCheckGraph` promises **no** no-junk
property. That is harmless exactly because every observation and every projection retains its
pair guard — `⟨w, g⟩ ∈ H`, never `h ∈ H` — a discipline this module states and its consumers
keep.

## Agreement does the assembly work

Unlike `IsNameDomain`, the third clause quantifies over *other entries of the graph*, so joining
two graphs creates new obligations: an entry of `H₁` must also see the `H₂`-entries of its
members. The semantic laws are therefore proved in this order, all axiom-free:

1. **soundness** — an entry's value is the check code of its key (∈-induction);
2. **agreement** — two graphs agree on shared keys; functionality within a graph, with no
   functionality clause in the formula;
3. **closure under union** — the new obligations are discharged by agreement;
4. **extension** — adjoining `⟨x, Pₓ⟩` when every member of `x` already has an entry, **with no
   freshness assumption**: every value of the extended graph is the check code of its key
   (soundness for the old entries, the characterization of `Pₓ` for the new one), so old and
   new entries are handled alike, whether or not `x` already occurs.

`isCheckGraph_union` is the two-graph join pressure test.

## The formulas

Term-parameterized, membership and pairing only; `checkCode` never appears inside a formula.
Every quantifier bridge in the realization laws is carrier transitivity or pair-component
membership. The five instance formulas are the ones the internal construction
(`CheckNames.lean`) cites.

## Main definitions

* `Forcing.checkCode`, `Forcing.IsCheckGraph`, `Forcing.CheckGraphAt`.
* `Forcing.checkGraphDef`, `Forcing.checkGraphAtDef`, `Forcing.valueImageDef`,
  `Forcing.pairImageDef`: the formulas; `checkGatherFormula`, `checkFilterFormula`,
  `valueImageFormula`, `pairImageGatherFormula`, `pairImageFilterFormula`: the instances.

## Main results

* `Forcing.mem_checkCode_iff`; `Forcing.IsCheckGraph.eq_checkCode` (soundness),
  `Forcing.IsCheckGraph.agree`, `Forcing.isCheckGraph_sUnion`, `Forcing.isCheckGraph_union`,
  `Forcing.IsCheckGraph.extend`.
* `Forcing.realize_checkGraphDef`, `…realize_checkGraphAtDef`, `…realize_valueImageDef`,
  `…realize_pairImageDef`: the exact realization laws.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-! ### The code, and the certificate, on sets -/

/-- **The check code** of `x` at condition code `c`: `{⟨c, checkCode c y⟩ : y ∈ x}`. External
∈-recursion; never appears inside a formula. -/
noncomputable def checkCode (c : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  ZFSet.mem_wf.fix fun x IH ↦ ZFSet.range fun y : x ↦ ZFSet.pair c (IH y.1 y.2)

theorem mem_checkCode_iff {c x b : ZFSet.{u}} :
    b ∈ checkCode c x ↔ ∃ y ∈ x, b = ZFSet.pair c (checkCode c y) := by
  rw [checkCode, ZFSet.mem_wf.fix_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **A check graph** at `c`: every entry `⟨z, g⟩` has its key's members in the domain, and its
value consists of exactly the `c`-tagged values of those members' entries. Non-pair members
impose nothing. -/
def IsCheckGraph (c H : ZFSet.{u}) : Prop :=
  ∀ z g, ZFSet.pair z g ∈ H →
    (∀ w ∈ z, ∃ g', ZFSet.pair w g' ∈ H) ∧
    (∀ b ∈ g, ∃ w ∈ z, ∃ g', ZFSet.pair w g' ∈ H ∧ b = ZFSet.pair c g') ∧
    (∀ w ∈ z, ∀ g', ZFSet.pair w g' ∈ H → ZFSet.pair c g' ∈ g)

/-- A check graph with an entry at `w`. The relation the gathering Collection instance uses. -/
def CheckGraphAt (c w H : ZFSet.{u}) : Prop :=
  IsCheckGraph c H ∧ ∃ g, ZFSet.pair w g ∈ H

namespace IsCheckGraph

variable {c H : ZFSet.{u}}

/-- **Soundness**: an entry's value is the check code of its key. ∈-induction on the key. -/
theorem eq_checkCode (hH : IsCheckGraph c H) :
    ∀ z g, ZFSet.pair z g ∈ H → g = checkCode c z := by
  intro z
  induction z using ZFSet.inductionOn with
  | h z ih =>
    intro g hzg
    obtain ⟨hdom, hbr, hcomp⟩ := hH z g hzg
    refine ZFSet.ext fun b ↦ ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩
    · obtain ⟨w, hw, g', hwg', rfl⟩ := hbr b hb
      exact mem_checkCode_iff.2 ⟨w, hw, by rw [ih w hw g' hwg']⟩
    · obtain ⟨w, hw, rfl⟩ := mem_checkCode_iff.1 hb
      obtain ⟨g', hwg'⟩ := hdom w hw
      rw [← ih w hw g' hwg']
      exact hcomp w hw g' hwg'

/-- **Agreement**: two check graphs agree on shared keys. -/
theorem agree {H' : ZFSet.{u}} (hH : IsCheckGraph c H) (hH' : IsCheckGraph c H')
    {z g g' : ZFSet.{u}} (h : ZFSet.pair z g ∈ H) (h' : ZFSet.pair z g' ∈ H') : g = g' := by
  rw [hH.eq_checkCode z g h, hH'.eq_checkCode z g' h']

end IsCheckGraph

/-- **Closure under union**: the new cross-graph obligations are discharged by agreement. -/
theorem isCheckGraph_sUnion {c F : ZFSet.{u}} (hF : ∀ H ∈ F, IsCheckGraph c H) :
    IsCheckGraph c (ZFSet.sUnion F) := by
  intro z g hzg
  obtain ⟨H, hHF, hzgH⟩ := ZFSet.mem_sUnion.1 hzg
  obtain ⟨hdom, hbr, hcomp⟩ := hF H hHF z g hzgH
  refine ⟨fun w hw ↦ ?_, fun b hb ↦ ?_, fun w hw g' hwg' ↦ ?_⟩
  · obtain ⟨g', hwg'⟩ := hdom w hw
    exact ⟨g', ZFSet.mem_sUnion.2 ⟨H, hHF, hwg'⟩⟩
  · obtain ⟨w, hw, g', hwg', rfl⟩ := hbr b hb
    exact ⟨w, hw, g', ZFSet.mem_sUnion.2 ⟨H, hHF, hwg'⟩, rfl⟩
  · obtain ⟨H', hH'F, hwg'H'⟩ := ZFSet.mem_sUnion.1 hwg'
    obtain ⟨g'', hwg''⟩ := hdom w hw
    rw [(hF H' hH'F).agree (hF H hHF) hwg'H' hwg'']
    exact hcomp w hw g'' hwg''

/-- **The two-graph join**, the pressure test: entries of either graph now see the other's
entries at their members. -/
theorem isCheckGraph_union {c H₁ H₂ : ZFSet.{u}} (h₁ : IsCheckGraph c H₁)
    (h₂ : IsCheckGraph c H₂) : IsCheckGraph c (H₁ ∪ H₂) := by
  have hF : ∀ H ∈ ({H₁, H₂} : ZFSet.{u}), IsCheckGraph c H := by
    intro H hH
    rcases ZFSet.mem_pair.1 hH with rfl | rfl
    · exact h₁
    · exact h₂
  have hsu : ZFSet.sUnion ({H₁, H₂} : ZFSet.{u}) = H₁ ∪ H₂ :=
    ZFSet.ext fun z ↦ by
      simp only [ZFSet.mem_sUnion, ZFSet.mem_union, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
      constructor
      · rintro ⟨w, rfl | rfl, hz⟩
        · exact Or.inl hz
        · exact Or.inr hz
      · rintro (hz | hz)
        · exact ⟨H₁, Or.inl rfl, hz⟩
        · exact ⟨H₂, Or.inr rfl, hz⟩
  exact hsu ▸ isCheckGraph_sUnion hF

/-- **Extension**: if every member of `x` has an entry in the check graph `U`, and `Pₓ` is the set
of `c`-tagged values of those entries, then `Pₓ = checkCode c x` and `U ∪ {⟨x, Pₓ⟩}` is a check
graph. **No freshness assumption** on `x`. -/
theorem IsCheckGraph.extend {c U x Px : ZFSet.{u}} (hU : IsCheckGraph c U)
    (hcov : ∀ w ∈ x, ∃ g, ZFSet.pair w g ∈ U)
    (hPx : ∀ p, p ∈ Px ↔ ∃ w ∈ x, ∃ g, ZFSet.pair w g ∈ U ∧ p = ZFSet.pair c g) :
    Px = checkCode c x ∧ IsCheckGraph c (U ∪ {ZFSet.pair x Px}) := by
  have hPx' : Px = checkCode c x := by
    refine ZFSet.ext fun p ↦ ?_
    rw [hPx, mem_checkCode_iff]
    constructor
    · rintro ⟨w, hw, g, hwg, rfl⟩
      exact ⟨w, hw, by rw [hU.eq_checkCode w g hwg]⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨g, hwg⟩ := hcov w hw
      exact ⟨w, hw, g, hwg, by rw [hU.eq_checkCode w g hwg]⟩
  refine ⟨hPx', fun z g hzg ↦ ?_⟩
  -- a value at key `w` in the extended graph is the check code of `w`
  have hval : ∀ w g', ZFSet.pair w g' ∈ U ∪ {ZFSet.pair x Px} → g' = checkCode c w := by
    intro w g' hwg'
    rcases ZFSet.mem_union.1 hwg' with hwg' | hwg'
    · exact hU.eq_checkCode w g' hwg'
    · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 hwg')
      exact hPx'
  rcases ZFSet.mem_union.1 hzg with hzg | hzg
  · obtain ⟨hdom, hbr, hcomp⟩ := hU z g hzg
    refine ⟨fun w hw ↦ ?_, fun b hb ↦ ?_, fun w hw g' hwg' ↦ ?_⟩
    · obtain ⟨g', hwg'⟩ := hdom w hw
      exact ⟨g', ZFSet.mem_union.2 (Or.inl hwg')⟩
    · obtain ⟨w, hw, g', hwg', rfl⟩ := hbr b hb
      exact ⟨w, hw, g', ZFSet.mem_union.2 (Or.inl hwg'), rfl⟩
    · obtain ⟨g'', hwg''⟩ := hdom w hw
      rw [hval w g' hwg', ← hU.eq_checkCode w g'' hwg'']
      exact hcomp w hw g'' hwg''
  · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 hzg)
    refine ⟨fun w hw ↦ ?_, fun b hb ↦ ?_, fun w hw g' hwg' ↦ ?_⟩
    · obtain ⟨g', hwg'⟩ := hcov w hw
      exact ⟨g', ZFSet.mem_union.2 (Or.inl hwg')⟩
    · obtain ⟨w, hw, g', hwg', rfl⟩ := (hPx b).1 hb
      exact ⟨w, hw, g', ZFSet.mem_union.2 (Or.inl hwg'), rfl⟩
    · obtain ⟨g'', hwg''⟩ := hcov w hw
      rw [hval w g' hwg', ← hU.eq_checkCode w g'' hwg'']
      exact (hPx _).2 ⟨w, hw, g'', hwg'', rfl⟩

/-! ### The formulas -/

section Syntax

variable {α : Type v} {n : ℕ}

/-- `∀ w ∈ z, ∃ g', ⟨w, g'⟩ ∈ H`. -/
def checkDomainDef (H z : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm z) ⟹
    ∃' pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) (liftTerm (liftTerm H)))

/-- `∀ b ∈ g, ∃ w ∈ z, ∃ g', ⟨w, g'⟩ ∈ H ∧ b = ⟨c, g'⟩`. -/
def checkBranchDef (c H z g : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm g) ⟹
    ∃' (memFormula (&(Fin.last (n + 1))) (liftTerm (liftTerm z)) ⊓
      ∃' (pairMemDef (&(Fin.castSucc (Fin.last (n + 1)))) (&(Fin.last (n + 2)))
          (liftTerm (liftTerm (liftTerm H))) ⊓
        pairDef (liftTerm (liftTerm (liftTerm c))) (&(Fin.last (n + 2)))
          (&(Fin.castSucc (Fin.castSucc (Fin.last n)))))))

/-- `∀ w ∈ z, ∀ g', ⟨w, g'⟩ ∈ H → ⟨c, g'⟩ ∈ g`. -/
def checkCompleteDef (c H z g : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' (memFormula (&(Fin.last n)) (liftTerm z) ⟹
    ∀' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) (liftTerm (liftTerm H)) ⟹
      pairMemDef (liftTerm (liftTerm c)) (&(Fin.last (n + 1))) (liftTerm (liftTerm g))))

/-- **The check-graph formula**: `∀ z g, ⟨z, g⟩ ∈ H → domain ∧ branch ∧ complete`. -/
def checkGraphDef (c H : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))
      (liftTerm (liftTerm H)) ⟹
    (checkDomainDef (liftTerm (liftTerm H)) (&(Fin.castSucc (Fin.last n))) ⊓
      (checkBranchDef (liftTerm (liftTerm c)) (liftTerm (liftTerm H))
          (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) ⊓
        checkCompleteDef (liftTerm (liftTerm c)) (liftTerm (liftTerm H))
          (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))))))

/-- **A check graph with an entry at `w`.** -/
def checkGraphAtDef (c w H : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  checkGraphDef c H ⊓ ∃' pairMemDef (liftTerm w) (&(Fin.last n)) (liftTerm H)

/-- `∃ w ∈ x, ⟨w, g⟩ ∈ U`: `g` is a value at some member of `x`. -/
def valueImageDef (x U g : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (memFormula (&(Fin.last n)) (liftTerm x) ⊓
    pairMemDef (&(Fin.last n)) (liftTerm g) (liftTerm U))

/-- `∃ g ∈ V, p = ⟨c, g⟩`: `p` is a `c`-tagged member of `V`. -/
def pairImageDef (c V p : memLang.Term (α ⊕ Fin n)) : memLang.BoundedFormula α n :=
  ∃' (memFormula (&(Fin.last n)) (liftTerm V) ⊓
    pairDef (liftTerm c) (&(Fin.last n)) (liftTerm p))

/-- **Graph gather** (Collection; parameter `c`; index `w`, witness `H`). -/
def checkGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  checkGraphAtDef (var (Sum.inl 0)) (&0) (&1)

/-- **Graph filter** (Separation; parameters `c`, `x`): `∃ w ∈ x, CheckGraphAt c w H`. -/
def checkFilterFormula : memLang.BoundedFormula (Fin 2) 1 :=
  ∃' (memFormula (&(Fin.last 1)) (liftTerm (var (Sum.inl 1))) ⊓
    checkGraphAtDef (liftTerm (var (Sum.inl 0))) (&(Fin.last 1)) (liftTerm (&(0 : Fin 1))))

/-- **Value image** (Separation; parameters `x`, `U`). -/
def valueImageFormula : memLang.BoundedFormula (Fin 2) 1 :=
  valueImageDef (var (Sum.inl 0)) (var (Sum.inl 1)) (&0)

/-- **Pair-image gather** (Collection; parameter `c`; index `g`, witness `p = ⟨c, g⟩`). -/
def pairImageGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  pairDef (var (Sum.inl 0)) (&0) (&1)

/-- **Pair-image filter** (Separation; parameters `c`, `V`). -/
def pairImageFilterFormula : memLang.BoundedFormula (Fin 2) 1 :=
  pairImageDef (var (Sum.inl 0)) (var (Sum.inl 1)) (&0)

def checkGatherSentence : memLang.Sentence := collectionSentence checkGatherFormula
def checkFilterSentence : memLang.Sentence := separationSentence checkFilterFormula
def valueImageSentence : memLang.Sentence := separationSentence valueImageFormula
def pairImageGatherSentence : memLang.Sentence := collectionSentence pairImageGatherFormula
def pairImageFilterSentence : memLang.Sentence := separationSentence pairImageFilterFormula

theorem checkGatherSentence_mem_scheme : checkGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme checkGatherFormula
theorem checkFilterSentence_mem_scheme : checkFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme checkFilterFormula
theorem valueImageSentence_mem_scheme : valueImageSentence ∈ separationScheme :=
  separationSentence_mem_scheme valueImageFormula
theorem pairImageGatherSentence_mem_scheme : pairImageGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme pairImageGatherFormula
theorem pairImageFilterSentence_mem_scheme : pairImageFilterSentence ∈ separationScheme :=
  separationSentence_mem_scheme pairImageFilterFormula

end Syntax

/-! ### Realization laws -/

section Realization

variable {α : Type v} {n : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin n → M}

set_option quotPrecheck false in
/-- The set a term realizes to; local to this section. -/
local notation "⟪" t "⟫" => ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet)

theorem realize_checkDomainDef {H z : memLang.Term (α ⊕ Fin n)} :
    (checkDomainDef H z).Realize v xs ↔ ∀ w ∈ ⟪z⟫, ∃ g', ZFSet.pair w g' ∈ ⟪H⟫ := by
  have hzM : ⟪z⟫ ∈ M := (Term.realize (Sum.elim v xs) z : ↥M).2
  have hHM : ⟪H⟫ ∈ M := (Term.realize (Sum.elim v xs) H : ↥M).2
  simp only [checkDomainDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, memFormula, BoundedFormula.realize_rel₂, relMap_mem,
    Matrix.cons_val_zero, Matrix.cons_val_one, realize_pairMemDef, Term.realize_var,
    Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm]
  constructor
  · intro h w hw
    obtain ⟨g', hg'⟩ := h ⟨w, M.mem_trans hw hzM⟩ hw
    exact ⟨g', hg'⟩
  · intro h w hw
    obtain ⟨g', hg'⟩ := h w hw
    exact ⟨⟨g', (M.pair_components_mem_of_mem hHM hg').2⟩, hg'⟩

theorem realize_checkBranchDef {c H z g : memLang.Term (α ⊕ Fin n)} :
    (checkBranchDef c H z g).Realize v xs ↔
      ∀ b ∈ ⟪g⟫, ∃ w ∈ ⟪z⟫, ∃ g', ZFSet.pair w g' ∈ ⟪H⟫ ∧ b = ZFSet.pair ⟪c⟫ g' := by
  have hzM : ⟪z⟫ ∈ M := (Term.realize (Sum.elim v xs) z : ↥M).2
  have hgM : ⟪g⟫ ∈ M := (Term.realize (Sum.elim v xs) g : ↥M).2
  have hHM : ⟪H⟫ ∈ M := (Term.realize (Sum.elim v xs) H : ↥M).2
  simp only [checkBranchDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply,
    Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm]
  constructor
  · intro h b hb
    obtain ⟨w, hw, g', hwg', hb'⟩ := h ⟨b, M.mem_trans hb hgM⟩ hb
    exact ⟨w, hw, g', hwg', hb'⟩
  · intro h b hb
    obtain ⟨w, hw, g', hwg', hb'⟩ := h b hb
    exact ⟨⟨w, M.mem_trans hw hzM⟩, hw, ⟨g', (M.pair_components_mem_of_mem hHM hwg').2⟩, hwg',
      hb'⟩

theorem realize_checkCompleteDef {c H z g : memLang.Term (α ⊕ Fin n)} :
    (checkCompleteDef c H z g).Realize v xs ↔
      ∀ w ∈ ⟪z⟫, ∀ g', ZFSet.pair w g' ∈ ⟪H⟫ → ZFSet.pair ⟪c⟫ g' ∈ ⟪g⟫ := by
  have hzM : ⟪z⟫ ∈ M := (Term.realize (Sum.elim v xs) z : ↥M).2
  have hHM : ⟪H⟫ ∈ M := (Term.realize (Sum.elim v xs) H : ↥M).2
  simp only [checkCompleteDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_pairMemDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, realize_liftTerm]
  constructor
  · intro h w hw g' hwg'
    exact h ⟨w, M.mem_trans hw hzM⟩ hw ⟨g', (M.pair_components_mem_of_mem hHM hwg').2⟩ hwg'
  · intro h w hw g' hwg'
    exact h w hw g' hwg'

/-- **The check-graph law**: exact against `IsCheckGraph`. -/
theorem realize_checkGraphDef {c H : memLang.Term (α ⊕ Fin n)} :
    (checkGraphDef c H).Realize v xs ↔ IsCheckGraph ⟪c⟫ ⟪H⟫ := by
  have hHM : ⟪H⟫ ∈ M := (Term.realize (Sum.elim v xs) H : ↥M).2
  have hw : ∀ z g : ↥M,
      ((checkDomainDef (liftTerm (liftTerm H)) (&(Fin.castSucc (Fin.last n))) ⊓
        (checkBranchDef (liftTerm (liftTerm c)) (liftTerm (liftTerm H))
            (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1))) ⊓
          checkCompleteDef (liftTerm (liftTerm c)) (liftTerm (liftTerm H))
            (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))))).Realize v
          (Fin.snoc (Fin.snoc xs z) g) ↔
      (∀ w ∈ (z : ZFSet.{u}), ∃ g', ZFSet.pair w g' ∈ ⟪H⟫) ∧
      (∀ b ∈ (g : ZFSet.{u}), ∃ w ∈ (z : ZFSet.{u}), ∃ g', ZFSet.pair w g' ∈ ⟪H⟫ ∧
        b = ZFSet.pair ⟪c⟫ g') ∧
      (∀ w ∈ (z : ZFSet.{u}), ∀ g', ZFSet.pair w g' ∈ ⟪H⟫ →
        ZFSet.pair ⟪c⟫ g' ∈ (g : ZFSet.{u})) := by
    intro z g
    rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf, realize_checkDomainDef,
      realize_checkBranchDef, realize_checkCompleteDef]
    simp [realize_liftTerm]
  simp only [checkGraphDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm, IsCheckGraph]
  constructor
  · intro h z g hzg
    obtain ⟨hzM, hgM⟩ := M.pair_components_mem_of_mem hHM hzg
    exact (hw ⟨z, hzM⟩ ⟨g, hgM⟩).1 (h ⟨z, hzM⟩ ⟨g, hgM⟩ hzg)
  · intro h z g hzg
    exact (hw z g).2 (h z g hzg)

/-- **The entry law**: exact against `CheckGraphAt`. -/
theorem realize_checkGraphAtDef {c w H : memLang.Term (α ⊕ Fin n)} :
    (checkGraphAtDef c w H).Realize v xs ↔ CheckGraphAt ⟪c⟫ ⟪w⟫ ⟪H⟫ := by
  have hHM : ⟪H⟫ ∈ M := (Term.realize (Sum.elim v xs) H : ↥M).2
  rw [checkGraphAtDef, BoundedFormula.realize_inf, realize_checkGraphDef, CheckGraphAt]
  refine and_congr_right fun _ ↦ ?_
  simp only [BoundedFormula.realize_ex, realize_pairMemDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, realize_liftTerm]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, hg⟩,
    fun ⟨g, hg⟩ ↦ ⟨⟨g, (M.pair_components_mem_of_mem hHM hg).2⟩, hg⟩⟩

/-- **The value-image law.** -/
theorem realize_valueImageDef {x U g : memLang.Term (α ⊕ Fin n)} :
    (valueImageDef x U g).Realize v xs ↔ ∃ w ∈ ⟪x⟫, ZFSet.pair w ⟪g⟫ ∈ ⟪U⟫ := by
  have hxM : ⟪x⟫ ∈ M := (Term.realize (Sum.elim v xs) x : ↥M).2
  simp only [valueImageDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairMemDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    realize_liftTerm]
  exact ⟨fun ⟨w, hw, h⟩ ↦ ⟨w, hw, h⟩, fun ⟨w, hw, h⟩ ↦ ⟨⟨w, M.mem_trans hw hxM⟩, hw, h⟩⟩

/-- **The pair-image law.** -/
theorem realize_pairImageDef {c V p : memLang.Term (α ⊕ Fin n)} :
    (pairImageDef c V p).Realize v xs ↔ ∃ g ∈ ⟪V⟫, ⟪p⟫ = ZFSet.pair ⟪c⟫ g := by
  have hVM : ⟪V⟫ ∈ M := (Term.realize (Sum.elim v xs) V : ↥M).2
  simp only [pairImageDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    realize_liftTerm]
  exact ⟨fun ⟨g, hg, h⟩ ↦ ⟨g, hg, h⟩, fun ⟨g, hg, h⟩ ↦ ⟨⟨g, M.mem_trans hg hVM⟩, hg, h⟩⟩

end Realization

end Forcing
