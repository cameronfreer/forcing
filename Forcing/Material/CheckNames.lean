/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.CheckGraph
import Forcing.Material.MaximalNames
import Forcing.Material.Axioms

/-!
# Check names are represented in the maximal family

M7 item 6 (#241), check-name representation, second PR. At a supplied condition `q`, every
ground element `x` has a maximal name whose value is `x` along every condition set containing
`q`:

```text
∀ x ∈ M, ∃ τ ∈ (maximal Pres).names, ∀ S, q ∈ S → zval S τ = x
```

The name is the one coded by `checkCode ⌜q⌝ x`. Three intermediate results, kept separate:

1. **Internal certificate existence** (`exists_checkGraph`): for `c, x ∈ M`, some check graph
   in the ground has an entry at `x`. External ∈-induction on `x`, carrying `x ∈ M`.
2. **Check-code membership** (`checkCode_mem`): read the value at `x` off that graph by
   pair-component transitivity, and identify it with `checkCode c x` by soundness.
3. **Representation** (`check_represented`): membership plus name-code validity
   (`isNameCode_checkCode`, axiom-free) put the code in the maximal family; valuation
   correctness (`zval_decode_checkCode`, axiom-free) is ∈-induction through
   `MaximalNames.mem_zval_decode_iff`.

## The inductive step

At `x`, with a graph in the ground for each member (the induction hypothesis):

* **gather** (Collection, `checkGatherSentence`, parameter `c`): a set `B` containing, for each
  `w ∈ x`, a graph with an entry at `w`;
* **filter** (Separation, `checkFilterSentence`, parameters `c`, `x`): `F ⊆ B`, the members of
  `B` that are graphs with an entry at some member of `x`. Coverage only — `F` need not contain
  every such graph;
* **flatten** (General Union): `U = ⋃₀ F`, a check graph by `isCheckGraph_sUnion` (agreement);
* **value image** (Separation, `valueImageSentence`, parameters `x`, `U`): the values of `U` at
  members of `x`, carved from `⋃⋃U` (General Union twice);
* **pair image** (Collection `pairImageGatherSentence`, parameter `c`, with Pairing witnesses;
  then Separation `pairImageFilterSentence`, parameters `c`, `V`): `Pₓ = {⟨c, g⟩ : g ∈ V}`;
* **extend** (Pairing, General Union): `U ∪ {⟨x, Pₓ⟩}` by `IsCheckGraph.extend`, with no
  freshness assumption.

**There is no base case.** When `x` has no members, the same steps run with vacuous witness
obligations: Collection returns *some* bound, the filter empties it, and the extension adjoins
`⟨x, Pₓ⟩` with `Pₓ` empty. No internal empty set is assumed in advance; Empty Set is not charged.

## Ledger

Read off `exists_checkGraph`: **two Collection instances** (`checkGatherSentence`,
`pairImageGatherSentence`), **three Separation instances** (`checkFilterSentence`,
`valueImageSentence`, `pairImageFilterSentence`), **Pairing**, and **General Union**. No
Infinity, no Empty Set, no Binary Union (unions go through `union_mem_of_sUnion`), no Power Set.

## Main results

* `Forcing.isNameCode_checkCode`: check codes at a valid condition code are valid.
* `Forcing.MaterialGround.exists_checkGraph`: internal certificate existence.
* `Forcing.MaterialGround.checkCode_mem`: check codes of ground elements are in the ground.
* `Forcing.MaterialGround.zval_decode_checkCode`: valuation correctness.
* `Forcing.MaterialGround.check_represented`: representation at a supplied condition.
-/

universe u

namespace Forcing

open FirstOrder Language PName

/-- **Check codes are valid name codes**, at a valid condition code. ∈-induction; axiom-free. -/
theorem isNameCode_checkCode {cs c : ZFSet.{u}} (hc : c ∈ cs) (x : ZFSet.{u}) :
    IsNameCode cs (checkCode c x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    refine IsNameCode.mk _ (fun b hb ↦ ?_) (fun b hb c' e hb' ↦ ?_)
    · obtain ⟨y, -, rfl⟩ := mem_checkCode_iff.1 hb
      exact ⟨c, _, rfl, hc⟩
    · obtain ⟨y, hy, rfl⟩ := mem_checkCode_iff.1 hb
      obtain ⟨-, rfl⟩ := ZFSet.pair_inj.1 hb'
      exact ih y hy

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-! ### The instances, at concrete parameters -/

theorem realize_checkGatherFormula (c w H : ↥M.toMaterialCarrier) :
    checkGatherFormula.Realize ![c] ![w, H] ↔
      CheckGraphAt (c : ZFSet.{u}) (w : ZFSet.{u}) (H : ZFSet.{u}) := by
  rw [checkGatherFormula, realize_checkGraphAtDef]
  simp

theorem realize_checkFilterFormula (c x H : ↥M.toMaterialCarrier) :
    checkFilterFormula.Realize ![c, x] ![H] ↔
      ∃ w ∈ (x : ZFSet.{u}), CheckGraphAt (c : ZFSet.{u}) w (H : ZFSet.{u}) := by
  have hw : ∀ w : ↥M.toMaterialCarrier,
      (checkGraphAtDef (liftTerm (var (Sum.inl 0))) (&(Fin.last 1))
        (liftTerm (&(0 : Fin 1)))).Realize ![c, x] (Fin.snoc ![H] w) ↔
      CheckGraphAt (c : ZFSet.{u}) (w : ZFSet.{u}) (H : ZFSet.{u}) := by
    intro w
    rw [realize_checkGraphAtDef]
    simp [liftTerm]
  simp only [checkFilterFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    memFormula, BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Sum.elim_inl, Function.comp_apply, Fin.snoc_last, Matrix.cons_val_zero, Matrix.cons_val_one,
    realize_liftTerm]
  exact ⟨fun ⟨w, hw', h⟩ ↦ ⟨(w : ZFSet.{u}), hw', (hw w).1 h⟩,
    fun ⟨w, hw', h⟩ ↦ ⟨⟨w, M.toMaterialCarrier.mem_trans hw' x.2⟩, hw', (hw _).2 h⟩⟩

theorem realize_valueImageFormula (x U g : ↥M.toMaterialCarrier) :
    valueImageFormula.Realize ![x, U] ![g] ↔
      ∃ w ∈ (x : ZFSet.{u}), ZFSet.pair w (g : ZFSet.{u}) ∈ (U : ZFSet.{u}) := by
  rw [valueImageFormula, realize_valueImageDef]
  simp

theorem realize_pairImageGatherFormula (c g p : ↥M.toMaterialCarrier) :
    pairImageGatherFormula.Realize ![c] ![g, p] ↔
      (p : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (g : ZFSet.{u}) := by
  rw [pairImageGatherFormula, realize_pairDef]
  simp

theorem realize_pairImageFilterFormula (c V p : ↥M.toMaterialCarrier) :
    pairImageFilterFormula.Realize ![c, V] ![p] ↔
      ∃ g ∈ (V : ZFSet.{u}), (p : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) g := by
  rw [pairImageFilterFormula, realize_pairImageDef]
  simp

/-! ### Internal certificate existence -/

/-- **Internal certificate existence**: for `c, x` in the ground, some check graph in the ground
has an entry at `x`. External ∈-induction on `x`, carrying `x ∈ M`; gather and filter give
validity and coverage, not every possible certificate. Ledger: two Collection instances, three
Separation instances, Pairing, General Union. -/
theorem exists_checkGraph (hcg : checkGatherSentence ∈ T) (hcf : checkFilterSentence ∈ T)
    (hvi : valueImageSentence ∈ T) (hpg : pairImageGatherSentence ∈ T)
    (hpf : pairImageFilterSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {c : ZFSet.{u}} (hc : c ∈ M) (x : ZFSet.{u}) : x ∈ M → ∃ H ∈ M, CheckGraphAt c x H := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
  intro hx
  -- gather
  obtain ⟨B, hB⟩ := M.exists_collection (φ := checkGatherFormula) hcg ![⟨c, hc⟩] ⟨x, hx⟩
    (fun w hw ↦ by
      obtain ⟨H, hHM, hH⟩ := ih w hw (M.mem_trans hw hx)
      exact ⟨⟨H, hHM⟩, (M.realize_checkGatherFormula ⟨c, hc⟩ w ⟨H, hHM⟩).2 hH⟩)
  -- filter
  obtain ⟨F, hF⟩ := M.exists_separation (φ := checkFilterFormula) hcf ![⟨c, hc⟩, ⟨x, hx⟩] B
  have hFgraph : ∀ H ∈ (F : ZFSet.{u}), IsCheckGraph c H := by
    intro H hHF
    have hHM := M.mem_trans hHF F.2
    obtain ⟨-, hH⟩ := (hF ⟨H, hHM⟩).1 hHF
    obtain ⟨-, -, hH, -⟩ := (M.realize_checkFilterFormula _ _ ⟨H, hHM⟩).1 hH
    exact hH
  -- flatten
  have hUM : ZFSet.sUnion (F : ZFSet.{u}) ∈ M := M.sUnion_mem huni F.2
  have hU : IsCheckGraph c (ZFSet.sUnion (F : ZFSet.{u})) := isCheckGraph_sUnion hFgraph
  have hcov : ∀ w ∈ x, ∃ g, ZFSet.pair w g ∈ ZFSet.sUnion (F : ZFSet.{u}) := by
    intro w hw
    obtain ⟨H, hHB, hH⟩ := hB ⟨w, M.mem_trans hw hx⟩ hw
    rw [M.realize_checkGatherFormula] at hH
    have hHF : (H : ZFSet.{u}) ∈ (F : ZFSet.{u}) :=
      (hF H).2 ⟨hHB, (M.realize_checkFilterFormula _ _ H).2 ⟨w, hw, hH⟩⟩
    obtain ⟨-, g, hg⟩ := hH
    exact ⟨g, ZFSet.mem_sUnion.2 ⟨H, hHF, hg⟩⟩
  -- value image, carved from `⋃⋃U`
  obtain ⟨V, hV⟩ := M.exists_separation (φ := valueImageFormula) hvi ![⟨x, hx⟩, ⟨_, hUM⟩]
    ⟨_, M.sUnion_mem huni (M.sUnion_mem huni hUM)⟩
  have hVmem : ∀ g, g ∈ (V : ZFSet.{u}) ↔
      ∃ w ∈ x, ZFSet.pair w g ∈ ZFSet.sUnion (F : ZFSet.{u}) := by
    intro g
    constructor
    · intro hg
      obtain ⟨-, h⟩ := (hV ⟨g, M.mem_trans hg V.2⟩).1 hg
      exact (M.realize_valueImageFormula _ _ ⟨g, _⟩).1 h
    · rintro ⟨w, hw, hwg⟩
      have hgM := (MaterialCarrier.pair_components_mem_of_mem hUM hwg).2
      exact (hV ⟨g, hgM⟩).2 ⟨(components_mem_sUnion_sUnion hwg).2,
        (M.realize_valueImageFormula _ _ ⟨g, hgM⟩).2 ⟨w, hw, hwg⟩⟩
  -- pair image: gather `⟨c, g⟩` for `g ∈ V` with Pairing witnesses, then filter
  obtain ⟨B', hB'⟩ := M.exists_collection (φ := pairImageGatherFormula) hpg ![⟨c, hc⟩] V
    (fun g _ ↦ ⟨⟨_, M.pair_mem hp hc g.2⟩,
      (M.realize_pairImageGatherFormula ⟨c, hc⟩ g ⟨_, M.pair_mem hp hc g.2⟩).2 rfl⟩)
  obtain ⟨Px, hPx⟩ := M.exists_separation (φ := pairImageFilterFormula) hpf ![⟨c, hc⟩, V] B'
  have hPxmem : ∀ p, p ∈ (Px : ZFSet.{u}) ↔
      ∃ w ∈ x, ∃ g, ZFSet.pair w g ∈ ZFSet.sUnion (F : ZFSet.{u}) ∧ p = ZFSet.pair c g := by
    intro p
    constructor
    · intro hp'
      obtain ⟨-, h⟩ := (hPx ⟨p, M.mem_trans hp' Px.2⟩).1 hp'
      obtain ⟨g, hg, rfl⟩ := (M.realize_pairImageFilterFormula _ _ ⟨p, _⟩).1 h
      obtain ⟨w, hw, hwg⟩ := (hVmem g).1 hg
      exact ⟨w, hw, g, hwg, rfl⟩
    · rintro ⟨w, hw, g, hwg, rfl⟩
      have hg := (hVmem g).2 ⟨w, hw, hwg⟩
      obtain ⟨⟨p', hp'M⟩, hp'B, hp'⟩ := hB' ⟨g, M.mem_trans hg V.2⟩ hg
      rw [M.realize_pairImageGatherFormula] at hp'
      change p' = ZFSet.pair c g at hp'
      subst hp'
      refine (hPx ⟨_, hp'M⟩).2 ⟨hp'B, ?_⟩
      exact (M.realize_pairImageFilterFormula _ _ ⟨_, hp'M⟩).2 ⟨g, hg, rfl⟩
  -- extend
  obtain ⟨-, hext⟩ := hU.extend hcov hPxmem
  exact ⟨_, M.union_mem_of_sUnion huni hp hUM (M.singleton_mem hp (M.pair_mem hp hx Px.2)),
    hext, Px, ZFSet.mem_union.2 (Or.inr (ZFSet.mem_singleton.2 rfl))⟩

/-! ### Check-code membership -/

/-- **Check codes of ground elements are in the ground**: the value at `x` is read off an
internal graph by pair-component transitivity and identified with `checkCode c x` by
soundness. -/
theorem checkCode_mem (hcg : checkGatherSentence ∈ T) (hcf : checkFilterSentence ∈ T)
    (hvi : valueImageSentence ∈ T) (hpg : pairImageGatherSentence ∈ T)
    (hpf : pairImageFilterSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {c x : ZFSet.{u}} (hc : c ∈ M) (hx : x ∈ M) : checkCode c x ∈ M := by
  obtain ⟨H, hHM, hH, g, hxg⟩ := M.exists_checkGraph hcg hcf hvi hpg hpf hp huni hc x hx
  rw [← hH.eq_checkCode x g hxg]
  exact (MaterialCarrier.pair_components_mem_of_mem hHM hxg).2

end MaterialGround

namespace MaximalNames

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable (Pres : InternalForcingPresentation M P)

/-- **Valuation correctness**: a maximal name coded by `checkCode ⌜q⌝ x` values to `x` along
every condition set containing `q`. ∈-induction through the decode-valuation reader;
axiom-free. -/
theorem zval_decode_checkCode (q : P) {S : Set P} (hq : q ∈ S) (x : ZFSet.{u}) :
    ∀ i : (maximal Pres).Code,
      (maximal Pres).code i = checkCode (ZFSet.mk (Pres.conditionCode.repr q)) x →
        zval S ((maximal Pres).decode i) = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro i hi
    refine ZFSet.ext fun y ↦ ?_
    rw [mem_zval_decode_iff]
    constructor
    · rintro ⟨p, -, j, hpj, rfl⟩
      rw [hi] at hpj
      obtain ⟨w, hw, hpw⟩ := mem_checkCode_iff.1 hpj
      rw [ih w hw j (ZFSet.pair_inj.1 hpw).2]
      exact hw
    · intro hy
      have hb : ZFSet.pair (ZFSet.mk (Pres.conditionCode.repr q))
          (checkCode (ZFSet.mk (Pres.conditionCode.repr q)) y) ∈ (maximal Pres).code i :=
        hi ▸ mem_checkCode_iff.2 ⟨y, hy, rfl⟩
      have hyM := (MaterialCarrier.pair_components_mem_of_mem ((maximal Pres).code_mem i) hb).2
      obtain ⟨j, hj⟩ := (mem_range_code_iff Pres).2
        ⟨hyM, isNameCode_checkCode (Pres.code_mem q) y⟩
      exact ⟨q, hq, j, hj ▸ hb, (ih y hy j hj).symm⟩

end MaximalNames

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-- **Check names are represented** at a supplied condition `q`: every ground element is the
value of a maximal name along every condition set containing `q`. Combines check-code
membership, name-code validity, and valuation correctness. -/
theorem check_represented (hcg : checkGatherSentence ∈ T) (hcf : checkFilterSentence ∈ T)
    (hvi : valueImageSentence ∈ T) (hpg : pairImageGatherSentence ∈ T)
    (hpf : pairImageFilterSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    (q : P) :
    ∀ x ∈ M, ∃ τ ∈ (MaximalNames.maximal Pres).names, ∀ S : Set P, q ∈ S → zval S τ = x := by
  intro x hx
  have hc : ZFSet.mk (Pres.conditionCode.repr q) ∈ M :=
    M.mem_trans (Pres.code_mem q) Pres.conditionSet.2
  obtain ⟨i, hi⟩ := (MaximalNames.mem_range_code_iff Pres).2
    ⟨M.checkCode_mem hcg hcf hvi hpg hpf hp huni hc hx,
      isNameCode_checkCode (Pres.code_mem q) x⟩
  exact ⟨_, (MaximalNames.maximal Pres).decode_mem_names i,
    fun S hq ↦ MaximalNames.zval_decode_checkCode Pres q hq x i hi⟩

end MaterialGround

end Forcing
