/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.CheckNames
import Forcing.Material.Extension

/-!
# Infinity in the extension

M7 item 6 (#241), the Infinity row. The extension along **any** condition set `S` containing a
supplied condition `q` satisfies Infinity:

```text
↥((maximal Pres).extensionCarrier S) ⊨ infinitySentence
```

No filter, no genericity, no `OrderTop`, and no truth lemma. The proof takes the ground's
inductive set `w` (`exists_inductive`), represents it in the extension by its check name at `q`
(`check_represented`), and applies `realize_inductiveDef` on the extension carrier: that law has
no hypotheses, because carrier transitivity supplies the witnesses for `∅` and for each
successor from the members of `w`.

## Ledger

`infinitySentence` plus the check-name ledger of `check_represented`: two Collection instances
(`checkGatherSentence`, `pairImageGatherSentence`), three Separation instances
(`checkFilterSentence`, `valueImageSentence`, `pairImageFilterSentence`), Pairing, General
Union. No truth-lemma ledger and no new scheme instance.

## Main results

* `Forcing.MaterialGround.extension_models_infinity`.
-/

universe u

namespace Forcing

open FirstOrder Language

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable {P : Type u} [Preorder P] (Pres : InternalForcingPresentation M.toMaterialCarrier P)

/-- **Infinity holds in the extension** along every condition set containing a supplied
condition `q`: the check name of the ground's inductive set values to that set, which is
inductive in any carrier containing it. -/
theorem extension_models_infinity (hinf : infinitySentence ∈ T)
    (hcg : checkGatherSentence ∈ T) (hcf : checkFilterSentence ∈ T)
    (hvi : valueImageSentence ∈ T) (hpg : pairImageGatherSentence ∈ T)
    (hpf : pairImageFilterSentence ∈ T) (hp : pairingSentence ∈ T) (huni : unionSentence ∈ T)
    {q : P} {S : Set P} (hq : q ∈ S) :
    ↥((MaximalNames.maximal Pres).extensionCarrier S) ⊨ infinitySentence := by
  obtain ⟨w, hwM, hw⟩ := M.exists_inductive hinf
  obtain ⟨τ, hτ, hval⟩ := M.check_represented Pres hcg hcf hvi hpg hpf hp huni q w hwM
  have hwE : w ∈ (MaximalNames.maximal Pres).extensionCarrier S :=
    (MaximalNames.maximal Pres).mem_extensionCarrier_of_mem_of_zval_eq hτ (hval S hq)
  simp only [infinitySentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex]
  exact ⟨⟨w, hwE⟩, realize_inductiveDef.2 hw⟩

end MaterialGround

end Forcing
