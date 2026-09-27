/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AxiomSchemes

/-!
# The pair-image gather

One Collection instance with two consumers: for a fixed left coordinate `c`, gather the pairs
`⟨c, g⟩` over an index set, with Pairing supplying each witness. The check-name construction
(`Forcing/Material/CheckNames.lean`) uses it for the pair image of a check code, and the union
construction (`Forcing/Material/ExtensionUnion.lean`) for the fibers `{s} × R` of its bound.
It lives here, apart from both, so neither consumer imports the other's machinery.

## Main definitions

* `Forcing.pairImageGatherFormula`, `Forcing.pairImageGatherSentence`.

## Main results

* `Forcing.MaterialGround.realize_pairImageGatherFormula`: the law at concrete parameters.
-/

universe u

namespace Forcing

open FirstOrder Language

/-- **Pair-image gather** (Collection; parameter `c`; index `g`, witness `p = ⟨c, g⟩`). -/
def pairImageGatherFormula : memLang.BoundedFormula (Fin 1) 2 :=
  pairDef (var (Sum.inl 0)) (&0) (&1)

def pairImageGatherSentence : memLang.Sentence := collectionSentence pairImageGatherFormula

theorem pairImageGatherSentence_mem_scheme : pairImageGatherSentence ∈ collectionScheme :=
  collectionSentence_mem_scheme pairImageGatherFormula

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

theorem realize_pairImageGatherFormula (c g p : ↥M.toMaterialCarrier) :
    pairImageGatherFormula.Realize ![c] ![g, p] ↔
      (p : ZFSet.{u}) = ZFSet.pair (c : ZFSet.{u}) (g : ZFSet.{u}) := by
  rw [pairImageGatherFormula, realize_pairDef]
  simp

end MaterialGround

end Forcing
