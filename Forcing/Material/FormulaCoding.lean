/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Coding.Formula
import Forcing.Material.Axioms

/-!
# Formula codes inside a ground

The single place where the formula coding meets a material ground: **each individual formula
code lies in the ground**, priced at exactly the finite closure axioms — empty set, pairing,
and union (the last because the von Neumann numerals of the tags and arities are built by
`insert`).

The separation of the three costs is the point. Defining the code costs no theory at all and
lives in `Forcing/Coding/Formula.lean`, independent of `P`, orders, filters, and forcing.
Membership of an individual code costs finite closure, proved here by structural recursion —
each code is a finite tree, so no scheme is needed. **Collecting every formula code into one
member of the ground is a substantially stronger demand and is deliberately absent**: nothing
below quantifies a set of codes into existence, and item 3 is expected to recognize codes
through the parser characterization (`IsFormulaCode`) rather than through membership in a
coded set of all formulas.

## Main results

* `Forcing.MaterialGround.node_mem`, `Forcing.MaterialGround.termCode_mem`,
  `Forcing.MaterialGround.formulaCode_mem`: the codes lie in the ground, priced at empty set,
  pairing, and union.
-/

universe u

namespace Forcing

open FirstOrder

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)
variable (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)

include he hp hu in
/-- A node lies in the ground when its payload does: tags and arities are numerals, and the
node is built from Kuratowski pairs. -/
theorem node_mem {tag k n : ℕ} {payload : ZFSet.{u}} (hx : payload ∈ M) :
    node tag k n payload ∈ M :=
  M.pair_mem hp (M.natCode_mem he hp hu tag)
    (M.pair_mem hp (M.pair_mem hp (M.natCode_mem he hp hu k) (M.natCode_mem he hp hu n)) hx)

include he hp hu in
/-- Term codes lie in the ground. -/
theorem termCode_mem {k n : ℕ} (t : memLang.Term (Fin k ⊕ Fin n)) : termCode t ∈ M := by
  match t with
  | .var (Sum.inl i) => exact M.node_mem he hp hu (M.natCode_mem he hp hu i)
  | .var (Sum.inr j) => exact M.node_mem he hp hu (M.natCode_mem he hp hu j)
  | .func f _ => exact f.elim

include he hp hu in
/-- **Individual formula codes lie in the ground**, by structural recursion — each code is a
finite tree, so the price is exactly the finite closure axioms. No collection of all codes is
constructed. -/
theorem formulaCode_mem : ∀ {k n : ℕ} (φ : memLang.BoundedFormula (Fin k) n),
    formulaCode φ ∈ M
  | _, _, .falsum => by
    rw [formulaCode_falsum]; exact M.node_mem he hp hu (M.empty_mem he)
  | _, _, .equal t₁ t₂ => by
    rw [formulaCode_equal]
    exact M.node_mem he hp hu
      (M.pair_mem hp (M.termCode_mem he hp hu t₁) (M.termCode_mem he hp hu t₂))
  | _, _, .rel .mem ts => by
    rw [formulaCode_rel]
    exact M.node_mem he hp hu
      (M.pair_mem hp (M.termCode_mem he hp hu (ts 0)) (M.termCode_mem he hp hu (ts 1)))
  | _, _, .imp φ ψ => by
    rw [formulaCode_imp]
    exact M.node_mem he hp hu
      (M.pair_mem hp (formulaCode_mem φ) (formulaCode_mem ψ))
  | _, _, .all φ => by
    rw [formulaCode_all]
    exact M.node_mem he hp hu (formulaCode_mem φ)

end MaterialGround

end Forcing
