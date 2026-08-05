/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.MaterialPresentation
import Forcing.Cohen.Avoidance
import Forcing.Material.Extension

/-!
# The final material composition: Cohen forcing adds a new real

This filename was retired at the M3 reframe and returns exactly when its phrase is earned.
The two halves of the material bridge meet here — and only here: the derived visibility of
the Cohen material presentation (membership side absent) and the material extension of the
internal names (visibility side absent).

The theorem levels, in dependency order:

* **Genericity-free membership**: a semantic representative of the Cohen-real name
  (`HasCohenRealName` — deliberately a standalone bundle, not merged into
  `HasCanonicalNames`) puts `zval S cohenRealName` in the extension carrier along any
  condition set containing `⊤`, with the total-union specialization via the strong
  partial-union theorem.
* **Countability-free adequacy** (`exists_realCode_mem_not_mem`): an already-generic `G`
  yields the new-real pair for the canonical extracted real —
  `realCode c_G ∈ M[G] ∧ realCode c_G ∉ M` — where totality comes from the derived `Sees`
  and genericity, membership from the Cohen-real representative, and nonmembership from M3
  avoidance read through the derived designated reals. No countability, no
  `HasCanonicalNames`.
* **The full `M[G]` contract and existence** (`addsNewReal`): with canonical names, ground
  inclusion holds by the existing extension-contract declarations, and external countability
  of the carrier supplies a generic filter through any condition — packaging genericity,
  ground inclusion, and the new-real pair. Only this last step consumes countability.

Adequacy and existence stay separate to the end, and the non-claims stand: no ZFC-in-`M[G]`,
no truth lemma, no minimality — the eventual `M[G] = M[c_G]` must compare against an
independently characterized extension.

## Main definitions

* `Forcing.Cohen.HasCohenRealName`: the semantic Cohen-real-name bundle.

## Main results

* `Forcing.Cohen.exists_realCode_mem_not_mem`: countability-free adequacy — the new-real
  pair over any generic filter.
* `Forcing.Cohen.addsNewReal`: **Cohen forcing adds a new real** — the reserved phrase,
  earned.
-/

namespace Forcing.Cohen

open FinitePartialFunction PName InternalNamePresentation Order

variable {M : MaterialCarrier.{0}} {N : InternalNamePresentation M Cond}

/-- The semantic Cohen-real-name bundle: some internal name agrees with `cohenRealName` in
valuation along every condition set containing `⊤`. Standalone — deliberately not merged into
`HasCanonicalNames`, so the adequacy theorem consumes exactly this and nothing more. -/
structure HasCohenRealName (N : InternalNamePresentation M Cond) : Prop where
  /-- The semantic representative of the Cohen-real name. -/
  represented : ∃ τ ∈ N.names, ∀ S : Set Cond, (⊤ : Cond) ∈ S →
    zval S τ = zval S cohenRealName

namespace HasCohenRealName

/-- **Genericity-free membership**: the value of the Cohen-real name lands in the extension
carrier, along any condition set containing `⊤`. -/
theorem zval_mem_extensionCarrier (h : HasCohenRealName N) {S : Set Cond}
    (hS : (⊤ : Cond) ∈ S) : zval S cohenRealName ∈ N.extensionCarrier S := by
  obtain ⟨τ, hτ, hval⟩ := h.represented
  exact N.mem_extensionCarrier_of_mem_of_zval_eq hτ (hval S hS)

/-- The total-union specialization, via the strong partial-union theorem: for a filter with a
total union, the *real code of the extracted real* is in the extension carrier. -/
theorem realCode_totalUnion_mem (h : HasCohenRealName N) {G : PFilter Cond}
    (htotal : ∀ n, (genericFun G n).isSome) :
    realCode (totalUnion G htotal) ∈ N.extensionCarrier (G : Set Cond) := by
  rw [← zval_cohenRealName_totalUnion htotal]
  exact h.zval_mem_extensionCarrier G.top_mem

end HasCohenRealName

/-- **Countability-free adequacy**: an `M`-generic filter (over the derived context) yields
the new-real pair for its canonical extracted real — membership in the extension carrier from
the Cohen-real representative, material nonmembership from M3 avoidance through the derived
designated reals. Totality is derived, not assumed; no countability, no `HasCanonicalNames`. -/
theorem exists_realCode_mem_not_mem (C : CohenMaterialPresentation M)
    (hreal : HasCohenRealName N) {G : PFilter Cond}
    (hG : C.derivedContext.GenericOver G) :
    ∃ htotal : ∀ n, (genericFun G n).isSome,
      realCode (totalUnion G htotal) ∈ N.extensionCarrier (G : Set Cond) ∧
        realCode (totalUnion G htotal) ∉ M := by
  have htotal := isSome_genericFun_of_genericOver C.sees_derivedContext hG
  exact ⟨htotal, hreal.realCode_totalUnion_mem htotal,
    C.not_mem_designatedReals_iff.1
      (not_mem_designatedReals_of_genericOver C.sees_derivedContext hG
        (unionFun_totalUnion htotal))⟩

/-- **Cohen forcing adds a new real** — the reserved phrase, earned: through any condition
there is a filter generic over the derived context whose extension satisfies the full
contract — ground inclusion (by the existing extension-contract declarations, consumed here
rather than reproved) together with the new-real pair. Only this existence step consumes
countability, and only of the carrier. -/
theorem addsNewReal (C : CohenMaterialPresentation M)
    (hcan : HasCanonicalNames C.forcing N) (hreal : HasCohenRealName N)
    (hM : (M : Set ZFSet.{0}).Countable) (p : Cond) :
    ∃ G : PFilter Cond, p ∈ G ∧ C.derivedContext.GenericOver G ∧
      (∀ x ∈ M, x ∈ N.extensionCarrier (G : Set Cond)) ∧
      ∃ htotal : ∀ n, (genericFun G n).isSome,
        realCode (totalUnion G htotal) ∈ N.extensionCarrier (G : Set Cond) ∧
          realCode (totalUnion G htotal) ∉ M := by
  obtain ⟨G, hpG, hG⟩ :=
    exists_pfilter_genericOver p (C.countable_visibleDenseOpen_derivedContext hM)
  exact ⟨G, hpG, hG, fun _ hx ↦ hcan.mem_extensionCarrier_of_mem_pfilter hx G,
    exists_realCode_mem_not_mem C hreal hG⟩

/-!
### Sanity examples

The generic-filter code's membership is adjacent to the contract via the existing extension
declarations; the avoidance composition that motivated the derived context reads with zero
glue; and the adequacy theorem consumes exactly `Sees`-derived totality plus the Cohen-real
representative — no canonical names anywhere in its proof.
-/

example (C : CohenMaterialPresentation M) (hcan : HasCanonicalNames C.forcing N)
    (G : PFilter Cond) :
    zval (G : Set Cond) (genName C.forcing.conditionCode) ∈
      N.extensionCarrier (G : Set Cond) :=
  hcan.zval_genName_mem_extensionCarrier_pfilter G

example (C : CohenMaterialPresentation M) {G : PFilter Cond}
    (hG : C.derivedContext.GenericOver G) {c : ℕ → Bool}
    (hc : ∀ n, genericFun G n = some (c n)) : realCode c ∉ M :=
  C.not_mem_designatedReals_iff.1
    (not_mem_designatedReals_of_genericOver C.sees_derivedContext hG hc)

end Forcing.Cohen
