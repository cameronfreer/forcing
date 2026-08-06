/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Name.FormulaTests
import Forcing.Name.AtomicAdequacy
import Forcing.Material.Semantics

/-!
# The semantic truth lemma over the material extension

The bounded-formula equivalence between realization in the extension carrier and forcing
along the filter:

```text
φ.Realize (extVal-valued assignments) ↔ ∃ p ∈ G, ForcesFormula N.names v p φ xs
```

with the sentence specialization (`truth_lemma_sentence`). The boundary is deliberate: the
theorem requires only an `InternalNamePresentation` (subname closure is its theorem,
`subnameClosed_names`), the test budgets, and the filter — **no** canonical names, internal
forcing presentation, top, countability, or ZFC assumptions.

The budgets are exactly three, and the two layers of the adequacy discipline persist to the
end: the observer-free theorem (`truth_lemma`) consumes the atomic `hmem`/`heq` budgets plus
`GenericFor (formulaTests N.names v φ xs) G`; the `GenericOver` corollary
(`truth_lemma_of_genericOver`) assumes only *visibility* of every test — their
dense-openness is already structural (`isDenseOpen_of_mem_formulaTests`,
`isDenseOpen_localizeBelow`, `isDenseOpen_eqDecision`). Genericity is only the bridge from
visible tests to meetings; countability appears nowhere.

The induction is structural on the formula: atomic cases are the atomic adequacy composed
with the carrier semantics (`realize_term_extVal`, `Subtype.ext_iff`); implication meets its
decision test, with the obstruction refuted through the subformula equivalences; the
universal quantifier crosses the carrier-quantifier bridge
(`forall_extensionCarrier_iff_names`) and meets its decision test the same way.

## Main results

* `Forcing.InternalNamePresentation.truth_lemma`: the bounded-formula equivalence,
  observer-free.
* `Forcing.InternalNamePresentation.truth_lemma_of_genericOver`: the visibility corollary.
* `Forcing.InternalNamePresentation.truth_lemma_sentence`: the sentence specialization.
-/

universe u v

namespace Forcing

open FirstOrder PName Order

namespace InternalNamePresentation

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]
variable {N : InternalNamePresentation M P} {β : Type v} {v : β → PName P} {G : PFilter P}

omit [Preorder P] in
private theorem snoc_mem_names {n} {xs : Fin n → PName P} (hxs : ∀ i, xs i ∈ N.names)
    {τ : PName P} (hτ : τ ∈ N.names) :
    ∀ i, Fin.snoc (α := fun _ ↦ PName P) xs τ i ∈ N.names := fun i ↦
  Fin.lastCases (by simpa using hτ) (fun j ↦ by simpa using hxs j) i

omit [Preorder P] in
private theorem snoc_extVal {n} {xs : Fin n → PName P} (hxs : ∀ i, xs i ∈ N.names)
    {τ : PName P} (hτ : τ ∈ N.names) {S : Set P} :
    (Fin.snoc (fun i ↦ N.extVal S (xs i) (hxs i)) (N.extVal S τ hτ) :
        Fin (n + 1) → N.extensionCarrier S) =
      fun i ↦ N.extVal S (Fin.snoc (α := fun _ ↦ PName P) xs τ i)
        (snoc_mem_names hxs hτ i) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> · apply Subtype.ext; simp

/-- **The semantic truth lemma**, observer-free: realization in the extension carrier is
equivalent to forcing along the filter, for formulas valued in the internal name family,
under the atomic budgets and the formula-test budget. -/
theorem truth_lemma (hv : ∀ b, v b ∈ N.names)
    (hmem : ∀ τ ∈ N.names, ∀ σ ∈ N.names, ∀ p ∈ G, ForcesMem p τ σ →
      Meets G (localizeBelow (memWitness τ σ) p))
    (heq : ∀ τ ∈ N.names, ∀ σ ∈ N.names, Meets G (eqDecision τ σ)) :
    ∀ {n} (φ : memLang.BoundedFormula β n) (xs : Fin n → PName P)
      (hxs : ∀ i, xs i ∈ N.names),
      GenericFor (formulaTests N.names v φ xs) G →
      (φ.Realize (fun b ↦ N.extVal (G : Set P) (v b) (hv b))
          (fun i ↦ N.extVal (G : Set P) (xs i) (hxs i)) ↔
        ∃ p ∈ G, ForcesFormula N.names v p φ xs)
  | _, .falsum, xs, hxs, _ =>
    ⟨fun h ↦ (h : False).elim, fun ⟨_, _, h⟩ ↦ (h : False).elim⟩
  | _, .equal t₁ t₂, xs, hxs, _ => by
    have ha : ∀ g, Sum.elim v xs g ∈ N.names := fun g ↦ by
      cases g with
      | inl b => exact hv b
      | inr i => exact hxs i
    have key := (forces_adequacy N.subnameClosed_names hmem heq
      (evalTerm (Sum.elim v xs) t₁) (evalTerm (Sum.elim v xs) t₂)
      (evalTerm_mem ha t₁) (evalTerm_mem ha t₂)).2
    rw [show Language.BoundedFormula.equal t₁ t₂ = Language.Term.bdEqual t₁ t₂ from rfl,
      Language.BoundedFormula.realize_bdEqual,
      show (Sum.elim (fun b ↦ N.extVal (G : Set P) (v b) (hv b))
          (fun i ↦ N.extVal (G : Set P) (xs i) (hxs i))) =
        fun g ↦ N.extVal (G : Set P) (Sum.elim v xs g) (ha g) from
        funext fun g ↦ by cases g <;> rfl,
      N.realize_term_extVal ha t₁, N.realize_term_extVal ha t₂]
    exact Subtype.ext_iff.trans key
  | _, .rel .mem ts, xs, hxs, _ => by
    have ha : ∀ g, Sum.elim v xs g ∈ N.names := fun g ↦ by
      cases g with
      | inl b => exact hv b
      | inr i => exact hxs i
    have key := (forces_adequacy N.subnameClosed_names hmem heq
      (evalTerm (Sum.elim v xs) (ts 0)) (evalTerm (Sum.elim v xs) (ts 1))
      (evalTerm_mem ha (ts 0)) (evalTerm_mem ha (ts 1))).1
    rw [show Language.BoundedFormula.rel memRel.mem ts =
        Language.Relations.boundedFormula (L := memLang) memRel.mem ts from rfl,
      Language.BoundedFormula.realize_rel,
      show (Sum.elim (fun b ↦ N.extVal (G : Set P) (v b) (hv b))
          (fun i ↦ N.extVal (G : Set P) (xs i) (hxs i))) =
        fun g ↦ N.extVal (G : Set P) (Sum.elim v xs g) (ha g) from
        funext fun g ↦ by cases g <;> rfl]
    simp only [N.realize_term_extVal ha]
    exact key
  | _, .imp φ ψ, xs, hxs, hT => by
    have hTφ : GenericFor (formulaTests N.names v φ xs) G := fun D hD ↦
      hT D (Set.mem_insert_iff.2 (Or.inr (Set.mem_union_left _ hD)))
    have hTψ : GenericFor (formulaTests N.names v ψ xs) G := fun D hD ↦
      hT D (Set.mem_insert_iff.2 (Or.inr (Set.mem_union_right _ hD)))
    have ihφ := truth_lemma hv hmem heq φ xs hxs hTφ
    have ihψ := truth_lemma hv hmem heq ψ xs hxs hTψ
    rw [Language.BoundedFormula.realize_imp]
    constructor
    · intro hRe
      obtain ⟨p, hpG, hp⟩ := hT _ (Set.mem_insert _ _)
      rcases hp with hp | ⟨hpφ, hblock⟩
      · exact ⟨p, hpG, hp⟩
      · exfalso
        obtain ⟨q, hqG, hqψ⟩ := ihψ.1 (hRe (ihφ.2 ⟨p, hpG, hpφ⟩))
        obtain ⟨r, hrG, hrp, hrq⟩ := exists_mem_le_le hpG hqG
        exact hblock r hrp (ForcesFormula.mono ψ hqψ hrq)
    · rintro ⟨p, hpG, hpF⟩ hReφ
      obtain ⟨q, hqG, hqφ⟩ := ihφ.1 hReφ
      obtain ⟨r, hrG, hrp, hrq⟩ := exists_mem_le_le hpG hqG
      exact ihψ.2 ⟨r, hrG, hpF r hrp (ForcesFormula.mono φ hqφ hrq)⟩
  | _, .all φ, xs, hxs, hT => by
    rw [Language.BoundedFormula.realize_all, N.forall_extensionCarrier_iff_names]
    constructor
    · intro hRe
      obtain ⟨p, hpG, hp⟩ := hT _ (Set.mem_insert _ _)
      rcases hp with hp | ⟨τ, hτ, hblock⟩
      · exact ⟨p, hpG, hp⟩
      · exfalso
        have ih := truth_lemma hv hmem heq φ (Fin.snoc xs τ) (snoc_mem_names hxs hτ)
          (fun D hD ↦ hT D (Set.mem_insert_iff.2 (Or.inr (Set.mem_biUnion hτ hD))))
        have hRτ := hRe τ hτ
        rw [snoc_extVal hxs hτ] at hRτ
        obtain ⟨q, hqG, hqF⟩ := ih.1 hRτ
        obtain ⟨r, hrG, hrp, hrq⟩ := exists_mem_le_le hpG hqG
        exact hblock r hrp (ForcesFormula.mono φ hqF hrq)
    · rintro ⟨p, hpG, hpF⟩ τ hτ
      have ih := truth_lemma hv hmem heq φ (Fin.snoc xs τ) (snoc_mem_names hxs hτ)
        (fun D hD ↦ hT D (Set.mem_insert_iff.2 (Or.inr (Set.mem_biUnion hτ hD))))
      rw [snoc_extVal hxs hτ]
      exact ih.2 ⟨p, hpG, hpF τ hτ⟩

/-- **The visibility corollary**: over a generic filter, all three budgets are discharged
from visibility — the atomic tests as before, and the formula tests using their structural
dense-openness. -/
theorem truth_lemma_of_genericOver {Mv : VisibilityContext P} (hG : GenericOver Mv G)
    (hv : ∀ b, v b ∈ N.names)
    (hvmem : ∀ τ ∈ N.names, ∀ σ ∈ N.names, ∀ p ∈ G, ForcesMem p τ σ →
      Mv.Visible (localizeBelow (memWitness τ σ) p))
    (hveq : ∀ τ ∈ N.names, ∀ σ ∈ N.names, Mv.Visible (eqDecision τ σ))
    {n} (φ : memLang.BoundedFormula β n) (xs : Fin n → PName P)
    (hxs : ∀ i, xs i ∈ N.names)
    (hvT : ∀ D ∈ formulaTests N.names v φ xs, Mv.Visible D) :
    φ.Realize (fun b ↦ N.extVal (G : Set P) (v b) (hv b))
        (fun i ↦ N.extVal (G : Set P) (xs i) (hxs i)) ↔
      ∃ p ∈ G, ForcesFormula N.names v p φ xs :=
  truth_lemma hv
    (fun τ hτ σ hσ p hpG hF ↦
      hG _ ⟨hvmem τ hτ σ hσ p hpG hF, isDenseOpen_localizeBelow hF⟩)
    (fun τ hτ σ hσ ↦ hG _ ⟨hveq τ hτ σ hσ, isDenseOpen_eqDecision τ σ⟩)
    φ xs hxs
    (fun D hD ↦ hG D ⟨hvT D hD, isDenseOpen_of_mem_formulaTests φ xs D hD⟩)

/-- The sentence specialization: `φ` holds in the extension exactly when some condition of
`G` forces it. -/
theorem truth_lemma_sentence
    (hmem : ∀ τ ∈ N.names, ∀ σ ∈ N.names, ∀ p ∈ G, ForcesMem p τ σ →
      Meets G (localizeBelow (memWitness τ σ) p))
    (heq : ∀ τ ∈ N.names, ∀ σ ∈ N.names, Meets G (eqDecision τ σ))
    (φ : memLang.Sentence)
    (hT : GenericFor (formulaTests N.names Empty.elim φ fun i ↦ i.elim0) G) :
    Language.BoundedFormula.Realize (M := N.extensionCarrier (G : Set P)) φ
        (fun b ↦ b.elim) (fun i ↦ i.elim0) ↔
      ∃ p ∈ G, p ⊩[N.names] φ := by
  have h := truth_lemma (N := N) (v := Empty.elim) (fun b ↦ b.elim) hmem heq φ
    (fun i ↦ i.elim0) (fun i ↦ i.elim0) hT
  refine Iff.trans (iff_of_eq ?_) h
  exact congrArg₂ (fun a b ↦ Language.BoundedFormula.Realize φ a b)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end InternalNamePresentation

end Forcing
