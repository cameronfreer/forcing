/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Semantics
import Forcing.Material.UnionIteration

/-!
# Union iteration: the approximation formulas

The syntax layer for `Forcing/Material/UnionIteration.lean`, one formula and one realization
law per semantic component. Everything is built on the shared vocabulary — `pairDef`,
`pairMemDef`, `emptyDef`, `successorDef`, `sUnionDef` — so no notion of successor or of
general union is introduced here.

**Every realization law below is hypothesis-free and axiom-free.** Each quantifier bridge is
carrier transitivity: a value reaches the carrier through the pair entry that mentions it, and
the components of a coded pair reach it by descending the Kuratowski coding.

## The successor is quantified, not constructed

`approxStepDef` universally quantifies a candidate successor `s` and *assumes*
`successorDef k s`. It does **not** existentially build one. The difference is what keeps this
component's law standalone: an existential form would have to produce `insert k k` inside the
carrier, which is a closure fact belonging to another component, and the law would stop being
axiom-free.

The universal form costs nothing, because the forward direction instantiates `s` only when an
actual successor entry `⟨insert k k, U⟩ ∈ t` is in hand — and *that* entry supplies
`insert k k` as a carrier element by transitivity through `t`.

The base formula, by contrast, may bind its empty representative existentially: the base pair's
membership in `t` supplies `∅` structurally, for the same reason.

## Deliberately absent

No `ω`, no `MaterialGround`, no scheme instance, and no Infinity, exactly as in the semantic
layer. `IsApprox` is assembled only after all four component laws compile.
-/

universe u v

namespace Forcing

open FirstOrder Language UnionIteration

/-- The bounded-domain condition, as a formula. -/
def inApproxDomainDef {α : Type v} {m : ℕ} (n k : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  memFormula k n ⊔ (k =' n)

/-- **Bounded no-junk support**, as a formula. -/
def approxSupportDef {α : Type v} {m : ℕ} (n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (memFormula (&(Fin.last m)) (liftTerm t) ⟹
    ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last (m + 1)))) (&(Fin.last (m + 2)))
        (&(Fin.castSucc (Fin.castSucc (Fin.last m)))) ⊓
      inApproxDomainDef (liftTerm (liftTerm (liftTerm n)))
        (&(Fin.castSucc (Fin.last (m + 1))))))

/-- **Totality and functionality**, as a formula. -/
def approxTotalFunctionalDef {α : Type v} {m : ℕ} (n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (inApproxDomainDef (liftTerm n) (&(Fin.last m)) ⟹
    ∃' (pairMemDef (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1)))
        (liftTerm (liftTerm t)) ⊓
      ∀' (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last m)))) (&(Fin.last (m + 2)))
          (liftTerm (liftTerm (liftTerm t))) ⟹
        (&(Fin.last (m + 2)) =' &(Fin.castSucc (Fin.last (m + 1)))))))

/-- **The base value**, as a formula. The empty representative is bound existentially; the
base pair's membership in `t` supplies it structurally. -/
def approxBaseDef {α : Type v} {m : ℕ} (seed t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∃' (emptyDef (&(Fin.last m)) ⊓
    pairMemDef (&(Fin.last m)) (liftTerm seed) (liftTerm t))

/-- **The recurrence**, as a formula. The candidate successor `s` is **universally quantified
under `successorDef k s`**, never constructed — see the module docstring. -/
def approxStepDef {α : Type v} {m : ℕ} (n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (memFormula (&(Fin.last m)) (liftTerm n) ⟹
    ∀' (successorDef (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1))) ⟹
      ∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last m)))))
            (&(Fin.castSucc (Fin.last (m + 2)))) (liftTerm (liftTerm (liftTerm (liftTerm t)))) ⟹
        (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last (m + 1)))))
            (&(Fin.last (m + 3))) (liftTerm (liftTerm (liftTerm (liftTerm t)))) ⟹
          sUnionDef (&(Fin.castSucc (Fin.last (m + 2)))) (&(Fin.last (m + 3)))))))

/-- **An approximation**, as a formula: the conjunction of the four components. -/
def isApproxDef {α : Type v} {m : ℕ} (seed n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  approxSupportDef n t ⊓ (approxTotalFunctionalDef n t ⊓
    (approxBaseDef seed t ⊓ approxStepDef n t))

section Realization

variable {α : Type v} {m : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin m → M}

/-- **The bounded-domain law.** -/
theorem realize_inApproxDomainDef {n k : memLang.Term (α ⊕ Fin m)} :
    (inApproxDomainDef n k).Realize v xs ↔
      InApproxDomain ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) k : ↥M) : ZFSet.{u}) := by
  simp only [inApproxDomainDef, BoundedFormula.realize_sup,
    BoundedFormula.realize_bdEqual, memFormula, BoundedFormula.realize_rel₂, relMap_mem,
    Matrix.cons_val_zero, Matrix.cons_val_one, InApproxDomain, Subtype.ext_iff]

/-- **The support law.** Backward direction axiom-free: an entry of `t` is a member of a
member, and the components of the coded pair descend from it. -/
theorem realize_approxSupportDef {n t : memLang.Term (α ⊕ Fin m)} :
    (approxSupportDef n t).Realize v xs ↔
      ApproxSupport ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) := by
  have htM : ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) t : ↥M).2
  simp only [approxSupportDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairDef, realize_inApproxDomainDef,
    ApproxSupport]
  constructor
  · intro h e he
    obtain ⟨k, S, hpair, hdom⟩ := h ⟨e, M.mem_trans he htM⟩ he
    exact ⟨(k : ZFSet.{u}), (S : ZFSet.{u}), hpair, hdom⟩
  · intro h e he
    obtain ⟨k, S, hpair, hdom⟩ := h (e : ZFSet.{u}) he
    have hpM : ZFSet.pair k S ∈ M := hpair ▸ M.mem_trans he htM
    refine ⟨⟨k, ?_⟩, ⟨S, ?_⟩, hpair, hdom⟩
    · exact M.mem_trans (ZFSet.mem_pair.2 (Or.inl rfl))
        (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
    · exact M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
        (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)

/-- **The totality-and-functionality law.** The value returns to the carrier through its pair
entry, so nothing is charged. -/
theorem realize_approxTotalFunctionalDef {n t : memLang.Term (α ⊕ Fin m)} :
    (approxTotalFunctionalDef n t).Realize v xs ↔
      ApproxTotalFunctional ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) := by
  have htM : ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) t : ↥M).2
  have hnM : ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) n : ↥M).2
  -- The value of a pair entry is a carrier element.
  have hval : ∀ a b : ZFSet.{u}, ZFSet.pair a b ∈
      ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) → b ∈ M := by
    intro a b hab
    have hpM : ZFSet.pair a b ∈ M := M.mem_trans hab htM
    exact M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
      (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
  simp only [approxTotalFunctionalDef, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    BoundedFormula.realize_ex, BoundedFormula.realize_inf, BoundedFormula.realize_bdEqual,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    realize_liftTerm, realize_pairMemDef, realize_inApproxDomainDef,
    ApproxTotalFunctional, Subtype.ext_iff]
  constructor
  · intro h k hdom
    -- `k` is a carrier element: it is a member of `n`, or is `n`.
    have hkM : k ∈ M := by
      rcases hdom with h1 | rfl
      · exact M.mem_trans h1 hnM
      · exact hnM
    obtain ⟨S, hSt, hfun⟩ := h ⟨k, hkM⟩ hdom
    exact ⟨(S : ZFSet.{u}), hSt, fun U hU ↦ hfun ⟨U, hval k U hU⟩ hU⟩
  · intro h k hdom
    obtain ⟨S, hSt, hfun⟩ := h (k : ZFSet.{u}) hdom
    exact ⟨⟨S, hval (k : ZFSet.{u}) S hSt⟩, hSt, fun U hU ↦ hfun (U : ZFSet.{u}) hU⟩

/-- **The base law.** The empty representative is supplied by the base pair's membership in
`t`, structurally. -/
theorem realize_approxBaseDef {seed t : memLang.Term (α ⊕ Fin m)} :
    (approxBaseDef seed t).Realize v xs ↔
      ApproxBase ((Term.realize (Sum.elim v xs) seed : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) := by
  have htM : ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) t : ↥M).2
  simp only [approxBaseDef, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, realize_liftTerm,
    realize_emptyDef, realize_pairMemDef, ApproxBase]
  constructor
  · rintro ⟨e, he, hmem⟩
    rwa [he] at hmem
  · intro h
    have hpM : ZFSet.pair (∅ : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) seed : ↥M) : ZFSet.{u}) ∈ M := M.mem_trans h htM
    have h0M : (∅ : ZFSet.{u}) ∈ M :=
      M.mem_trans (ZFSet.mem_pair.2 (Or.inl rfl))
        (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)
    exact ⟨⟨∅, h0M⟩, rfl, h⟩

/-- **The recurrence law.** The forward direction instantiates the universally quantified
successor only when an actual successor entry is in hand, and *that* entry supplies
`insert k k` as a carrier element by transitivity through `t`. Nothing is charged. -/
theorem realize_approxStepDef {n t : memLang.Term (α ⊕ Fin m)} :
    (approxStepDef n t).Realize v xs ↔
      ApproxStep ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) := by
  have htM : ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) t : ↥M).2
  have hnM : ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) n : ↥M).2
  have hidx : ∀ a b : ZFSet.{u}, ZFSet.pair a b ∈
      ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) → a ∈ M ∧ b ∈ M := by
    intro a b hab
    have hpM : ZFSet.pair a b ∈ M := M.mem_trans hab htM
    exact ⟨M.mem_trans (ZFSet.mem_pair.2 (Or.inl rfl))
        (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM),
      M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl))
        (M.mem_trans (ZFSet.mem_pair.2 (Or.inr rfl)) hpM)⟩
  simp only [approxStepDef, BoundedFormula.realize_all, BoundedFormula.realize_imp, memFormula,
    BoundedFormula.realize_rel₂, relMap_mem, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc, Matrix.cons_val_zero,
    Matrix.cons_val_one, realize_liftTerm, realize_pairMemDef, realize_successorDef,
    realize_sUnionDef, ApproxStep]
  constructor
  · intro h k hk S U hSt hUt
    have hkM := M.mem_trans hk hnM
    -- The successor entry supplies `insert k k` as a carrier element.
    have hsM := (hidx _ _ hUt).1
    exact h ⟨k, hkM⟩ hk ⟨insert k k, hsM⟩ rfl ⟨S, (hidx _ _ hSt).2⟩
      ⟨U, (hidx _ _ hUt).2⟩ hSt hUt
  · intro h k hk s hs S U hSt hUt
    rw [hs] at hUt
    exact h (k : ZFSet.{u}) hk (S : ZFSet.{u}) (U : ZFSet.{u}) hSt hUt

/-- **The approximation law.** Its hypotheses are the union of the four components' — which is
to say, none. Every component is hypothesis-free and axiom-free, so the conjunction is too,
and the conjuncts may be proved in any order. -/
theorem realize_isApproxDef {seed n t : memLang.Term (α ⊕ Fin m)} :
    (isApproxDef seed n t).Realize v xs ↔
      IsApprox ((Term.realize (Sum.elim v xs) seed : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) n : ↥M) : ZFSet.{u})
        ((Term.realize (Sum.elim v xs) t : ↥M) : ZFSet.{u}) := by
  rw [isApproxDef, IsApprox]
  simp only [BoundedFormula.realize_inf]
  exact and_congr realize_approxSupportDef
    (and_congr realize_approxTotalFunctionalDef
      (and_congr realize_approxBaseDef realize_approxStepDef))

end Realization

end Forcing
