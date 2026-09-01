/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Compiler
import Forcing.Name.FormulaForcing

/-!
# The bridge to external forcing

What the structural correctness proof will quantify over. Nothing here is an induction; these are
the two computation laws and the one invariant that the induction's cases consume.

## Canonical, not relational

The valuation is **not** related to an assignment code by a pointwise representation predicate.
It is *constructed* from codes: a correctness statement takes `free : Fin k → N.Code` and
`bound : Fin sn → N.Code` and reads the external side off them as `N.decode ∘ free` and
`N.decode ∘ bound`. Two consequences, both deliberate:

* the external family is exactly `N.names`, so no transport equality against an arbitrary `𝒩`
  is carried through the induction;
* representation holds by construction, so the induction hypothesis needs no side condition
  saying the valuation is representable.

`combinedCodes` is the corresponding assignment on the compiled side: arity `k + sn`, free before
bound, matching the convention `srcIndex` and `srcPeel` already fix.

## The two computation laws

* `decode_combinedCodes_srcIndex` — evaluating a source term externally agrees with decoding the
  combined assignment at `srcIndex`. This is what the `.equal` and `.rel` cases consume, on top of
  the orientation guards.
* `combinedCodes_snoc` — extending the *bound* valuation is `Fin.snoc` on the combined assignment.
  This is what the `.all` case consumes, on top of the extension guard. Its statement typechecks
  only because `k + (sn + 1)` is definitionally `(k + sn) + 1`.

## The invariant

`CompilerParams.Realizes` records what the **fixed** block must denote: the two tags, the coded
condition set and coded order, and the recognizer's parameters. `Realizes.lift` is its
preservation law, the one fact every binder-crossing case needs.

The condition `p` and the assignment `a` are deliberately **not** in it, exactly as they are not
in `CompilerParams`: they vary down the recursion, so their equations belong at each use site,
not in an invariant carried through it.

## Main results

* `Forcing.combinedCodes`, `Forcing.combinedCodes_finSumFinEquiv`: the combined assignment.
* `Forcing.combinedCodes_snoc`, `Forcing.decode_combinedCodes_srcIndex`: the two computation laws.
* `Forcing.CompilerParams.Realizes`, `Forcing.CompilerParams.Realizes.lift`: the invariant.
* `Forcing.realize_forcesDef_equal_bridge`, `…_rel_bridge`, `…_imp_bridge`, `…_all_bridge`: the
  guards, in the shape the induction's cases call them.
* `Forcing.exists_typed_of_imp_guard`, `Forcing.imp_guard_of_typed`: the implication guard routes
  both ways.
-/

universe u v

namespace Forcing

open FirstOrder Language AtomicRecursion

/-! ### The combined assignment -/

section Combined

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P} {k sn : ℕ}

/-- The combined code assignment: free variables first, bound variables after, matching the
convention `srcIndex` fixes. This is `Sum.elim` transported along `finSumFinEquiv.symm`, which is
exactly `Fin.append`. -/
def combinedCodes (free : Fin k → N.Code) (bound : Fin sn → N.Code) : Fin (k + sn) → N.Code :=
  Fin.append free bound

/-- **The defining law.** Reading the combined assignment at `finSumFinEquiv i` is reading the
two pieces at `i`. -/
@[simp] theorem combinedCodes_finSumFinEquiv (free : Fin k → N.Code) (bound : Fin sn → N.Code)
    (i : Fin k ⊕ Fin sn) :
    combinedCodes free bound (finSumFinEquiv i) = Sum.elim free bound i := by
  cases i with
  | inl a => simp [combinedCodes, finSumFinEquiv_apply_left, Fin.append_left]
  | inr b => simp [combinedCodes, finSumFinEquiv_apply_right, Fin.append_right]

/-- **The extension law.** Extending the bound valuation is `Fin.snoc` on the combined
assignment — the new name last, hence outermost in `assignmentCode`, hence at peel zero.

This typechecks only because `k + (sn + 1)` is definitionally `(k + sn) + 1`. -/
theorem combinedCodes_snoc (free : Fin k → N.Code) (bound : Fin sn → N.Code) (i : N.Code) :
    combinedCodes free (Fin.snoc bound i) = Fin.snoc (combinedCodes free bound) i :=
  Fin.append_snoc free bound i

/-- **The evaluation law.** Decoding the combined assignment at a source term's index is
evaluating that term at the decoded valuation.

`memLang` is function-free, so this is a one-case computation; the point is that it is a
*computation* and not a hypothesis carried through the induction. -/
theorem decode_combinedCodes_srcIndex (free : Fin k → N.Code) (bound : Fin sn → N.Code)
    (t : memLang.Term (Fin k ⊕ Fin sn)) :
    N.decode (combinedCodes free bound (srcIndex t)) =
      evalTerm (Sum.elim (N.decode ∘ free) (N.decode ∘ bound)) t := by
  cases t with
  | var i =>
    rw [srcIndex, combinedCodes_finSumFinEquiv, evalTerm_var]
    cases i <;> rfl
  | func f _ => exact Empty.elim f

/-- Every decoded name is in the family — the `.all` case's side condition, discharged by
construction rather than assumed. -/
theorem decode_combinedCodes_mem_names (free : Fin k → N.Code) (bound : Fin sn → N.Code)
    (j : Fin (k + sn)) : N.decode (combinedCodes free bound j) ∈ N.names :=
  N.decode_mem_names _

end Combined

/-! ### The fixed-parameter invariant -/

namespace CompilerParams

variable {α : Type v} {m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P}

/-- What the compiler's **fixed** parameters must denote: the two tags at their numerals, the
coded condition set and coded order at supplied targets, and the recognizer's parameters at the
recognizer's own.

The condition `p` and the assignment `a` are absent by design — they vary down the recursion, so
their equations belong at each use site rather than in an invariant carried across it. -/
structure Realizes (R : InternalNameRecognition N) (condSet orderCode : ZFSet.{u})
    (Γ : CompilerParams α R.arity m) (v : α → M) (xs : Fin m → M) : Prop where
  /-- The membership-witness tag is its numeral. -/
  tagMem_eq : ((Term.realize (Sum.elim v xs) Γ.tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag
  /-- The forced-equality tag is its numeral. -/
  tagEq_eq : ((Term.realize (Sum.elim v xs) Γ.tagEq : ↥M) : ZFSet.{u}) = natCode eqTag
  /-- The coded condition set is the supplied one. -/
  condSet_eq : ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u}) = condSet
  /-- The coded order is the supplied one. -/
  orderCode_eq : ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u}) = orderCode
  /-- The recognizer sits at its own parameters. -/
  recParams_eq : ∀ i, Sum.elim v xs (Γ.recParams i) = R.params i

/-- **Preservation.** The invariant survives every binder the compiler introduces. This is the
single fact each binder-crossing case needs, and the reason the fixed block is bundled. -/
theorem Realizes.lift {R : InternalNameRecognition N} {condSet orderCode : ZFSet.{u}}
    {Γ : CompilerParams α R.arity m} {v : α → M} {xs : Fin m → M}
    (h : Realizes R condSet orderCode Γ v xs) (w : ↥M) :
    Realizes R condSet orderCode Γ.lift v (Fin.snoc xs w) where
  tagMem_eq := by simpa [CompilerParams.lift, realize_liftTerm] using h.tagMem_eq
  tagEq_eq := by simpa [CompilerParams.lift, realize_liftTerm] using h.tagEq_eq
  condSet_eq := by simpa [CompilerParams.lift, realize_liftTerm] using h.condSet_eq
  orderCode_eq := by simpa [CompilerParams.lift, realize_liftTerm] using h.orderCode_eq
  recParams_eq := by
    intro i
    rw [← h.recParams_eq i]
    cases hi : Γ.recParams i with
    | inl _ => simp [CompilerParams.lift, hi]
    | inr j =>
      simp only [CompilerParams.lift, hi, Sum.map_inr, Sum.elim_inr]
      simp

end CompilerParams

/-! ### The guards, in the shape the induction calls them

Each restates a `Compiler` guard with the invariant supplying the fixed-parameter equations and
`combinedCodes` supplying the assignment. These are the case hypotheses of the coming structural
induction; nothing here inducts. -/

section Cases

variable {α : Type v} {k sn m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P} {Rec : InternalNameRecognition N}
variable {condSet orderCode : ZFSet.{u}}
variable {Γ : CompilerParams α Rec.arity m} {p a : memLang.Term (α ⊕ Fin m)}
variable {v : α → M} {xs : Fin m → M}
variable {free : Fin k → N.Code} {bound : Fin sn → N.Code}

/-- **The equality case.** Both codes are pinned to the combined assignment at `srcIndex`, and the
coded condition set and order come from the invariant rather than from the terms. -/
theorem realize_forcesDef_equal_bridge {t₁ t₂ : memLang.Term (Fin k ⊕ Fin sn)}
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound))
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (forcesDef Rec.formula (.equal t₁ t₂) Γ p a).Realize v xs ↔
      ∃ x y : ↥M,
        ((x : ↥M) : ZFSet.{u}) = N.code (combinedCodes free bound (srcIndex t₁)) ∧
        ((y : ↥M) : ZFSet.{u}) = N.code (combinedCodes free bound (srcIndex t₂)) ∧
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn condSet orderCode ((A : ↥M) : ZFSet.{u})
              ((R : ↥M) : ZFSet.{u}) ∧
            entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
  rw [realize_forcesDef_equal_of_assignmentCode (combinedCodes free bound) ha
    hΓ.tagMem_eq hΓ.tagEq_eq, hΓ.condSet_eq, hΓ.orderCode_eq]

/-- **The membership case.** -/
theorem realize_forcesDef_rel_bridge {ts : Fin 2 → memLang.Term (Fin k ⊕ Fin sn)}
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound))
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (forcesDef Rec.formula (.rel .mem ts) Γ p a).Realize v xs ↔
      ∃ x y : ↥M,
        ((x : ↥M) : ZFSet.{u}) = N.code (combinedCodes free bound (srcIndex (ts 0))) ∧
        ((y : ↥M) : ZFSet.{u}) = N.code (combinedCodes free bound (srcIndex (ts 1))) ∧
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn condSet orderCode ((A : ↥M) : ZFSet.{u})
              ((R : ↥M) : ZFSet.{u}) ∧
            DenseMem condSet orderCode ((R : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) := by
  rw [realize_forcesDef_rel_of_assignmentCode (combinedCodes free bound) ha
    hΓ.tagMem_eq hΓ.tagEq_eq, hΓ.condSet_eq, hΓ.orderCode_eq]

/-- **The implication case.** Both conjuncts come from the invariant: condition-set membership
and the coded order. -/
theorem realize_forcesDef_imp_bridge {φ ψ : memLang.BoundedFormula (Fin k) sn}
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (forcesDef Rec.formula (φ.imp ψ) Γ p a).Realize v xs ↔
      ∀ q : ↥M, ((q : ↥M) : ZFSet.{u}) ∈ condSet →
        ZFSet.pair ((q : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u}) ∈ orderCode →
        ((forcesDef Rec.formula φ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v
            (Fin.snoc xs q) →
          (forcesDef Rec.formula ψ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v
            (Fin.snoc xs q)) := by
  rw [realize_forcesDef_imp, hΓ.condSet_eq, hΓ.orderCode_eq]

/-- **The universal case.** The admitted extension is exactly the code of the combined assignment
with the bound valuation extended — `combinedCodes_snoc` composed with the extension guard.

This is the shape the induction hypothesis applies to: same `free`, bound valuation extended by
one, so the recursive call's own `combinedCodes` is the assignment now in hand. -/
theorem realize_forcesDef_all_bridge {φ : memLang.BoundedFormula (Fin k) (sn + 1)}
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) =
      N.assignmentCode (combinedCodes free bound))
    (hΓ : Γ.Realizes Rec condSet orderCode v xs) :
    (forcesDef Rec.formula φ.all Γ p a).Realize v xs ↔
      ∀ (i : N.Code) (c a' : ↥M), ((c : ↥M) : ZFSet.{u}) = N.code i →
        ((a' : ↥M) : ZFSet.{u}) = N.assignmentCode (combinedCodes free (Fin.snoc bound i)) →
          (forcesDef Rec.formula φ Γ.lift.lift (liftTerm (liftTerm p))
            (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs c) a') := by
  rw [realize_forcesDef_all_of_assignmentCode_arity Rec (combinedCodes free bound) ha
    hΓ.recParams_eq]
  constructor
  · intro h i c a' hc ha'
    exact h i (combinedCodes free (Fin.snoc bound i)) (combinedCodes_snoc free bound i) c a' hc ha'
  · rintro h i asg' rfl c a' hc ha'
    exact h i c a' hc (by rwa [combinedCodes_snoc])

end Cases

/-! ### The implication guard routes both ways

The two facts the `.imp` case needs, one per direction of the correctness proof. Together they are
why the amended guard is exactly right: neither conjunct is redundant and neither direction needs
more. Note which is used where — decoding is what *proving* the compiled formula needs, encoding is
what *using* it needs.

`code_surjective` consumes condition-set membership, and `order_iff` speaks only of pairs of
already-typed codes — so the membership conjunct is what turns an internally quantified carrier
element into a `q : P` at all. Without it the compiled implication would range over junk elements
of `orderCode`'s first coordinate, and correctness would be false in any presentation carrying
such a pair. -/

section ImpRouting

variable {M : MaterialCarrier.{u}} {P : Type u} [Preorder P]

/-- **Used in external forcing → compiled realization.** The compiled goal hands us an arbitrary
internal `q` meeting both conjuncts; this decodes it to a genuine condition and a strengthening,
which is what lets the external hypothesis be applied to it. -/
theorem exists_typed_of_imp_guard (Pres : InternalForcingPresentation M P) {q : ZFSet.{u}} {p : P}
    (hmem : q ∈ (Pres.conditionSet : ZFSet.{u}))
    (horder : ZFSet.pair q (condCode Pres p) ∈ (Pres.orderCode : ZFSet.{u})) :
    ∃ q' : P, q = condCode Pres q' ∧ q' ≤ p := by
  obtain ⟨q', rfl⟩ := Pres.code_surjective q hmem
  exact ⟨q', rfl, (Pres.order_iff p q').1 horder⟩

/-- **Used in compiled realization → external forcing.** The external goal hands us a typed
strengthening; this encodes it to both conjuncts, which is what lets the compiled universal
hypothesis be instantiated at it. Costs nothing beyond the presentation's own fields. -/
theorem imp_guard_of_typed (Pres : InternalForcingPresentation M P) {q p : P} (h : q ≤ p) :
    condCode Pres q ∈ (Pres.conditionSet : ZFSet.{u}) ∧
      ZFSet.pair (condCode Pres q) (condCode Pres p) ∈ (Pres.orderCode : ZFSet.{u}) :=
  ⟨Pres.code_mem q, (Pres.order_iff p q).2 h⟩

end ImpRouting

end Forcing
