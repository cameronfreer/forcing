/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.ModelTheory.Semantics
import Forcing.Name.MemLang
import Forcing.Material.Extension

/-!
# Membership semantics on material carriers

The audited carrier semantics of ADR 0003, exposed cleanly: the membership-language structure
on a material carrier (a **scoped** instance — available to everything that opens `Forcing`,
never leaking as a global default), the name-to-extension-value helper (`extVal`), and the
carrier-quantifier bridge (`forall_extensionCarrier_iff_names`) — quantification over the
extension carrier *is* quantification over the internal names, through
`mem_extensionCarrier_iff`.

This module is the `Semantics`-side counterpart of the Syntax-only `MemLang`: per the ADR's
normative import boundary, `Mathlib.ModelTheory.Semantics` enters here and nowhere below the
truth layer.

## Main definitions

* the scoped `memLang.Structure` instance on material carriers;
* `Forcing.InternalNamePresentation.extVal`: a name's value as a carrier element.

## Main results

* `Forcing.InternalNamePresentation.realize_term_extVal`: term realization is `extVal` of
  `evalTerm`.
* `Forcing.InternalNamePresentation.forall_extensionCarrier_iff_names`: the
  carrier-quantifier bridge.
-/

universe u v

namespace Forcing

open FirstOrder PName

/-- Membership semantics on a material carrier: the single relation is `ZFSet` membership of
the underlying elements. Scoped, so it never becomes a global default. -/
scoped instance (M : MaterialCarrier.{u}) : memLang.Structure M where
  funMap f _ := f.elim
  RelMap := fun r x ↦ match r with | .mem => (x 0 : ZFSet) ∈ (x 1 : ZFSet)

/-- The membership relation is interpreted as `ZFSet` membership of the underlying
elements. -/
@[simp] theorem relMap_mem {M : MaterialCarrier.{u}} {x : Fin 2 → M} :
    Language.Structure.RelMap (L := memLang) memRel.mem x ↔ (x 0 : ZFSet.{u}) ∈ (x 1 : ZFSet.{u}) :=
  Iff.rfl

/-! ### Realization of the pair formulas

The pair builders of the language layer, realized in a material carrier. **No theory axiom is
consumed**: every intermediate set the backward directions need is already a member of a
member of the carrier, so **transitivity** supplies it. Pairing becomes a construction cost
only when an existence proof must build genuinely new sets. -/

section PairRealization

variable {M : MaterialCarrier.{u}} {α : Type v} {n : ℕ} {x y z : memLang.Term (α ⊕ Fin n)}
variable {v : α → M} {xs : Fin n → M}

theorem realize_liftTerm (t : memLang.Term (α ⊕ Fin n)) (w : M) :
    Language.Term.realize (Sum.elim v (Fin.snoc xs w)) (liftTerm t) =
      Language.Term.realize (Sum.elim v xs) t := by
  rw [liftTerm, Language.Term.realize_relabel]
  congr 1
  funext i
  cases i with
  | inl a => rfl
  | inr i => simp

/-- **The unordered-pair law**: the formula holds exactly when the third term names the
unordered pair of the first two. -/
theorem realize_unorderedPairDef :
    (unorderedPairDef x y z).Realize v xs ↔
      ((Language.Term.realize (Sum.elim v xs) z : ↥M) : ZFSet.{u}) =
        {((Language.Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}),
          ((Language.Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})} := by
  simp only [unorderedPairDef, Language.BoundedFormula.realize_all,
    Language.BoundedFormula.realize_iff, Language.BoundedFormula.realize_sup,
    Language.BoundedFormula.realize_bdEqual, memFormula,
    Language.BoundedFormula.realize_rel₂, relMap_mem, Language.Term.realize_var,
    Sum.elim_inr, Fin.snoc_last, realize_liftTerm, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h
    refine ZFSet.ext fun w ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · have hwM : w ∈ M :=
        M.mem_trans hw (Language.Term.realize (Sum.elim v xs) z).2
      rcases (h ⟨w, hwM⟩).1 hw with h1 | h1
      · exact ZFSet.mem_pair.2 (Or.inl (congrArg Subtype.val h1))
      · exact ZFSet.mem_pair.2 (Or.inr (congrArg Subtype.val h1))
    · rcases ZFSet.mem_pair.1 hw with rfl | rfl
      · exact (h _).2 (Or.inl rfl)
      · exact (h _).2 (Or.inr rfl)
  · intro h w
    rw [h]
    constructor
    · intro hw
      rcases ZFSet.mem_pair.1 hw with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    · rintro (rfl | rfl)
      · exact ZFSet.mem_pair.2 (Or.inl rfl)
      · exact ZFSet.mem_pair.2 (Or.inr rfl)

/-- **The Kuratowski-pair law**: the formula holds exactly when the third term names the
ordered pair of the first two. The backward direction needs the two intermediate sets in the
carrier, and **transitivity supplies them** — they are members of a member. -/
theorem realize_pairDef :
    (pairDef x y z).Realize v xs ↔
      ((Language.Term.realize (Sum.elim v xs) z : ↥M) : ZFSet.{u}) =
        ZFSet.pair ((Language.Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})
          ((Language.Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u}) := by
  have hself : ∀ a : ZFSet.{u}, ({a, a} : ZFSet.{u}) = {a} :=
    fun a ↦ ZFSet.ext fun w ↦ by simp
  simp only [pairDef, Language.BoundedFormula.realize_ex,
    Language.BoundedFormula.realize_inf, realize_unorderedPairDef, realize_liftTerm,
    Language.Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc]
  constructor
  · rintro ⟨u, w, hu, hw, hz⟩
    rw [hz, hu, hw, hself]
    rfl
  · intro hz
    have hzM : ((Language.Term.realize (Sum.elim v xs) z : ↥M) : ZFSet.{u}) ∈ M :=
      (Language.Term.realize (Sum.elim v xs) z : ↥M).2
    have h1 : ({((Language.Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u})} : ZFSet.{u}) ∈
        ((Language.Term.realize (Sum.elim v xs) z : ↥M) : ZFSet.{u}) := by
      rw [hz, ZFSet.pair]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    have h2 : ({((Language.Term.realize (Sum.elim v xs) x : ↥M) : ZFSet.{u}),
          ((Language.Term.realize (Sum.elim v xs) y : ↥M) : ZFSet.{u})} : ZFSet.{u}) ∈
        ((Language.Term.realize (Sum.elim v xs) z : ↥M) : ZFSet.{u}) := by
      rw [hz, ZFSet.pair]
      exact ZFSet.mem_pair.2 (Or.inr rfl)
    refine ⟨⟨_, M.mem_trans h1 hzM⟩, ⟨_, M.mem_trans h2 hzM⟩, ?_, rfl, ?_⟩
    · exact (hself _).symm
    · exact hz

end PairRealization

namespace InternalNamePresentation

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P}
variable {S : Set P}

/-- A name of the family, as an element of the extension carrier. -/
def extVal (N : InternalNamePresentation M P) (S : Set P) (τ : PName P) (hτ : τ ∈ N.names) :
    N.extensionCarrier S :=
  ⟨zval S τ, N.mem_extensionCarrier_of_mem_of_zval_eq hτ rfl⟩

@[simp] theorem coe_extVal {τ : PName P} (hτ : τ ∈ N.names) :
    (N.extVal S τ hτ : ZFSet.{u}) = zval S τ :=
  rfl

/-- Realization of a function-free term along `extVal`-valued assignments is `extVal` of the
syntactic evaluation. -/
theorem realize_term_extVal {γ : Type v} {a : γ → PName P} (ha : ∀ g, a g ∈ N.names) :
    ∀ t : memLang.Term γ,
      (Language.Term.realize (M := N.extensionCarrier S)
        (fun g ↦ N.extVal S (a g) (ha g)) t) = N.extVal S (evalTerm a t) (evalTerm_mem ha t)
  | .var _ => rfl
  | .func f _ => f.elim

/-- **The carrier-quantifier bridge**: quantification over the extension carrier is
quantification over the internal names — every carrier element is the value of a decoded
name, and every name's value lands in the carrier. -/
theorem forall_extensionCarrier_iff_names (Φ : N.extensionCarrier S → Prop) :
    (∀ x, Φ x) ↔ ∀ τ, ∀ hτ : τ ∈ N.names, Φ (N.extVal S τ hτ) := by
  constructor
  · exact fun h τ hτ ↦ h _
  · rintro h ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := N.mem_extensionCarrier_iff.1 hx
    exact h (N.decode i) (N.decode_mem_names i)

end InternalNamePresentation

end Forcing
