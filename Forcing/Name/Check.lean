/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.PFilter
import Forcing.Name.Valuation

/-!
# Check names

The check name `x̌` embeds the ambient universe into names: every branch is tagged with the
distinguished element `⊤`, and valuation undoes the embedding. The `Set P` valuation API
exposes the exact prices:

* constructing a check name needs only a distinguished element (`[Top P]` — no order);
* evaluating it correctly needs only `⊤ ∈ S` (`val_check_equiv`, `zval_check`);
* `[Preorder P] [OrderTop P]` plus the filter laws supply that membership automatically
  (`Order.PFilter.top_mem`), so the forcing-filter statement is a corollary
  (`zval_check_pfilter`).

The intensional law is a `PSet.Equiv`, the extensional law an honest `ZFSet` equality.
On-the-nose `PSet` equality of `(check x).val S` with `x` is not expected in general — the
index type of the valuation is a subtype over a trivially-true condition.

## Main definitions

* `Forcing.PName.check`: the check name of a `PSet`.
* `Forcing.PName.checkZF`: the check name of a `ZFSet`, via `Quotient.out`.

## Main results

* `Forcing.PName.val_check_equiv`, `Forcing.PName.zval_check`: valuation undoes check, under
  exactly `⊤ ∈ S`.
* `Forcing.PName.zval_check_pfilter`, `Forcing.PName.zval_checkZF_pfilter`: the filter
  corollaries.
-/

universe u

namespace Forcing.PName

variable {P : Type u}

/-- The check name `x̌`: every branch tagged with the distinguished element. Needs only
`[Top P]` — no order. -/
def check [Top P] : PSet.{u} → PName P
  | .mk α A => .mk α (fun a ↦ check (A a)) fun _ ↦ (⊤ : P)

@[simp] theorem check_mk [Top P] (α : Type u) (A : α → PSet.{u}) :
    (check (.mk α A) : PName P) = mk α (fun a ↦ check (A a)) fun _ ↦ (⊤ : P) :=
  rfl

/-- **Valuation undoes check**, intensionally: along any condition set containing `⊤`, the
check name of `x` values to a `PSet` extensionally equal to `x`. -/
theorem val_check_equiv [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) (x : PSet.{u}) :
    PSet.Equiv ((check x : PName P).val S) x := by
  induction x with
  | mk α A IH =>
    exact ⟨fun i ↦ ⟨i.1, IH i.1⟩, fun a ↦ ⟨⟨a, hS⟩, IH a⟩⟩

/-- **Valuation undoes check**, extensionally: the honest equality, at `ZFSet`. -/
theorem zval_check [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) (x : PSet.{u}) :
    zval S (check x) = ZFSet.mk x :=
  ZFSet.sound (val_check_equiv hS x)

/-- The forcing-filter corollary: the order and the filter laws supply `⊤ ∈ G` automatically
(`Order.PFilter.top_mem`). -/
theorem zval_check_pfilter [Preorder P] [OrderTop P] (G : Order.PFilter P) (x : PSet.{u}) :
    zval (G : Set P) (check x) = ZFSet.mk x :=
  zval_check G.top_mem x

/-- Check from the quotient side, via `Quotient.out`. -/
noncomputable def checkZF [Top P] (x : ZFSet.{u}) : PName P :=
  check x.out

/-- Valuation undoes `checkZF`, under exactly `⊤ ∈ S`. -/
theorem zval_checkZF [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) (x : ZFSet.{u}) :
    zval S (checkZF x) = x := by
  rw [checkZF, zval_check hS, ZFSet.mk_out]

/-- The forcing-filter corollary for `checkZF`. -/
theorem zval_checkZF_pfilter [Preorder P] [OrderTop P] (G : Order.PFilter P) (x : ZFSet.{u}) :
    zval (G : Set P) (checkZF x) = x :=
  zval_checkZF G.top_mem x

end Forcing.PName
