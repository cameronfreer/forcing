/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Syntax.MemLang
import Forcing.Coding.Nat

/-!
# Coding membership-language formulas as sets

Formulas of the fragment `memLang.BoundedFormula (Fin k) n` are coded as **tagged finite
trees carrying their arities**. Arbitrary free-variable types cannot be coded uniformly, and
the finitely indexed fragment suffices: parameters travel through the separately coded finite
assignment, not through the formula code.

Every node stores its constructor tag together with `k` and `n` (`node`), which is what makes
the code parseable: falsum at unrelated assignment contexts is *not* the same set, so an
internal parser can recover the context it is looking at. From node injectivity follow
constructor disjointness, exact decoding of the payloads, recovery of `k` and `n`, index
recovery for variables, and injectivity across the dependent indices
(`formulaCode_inj`).

**No substitution.** The forcing recursion extends assignments with `Fin.snoc`; it never
substitutes syntactically. Substitution infrastructure is consumer-gated and is deliberately
absent until a consumer demonstrates the need.

**Three costs, kept apart.** Defining the code below costs **no ground theory** at all — this
module is pure external set coding, independent of `P`, orders, filters, and forcing. Proving
that an individual code lies in a ground costs **finite closure only** (`formulaCode_mem`, in
the single section that mentions `MaterialGround`, priced at empty set, pairing, and union).
Collecting *all* formula codes into one member of the ground is a substantially stronger
demand and is **deliberately absent**.

The parser characterization (`IsFormulaCode`) is the boundary this layer owes item 3: an
inductive description of the well-formed codes, with soundness
(`isFormulaCode_formulaCode`) and no-junk completeness (`exists_formulaCode`), so the coded
forcing relation can recognize constructor cases without appealing to an external inverse
function. Item 3 begins where this file stops.

## Main definitions

* `Forcing.termCode`, `Forcing.formulaCode`: the codes.
* `Forcing.IsFormulaCode`: the parser characterization.

## Main results

* `Forcing.node_inj`: the node law, from which the constructor laws follow.
* `Forcing.formulaCode_inj`: injectivity across the dependent indices.
* `Forcing.exists_formulaCode`: no junk — every well-formed code is a code.
-/

namespace Forcing

open FirstOrder

/-! ### Nodes -/

/-- A coded node: its constructor tag, its arities, and its payload. -/
def node (tag k n : ℕ) (payload : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.pair (natCode tag) (ZFSet.pair (ZFSet.pair (natCode k) (natCode n)) payload)

/-- **The node law**: nodes are equal exactly when tag, arities, and payload all agree.
Constructor disjointness, arity recovery, and payload decoding are all corollaries. -/
@[simp] theorem node_inj {tag k n tag' k' n' : ℕ} {p p' : ZFSet.{0}} :
    node tag k n p = node tag' k' n' p' ↔ tag = tag' ∧ k = k' ∧ n = n' ∧ p = p' := by
  simp only [node, ZFSet.pair_inj, and_assoc]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨natCode.injective h1, natCode.injective h2,
      natCode.injective h3, h4⟩,
    fun ⟨h1, h2, h3, h4⟩ ↦ ⟨congrArg _ h1, congrArg _ h2, congrArg _ h3, h4⟩⟩

/-! ### Term codes -/

/-- The code of a term of the coded fragment. Terms are variables — free (tag `0`) or bound
(tag `1`) — since the language is function-free; the arities travel in the node. -/
def termCode {k n : ℕ} : memLang.Term (Fin k ⊕ Fin n) → ZFSet.{0}
  | .var (Sum.inl i) => node 0 k n (natCode i)
  | .var (Sum.inr j) => node 1 k n (natCode j)
  | .func f _ => f.elim

@[simp] theorem termCode_free {k n : ℕ} (i : Fin k) :
    termCode (n := n) (.var (Sum.inl i)) = node 0 k n (natCode i) :=
  rfl

@[simp] theorem termCode_bound {k n : ℕ} (j : Fin n) :
    termCode (k := k) (.var (Sum.inr j)) = node 1 k n (natCode j) :=
  rfl

/-- **Variable-index recovery**: term codes determine the variable, free or bound. -/
theorem termCode_inj {k n : ℕ} {s t : memLang.Term (Fin k ⊕ Fin n)}
    (h : termCode s = termCode t) : s = t := by
  match s, t with
  | .var (Sum.inl i), .var (Sum.inl i') =>
    simp only [termCode_free, node_inj] at h
    exact congrArg _ (congrArg _ (Fin.val_injective (natCode.injective h.2.2.2)))
  | .var (Sum.inr j), .var (Sum.inr j') =>
    simp only [termCode_bound, node_inj] at h
    exact congrArg _ (congrArg _ (Fin.val_injective (natCode.injective h.2.2.2)))
  | .var (Sum.inl _), .var (Sum.inr _) => simp at h
  | .var (Sum.inr _), .var (Sum.inl _) => simp at h
  | .func f _, _ => exact f.elim
  | _, .func f _ => exact f.elim

/-! ### Formula codes -/

/-- The code of a formula of the coded fragment: a tagged tree carrying its arities. -/
def formulaCode : ∀ {k n : ℕ}, memLang.BoundedFormula (Fin k) n → ZFSet.{0}
  | k, n, .falsum => node 2 k n ∅
  | k, n, .equal t₁ t₂ => node 3 k n (ZFSet.pair (termCode t₁) (termCode t₂))
  | k, n, .rel .mem ts => node 4 k n (ZFSet.pair (termCode (ts 0)) (termCode (ts 1)))
  | k, n, .imp φ ψ => node 5 k n (ZFSet.pair (formulaCode φ) (formulaCode ψ))
  | k, n, .all φ => node 6 k n (formulaCode φ)

@[simp] theorem formulaCode_falsum {k n : ℕ} :
    formulaCode (.falsum : memLang.BoundedFormula (Fin k) n) = node 2 k n ∅ := by
  rw [formulaCode]

@[simp] theorem formulaCode_equal {k n : ℕ} (t₁ t₂ : memLang.Term (Fin k ⊕ Fin n)) :
    formulaCode (.equal t₁ t₂) = node 3 k n (ZFSet.pair (termCode t₁) (termCode t₂)) := by
  rw [formulaCode]

@[simp] theorem formulaCode_rel {k n : ℕ} (ts : Fin 2 → memLang.Term (Fin k ⊕ Fin n)) :
    formulaCode (.rel memRel.mem ts) =
      node 4 k n (ZFSet.pair (termCode (ts 0)) (termCode (ts 1))) := by
  rw [formulaCode]

@[simp] theorem formulaCode_imp {k n : ℕ} (φ ψ : memLang.BoundedFormula (Fin k) n) :
    formulaCode (φ.imp ψ) = node 5 k n (ZFSet.pair (formulaCode φ) (formulaCode ψ)) := by
  rw [formulaCode]

@[simp] theorem formulaCode_all {k n : ℕ} (φ : memLang.BoundedFormula (Fin k) (n + 1)) :
    formulaCode φ.all = node 6 k n (formulaCode φ) := by
  rw [formulaCode]

/-- Every formula code is a node at its own arities — the shape arity recovery reads. -/
theorem exists_node {k n : ℕ} (φ : memLang.BoundedFormula (Fin k) n) :
    ∃ tag p, formulaCode φ = node tag k n p := by
  match φ with
  | .falsum => exact ⟨2, ∅, by simp⟩
  | .equal t₁ t₂ => exact ⟨3, ZFSet.pair (termCode t₁) (termCode t₂), by simp⟩
  | .rel .mem ts => exact ⟨4, ZFSet.pair (termCode (ts 0)) (termCode (ts 1)), by simp⟩
  | .imp φ ψ => exact ⟨5, ZFSet.pair (formulaCode φ) (formulaCode ψ), by simp⟩
  | .all φ => exact ⟨6, formulaCode φ, by simp⟩

/-- **Arity recovery**: a formula code determines `k` and `n`, with no induction — every
constructor stores them. -/
theorem arity_eq {k n k' n' : ℕ} {φ : memLang.BoundedFormula (Fin k) n}
    {ψ : memLang.BoundedFormula (Fin k') n'} (h : formulaCode φ = formulaCode ψ) :
    k = k' ∧ n = n' := by
  obtain ⟨t, p, hp⟩ := exists_node φ
  obtain ⟨t', p', hp'⟩ := exists_node ψ
  rw [hp, hp', node_inj] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-- Injectivity at fixed arities. -/
theorem formulaCode_inj_of_arity : ∀ {k n : ℕ} (φ ψ : memLang.BoundedFormula (Fin k) n),
    formulaCode φ = formulaCode ψ → φ = ψ
  | _, _, .falsum, .falsum, _ => rfl
  | _, _, .equal t₁ t₂, .equal s₁ s₂, h => by
    simp only [formulaCode_equal, node_inj, ZFSet.pair_inj] at h
    rw [termCode_inj h.2.2.2.1, termCode_inj h.2.2.2.2]
  | _, _, .rel .mem ts, .rel .mem ss, h => by
    simp only [formulaCode_rel, node_inj, ZFSet.pair_inj] at h
    have h0 := termCode_inj h.2.2.2.1
    have h1 := termCode_inj h.2.2.2.2
    have hts : ts = ss := by
      funext i
      match i with
      | 0 => exact h0
      | 1 => exact h1
    rw [hts]
  | _, _, .imp φ ψ, .imp φ' ψ', h => by
    simp only [formulaCode_imp, node_inj, ZFSet.pair_inj] at h
    rw [formulaCode_inj_of_arity φ φ' h.2.2.2.1, formulaCode_inj_of_arity ψ ψ' h.2.2.2.2]
  | _, _, .all φ, .all φ', h => by
    simp only [formulaCode_all, node_inj] at h
    rw [formulaCode_inj_of_arity φ φ' h.2.2.2]
  | _, _, .falsum, .equal _ _, h => by simp at h
  | _, _, .falsum, .rel .mem _, h => by simp at h
  | _, _, .falsum, .imp _ _, h => by simp at h
  | _, _, .falsum, .all _, h => by simp at h
  | _, _, .equal _ _, .falsum, h => by simp at h
  | _, _, .equal _ _, .rel .mem _, h => by simp at h
  | _, _, .equal _ _, .imp _ _, h => by simp at h
  | _, _, .equal _ _, .all _, h => by simp at h
  | _, _, .rel .mem _, .falsum, h => by simp at h
  | _, _, .rel .mem _, .equal _ _, h => by simp at h
  | _, _, .rel .mem _, .imp _ _, h => by simp at h
  | _, _, .rel .mem _, .all _, h => by simp at h
  | _, _, .imp _ _, .falsum, h => by simp at h
  | _, _, .imp _ _, .equal _ _, h => by simp at h
  | _, _, .imp _ _, .rel .mem _, h => by simp at h
  | _, _, .imp _ _, .all _, h => by simp at h
  | _, _, .all _, .falsum, h => by simp at h
  | _, _, .all _, .equal _ _, h => by simp at h
  | _, _, .all _, .rel .mem _, h => by simp at h
  | _, _, .all _, .imp _ _, h => by simp at h

/-- **Injectivity across the dependent indices**: equal codes have equal arities, and the
formulas agree once transported. -/
theorem formulaCode_inj {k n k' n' : ℕ} {φ : memLang.BoundedFormula (Fin k) n}
    {ψ : memLang.BoundedFormula (Fin k') n'} (h : formulaCode φ = formulaCode ψ) :
    k = k' ∧ n = n' ∧ HEq φ ψ := by
  obtain ⟨rfl, rfl⟩ := arity_eq h
  exact ⟨rfl, rfl, heq_of_eq (formulaCode_inj_of_arity φ ψ h)⟩

/-! ### The parser characterization -/

/-- **Well-formed formula codes**, described inductively in the *code* rather than through an
external inverse: the boundary this layer owes the coded forcing relation. -/
inductive IsFormulaCode : ℕ → ℕ → ZFSet.{0} → Prop
  | falsum (k n : ℕ) : IsFormulaCode k n (node 2 k n ∅)
  | equal {k n : ℕ} (t₁ t₂ : memLang.Term (Fin k ⊕ Fin n)) :
      IsFormulaCode k n (node 3 k n (ZFSet.pair (termCode t₁) (termCode t₂)))
  | rel {k n : ℕ} (t₁ t₂ : memLang.Term (Fin k ⊕ Fin n)) :
      IsFormulaCode k n (node 4 k n (ZFSet.pair (termCode t₁) (termCode t₂)))
  | imp {k n : ℕ} {x y : ZFSet.{0}} : IsFormulaCode k n x → IsFormulaCode k n y →
      IsFormulaCode k n (node 5 k n (ZFSet.pair x y))
  | all {k n : ℕ} {x : ZFSet.{0}} : IsFormulaCode k (n + 1) x →
      IsFormulaCode k n (node 6 k n x)

/-- **Soundness of the parser**: every code is well-formed. -/
theorem isFormulaCode_formulaCode : ∀ {k n : ℕ} (φ : memLang.BoundedFormula (Fin k) n),
    IsFormulaCode k n (formulaCode φ) := by
  intro k n φ
  induction φ with
  | falsum => simpa using IsFormulaCode.falsum _ _
  | equal t₁ t₂ => simpa using IsFormulaCode.equal t₁ t₂
  | rel R ts => cases R; simpa using IsFormulaCode.rel (ts 0) (ts 1)
  | imp _ _ ihφ ihψ => simpa using IsFormulaCode.imp ihφ ihψ
  | all _ ih => simpa using IsFormulaCode.all ih

/-- **No junk**: every well-formed code is the code of a formula. Together with soundness,
this is the characterization item 3 recognizes constructor cases against. -/
theorem exists_formulaCode {k n : ℕ} {x : ZFSet.{0}} (h : IsFormulaCode k n x) :
    ∃ φ : memLang.BoundedFormula (Fin k) n, formulaCode φ = x := by
  induction h with
  | falsum _ => exact ⟨.falsum, by simp⟩
  | equal t₁ t₂ => exact ⟨.equal t₁ t₂, by simp⟩
  | rel t₁ t₂ => exact ⟨.rel memRel.mem ![t₁, t₂], by simp⟩
  | imp _ _ ihx ihy =>
    obtain ⟨φ, rfl⟩ := ihx
    obtain ⟨ψ, rfl⟩ := ihy
    exact ⟨φ.imp ψ, by simp⟩
  | all _ ih =>
    obtain ⟨φ, rfl⟩ := ih
    exact ⟨φ.all, by simp⟩

end Forcing
