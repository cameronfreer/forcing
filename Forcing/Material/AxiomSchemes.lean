/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Axioms

/-!
# Axiom schemes: Separation, Collection, and Foundation

The scheme layer of the ledger. Separation and Collection are genuinely **formula-indexed
schemes**; Foundation is a **single sentence**, not presented as a scheme. Infinity is
deliberately absent — it waits for the uniform transitive-closure theorem — and Replacement
and Power Set are absent until an actual consumer appears (ADR 0005).

**Finite parameter contexts throughout.** Every scheme instance is indexed by a formula with
`k` free variables, universally closed in the sentence. Parameter-free schemes would not
support the forcing presentation, name codes, the transitive-set parameter, or the recursion
functional, so parameters are present from the start.

**Semantic forms are primary.** The public API is the consequence theorems
(`exists_separation`, `exists_collection`, `exists_minimal`), each requiring only the
*individual* membership hypothesis `separationSentence φ ∈ T` and obtaining its witness
through `MaterialGround.realize_of_mem`. The named theory families
(`separationScheme`, `collectionScheme`) exist only so that statements like
`separationScheme ⊆ T` can *supply* those individual memberships; a whole-scheme inclusion is
never a field, a typeclass, or a bundled "supports separation" capability.

`Collection` is stated honestly: it does **not** assume functionality, and it does **not**
add a reverse "every member of `b` is used" clause — either would silently turn it into
Replacement or Strong Collection.

Nothing here smuggles in nonemptiness: the empty carrier satisfies all of these vacuously,
and `memLang.nonemptyTheory` remains the separate price.

**Foundation is free** (`realize_foundationSentence`, and `MaterialGround.exists_minimal`
with no hypothesis): a material carrier is a transitive collection of ambient well-founded
sets, so `MaterialCarrier.exists_minimal` gives the minimal-element consequence
unconditionally. The sentence stays named for general model-theoretic use — models of `T`
in other settings may need it as an axiom — but the recursion layer must **not** be charged
for it here. No global well-founded membership instance is installed, and any relation
instance stays local to the proof that needs it.

## Main definitions

* `Forcing.separationSentence`, `Forcing.collectionSentence`, `Forcing.foundationSentence`.
* `Forcing.separationScheme`, `Forcing.collectionScheme`: the named families.

## Main results

* `Forcing.MaterialGround.exists_separation`, `Forcing.MaterialGround.exists_collection`,
  `Forcing.MaterialGround.exists_minimal`: the semantic consequences.
-/

universe u

namespace Forcing

open FirstOrder Language

variable {k : ℕ}

/-- The parameter-and-`x` formula, moved into an all-bound context: parameters occupy
`&0 … &(k-1)` and the separated variable `&k`. Bookkeeping helper — consumers use the
semantic theorems, not this. -/
private def toBound (φ : memLang.BoundedFormula (Fin k) 1) : memLang.BoundedFormula Empty (k + 1) :=
  φ.relabel Sum.inr

/-- The two-variable version, for Collection: parameters `&0 … &(k-1)`, then `x`, then `y`. -/
private def toBound₂ (φ : memLang.BoundedFormula (Fin k) 2) :
    memLang.BoundedFormula Empty (k + 2) :=
  φ.relabel Sum.inr

/-- **The Separation scheme**, one sentence per formula: for parameters and `a`, the elements
of `a` satisfying `φ` form a set. -/
def separationSentence (φ : memLang.BoundedFormula (Fin k) 1) : memLang.Sentence :=
  (∀' ∃' ∀' (memFormula &⟨k + 2, by omega⟩ &⟨k + 1, by omega⟩ ⇔
      (memFormula &⟨k + 2, by omega⟩ &⟨k, by omega⟩ ⊓ (toBound φ).liftAt 2 k))).alls

/-- **The Collection scheme**, one sentence per formula: if every element of `a` has a
`φ`-witness, some set contains a witness for each. Functionality is **not** assumed, and
there is no reverse clause — this is Collection, not Replacement or Strong Collection. -/
def collectionSentence (φ : memLang.BoundedFormula (Fin k) 2) : memLang.Sentence :=
  (∀' ((∀' (memFormula &⟨k + 1, by omega⟩ &⟨k, by omega⟩ ⟹
        ∃' (toBound₂ φ).liftAt 1 k)) ⟹
      ∃' ∀' (memFormula &⟨k + 2, by omega⟩ &⟨k, by omega⟩ ⟹
        ∃' (memFormula &⟨k + 3, by omega⟩ &⟨k + 1, by omega⟩ ⊓
          (toBound₂ φ).liftAt 2 k)))).alls

/-- **Foundation**, a single sentence: every set with a member has an `∈`-minimal member. -/
def foundationSentence : memLang.Sentence :=
  ∀' ((∃' memFormula &1 &0) ⟹
    ∃' (memFormula &1 &0 ⊓ ∼(∃' (memFormula &2 &1 ⊓ memFormula &2 &0))))

/-- The named Separation family — its only job is to supply individual memberships. -/
def separationScheme : memLang.Theory :=
  ⋃ k : ℕ, Set.range (separationSentence (k := k))

/-- The named Collection family — likewise. -/
def collectionScheme : memLang.Theory :=
  ⋃ k : ℕ, Set.range (collectionSentence (k := k))

theorem separationSentence_mem_scheme (φ : memLang.BoundedFormula (Fin k) 1) :
    separationSentence φ ∈ separationScheme :=
  Set.mem_iUnion.2 ⟨k, Set.mem_range_self φ⟩

theorem collectionSentence_mem_scheme (φ : memLang.BoundedFormula (Fin k) 2) :
    collectionSentence φ ∈ collectionScheme :=
  Set.mem_iUnion.2 ⟨k, Set.mem_range_self φ⟩

/-! ### Variable bookkeeping

The `Fin` reassociation, lifting, and `snoc` arithmetic live here and nowhere else, so that
no later proof has to reopen the binder mechanics. -/

private theorem comp_shift_castAdd {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ∘
        fun i : Fin (k + 1) => if (i : ℕ) < k then Fin.castAdd 2 i else Fin.addNat i 2) ∘
      Fin.castAdd 1 = xs := by
  funext i
  have hi : (i : ℕ) < k := i.isLt
  simp [Fin.castAdd, Fin.castLE, Fin.snoc, hi, Nat.lt_trans hi (by omega : k < k + 1),
    Nat.lt_trans hi (by omega : k < k + 2)]

private theorem comp_shift_natAdd {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ∘
        fun i : Fin (k + 1) => if (i : ℕ) < k then Fin.castAdd 2 i else Fin.addNat i 2) ∘
      Fin.natAdd k = ![w] := by
  funext i
  have hi : (i : ℕ) = 0 := Nat.lt_one_iff.1 i.isLt
  simp [Fin.natAdd, Fin.addNat, Fin.snoc]

@[simp] private theorem snoc₃_at_last {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M)
    (h : k + 2 < k + 3) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ⟨k + 2, h⟩ = w := by
  simp [Fin.snoc]

@[simp] private theorem snoc₃_at_mid {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M)
    (h : k + 1 < k + 3) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ⟨k + 1, h⟩ = z := by
  simp [Fin.snoc]

@[simp] private theorem snoc₃_at_first {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M)
    (h : k < k + 3) :
    (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ⟨k, h⟩ = y := by
  simp [Fin.snoc]

@[simp] private theorem snoc₂_at {k : ℕ} {M : Type u} (xs : Fin k → M) (y z : M) :
    ((Fin.snoc (Fin.snoc xs y) z : Fin (k + 2) → M) ⟨k, by omega⟩ = y)
      ∧ ((Fin.snoc (Fin.snoc xs y) z : Fin (k + 2) → M) ⟨k + 1, by omega⟩ = z) := by
  refine ⟨?_, ?_⟩ <;> simp [Fin.snoc]

@[simp] private theorem snoc₄_at {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w t : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w) t : Fin (k + 4) → M) ⟨k, by omega⟩ = y)
      ∧ ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w) t : Fin (k + 4) → M)
          ⟨k + 1, by omega⟩ = z)
      ∧ ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w) t : Fin (k + 4) → M)
          ⟨k + 2, by omega⟩ = w)
      ∧ ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w) t : Fin (k + 4) → M)
          ⟨k + 3, by omega⟩ = t) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Fin.snoc]

private theorem comp_shift₁_castAdd {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ∘
        fun i : Fin (k + 2) => if (i : ℕ) < k then Fin.castAdd 1 i else i.succ) ∘
      Fin.castAdd 2 = xs := by
  funext i
  have hi : (i : ℕ) < k := i.isLt
  simp [Fin.castAdd, Fin.castLE, Fin.snoc, hi, Nat.lt_trans hi (by omega : k < k + 1),
    Nat.lt_trans hi (by omega : k < k + 2)]

private theorem comp_shift₁_natAdd {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w : Fin (k + 3) → M) ∘
        fun i : Fin (k + 2) => if (i : ℕ) < k then Fin.castAdd 1 i else i.succ) ∘
      Fin.natAdd k = ![z, w] := by
  funext i
  match i with
  | 0 => simp [Fin.natAdd, Fin.succ, Fin.snoc]
  | 1 => simp [Fin.natAdd, Fin.succ, Fin.snoc]

private theorem comp_shift₂_castAdd {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w t : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w) t : Fin (k + 4) → M) ∘
        fun i : Fin (k + 2) => if (i : ℕ) < k then Fin.castAdd 2 i else Fin.addNat i 2) ∘
      Fin.castAdd 2 = xs := by
  funext i
  have hi : (i : ℕ) < k := i.isLt
  simp [Fin.castAdd, Fin.castLE, Fin.snoc, hi, Nat.lt_trans hi (by omega : k < k + 1),
    Nat.lt_trans hi (by omega : k < k + 2), Nat.lt_trans hi (by omega : k < k + 3)]

private theorem comp_shift₂_natAdd {k : ℕ} {M : Type u} (xs : Fin k → M) (y z w t : M) :
    ((Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs y) z) w) t : Fin (k + 4) → M) ∘
        fun i : Fin (k + 2) => if (i : ℕ) < k then Fin.castAdd 2 i else Fin.addNat i 2) ∘
      Fin.natAdd k = ![w, t] := by
  funext i
  match i with
  | 0 => simp [Fin.natAdd, Fin.addNat, Fin.snoc]
  | 1 => simp [Fin.natAdd, Fin.addNat, Fin.snoc]

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **Separation, semantically**: the elements of `a` satisfying `φ` at the given parameters
form a member of the ground. Requires only the individual sentence's membership in `T`. -/
theorem exists_separation {φ : memLang.BoundedFormula (Fin k) 1}
    (hφ : separationSentence φ ∈ T) (params : Fin k → ↥M.toMaterialCarrier)
    (a : ↥M.toMaterialCarrier) :
    ∃ b : ↥M.toMaterialCarrier, ∀ x : ↥M.toMaterialCarrier,
      (x : ZFSet.{u}) ∈ (b : ZFSet.{u}) ↔
        (x : ZFSet.{u}) ∈ (a : ZFSet.{u}) ∧ φ.Realize params ![x] := by
  have hr := M.realize_of_mem hφ
  have key : ∀ ps : Fin k → ↥M.toMaterialCarrier, ∀ c : ↥M.toMaterialCarrier,
      ∃ b : ↥M.toMaterialCarrier, ∀ x : ↥M.toMaterialCarrier,
        (x : ZFSet.{u}) ∈ (b : ZFSet.{u}) ↔
          (x : ZFSet.{u}) ∈ (c : ZFSet.{u}) ∧ φ.Realize ps ![x] := by
    simpa [separationSentence, toBound, memFormula, Sentence.Realize,
      BoundedFormula.realize_liftAt, BoundedFormula.realize_relabel,
      comp_shift_castAdd, comp_shift_natAdd] using hr
  exact key params a

/-- **Collection, semantically**: if every element of `a` has a `φ`-witness, some member of
the ground contains a witness for each. No functionality, no reverse clause. -/
theorem exists_collection {φ : memLang.BoundedFormula (Fin k) 2}
    (hφ : collectionSentence φ ∈ T) (params : Fin k → ↥M.toMaterialCarrier)
    (a : ↥M.toMaterialCarrier)
    (hwit : ∀ x : ↥M.toMaterialCarrier, (x : ZFSet.{u}) ∈ (a : ZFSet.{u}) →
      ∃ y : ↥M.toMaterialCarrier, φ.Realize params ![x, y]) :
    ∃ b : ↥M.toMaterialCarrier, ∀ x : ↥M.toMaterialCarrier,
      (x : ZFSet.{u}) ∈ (a : ZFSet.{u}) →
        ∃ y : ↥M.toMaterialCarrier, (y : ZFSet.{u}) ∈ (b : ZFSet.{u}) ∧
          φ.Realize params ![x, y] := by
  have hr := M.realize_of_mem hφ
  have key : ∀ ps : Fin k → ↥M.toMaterialCarrier, ∀ c : ↥M.toMaterialCarrier,
      (∀ x : ↥M.toMaterialCarrier, (x : ZFSet.{u}) ∈ (c : ZFSet.{u}) →
          ∃ y : ↥M.toMaterialCarrier, φ.Realize ps ![x, y]) →
      ∃ b : ↥M.toMaterialCarrier, ∀ x : ↥M.toMaterialCarrier,
        (x : ZFSet.{u}) ∈ (c : ZFSet.{u}) →
          ∃ y : ↥M.toMaterialCarrier, (y : ZFSet.{u}) ∈ (b : ZFSet.{u}) ∧
            φ.Realize ps ![x, y] := by
    simpa [collectionSentence, toBound₂, memFormula, Sentence.Realize,
      BoundedFormula.realize_liftAt, BoundedFormula.realize_relabel,
      comp_shift₁_castAdd, comp_shift₁_natAdd, comp_shift₂_castAdd, comp_shift₂_natAdd,
      snoc₂_at, snoc₄_at] using hr
  exact key params a hwit

/-- **Foundation is free here** — no hypothesis on `T`. A material carrier is a transitive
collection of ambient well-founded sets, so the minimal-element consequence the recursion
layer consumes is `MaterialCarrier.exists_minimal`, available unconditionally. The
`foundationSentence` remains a named sentence for general model-theoretic use, but it is
**not a cost of recursion over transitive `ZFSet` carriers**. -/
theorem exists_minimal {a : ↥M.toMaterialCarrier} {x : ↥M.toMaterialCarrier}
    (hx : (x : ZFSet.{u}) ∈ (a : ZFSet.{u})) :
    ∃ y : ↥M.toMaterialCarrier, (y : ZFSet.{u}) ∈ (a : ZFSet.{u}) ∧
      ∀ z : ↥M.toMaterialCarrier, (z : ZFSet.{u}) ∈ (y : ZFSet.{u}) →
        (z : ZFSet.{u}) ∉ (a : ZFSet.{u}) := by
  obtain ⟨y, hya, hyM, hmin⟩ := M.toMaterialCarrier.exists_minimal a.2 hx
  exact ⟨⟨y, hyM⟩, hya, fun z hzy hza ↦ hmin z hzy hza⟩

/-- **Every material carrier models Foundation**, with no theory hypothesis — the audit
result, stated where the sentence lives. -/
theorem realize_foundationSentence : ↥M.toMaterialCarrier ⊨ foundationSentence := by
  have key : ∀ b : ↥M.toMaterialCarrier,
      (∃ w : ↥M.toMaterialCarrier, (w : ZFSet.{u}) ∈ (b : ZFSet.{u})) →
      ∃ y : ↥M.toMaterialCarrier, (y : ZFSet.{u}) ∈ (b : ZFSet.{u}) ∧
        ¬∃ z : ↥M.toMaterialCarrier, (z : ZFSet.{u}) ∈ (y : ZFSet.{u}) ∧
          (z : ZFSet.{u}) ∈ (b : ZFSet.{u}) := by
    rintro b ⟨w, hw⟩
    obtain ⟨y, hyb, hmin⟩ := M.exists_minimal hw
    exact ⟨y, hyb, fun ⟨z, hzy, hzb⟩ ↦ hmin z hzy hzb⟩
  simpa [foundationSentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc]
    using key

/-!
### Acceptance pressure test

A **nonfunctional** Collection instance with parameters: the witnessing relation below relates
each element to *every* member of a parameter set, so functionality fails wherever that set
has more than one element — and the scheme still returns exactly the bounded witness set,
with no reverse clause available. This is the shape the recursion theorem consumes.
-/

example {φ : memLang.BoundedFormula (Fin 1) 2} (hφ : collectionSentence φ ∈ T)
    (params : Fin 1 → ↥M.toMaterialCarrier) (a : ↥M.toMaterialCarrier)
    (hwit : ∀ x : ↥M.toMaterialCarrier, (x : ZFSet.{u}) ∈ (a : ZFSet.{u}) →
      ∃ y : ↥M.toMaterialCarrier, φ.Realize params ![x, y]) :
    ∃ b : ↥M.toMaterialCarrier, ∀ x : ↥M.toMaterialCarrier,
      (x : ZFSet.{u}) ∈ (a : ZFSet.{u}) →
        ∃ y : ↥M.toMaterialCarrier, (y : ZFSet.{u}) ∈ (b : ZFSet.{u}) ∧
          φ.Realize params ![x, y] :=
  M.exists_collection hφ params a hwit

/-- The empty carrier models every scheme instance vacuously — nonemptiness is never smuggled
in, and `memLang.nonemptyTheory` remains the separate price. -/
example : MaterialGround.{u} ∅ :=
  ⟨⟨∅, ZFSet.isTransitive_empty⟩, ⟨fun _ hφ ↦ absurd hφ (Set.notMem_empty _)⟩⟩

end MaterialGround

end Forcing
