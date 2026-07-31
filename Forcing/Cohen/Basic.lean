/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finmap
import Mathlib.Data.Fintype.EquivFin
import Forcing.Order.Basic

/-!
# Cohen forcing conditions

The Cohen forcing notion `Fn(ω, 2)`: finite partial functions `ℕ ⇀ Bool`, ordered by reverse
inclusion, so that a stronger condition decides at least as much. Conditions are backed by
`Finmap` (see `docs/decisions/0001-cohen-carrier.md`), wrapped in a one-field structure rather
than exposed as an abbreviation — an abbreviation would make the forcing order an orphan
instance on mathlib's `Finmap` and leak the forcing orientation globally.

The `Finmap` representation stays behind this file's API: downstream Cohen files use `lookup`,
`insert`, `keys`, and the lemmas here, never `toFinmap`.

## Main definitions

* `Forcing.Cohen.Cond`: a Cohen condition.
* `Forcing.Cohen.lookup`, `insert`, `keys`: the basic operations.
* `Forcing.Cohen.Agree`: two conditions agree wherever both are defined.

## Main results

* `Forcing.Cohen.instPartialOrder`, `Forcing.Cohen.instOrderTop`: the order structure, with the
  empty condition as `⊤` (the weakest condition, deciding nothing).
* `Forcing.Cohen.compatible_iff_agree`: compatibility is agreement, witnessed by the union.
* `Forcing.Cohen.insert_le_iff`: `insert` strengthens exactly when the coordinate is fresh or
  the value agrees — it is an operation, not unconditionally a strengthening.
* `Forcing.Cohen.exists_lookup_eq_none`: every condition leaves some coordinate undecided.
-/

namespace Forcing.Cohen

/-- A *Cohen condition*: a finite partial function `ℕ ⇀ Bool`, thought of as a finite amount of
information about a real. -/
@[ext] structure Cond where
  /-- The underlying finite map. Downstream files use `lookup`/`insert`/`keys` instead. -/
  toFinmap : Finmap (fun _ : ℕ => Bool)

namespace Cond

variable {p q r : Cond} {n m : ℕ} {b b' : Bool}

/-- The value a condition assigns to a coordinate, if any. -/
def lookup (p : Cond) (n : ℕ) : Option Bool :=
  p.toFinmap.lookup n

/-- The coordinates a condition decides. -/
def keys (p : Cond) : Finset ℕ :=
  p.toFinmap.keys

instance : Membership ℕ Cond :=
  ⟨fun p n ↦ n ∈ p.keys⟩

theorem mem_def : n ∈ p ↔ n ∈ p.keys :=
  .rfl

@[simp] theorem mem_keys : n ∈ p.keys ↔ (p.lookup n).isSome := by
  rw [keys, Finmap.mem_keys, lookup, ← Finmap.lookup_isSome]

theorem mem_iff_isSome : n ∈ p ↔ (p.lookup n).isSome := by
  rw [mem_def, mem_keys]

theorem lookup_eq_none_iff : p.lookup n = none ↔ n ∉ p := by
  simp [mem_iff_isSome, Option.isSome_iff_ne_none]

/-- Conditions are determined by their lookups. -/
theorem ext_lookup (h : ∀ n, p.lookup n = q.lookup n) : p = q :=
  Cond.ext (Finmap.ext_lookup h)

theorem ext_lookup_iff : p = q ↔ ∀ n, p.lookup n = q.lookup n :=
  ⟨fun h _ ↦ h ▸ rfl, ext_lookup⟩

/-- The empty condition, deciding nothing. -/
instance : EmptyCollection Cond :=
  ⟨⟨∅⟩⟩

@[simp] theorem lookup_empty : (∅ : Cond).lookup n = none :=
  Finmap.lookup_empty n

/-- Extend a condition by deciding one coordinate. This is an *operation*: whether it
strengthens the original condition depends on the coordinate being fresh or the value agreeing
(see `insert_le_iff`). -/
def insert (p : Cond) (n : ℕ) (b : Bool) : Cond :=
  ⟨p.toFinmap.insert n b⟩

@[simp] theorem lookup_insert_self : (p.insert n b).lookup n = some b :=
  Finmap.lookup_insert _

@[simp] theorem lookup_insert_of_ne (h : m ≠ n) : (p.insert n b).lookup m = p.lookup m :=
  Finmap.lookup_insert_of_ne _ h

/-- Reverse inclusion: `q ≤ p` means `q` decides everything `p` decides, the same way. -/
instance instPartialOrder : PartialOrder Cond where
  le q p := ∀ ⦃n b⦄, p.lookup n = some b → q.lookup n = some b
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc _ _ h := hab (hbc h)
  le_antisymm _ _ hpq hqp :=
    ext_lookup fun _ ↦ Option.ext fun _ ↦ ⟨fun h ↦ hqp h, fun h ↦ hpq h⟩

theorem le_def : q ≤ p ↔ ∀ ⦃n b⦄, p.lookup n = some b → q.lookup n = some b :=
  .rfl

theorem le_of_lookup (h : ∀ ⦃n b⦄, p.lookup n = some b → q.lookup n = some b) : q ≤ p :=
  h

/-- The empty condition is the weakest: it decides nothing, so every condition strengthens it.
Note the orientation — with smaller-is-stronger, `⊤` is the *weakest* condition. -/
instance instOrderTop : OrderTop Cond where
  top := ∅
  le_top _ := fun _ _ h ↦ by rw [lookup_empty] at h; simp at h

@[simp] theorem top_eq_empty : (⊤ : Cond) = ∅ :=
  rfl

@[simp] theorem lookup_top : (⊤ : Cond).lookup n = none :=
  lookup_empty

/-- `insert` strengthens exactly when the coordinate is fresh or the value agrees. -/
theorem insert_le_iff : p.insert n b ≤ p ↔ p.lookup n = none ∨ p.lookup n = some b := by
  constructor
  · intro h
    cases hp : p.lookup n with
    | none => exact Or.inl rfl
    | some b' =>
      have h1 := h hp
      rw [lookup_insert_self] at h1
      exact Or.inr h1.symm
  · intro h m c hm
    rcases eq_or_ne m n with rfl | hne
    · rcases h with h | h
      · rw [h] at hm
        simp at hm
      · rw [lookup_insert_self]
        exact h.symm.trans hm
    · rwa [lookup_insert_of_ne hne]

/-- Deciding a fresh coordinate strengthens the condition. -/
theorem insert_le_of_notMem (h : n ∉ p) : p.insert n b ≤ p :=
  insert_le_iff.2 (Or.inl (lookup_eq_none_iff.2 h))

/-- Re-deciding a coordinate the same way strengthens (indeed, does not change) the
condition. -/
theorem insert_le_of_lookup_eq (h : p.lookup n = some b) : p.insert n b ≤ p :=
  insert_le_iff.2 (Or.inr h)

/-- Every condition leaves some coordinate undecided: `keys` is finite and `ℕ` is not. -/
theorem exists_lookup_eq_none (p : Cond) : ∃ n, p.lookup n = none := by
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset p.keys
  exact ⟨n, lookup_eq_none_iff.2 fun h ↦ hn (mem_def.1 h)⟩

/-- Two conditions *agree* if they assign the same value wherever both are defined. -/
def Agree (p q : Cond) : Prop :=
  ∀ ⦃n b b'⦄, p.lookup n = some b → q.lookup n = some b' → b = b'

theorem Agree.symm (h : Agree p q) : Agree q p :=
  fun _ _ _ hp hq ↦ (h hq hp).symm

/-- The union of two conditions, left-biased. It is the canonical common strengthening of
compatible conditions (`union_le_left`, `union_le_right`). -/
def union (p q : Cond) : Cond :=
  ⟨p.toFinmap ∪ q.toFinmap⟩

theorem lookup_union_eq_some_iff :
    (p.union q).lookup n = some b ↔ p.lookup n = some b ∨ (n ∉ p ∧ q.lookup n = some b) :=
  Finmap.mem_lookup_union

theorem union_le_left (p q : Cond) : p.union q ≤ p :=
  fun _ _ h ↦ lookup_union_eq_some_iff.2 (Or.inl h)

theorem union_le_right (h : Agree p q) : p.union q ≤ q := by
  intro n b hb
  by_cases hn : n ∈ p
  · obtain ⟨b'', hb''⟩ := Finmap.mem_iff.1 hn
    rw [h (show p.lookup n = some b'' from hb'') hb] at hb''
    exact lookup_union_eq_some_iff.2 (Or.inl hb'')
  · exact lookup_union_eq_some_iff.2 (Or.inr ⟨hn, hb⟩)

/-- Compatibility is agreement: two conditions have a common strengthening exactly when they
assign the same values wherever both are defined, and the union witnesses it. -/
theorem compatible_iff_agree : Compatible p q ↔ Agree p q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ n b b' hp hq
    exact Option.some.inj ((hrp hp).symm.trans (hrq hq))
  · exact fun h ↦ ⟨p.union q, union_le_left p q, union_le_right h⟩

theorem Agree.compatible (h : Agree p q) : Compatible p q :=
  compatible_iff_agree.2 h

/-!
### Sanity examples

The two one-bit conditions disagreeing at coordinate `0` are incompatible — the basic reason
Cohen forcing is nontrivial — while deciding distinct coordinates always leaves conditions
compatible.
-/

example : Incompatible ((∅ : Cond).insert 0 true) ((∅ : Cond).insert 0 false) := by
  rw [Incompatible, compatible_iff_agree]
  intro h
  exact Bool.noConfusion (h lookup_insert_self lookup_insert_self)

example : Compatible ((∅ : Cond).insert 0 true) ((∅ : Cond).insert 1 false) := by
  rw [compatible_iff_agree]
  intro n b b' hb hb'
  rcases eq_or_ne n 0 with rfl | h0
  · rw [lookup_insert_of_ne (by omega), lookup_empty] at hb'
    simp at hb'
  · rw [lookup_insert_of_ne h0, lookup_empty] at hb
    simp at hb

end Cond

end Forcing.Cohen
