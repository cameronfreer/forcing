/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finmap
import Mathlib.Data.Fintype.EquivFin
import Forcing.Order.Basic

/-!
# Forcing-ordered finite partial functions

Finite partial functions `∀ i, β i`, ordered by reverse inclusion: a stronger condition decides
at least as much, the same way. This is the shared carrier of the finite-condition forcing
notions — Cohen forcing `Fn(ω, 2)` is `FinitePartialFunction (fun _ : ℕ => Bool)`, and
`Add(ω, κ)` and collapse forcing reuse it at other index and value types.

Conditions are backed by `Finmap` (see `docs/decisions/0001-cohen-carrier.md`), wrapped in a
one-field structure rather than exposed as an abbreviation: the order instance then belongs to
this wrapper rather than to mathlib's `Finmap`, so the forcing orientation is not leaked
globally. The representation stays behind this file's API — downstream files use `lookup`,
`insert`, `keys`, and the lemmas here, never `toFinmap`.

Note that `union` is *not* given a lattice instance: it is a common strengthening only under
agreement, and globally it is left-biased, noncommutative, and not a forcing meet.

## Main definitions

* `Forcing.FinitePartialFunction β`: a finite partial section of `β`.
* `Forcing.FinitePartialFunction.lookup`, `insert`, `keys`, `union`: the basic operations.
* `Forcing.FinitePartialFunction.Agree`: two conditions agree wherever both are defined.

## Main results

* `Forcing.FinitePartialFunction.instPartialOrder`, `instOrderTop`: the order structure, with
  the empty condition as `⊤` (the weakest condition, deciding nothing).
* `Forcing.FinitePartialFunction.compatible_iff_agree`: compatibility is agreement, witnessed by
  the union.
* `Forcing.FinitePartialFunction.insert_le_iff`: `insert` strengthens exactly when the
  coordinate is fresh or the value agrees — it is an operation, not unconditionally a
  strengthening; `insert_eq_self` covers the value-agreement case exactly.
* `Forcing.FinitePartialFunction.exists_lookup_eq_none`: over an infinite index type, every
  condition leaves some coordinate undecided.
-/

universe u v

namespace Forcing

/-- A *finite partial function*: a finite partial section of `β`, thought of as a finite amount
of information about a total section. Ordered by reverse inclusion (`instPartialOrder`), this is
the carrier of the finite-condition forcing notions. -/
@[ext] structure FinitePartialFunction {ι : Type u} (β : ι → Type v) where
  /-- The underlying finite map. Downstream files use `lookup`/`insert`/`keys` instead. -/
  toFinmap : Finmap β

namespace FinitePartialFunction

variable {ι : Type u} {β : ι → Type v} [DecidableEq ι]
variable {p q : FinitePartialFunction β} {i j : ι} {b b' : β i}

/-- The value a condition assigns to a coordinate, if any. -/
def lookup (p : FinitePartialFunction β) (i : ι) : Option (β i) :=
  p.toFinmap.lookup i

/-- The coordinates a condition decides. -/
def keys (p : FinitePartialFunction β) : Finset ι :=
  p.toFinmap.keys

instance : Membership ι (FinitePartialFunction β) :=
  ⟨fun p i ↦ i ∈ p.keys⟩

omit [DecidableEq ι] in
theorem mem_def : i ∈ p ↔ i ∈ p.keys :=
  .rfl

@[simp] theorem mem_keys : i ∈ p.keys ↔ (p.lookup i).isSome := by
  rw [keys, Finmap.mem_keys, lookup, ← Finmap.lookup_isSome]

theorem mem_iff_isSome : i ∈ p ↔ (p.lookup i).isSome := by
  rw [mem_def, mem_keys]

theorem lookup_eq_none_iff : p.lookup i = none ↔ i ∉ p := by
  simp [mem_iff_isSome, Option.isSome_iff_ne_none]

/-- Conditions are determined by their lookups. -/
theorem ext_lookup (h : ∀ i, p.lookup i = q.lookup i) : p = q :=
  FinitePartialFunction.ext (Finmap.ext_lookup h)

theorem ext_lookup_iff : p = q ↔ ∀ i, p.lookup i = q.lookup i :=
  ⟨fun h _ ↦ h ▸ rfl, ext_lookup⟩

/-- The empty condition, deciding nothing. -/
instance : EmptyCollection (FinitePartialFunction β) :=
  ⟨⟨∅⟩⟩

@[simp] theorem lookup_empty : (∅ : FinitePartialFunction β).lookup i = none :=
  Finmap.lookup_empty i

/-- Extend a condition by deciding one coordinate. This is an *operation*: whether it
strengthens the original condition depends on the coordinate being fresh or the value agreeing
(see `insert_le_iff`). -/
def insert (p : FinitePartialFunction β) (i : ι) (b : β i) : FinitePartialFunction β :=
  ⟨p.toFinmap.insert i b⟩

@[simp] theorem lookup_insert_self : (p.insert i b).lookup i = some b :=
  Finmap.lookup_insert _

@[simp] theorem lookup_insert_of_ne (h : j ≠ i) : (p.insert i b).lookup j = p.lookup j :=
  Finmap.lookup_insert_of_ne _ h

omit [DecidableEq ι] in
@[simp] theorem keys_empty : (∅ : FinitePartialFunction β).keys = ∅ :=
  Finmap.keys_empty

@[simp] theorem keys_insert : (p.insert i b).keys = Insert.insert i p.keys := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp
  · simp [mem_keys, lookup_insert_of_ne hne, hne]

/-- Reverse inclusion: `q ≤ p` means `q` decides everything `p` decides, the same way. -/
instance instPartialOrder : PartialOrder (FinitePartialFunction β) where
  le q p := ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc _ _ h := hab (hbc h)
  le_antisymm _ _ hpq hqp :=
    ext_lookup fun _ ↦ Option.ext fun _ ↦ ⟨fun h ↦ hqp h, fun h ↦ hpq h⟩

theorem le_def : q ≤ p ↔ ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b :=
  .rfl

theorem le_of_lookup (h : ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → q.lookup i = some b) : q ≤ p :=
  h

/-- A stronger condition decides every coordinate the weaker one decides. -/
theorem mem_mono (h : q ≤ p) (hi : i ∈ p) : i ∈ q := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (mem_iff_isSome.1 hi)
  exact mem_iff_isSome.2 (by rw [h hb]; rfl)

theorem keys_mono (h : q ≤ p) : p.keys ⊆ q.keys :=
  fun _ hi ↦ mem_def.1 (mem_mono h (mem_def.2 hi))

/-- The empty condition is the weakest: it decides nothing, so every condition strengthens it.
Note the orientation — with smaller-is-stronger, `⊤` is the *weakest* condition. -/
instance instOrderTop : OrderTop (FinitePartialFunction β) where
  top := ∅
  le_top _ := fun _ _ h ↦ by rw [lookup_empty] at h; simp at h

@[simp] theorem top_eq_empty : (⊤ : FinitePartialFunction β) = ∅ :=
  rfl

@[simp] theorem lookup_top : (⊤ : FinitePartialFunction β).lookup i = none :=
  lookup_empty

/-- `insert` strengthens exactly when the coordinate is fresh or the value agrees. -/
theorem insert_le_iff : p.insert i b ≤ p ↔ p.lookup i = none ∨ p.lookup i = some b := by
  constructor
  · intro h
    cases hp : p.lookup i with
    | none => exact Or.inl rfl
    | some b' =>
      have h1 := h hp
      rw [lookup_insert_self] at h1
      exact Or.inr h1.symm
  · intro h j c hj
    rcases eq_or_ne j i with rfl | hne
    · rcases h with h | h
      · rw [h] at hj
        simp at hj
      · rw [lookup_insert_self]
        exact h.symm.trans hj
    · rwa [lookup_insert_of_ne hne]

/-- Deciding a fresh coordinate strengthens the condition. -/
theorem insert_le_of_notMem (h : i ∉ p) : p.insert i b ≤ p :=
  insert_le_iff.2 (Or.inl (lookup_eq_none_iff.2 h))

/-- Re-deciding a coordinate the same way does not change the condition. -/
@[simp] theorem insert_eq_self (h : p.lookup i = some b) : p.insert i b = p := by
  refine ext_lookup fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hne
  · rw [lookup_insert_self, h]
  · rw [lookup_insert_of_ne hne]

/-- Re-deciding a coordinate the same way strengthens the condition — indeed leaves it
unchanged (`insert_eq_self`). -/
theorem insert_le_of_lookup_eq (h : p.lookup i = some b) : p.insert i b ≤ p :=
  insert_le_iff.2 (Or.inr h)

/-- Over an infinite index type, every condition leaves some coordinate undecided: `keys` is
finite. -/
theorem exists_lookup_eq_none [Infinite ι] (p : FinitePartialFunction β) :
    ∃ i, p.lookup i = none := by
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset p.keys
  exact ⟨i, lookup_eq_none_iff.2 fun h ↦ hi (mem_def.1 h)⟩

/-- Two conditions *agree* if they assign the same value wherever both are defined. -/
def Agree (p q : FinitePartialFunction β) : Prop :=
  ∀ ⦃i⦄ ⦃b b' : β i⦄, p.lookup i = some b → q.lookup i = some b' → b = b'

theorem Agree.symm (h : Agree p q) : Agree q p :=
  fun _ _ _ hp hq ↦ (h hq hp).symm

/-- The union of two conditions, left-biased. It is the canonical common strengthening of
compatible conditions (`union_le_left`, `union_le_right`). It is deliberately given no lattice
instance: it is a common strengthening only under agreement, and globally it is left-biased,
noncommutative, and not a forcing meet. -/
def union (p q : FinitePartialFunction β) : FinitePartialFunction β :=
  ⟨p.toFinmap ∪ q.toFinmap⟩

@[simp] theorem keys_union : (p.union q).keys = p.keys ∪ q.keys :=
  Finmap.keys_union

theorem lookup_union_eq_some_iff :
    (p.union q).lookup i = some b ↔ p.lookup i = some b ∨ (i ∉ p ∧ q.lookup i = some b) :=
  Finmap.mem_lookup_union

theorem union_le_left (p q : FinitePartialFunction β) : p.union q ≤ p :=
  fun _ _ h ↦ lookup_union_eq_some_iff.2 (Or.inl h)

theorem union_le_right (h : Agree p q) : p.union q ≤ q := by
  intro i b hb
  by_cases hi : i ∈ p
  · obtain ⟨b'', hb''⟩ := Finmap.mem_iff.1 hi
    rw [h (show p.lookup i = some b'' from hb'') hb] at hb''
    exact lookup_union_eq_some_iff.2 (Or.inl hb'')
  · exact lookup_union_eq_some_iff.2 (Or.inr ⟨hi, hb⟩)

/-- Compatibility is agreement: two conditions have a common strengthening exactly when they
assign the same values wherever both are defined, and the union witnesses it. -/
theorem compatible_iff_agree : Compatible p q ↔ Agree p q := by
  constructor
  · rintro ⟨r, hrp, hrq⟩ i b b' hp hq
    exact Option.some.inj ((hrp hp).symm.trans (hrq hq))
  · exact fun h ↦ ⟨p.union q, union_le_left p q, union_le_right h⟩

theorem Agree.compatible (h : Agree p q) : Compatible p q :=
  compatible_iff_agree.2 h

end FinitePartialFunction

end Forcing
