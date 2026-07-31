/- Spike candidate A: `Finmap (fun _ : ℕ => Bool)`. Disposable prototype for issue #9. -/
import Mathlib.Data.Finmap
import Forcing.Order.Basic

namespace SpikeFinmap

open Forcing

abbrev Cond : Type := Finmap (fun _ : ℕ => Bool)

-- Op 1: empty condition
def empty : Cond := ∅

-- Op 2: lookup
def look (p : Cond) (n : ℕ) : Option Bool := p.lookup n

-- Op 3: one-coordinate extension
def extend (p : Cond) (n : ℕ) (b : Bool) : Cond := p.insert n b

-- Order: reverse inclusion of bindings (smaller = more information)
instance : Preorder Cond where
  le q p := ∀ ⦃n : ℕ⦄ ⦃b : Bool⦄, p.lookup n = some b → q.lookup n = some b
  le_refl _ := fun _ _ h ↦ h
  le_trans _ _ _ hab hbc := fun _ _ h ↦ hab (hbc h)

theorem extend_le (p : Cond) (n : ℕ) (b : Bool) (hn : n ∉ p) : extend p n b ≤ p := by
  intro m c hm
  rcases eq_or_ne m n with rfl | hne
  · exact absurd (Finmap.lookup_isSome.1 (hm ▸ rfl)) hn
  · rw [extend, Finmap.lookup_insert_of_ne _ hne]
    exact hm

theorem look_extend_self (p : Cond) (n : ℕ) (b : Bool) : look (extend p n b) n = some b := by
  simp [look, extend]

-- Op 4: compatibility ↔ agreement, via the built-in (left-biased) union
def Agree (p q : Cond) : Prop :=
  ∀ ⦃n b b'⦄, p.lookup n = some b → q.lookup n = some b' → b = b'

theorem agree_of_compatible {p q : Cond} (h : Compatible p q) : Agree p q := by
  rintro n b b' hp hq
  obtain ⟨r, hrp, hrq⟩ := h
  exact Option.some.inj ((hrp hp).symm.trans (hrq hq))

theorem compatible_of_agree {p q : Cond} (h : Agree p q) : Compatible p q := by
  refine ⟨p ∪ q, fun n b hb ↦ ?_, fun n b hb ↦ ?_⟩
  · exact Finmap.mem_lookup_union.2 (Or.inl hb)
  · by_cases hn : n ∈ p
    · obtain ⟨b'', hb''⟩ := Finmap.mem_iff.1 hn
      rw [h hb'' hb] at hb''
      exact Finmap.mem_lookup_union.2 (Or.inl hb'')
    · exact Finmap.mem_lookup_union.2 (Or.inr ⟨hn, hb⟩)

-- THE test: generic-union uniqueness
theorem genericUnion_unique {S : Set Cond}
    (hS : ∀ p ∈ S, ∀ q ∈ S, Compatible p q) {p q : Cond} (hp : p ∈ S) (hq : q ∈ S)
    {n : ℕ} {b b' : Bool} (hpn : look p n = some b) (hqn : look q n = some b') : b = b' :=
  agree_of_compatible (hS p hp q hq) hpn hqn

end SpikeFinmap
