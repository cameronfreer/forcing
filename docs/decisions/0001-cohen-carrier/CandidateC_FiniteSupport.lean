/- Spike candidate C: finite-support `ℕ → Option Bool` subtype. Disposable prototype for #9. -/
import Mathlib.Data.Set.Finite.Basic
import Forcing.Order.Basic

namespace SpikeSupport

open Forcing

def Cond : Type := {f : ℕ → Option Bool // {n | f n ≠ none}.Finite}

-- Op 1: empty condition
def empty : Cond := ⟨fun _ ↦ none, by simp⟩

-- Op 2: lookup
def look (p : Cond) (n : ℕ) : Option Bool := p.1 n

-- Op 3: one-coordinate extension
def extend (p : Cond) (n : ℕ) (b : Bool) : Cond :=
  ⟨Function.update p.1 n (some b), (p.2.union (Set.finite_singleton n)).subset fun m hm ↦ by
    rcases eq_or_ne m n with rfl | hne
    · exact Or.inr rfl
    · exact Or.inl (by simpa [Function.update_of_ne hne] using hm)⟩

-- Order: reverse inclusion of bindings (smaller = more information)
instance : Preorder Cond where
  le q p := ∀ ⦃n : ℕ⦄ ⦃b : Bool⦄, p.1 n = some b → q.1 n = some b
  le_refl _ := fun _ _ h ↦ h
  le_trans _ _ _ hab hbc := fun _ _ h ↦ hab (hbc h)

-- Extensionality is free: conditions are functions.
theorem ext_look {p q : Cond} (h : ∀ n, look p n = look q n) : p = q :=
  Subtype.ext (funext h)

theorem extend_le (p : Cond) (n : ℕ) (b : Bool) (hn : p.1 n = none) : extend p n b ≤ p := by
  intro m c hm
  rcases eq_or_ne m n with rfl | hne
  · rw [hn] at hm
    simp at hm
  · show Function.update p.1 n (some b) m = some c
    rwa [Function.update_of_ne hne]

theorem look_extend_self (p : Cond) (n : ℕ) (b : Bool) : look (extend p n b) n = some b := by
  simp [look, extend]

-- Op 4: compatibility ↔ agreement, via the pointwise `orElse` join
def Agree (p q : Cond) : Prop :=
  ∀ ⦃n b b'⦄, p.1 n = some b → q.1 n = some b' → b = b'

theorem agree_of_compatible {p q : Cond} (h : Compatible p q) : Agree p q := by
  rintro n b b' hp hq
  obtain ⟨r, hrp, hrq⟩ := h
  exact Option.some.inj ((hrp hp).symm.trans (hrq hq))

def join (p q : Cond) : Cond :=
  ⟨fun n ↦ (p.1 n).or (q.1 n), (p.2.union q.2).subset fun m hm ↦ by
    simp only [Set.mem_setOf_eq] at hm
    match hpm : p.1 m with
    | some b => exact Or.inl (by simp [Set.mem_setOf_eq, hpm])
    | none => exact Or.inr (by simpa [Set.mem_setOf_eq, hpm] using hm)⟩

theorem compatible_of_agree {p q : Cond} (h : Agree p q) : Compatible p q := by
  refine ⟨join p q, fun n b hb ↦ ?_, fun n b hb ↦ ?_⟩
  · simp [join, hb]
  · match hpn : p.1 n with
    | none => simp [join, hpn, hb]
    | some b'' => rw [h hpn hb] at hpn; simp [join, hpn]

-- THE test: generic-union uniqueness
theorem genericUnion_unique {S : Set Cond}
    (hS : ∀ p ∈ S, ∀ q ∈ S, Compatible p q) {p q : Cond} (hp : p ∈ S) (hq : q ∈ S)
    {n : ℕ} {b b' : Bool} (hpn : look p n = some b) (hqn : look q n = some b') : b = b' :=
  agree_of_compatible (hS p hp q hq) hpn hqn

end SpikeSupport
