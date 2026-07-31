/- Spike candidate B: structure with `Finset ℕ` domain + normalized total function.
Disposable prototype for issue #9. -/
import Mathlib.Data.Finset.Basic
import Forcing.Order.Basic

namespace SpikeStruct

open Forcing

@[ext] structure Cond where
  dom : Finset ℕ
  val : ℕ → Bool
  -- Normalization outside the domain, needed so that structure equality is not finer than
  -- lookup equality. Without it, extensionality by lookup FAILS.
  norm : ∀ n ∉ dom, val n = false

-- Op 1: empty condition
def empty : Cond := ⟨∅, fun _ ↦ false, fun _ _ ↦ rfl⟩

-- Op 2: lookup
def look (p : Cond) (n : ℕ) : Option Bool := if n ∈ p.dom then some (p.val n) else none

-- Op 3: one-coordinate extension
def extend (p : Cond) (n : ℕ) (b : Bool) : Cond where
  dom := insert n p.dom
  val := Function.update p.val n b
  norm := fun m hm ↦ by
    have hmn : m ≠ n := fun h ↦ hm (h ▸ Finset.mem_insert_self n p.dom)
    rw [Function.update_of_ne hmn]
    exact p.norm m fun h ↦ hm (Finset.mem_insert_of_mem h)

-- Order: reverse inclusion of bindings
instance : Preorder Cond where
  le q p := ∀ ⦃n : ℕ⦄ ⦃b : Bool⦄, look p n = some b → look q n = some b
  le_refl _ := fun _ _ h ↦ h
  le_trans _ _ _ hab hbc := fun _ _ h ↦ hab (hbc h)

-- Extensionality by lookup: must reassemble dom from lookup and use norm for val outside dom.
theorem ext_look {p q : Cond} (h : ∀ n, look p n = look q n) : p = q := by
  have hdom : p.dom = q.dom := by
    ext n
    constructor <;> intro hn
    · by_contra hqn
      have := h n
      simp [look, hn, hqn] at this
    · by_contra hpn
      have := h n
      simp [look, hn, hpn] at this
  refine Cond.ext hdom (funext fun n ↦ ?_)
  by_cases hn : n ∈ p.dom
  · have := h n
    have hn' : n ∈ q.dom := hdom ▸ hn
    simpa [look, hn, hn'] using this
  · rw [p.norm n hn, q.norm n (hdom ▸ hn)]

-- Op 4: compatibility ↔ agreement, via a merged condition
def Agree (p q : Cond) : Prop :=
  ∀ ⦃n b b'⦄, look p n = some b → look q n = some b' → b = b'

theorem agree_of_compatible {p q : Cond} (h : Compatible p q) : Agree p q := by
  rintro n b b' hp hq
  obtain ⟨r, hrp, hrq⟩ := h
  exact Option.some.inj ((hrp hp).symm.trans (hrq hq))

def join (p q : Cond) : Cond where
  dom := p.dom ∪ q.dom
  val := fun n ↦ if n ∈ p.dom then p.val n else q.val n
  norm := fun m hm ↦ by
    have hp : m ∉ p.dom := fun h ↦ hm (Finset.mem_union_left _ h)
    have hq : m ∉ q.dom := fun h ↦ hm (Finset.mem_union_right _ h)
    rw [if_neg hp]
    exact q.norm m hq

theorem compatible_of_agree {p q : Cond} (h : Agree p q) : Compatible p q := by
  refine ⟨join p q, fun n b hb ↦ ?_, fun n b hb ↦ ?_⟩
  · have hn : n ∈ p.dom := by
      by_contra hn
      simp [look, hn] at hb
    have hval : p.val n = b := by simpa [look, hn] using hb
    simp [look, join, Finset.mem_union, hn, hval]
  · have hn : n ∈ q.dom := by
      by_contra hn
      simp [look, hn] at hb
    have hval : q.val n = b := by simpa [look, hn] using hb
    by_cases hp : n ∈ p.dom
    · have hpb : look p n = some (p.val n) := by simp [look, hp]
      have := h hpb hb
      simp [look, join, Finset.mem_union, hp, this]
    · simp [look, join, Finset.mem_union, hp, hn, hval]

-- THE test: generic-union uniqueness
theorem genericUnion_unique {S : Set Cond}
    (hS : ∀ p ∈ S, ∀ q ∈ S, Compatible p q) {p q : Cond} (hp : p ∈ S) (hq : q ∈ S)
    {n : ℕ} {b b' : Bool} (hpn : look p n = some b) (hqn : look q n = some b') : b = b' :=
  agree_of_compatible (hS p hp q hq) hpn hqn

end SpikeStruct
