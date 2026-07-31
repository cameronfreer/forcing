/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.FinitePartialFunction
import Forcing.Order.RasiowaSikorski
import Forcing.Order.Requirement

/-!
# The generic union of a filter of finite partial functions

A filter of finite partial functions is a coherent family of finite approximations, so its
members agree wherever two of them are both defined. The union therefore *is* a partial
function: that is `unionGraph_unique`, and it is entirely generic — it uses only that two filter
members have a common strengthening inside the filter.

Coordinate requirements then turn that partial function into a total one. Nothing here is
Cohen-specific; `Forcing/Cohen/` instantiates it.

The last section is the converse direction: a total function has a canonical filter
(`ofFunction`), and a filter meeting every coordinate requirement is *exactly* the canonical
filter of its own union (`eq_ofFunction`). Faithful recovery is a separate claim from adequacy,
and it is stated as its own theorem.

## Main definitions

* `Forcing.FinitePartialFunction.UnionGraph G i b`: some condition in `G` sends `i` to `b`.
* `Forcing.FinitePartialFunction.unionFun`: the union as a partial function.
* `Forcing.FinitePartialFunction.ofFunction`: the canonical filter of a total function.
* `Forcing.FinitePartialFunction.coordReq`: the requirement to decide a given coordinate.

## Main results

* `Forcing.FinitePartialFunction.unionGraph_unique`: the union graph is functional.
* `Forcing.FinitePartialFunction.isSome_unionFun`: meeting the coordinate requirements makes the
  union total.
* `Forcing.FinitePartialFunction.exists_pfilter_total`: such filters exist (Rasiowa–Sikorski).
* `Forcing.FinitePartialFunction.eq_ofFunction`: faithful recovery — a coordinate-generic filter
  is the canonical filter of its union.
-/

namespace Forcing.FinitePartialFunction

open Order

universe u v

variable {ι : Type u} {β : ι → Type v} [DecidableEq ι]
variable {G : PFilter (FinitePartialFunction β)} {p : FinitePartialFunction β}
variable {i : ι} {b b' : β i}

/-! ### The union as a partial function -/

/-- The graph of the union of a filter: some condition in `G` sends `i` to `b`. -/
def UnionGraph (G : PFilter (FinitePartialFunction β)) (i : ι) (b : β i) : Prop :=
  ∃ p ∈ G, p.lookup i = some b

theorem unionGraph_of_mem (hp : p ∈ G) (h : p.lookup i = some b) : UnionGraph G i b :=
  ⟨p, hp, h⟩

/-- **The union of a filter is a partial function.** Two conditions in a filter have a common
strengthening inside the filter, which decides the coordinate both ways at once. -/
theorem unionGraph_unique (h : UnionGraph G i b) (h' : UnionGraph G i b') : b = b' := by
  obtain ⟨p, hpG, hp⟩ := h
  obtain ⟨q, hqG, hq⟩ := h'
  obtain ⟨r, -, hrp, hrq⟩ := exists_mem_le_le hpG hqG
  exact Option.some.inj ((hrp hp).symm.trans (hrq hq))

/-- The union of a filter, as a partial function. -/
noncomputable def unionFun (G : PFilter (FinitePartialFunction β)) (i : ι) : Option (β i) :=
  letI := Classical.dec (∃ b, UnionGraph G i b)
  if h : ∃ b, UnionGraph G i b then some h.choose else none

theorem unionFun_eq_some_iff : unionFun G i = some b ↔ UnionGraph G i b := by
  letI := Classical.dec (∃ b, UnionGraph G i b)
  constructor
  · intro h
    by_cases hex : ∃ b, UnionGraph G i b
    · rw [unionFun, dif_pos hex] at h
      exact Option.some.inj h ▸ hex.choose_spec
    · rw [unionFun, dif_neg hex] at h
      simp at h
  · intro h
    have hex : ∃ b, UnionGraph G i b := ⟨b, h⟩
    rw [unionFun, dif_pos hex]
    exact congrArg some (unionGraph_unique hex.choose_spec h)

theorem isSome_unionFun_iff : (unionFun G i).isSome ↔ ∃ b, UnionGraph G i b := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    exact ⟨b, unionFun_eq_some_iff.1 hb⟩
  · rintro ⟨b, hb⟩
    rw [unionFun_eq_some_iff.2 hb]
    rfl

/-! ### The canonical filter of a total function

A total function determines a filter. This direction needs no genericity at all; the converse —
that a coordinate-generic filter is recovered from its union — is `eq_ofFunction` below.
-/

/-- The canonical filter of a total function: the conditions all of whose values agree with
`c`. -/
def ofFunction (c : ∀ i, β i) : PFilter (FinitePartialFunction β) :=
  (IsPFilter.of_def (F := {p | ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → c i = b})
    ⟨∅, fun _ _ h ↦ by rw [lookup_empty] at h; simp at h⟩
    (by
      rintro p hp q hq
      have hagree : Agree p q := fun _ _ _ hb hb' ↦ (hp hb).symm.trans (hq hb')
      refine ⟨p.union q, fun i b hb ↦ ?_, union_le_left p q, union_le_right hagree⟩
      rcases lookup_union_eq_some_iff.1 hb with h | ⟨-, h⟩
      · exact hp h
      · exact hq h)
    (fun hxy hx _ _ h ↦ hx (le_def.1 hxy h))).toPFilter

@[simp] theorem mem_ofFunction_iff {c : ∀ i, β i} :
    p ∈ ofFunction c ↔ ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → c i = b :=
  .rfl

/-- The one-coordinate condition agreeing with `c` belongs to its canonical filter. -/
theorem insert_empty_mem_ofFunction (c : ∀ i, β i) (i : ι) :
    (∅ : FinitePartialFunction β).insert i (c i) ∈ ofFunction c :=
  mem_ofFunction_iff.2 <| by
    intro j b' hb'
    rcases eq_or_ne j i with rfl | hne
    · rw [lookup_insert_self] at hb'
      exact Option.some.inj hb'
    · rw [lookup_insert_of_ne hne, lookup_empty] at hb'
      simp at hb'

theorem unionGraph_ofFunction {c : ∀ i, β i} : UnionGraph (ofFunction c) i b ↔ c i = b := by
  constructor
  · rintro ⟨q, hq, hqi⟩
    exact hq hqi
  · rintro rfl
    exact ⟨_, insert_empty_mem_ofFunction c i, lookup_insert_self⟩

@[simp] theorem unionFun_ofFunction {c : ∀ i, β i} : unionFun (ofFunction c) i = some (c i) :=
  unionFun_eq_some_iff.2 (unionGraph_ofFunction.2 rfl)

/-! ### Coordinate requirements -/

variable [∀ i, Nonempty (β i)]

/-- The requirement to decide the coordinate `i`. It is persistent because stronger conditions
decide more, and attainable because an undecided coordinate can simply be filled in. -/
def coordReq (i : ι) : Requirement (FinitePartialFunction β) where
  holds p := i ∈ p
  persistent _ _ hqp hp := mem_mono hqp hp
  attainable p := by
    by_cases hi : i ∈ p
    · exact ⟨p, le_rfl, hi⟩
    · exact ⟨p.insert i (Classical.arbitrary (β i)), insert_le_of_notMem hi,
        mem_iff_isSome.2 (by rw [lookup_insert_self]; rfl)⟩

@[simp] theorem mem_coordReq_support : p ∈ (coordReq i (β := β)).support ↔ i ∈ p :=
  .rfl

/-- **Meeting the coordinate requirement is exactly deciding the coordinate.** -/
theorem meets_coordReq_iff : Meets G (coordReq i (β := β)).support ↔ ∃ b, UnionGraph G i b := by
  constructor
  · rintro ⟨q, hqG, hq⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (mem_iff_isSome.1 hq)
    exact ⟨b, unionGraph_of_mem hqG hb⟩
  · rintro ⟨b, q, hqG, hq⟩
    exact ⟨q, hqG, mem_iff_isSome.2 (by rw [hq]; rfl)⟩

theorem meets_coordReq_iff_isSome_unionFun :
    Meets G (coordReq i (β := β)).support ↔ (unionFun G i).isSome :=
  meets_coordReq_iff.trans isSome_unionFun_iff.symm

theorem exists_unionGraph_of_meets (h : Meets G (coordReq i (β := β)).support) :
    ∃ b, UnionGraph G i b :=
  meets_coordReq_iff.1 h

/-- **Meeting every coordinate requirement makes the union total.** -/
theorem isSome_unionFun (h : ∀ i, Meets G (coordReq i (β := β)).support) (i : ι) :
    (unionFun G i).isSome :=
  isSome_unionFun_iff.2 (exists_unionGraph_of_meets (h i))

/-- Existence (Rasiowa–Sikorski): over a countable index type, every condition extends to a
filter whose union is total. Adequacy without existence would be vacuous, so this is stated
separately and explicitly. -/
theorem exists_pfilter_total [Countable ι] (p : FinitePartialFunction β) :
    ∃ G : PFilter (FinitePartialFunction β), p ∈ G ∧ ∀ i, (unionFun G i).isSome := by
  obtain ⟨G, hpG, hG⟩ :=
    exists_pfilter_genericFor p (fun i ↦ (coordReq i (β := β)).support)
      fun i ↦ (coordReq i (β := β)).isDense_support
  exact ⟨G, hpG, fun i ↦ isSome_unionFun hG i⟩

/-- The canonical filter of a total function meets every coordinate requirement. -/
theorem meets_coordReq_ofFunction (c : ∀ i, β i) (i : ι) :
    Meets (ofFunction c) (coordReq i (β := β)).support :=
  ⟨(∅ : FinitePartialFunction β).insert i (c i), insert_empty_mem_ofFunction c i,
    show i ∈ (∅ : FinitePartialFunction β).insert i (c i) from
      mem_iff_isSome.2 (by rw [lookup_insert_self]; rfl)⟩

/-- A coordinate-generic filter contains a condition deciding any prescribed finite set of
coordinates. -/
theorem exists_mem_keys_subset (h : ∀ i, Meets G (coordReq i (β := β)).support) (s : Finset ι) :
    ∃ r ∈ G, s ⊆ r.keys := by
  refine Finset.induction_on s ?_ ?_
  · obtain ⟨r, hr⟩ := G.nonempty
    exact ⟨r, hr, Finset.empty_subset _⟩
  · rintro j t - ⟨r, hrG, hrt⟩
    obtain ⟨q, hqG, hq⟩ := h j
    obtain ⟨s', hs'G, hs'r, hs'q⟩ := exists_mem_le_le hrG hqG
    refine ⟨s', hs'G, fun k hk ↦ ?_⟩
    rcases Finset.mem_insert.1 hk with rfl | hkt
    · exact mem_def.1 (mem_mono hs'q hq)
    · exact keys_mono hs'r (hrt hkt)

/-- **Faithful recovery**: a filter whose union is the total function `c` is exactly the
canonical filter of `c`. So the generic object determines its filter, not merely the other way
round — a separate claim from any adequacy statement.

Note what the hypothesis is *not*: coordinate genericity is not an extra assumption here, it is
equivalent evidence of totality (`meets_coordReq_iff`) and is derived inside the proof. Together
with `ofFunction` needing no genericity at all, recovery is genericity-free in both
directions. -/
theorem eq_ofFunction {c : ∀ i, β i} (hc : ∀ i, UnionGraph G i (c i)) : G = ofFunction c := by
  have h : ∀ i, Meets G (coordReq i (β := β)).support := fun i ↦ meets_coordReq_iff.2 ⟨c i, hc i⟩
  ext q
  constructor
  · intro hqG i b hb
    exact unionGraph_unique (hc i) (unionGraph_of_mem hqG hb)
  · intro hq
    obtain ⟨r, hrG, hrq⟩ := exists_mem_keys_subset h q.keys
    refine PFilter.mem_of_le (fun i b hb ↦ ?_) hrG
    obtain ⟨b'', hb''⟩ :=
      Option.isSome_iff_exists.1 (mem_keys.1 (hrq (mem_keys.2 (by rw [hb]; rfl))))
    have hbc : c i = b'' := unionGraph_unique (hc i) (unionGraph_of_mem hrG hb'')
    exact hb''.trans (congrArg some (hbc.symm.trans (hq hb)))

/-- Faithful recovery, stated through the union function. -/
theorem eq_ofFunction_of_unionFun {c : ∀ i, β i} (hc : ∀ i, unionFun G i = some (c i)) :
    G = ofFunction c :=
  eq_ofFunction fun i ↦ unionFun_eq_some_iff.1 (hc i)

end Forcing.FinitePartialFunction
