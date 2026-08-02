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

The correspondence runs in both directions and is exact: `unionFun` and `ofPartialFunction` are
mutually inverse with **no hypotheses at all** (`pfilterEquivPartialFunction`), so arbitrary
filters are exactly partial functions. Coordinate requirements carve out the total objects:
meeting them all is exactly totality of the union
(`forall_meets_coordReq_iff_isSome_unionFun`), extraction is `totalUnion`, and `ofFunction` —
the total specialization of `ofPartialFunction` — is the inclusion of total objects. Faithful
recovery of a filter from its total union (`eq_ofFunction`) is a corollary of the partial
correspondence, and in particular needs no nonemptiness of the value fibers.

Nothing here is Cohen-specific; `Forcing/Cohen/` instantiates it.

## Main definitions

* `Forcing.FinitePartialFunction.UnionGraph G i b`: some condition in `G` sends `i` to `b`.
* `Forcing.FinitePartialFunction.unionFun`: the union as a partial function.
* `Forcing.FinitePartialFunction.ofPartialFunction`: the canonical filter of a partial
  function.
* `Forcing.FinitePartialFunction.pfilterEquivPartialFunction`: filters are exactly partial
  functions.
* `Forcing.FinitePartialFunction.ofFunction`: the canonical filter of a total function — the
  total specialization.
* `Forcing.FinitePartialFunction.totalUnion`: the union of a coordinatewise-total filter, as a
  total function.
* `Forcing.FinitePartialFunction.coordReq`: the requirement to decide a given coordinate.

## Main results

* `Forcing.FinitePartialFunction.unionGraph_unique`: the union graph is functional.
* `Forcing.FinitePartialFunction.unionFun_principal_top`: an arbitrary filter's union really can
  be nowhere defined.
* `Forcing.FinitePartialFunction.unionFun_ofPartialFunction`,
  `Forcing.FinitePartialFunction.ofPartialFunction_unionFun`: the two inverse laws, the second
  for **every** filter, no hypotheses.
* `Forcing.FinitePartialFunction.isSome_unionFun`,
  `Forcing.FinitePartialFunction.forall_meets_coordReq_iff_isSome_unionFun`: meeting the
  coordinate requirements is exactly totality of the union.
* `Forcing.FinitePartialFunction.exists_pfilter_total`: such filters exist (Rasiowa–Sikorski).
* `Forcing.FinitePartialFunction.eq_ofFunction`: faithful recovery — a filter whose union is
  total is the canonical filter of that union.
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

/-- **Partiality actually occurs.** The principal filter at the weakest condition decides
nothing, so its union is nowhere defined: an arbitrary filter is not enough for totality. -/
@[simp] theorem unionFun_principal_top (i : ι) :
    unionFun (PFilter.principal (⊤ : FinitePartialFunction β)) i = none := by
  cases hu : unionFun (PFilter.principal (⊤ : FinitePartialFunction β)) i with
  | none => rfl
  | some b =>
    obtain ⟨p, hp, hpi⟩ := unionFun_eq_some_iff.1 hu
    have htop : (⊤ : FinitePartialFunction β).lookup i = some b :=
      le_def.1 (PFilter.mem_principal.1 hp) hpi
    rw [lookup_top] at htop
    simp at htop

theorem isSome_unionFun_iff : (unionFun G i).isSome ↔ ∃ b, UnionGraph G i b := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    exact ⟨b, unionFun_eq_some_iff.1 hb⟩
  · rintro ⟨b, hb⟩
    rw [unionFun_eq_some_iff.2 hb]
    rfl

/-! ### The canonical filter of a partial function

A partial function determines a filter — the conditions whose every decision it extends — and
the determination is exact: `unionFun` and `ofPartialFunction` are mutually inverse with no
hypotheses, so filters of finite partial functions *are* partial functions
(`pfilterEquivPartialFunction`). The total function version `ofFunction` is the specialization
along `fun i ↦ some (c i)`, and faithful recovery of a filter from its total union is a
corollary.
-/

/-- The canonical filter of a partial function: the conditions all of whose decisions agree
with `c`. No nonemptiness of the value fibers is required. -/
def ofPartialFunction (c : ∀ i, Option (β i)) : PFilter (FinitePartialFunction β) :=
  (IsPFilter.of_def (F := {p | ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → c i = some b})
    ⟨∅, fun _ _ h ↦ by rw [lookup_empty] at h; simp at h⟩
    (by
      rintro p hp q hq
      have hagree : Agree p q := fun _ _ _ hb hb' ↦
        Option.some.inj ((hp hb).symm.trans (hq hb'))
      refine ⟨p.union q, fun i b hb ↦ ?_, union_le_left p q, union_le_right hagree⟩
      rcases lookup_union_eq_some_iff.1 hb with h | ⟨-, h⟩
      · exact hp h
      · exact hq h)
    (fun hxy hx _ _ h ↦ hx (le_def.1 hxy h))).toPFilter

@[simp] theorem mem_ofPartialFunction_iff {c : ∀ i, Option (β i)} :
    p ∈ ofPartialFunction c ↔ ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → c i = some b :=
  .rfl

/-- The one-coordinate condition at a decided coordinate belongs to the canonical filter. -/
theorem insert_empty_mem_ofPartialFunction {c : ∀ i, Option (β i)} (h : c i = some b) :
    (∅ : FinitePartialFunction β).insert i b ∈ ofPartialFunction c :=
  mem_ofPartialFunction_iff.2 <| by
    intro j b' hb'
    rcases eq_or_ne j i with rfl | hne
    · rw [lookup_insert_self] at hb'
      exact h.trans hb'
    · rw [lookup_insert_of_ne hne, lookup_empty] at hb'
      simp at hb'

/-- **The first inverse law**: the union of the canonical filter is the partial function
itself. Where `c` is defined, the one-coordinate condition witnesses it; where `c` is
undefined, no member of the filter may decide it. -/
@[simp] theorem unionFun_ofPartialFunction (c : ∀ i, Option (β i)) :
    unionFun (ofPartialFunction c) = c := by
  funext i
  cases hc : c i with
  | some b =>
    exact unionFun_eq_some_iff.2
      ⟨_, insert_empty_mem_ofPartialFunction hc, lookup_insert_self⟩
  | none =>
    cases hu : unionFun (ofPartialFunction c) i with
    | none => rfl
    | some b =>
      obtain ⟨p, hp, hpi⟩ := unionFun_eq_some_iff.1 hu
      have hb := mem_ofPartialFunction_iff.1 hp hpi
      rw [hc] at hb
      simp at hb

/-- Assembly: a condition whose every decision is witnessed somewhere in the filter lies above
a single member of the filter. This is where recovery consumes two filter axioms:
*nonemptiness* supplies the base approximation (the `G.nonempty` opening move) and
*directedness* combines the finitely many coordinate witnesses. -/
theorem exists_mem_le_of_forall_unionGraph {q : FinitePartialFunction β}
    (h : ∀ ⦃i⦄ ⦃b : β i⦄, q.lookup i = some b → UnionGraph G i b) :
    ∃ r ∈ G, r ≤ q := by
  suffices h' : ∀ s : Finset ι, ∃ r ∈ G, ∀ i ∈ s, ∀ ⦃b : β i⦄, q.lookup i = some b →
      r.lookup i = some b by
    obtain ⟨r, hrG, hr⟩ := h' q.keys
    exact ⟨r, hrG, fun i b hb ↦ hr i (mem_keys.2 (by rw [hb]; rfl)) hb⟩
  intro s
  refine Finset.induction_on s ?_ ?_
  · obtain ⟨r, hrG⟩ := G.nonempty
    exact ⟨r, hrG, fun i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  · rintro j t - ⟨r, hrG, hrt⟩
    cases hq : q.lookup j with
    | none =>
      refine ⟨r, hrG, fun i hi ↦ ?_⟩
      intro b hb
      rcases Finset.mem_insert.1 hi with rfl | hit
      · rw [hq] at hb
        simp at hb
      · exact hrt i hit hb
    | some bj =>
      obtain ⟨pj, hpjG, hpj⟩ := h hq
      obtain ⟨r', hr'G, hr'r, hr'p⟩ := exists_mem_le_le hrG hpjG
      refine ⟨r', hr'G, fun i hi ↦ ?_⟩
      intro b hb
      rcases Finset.mem_insert.1 hi with rfl | hit
      · rw [hq] at hb
        exact Option.some.inj hb ▸ hr'p hpj
      · exact hr'r (hrt i hit hb)

/-- **The second inverse law**: every filter is the canonical filter of its own partial union —
with no genericity, determinacy, or fiber-nonemptiness hypothesis.

The two inclusions consume different filter axioms, and this theorem is where each earns its
keep. That a member's decisions lie in the union needs only *directedness* (uniqueness of the
union value, `unionGraph_unique`). The converse — a condition extended by the union already
belongs to the filter — consumes all three: *nonemptiness* and *directedness* for the assembly
(`exists_mem_le_of_forall_unionGraph`), then *upward closure* (`Order.PFilter.mem_of_le`) for
the final membership. -/
@[simp] theorem ofPartialFunction_unionFun : ofPartialFunction (unionFun G) = G := by
  ext q
  constructor
  · intro hq
    obtain ⟨r, hrG, hrq⟩ :=
      exists_mem_le_of_forall_unionGraph fun i b hb ↦
        unionFun_eq_some_iff.1 (mem_ofPartialFunction_iff.1 hq hb)
    exact PFilter.mem_of_le hrq hrG
  · intro hqG
    exact mem_ofPartialFunction_iff.2 fun i b hb ↦
      unionFun_eq_some_iff.2 (unionGraph_of_mem hqG hb)

/-- **Filters of finite partial functions are exactly partial functions.** Arbitrary filters
correspond to partial objects; coordinate-generic filters correspond to total objects
(`forall_meets_coordReq_iff_isSome_unionFun`, `eq_ofFunction`); `ofFunction` is the total
inclusion. -/
noncomputable def pfilterEquivPartialFunction :
    PFilter (FinitePartialFunction β) ≃ (∀ i, Option (β i)) where
  toFun := unionFun
  invFun := ofPartialFunction
  left_inv _ := ofPartialFunction_unionFun
  right_inv := unionFun_ofPartialFunction

/-- The canonical filter of a condition's own partial function is its principal filter. -/
@[simp] theorem ofPartialFunction_lookup (p : FinitePartialFunction β) :
    ofPartialFunction p.lookup = PFilter.principal p := by
  ext q
  exact ⟨fun h ↦ PFilter.mem_principal.2 (le_of_lookup (mem_ofPartialFunction_iff.1 h)),
    fun h ↦ mem_ofPartialFunction_iff.2 (le_def.1 (PFilter.mem_principal.1 h))⟩

/-- The union of a principal filter is the condition's own partial function — the
generalization of `unionFun_principal_top`. -/
@[simp] theorem unionFun_principal (p : FinitePartialFunction β) :
    unionFun (PFilter.principal p) = p.lookup := by
  rw [← ofPartialFunction_lookup, unionFun_ofPartialFunction]

/-! ### The canonical filter of a total function

The total specialization. This direction needs no genericity at all; the converse — that a
filter with total union is recovered from it — is `eq_ofFunction` below, a corollary of the
partial correspondence.
-/

/-- The canonical filter of a total function: the total specialization of
`ofPartialFunction`. -/
def ofFunction (c : ∀ i, β i) : PFilter (FinitePartialFunction β) :=
  ofPartialFunction fun i ↦ some (c i)

@[simp] theorem mem_ofFunction_iff {c : ∀ i, β i} :
    p ∈ ofFunction c ↔ ∀ ⦃i⦄ ⦃b : β i⦄, p.lookup i = some b → c i = b := by
  constructor
  · intro h i b hb
    exact Option.some.inj (mem_ofPartialFunction_iff.1 h hb)
  · intro h
    exact mem_ofPartialFunction_iff.2 fun i b hb ↦ congrArg some (h hb)

/-- The one-coordinate condition agreeing with `c` belongs to its canonical filter. -/
theorem insert_empty_mem_ofFunction (c : ∀ i, β i) (i : ι) :
    (∅ : FinitePartialFunction β).insert i (c i) ∈ ofFunction c :=
  insert_empty_mem_ofPartialFunction rfl

theorem unionGraph_ofFunction {c : ∀ i, β i} : UnionGraph (ofFunction c) i b ↔ c i = b := by
  constructor
  · rintro ⟨q, hq, hqi⟩
    exact mem_ofFunction_iff.1 hq hqi
  · rintro rfl
    exact ⟨_, insert_empty_mem_ofFunction c i, lookup_insert_self⟩

@[simp] theorem unionFun_ofFunction {c : ∀ i, β i} : unionFun (ofFunction c) i = some (c i) :=
  unionFun_eq_some_iff.2 (unionGraph_ofFunction.2 rfl)

/-! ### Total extraction and faithful recovery -/

/-- The union of a filter whose union is total, extracted as a total function. The
`Option.get` plumbing lives here and nowhere else. -/
noncomputable def totalUnion (G : PFilter (FinitePartialFunction β))
    (h : ∀ i, (unionFun G i).isSome) (i : ι) : β i :=
  (unionFun G i).get (h i)

@[simp] theorem unionFun_totalUnion (h : ∀ i, (unionFun G i).isSome) (i : ι) :
    unionFun G i = some (totalUnion G h i) :=
  (Option.some_get (h i)).symm

/-- **Faithful recovery**: a filter whose union is the total function `c` is exactly the
canonical filter of `c`. A corollary of the partial correspondence
(`ofPartialFunction_unionFun`), so it holds for every filter with no fiber-nonemptiness
hypothesis — the object determines the filter as a special case of the equivalence. -/
theorem eq_ofFunction {c : ∀ i, β i} (hc : ∀ i, UnionGraph G i (c i)) : G = ofFunction c := by
  have h : unionFun G = fun i ↦ some (c i) := funext fun i ↦ unionFun_eq_some_iff.2 (hc i)
  have hG := ofPartialFunction_unionFun (G := G)
  rw [h] at hG
  exact hG.symm

/-- Faithful recovery, stated through the union function. -/
theorem eq_ofFunction_of_unionFun {c : ∀ i, β i} (hc : ∀ i, unionFun G i = some (c i)) :
    G = ofFunction c :=
  eq_ofFunction fun i ↦ unionFun_eq_some_iff.1 (hc i)

/-- A filter with total union is the canonical filter of its extracted total union. -/
theorem eq_ofFunction_totalUnion (h : ∀ i, (unionFun G i).isSome) :
    G = ofFunction (totalUnion G h) :=
  eq_ofFunction_of_unionFun (unionFun_totalUnion h)

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

/-- **The global equivalence**: meeting *all* coordinate requirements is exactly totality of
the union. The pointwise version is `meets_coordReq_iff_isSome_unionFun`; under this
equivalence, coordinate-generic filters are exactly the total objects of
`pfilterEquivPartialFunction`. -/
theorem forall_meets_coordReq_iff_isSome_unionFun :
    (∀ i, Meets G (coordReq i (β := β)).support) ↔ ∀ i, (unionFun G i).isSome :=
  forall_congr' fun _ ↦ meets_coordReq_iff_isSome_unionFun

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

end Forcing.FinitePartialFunction
