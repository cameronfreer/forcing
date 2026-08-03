/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.Generic

/-!
# Diagonal requirements: the Cohen generic real diagonalizes a countable family

The coordinate requirements make the generic real total (`Forcing/Cohen/Generic.lean`); the
*diagonal* requirements make it differ from each member of a supplied countable family. Together
they give the external Cohen theorem, `exists_pfilter_total_diagonalizing`.

**This is not even avoidance over `M`.** The conclusion concerns only the supplied family; a
real that differs from every member of some countable family need not be generic, and no
observer plays any part at this milestone. Avoidance of the designated reals is the over-`M`
theorem (M3); "adds a new real" is reserved further still, for the material theorem
`realCode c ∈ M[G] ∧ realCode c ∉ M`. `parity_separation` below shows the first gap is real.

Diagonal attainability is where finiteness earns its keep: a condition decides only finitely many
coordinates, so a fresh one is available, and `Bool` has another value to put there. (For
`Fn(κ, λ)` these become "infinite `κ`" and "`Nontrivial λ`".)

## Main definitions

* `Forcing.Cohen.diagReq`: the requirement to differ from a given real.
* `Forcing.Cohen.parityReal`: the witness separating diagonalization from genericity.
* `Forcing.Cohen.oddTrueReq`: the separating test `oddTrue`, packaged as a requirement.

## Main results

* `Forcing.Cohen.exists_ne_of_meets_diagReq`: meeting the diagonal requirement forces
  disagreement.
* `Forcing.Cohen.exists_pfilter_total_diagonalizing`: the external Cohen theorem.
* `Forcing.Cohen.totality_separation`: the strict separation `J_total < J_new`.
* `Forcing.Cohen.parity_separation`: a filter meeting every coordinate *and* every diagonal
  requirement that is nonetheless not generic — the strict separation `J_new < J_full`.
-/

namespace Forcing.Cohen

open Order FinitePartialFunction

variable {G : PFilter Cond} {x : ℕ → Bool}

/-! ### The diagonal requirement -/

/-- The requirement to differ from the real `x` somewhere. Attainable because a condition leaves
some coordinate undecided, and `Bool` offers the other value there. -/
def diagReq (x : ℕ → Bool) : Requirement Cond where
  holds p := ∃ n b, p.lookup n = some b ∧ b ≠ x n
  persistent _ _ hqp := fun ⟨n, b, hb, hne⟩ ↦ ⟨n, b, hqp hb, hne⟩
  attainable p := by
    obtain ⟨n, hn⟩ := exists_lookup_eq_none p
    refine ⟨p.insert n (!x n), insert_le_of_notMem (lookup_eq_none_iff.1 hn),
      n, !x n, lookup_insert_self, ?_⟩
    cases x n <;> simp

@[simp] theorem mem_diagReq_support {p : Cond} :
    p ∈ (diagReq x).support ↔ ∃ n b, p.lookup n = some b ∧ b ≠ x n :=
  .rfl

/-- **Meeting the diagonal requirement forces the generic real to differ from `x`.** -/
theorem exists_ne_of_meets_diagReq (h : Meets G (diagReq x).support) :
    ∃ n b, genericFun G n = some b ∧ b ≠ x n := by
  obtain ⟨q, hqG, n, b, hb, hne⟩ := h
  exact ⟨n, b, unionFun_eq_some_iff.2 (unionGraph_of_mem hqG hb), hne⟩

/-- **The external Cohen theorem.** Through any condition there is a filter whose generic real is
total and differs from every member of a supplied countable family.

Note the statement: it is about the *supplied* family. It does not say the generic real is new,
which would need a ground model — see `parity_separation` for why the distinction matters. -/
theorem exists_pfilter_total_diagonalizing {ι : Type*} [Countable ι] (x : ι → ℕ → Bool)
    (p : Cond) :
    ∃ G : PFilter Cond, p ∈ G ∧ (∀ n, (genericFun G n).isSome) ∧
      ∀ i, ∃ n b, genericFun G n = some b ∧ b ≠ x i n := by
  obtain ⟨G, hpG, hG⟩ :=
    exists_pfilter_genericFor p
      (Sum.elim (fun n : ℕ ↦ (coordReq n).support) fun i : ι ↦ (diagReq (x i)).support)
      (Sum.rec (fun n ↦ (coordReq n).isDense_support) fun i ↦ (diagReq (x i)).isDense_support)
  exact ⟨G, hpG, fun n ↦ isSome_genericFun (fun m ↦ hG (.inl m)) n,
    fun i ↦ exists_ne_of_meets_diagReq (hG (.inr i))⟩

/-! ### The strict separation: diagonalizing is weaker than generic

A filter can meet every coordinate requirement and every diagonal requirement against a supplied
countable family and still fail to be generic. The witness is explicit — no perfect sets, no
cardinality argument.
-/

/-- The real diagonalizing the family `x` on even coordinates while staying `false` on all odd
ones. -/
def parityReal (x : ℕ → ℕ → Bool) (m : ℕ) : Bool :=
  if m % 2 = 0 then !x (m / 2) m else false

@[simp] theorem parityReal_even (x : ℕ → ℕ → Bool) (n : ℕ) :
    parityReal x (2 * n) = !x n (2 * n) := by
  have h : 2 * n % 2 = 0 := by omega
  have h' : 2 * n / 2 = n := by omega
  simp [parityReal, h, h']

@[simp] theorem parityReal_odd (x : ℕ → ℕ → Bool) (n : ℕ) : parityReal x (2 * n + 1) = false := by
  have h : (2 * n + 1) % 2 ≠ 0 := by omega
  simp [parityReal]

/-- The set of conditions putting `true` at some odd coordinate. -/
def oddTrue : Set Cond :=
  {p | ∃ n, p.lookup (2 * n + 1) = some true}

/-- `oddTrue` is persistent: putting `true` at an odd coordinate survives strengthening. -/
theorem isLowerSet_oddTrue : IsLowerSet oddTrue :=
  fun _ _ hba ⟨n, hn⟩ ↦ ⟨n, hba hn⟩

/-- `oddTrue` is dense: a condition decides only finitely many coordinates, so a large enough odd
coordinate is free. -/
theorem isDense_oddTrue : IsDense oddTrue := by
  intro p
  set n := p.keys.sup id + 1 with hn
  have hfresh : 2 * n + 1 ∉ p := by
    intro hmem
    have hle : 2 * n + 1 ≤ p.keys.sup id := Finset.le_sup (f := id) (mem_def.1 hmem)
    omega
  exact ⟨p.insert (2 * n + 1) true, ⟨n, lookup_insert_self⟩,
    insert_le_of_notMem hfresh⟩

/-- The separating test as a *requirement*: put `true` at some odd coordinate. Its persistence
and density proofs are exactly the two `Requirement` fields, so the separating test enters the
requirement vocabulary and composes with the requirement–visibility bridge
(`GenericOver.meets_requirement`) without unpacking `IsDenseOpen` by hand. -/
def oddTrueReq : Requirement Cond where
  holds p := p ∈ oddTrue
  persistent _ _ hqp hp := isLowerSet_oddTrue hqp hp
  attainable p := let ⟨q, hq, hqp⟩ := isDense_oddTrue p; ⟨q, hqp, hq⟩

@[simp] theorem support_oddTrueReq : oddTrueReq.support = oddTrue :=
  rfl

/-- `oddTrue` is a dense *open* test, so it belongs to the full doctrine `J_full`, which is
defined by dense-open tests. -/
theorem isDenseOpen_oddTrue : IsDenseOpen oddTrue :=
  oddTrueReq.isDenseOpen_support

/-- **The strict separation.** For any countable family, the canonical filter of `parityReal`
meets every coordinate requirement and every diagonal requirement against the family, yet misses
the dense set `oddTrue` — so it is not generic.

Meeting all the tests that make the union a real differing from every supplied real is therefore
strictly weaker than genericity: `J_new < J_full`. -/
theorem parity_separation (x : ℕ → ℕ → Bool) :
    (∀ n, Meets (ofFunction (parityReal x)) (coordReq n).support) ∧
      (∀ i, Meets (ofFunction (parityReal x)) (diagReq (x i)).support) ∧
      ¬Meets (ofFunction (parityReal x)) oddTrue := by
  refine ⟨meets_coordReq_ofFunction _, fun i ↦ ?_, ?_⟩
  · refine ⟨(∅ : Cond).insert (2 * i) (parityReal x (2 * i)),
      insert_empty_mem_ofFunction _ (2 * i), 2 * i, parityReal x (2 * i), lookup_insert_self, ?_⟩
    rw [parityReal_even]
    cases x i (2 * i) <;> simp
  · rintro ⟨q, hqG, n, hq⟩
    have := mem_ofFunction_iff.1 hqG hq
    rw [parityReal_odd] at this
    exact Bool.noConfusion this

/-- The separating filter's generic real is total and diagonalizes the family, and the filter is
still not generic — the separation in the form the genericity spectrum uses. -/
theorem parity_separation_total_diagonalizing (x : ℕ → ℕ → Bool) :
    (∀ n, (genericFun (ofFunction (parityReal x)) n).isSome) ∧
      (∀ i, ∃ n b, genericFun (ofFunction (parityReal x)) n = some b ∧ b ≠ x i n) ∧
      ¬Meets (ofFunction (parityReal x)) oddTrue :=
  ⟨fun n ↦ isSome_genericFun (meets_coordReq_ofFunction _) n,
    fun i ↦ exists_ne_of_meets_diagReq ((parity_separation x).2.1 i),
    (parity_separation x).2.2⟩

/-! ### The first strict separation: total is weaker than diagonalizing

The canonical filter of a real `x` decides every coordinate but cannot differ from `x`, so
`J_total < J_new`.
-/

/-- **The strict separation `J_total < J_new`.** The canonical filter of `x` meets every
coordinate requirement, yet misses the diagonal requirement against `x` itself: every condition
in it agrees with `x`. -/
theorem totality_separation (x : ℕ → Bool) :
    (∀ n, Meets (ofFunction x) (coordReq n).support) ∧
      ¬Meets (ofFunction x) (diagReq x).support := by
  refine ⟨meets_coordReq_ofFunction x, ?_⟩
  rintro ⟨q, hqG, n, b, hb, hne⟩
  exact hne (mem_ofFunction_iff.1 hqG hb).symm

end Forcing.Cohen
