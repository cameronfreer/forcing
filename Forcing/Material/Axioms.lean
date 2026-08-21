/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Ground
import Forcing.Syntax.MemLang
import Forcing.Coding.Nat

/-!
# Named axioms of the membership language, and their closure consequences

The theory ledger opens here. Each axiom is a **named sentence** of `memLang`, and its
consequence for a ground is a **reusable theorem** taking the membership of that sentence in
the theory as an explicit hypothesis — never a field on `MaterialGround`, and never an
implied background theory. A theorem's price is exactly the sentences it cites through
`MaterialGround.realize_of_mem`.

The named axioms introduced here are the ones the coding layers actually need:

* `emptySetSentence` — some set has no members;
* `pairingSentence` — any two sets have an unordered pair;
* `binaryUnionSentence` — any two sets have a union;
* `unionSentence` — every family has a union;
* `infinitySentence` — some set contains `∅` and is closed under successor.

**On the two unions.** General Union subsumes binary union: given pairing, `a ∪ b = ⋃₀ {a, b}`,
and `union_mem_of_sUnion` proves exactly that. They are both kept because the ledger records
what each theorem *actually* costs, and most of the coding layer costs only the binary
fragment. General Union is charged where a genuine family must be flattened — the atomic
recursion's rows, where Collection yields a set whose members are stage *sets* and the graph
needs their entries. For that construction the binary fragment does not suffice: the
prototype found no bound on the members-of-members of the collected family reachable from it.
That is a dependency finding about the construction being formalized, not a claim that no
alternative construction could avoid Union.

**On Infinity.** It is charged for exactly one job: supplying a transitive ambient domain
containing an arbitrary pair of name codes. The atomic recursion takes that domain as a
*parameter*, and its endpoint (`MaterialGround.exists_atomicCoherentOn`) is priced without
Infinity. That separation is the point of stating the parameterized version first, and it
should stay visible in the signatures rather than being collapsed into one theorem.

Empty set and pairing close a ground under `∅`, singletons, unordered pairs, and hence
Kuratowski pairs (`pair_mem`). Binary union is what `insert` costs — and therefore what the
von Neumann numerals cost (`natCode_mem`), a dependency-mining result rather than a
prediction: the successor code is an `insert`, so numeral membership prices at empty set,
pairing, **and** union, while still never reaching Infinity. **The distinction
that will recur**: each individual finite code is built by finite recursion and costs only
these finite closure axioms; a single *internal collection* of all such codes is a
substantially more expensive demand (Infinity and more), and is not made here.

Transitivity of the carrier does the rest of the work: the axioms speak about elements of the
ground, and transitivity is what turns "no member of `x` lies in the ground" into "`x` is
empty" and "the members of `c` inside the ground are exactly `a` and `b`" into an equality of
sets.

## Main definitions

* `Forcing.emptySetSentence`, `Forcing.pairingSentence`, `Forcing.binaryUnionSentence`,
  `Forcing.unionSentence`, `Forcing.infinitySentence`: the named axioms.

## Main results

* `Forcing.MaterialGround.empty_mem`, `Forcing.MaterialGround.insert_pair_mem`,
  `Forcing.MaterialGround.singleton_mem`, `Forcing.MaterialGround.pair_mem`: the closure
  consequences, each priced by the sentences it cites.
* `Forcing.MaterialGround.sUnion_mem`: closure under general union, the flattening step.
* `Forcing.MaterialGround.union_mem_of_sUnion`: general Union subsumes the binary fragment.
* `Forcing.MaterialGround.exists_inductive`: the consequence of Infinity.
* `Forcing.IsInductive`, `Forcing.inductiveDef`, `Forcing.realize_inductiveDef`: the shared
  notion of "inductive", so the axiom, the leastness condition defining `ω`, and the
  induction proof cannot drift apart.
-/

universe u v

namespace Forcing

open FirstOrder Language

/-- **The empty-set axiom**: some set has no members. -/
def emptySetSentence : memLang.Sentence :=
  ∃' ∀' ∼(memFormula &1 &0)

/-- **The pairing axiom**: any two sets have an unordered pair. -/
def pairingSentence : memLang.Sentence :=
  ∀' ∀' ∃' ∀' (memFormula &3 &2 ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

/-- **The binary-union axiom**: any two sets have a union. -/
def binaryUnionSentence : memLang.Sentence :=
  ∀' ∀' ∃' ∀' (memFormula &3 &2 ⇔ (memFormula &3 &0 ⊔ memFormula &3 &1))

/-- A set is **inductive**: it contains `∅` and is closed under successor. -/
def IsInductive (u : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ u ∧ ∀ x ∈ u, insert x x ∈ u

/-- **Inductiveness, as a formula**, function-free. Factored so that Infinity, the leastness
condition defining `ω`, and the induction proof cannot drift apart in what they mean by
"inductive" — all three are stated against this one definition. -/
def inductiveDef {α : Type v} {n : ℕ} (u : memLang.Term (α ⊕ Fin n)) :
    memLang.BoundedFormula α n :=
  (∃' (memFormula (&(Fin.last n)) (liftTerm u) ⊓ emptyDef (&(Fin.last n))))
  ⊓ ∀' (memFormula (&(Fin.last n)) (liftTerm u) ⟹
    ∃' (memFormula (&(Fin.last (n + 1))) (liftTerm (liftTerm u)) ⊓
      successorDef (&(Fin.castSucc (Fin.last n))) (&(Fin.last (n + 1)))))

/-- **The inductiveness law.** No hypotheses and no theory axioms: `∅` and each successor are
members of a carrier element, so transitivity supplies them. -/
theorem realize_inductiveDef {α : Type v} {n : ℕ} {M : MaterialCarrier.{u}}
    {v : α → M} {xs : Fin n → M} {u : memLang.Term (α ⊕ Fin n)} :
    (inductiveDef u).Realize v xs ↔
      IsInductive ((Term.realize (Sum.elim v xs) u : ↥M) : ZFSet.{u}) := by
  have huM : ((Term.realize (Sum.elim v xs) u : ↥M) : ZFSet.{u}) ∈ M :=
    (Term.realize (Sum.elim v xs) u : ↥M).2
  rw [inductiveDef, IsInductive]
  simp only [BoundedFormula.realize_inf, BoundedFormula.realize_ex, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, memFormula, BoundedFormula.realize_rel₂, relMap_mem,
    Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc,
    Matrix.cons_val_zero, Matrix.cons_val_one, realize_liftTerm, realize_emptyDef,
    realize_successorDef]
  refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨e, heU, hee⟩
    exact hee ▸ heU
  · intro h
    exact ⟨⟨∅, M.mem_trans h huM⟩, h, rfl⟩
  · intro h x hx
    obtain ⟨s, hsU, hse⟩ := h ⟨x, M.mem_trans hx huM⟩ hx
    exact hse ▸ hsU
  · intro h x hx
    exact ⟨⟨insert (x : ZFSet.{u}) (x : ZFSet.{u}),
      M.mem_trans (h (x : ZFSet.{u}) hx) huM⟩, h (x : ZFSet.{u}) hx, rfl⟩

/-- **Infinity**: some set contains the empty set and is closed under successor.

Charged **only** for the ambient domain of the atomic recursion — supplying a transitive set
containing an arbitrary pair of name codes. The recursion itself takes that set as a
parameter and never needs Infinity; see `Forcing/Material/RecursionExistence.lean`, whose
endpoint is priced without it. Keeping the two apart is the point of the parameterized
statement. -/
def infinitySentence : memLang.Sentence :=
  ∃' (inductiveDef (&(Fin.last 0)))

/-- **General Union**: every family has a union — the members of the members of `a` form a
set. Charged only where a genuine family is flattened; see the module docstring. -/
def unionSentence : memLang.Sentence :=
  ∀' ∃' (sUnionDef (&(Fin.castSucc (Fin.last 0))) (&(Fin.last 1)))

namespace MaterialGround

variable {T : memLang.Theory} (M : MaterialGround.{u} T)

/-- **Closure under `∅`**, priced at the empty-set axiom. Transitivity supplies the step from
"no member of the witness lies in the ground" to "the witness is empty". -/
theorem empty_mem (h : emptySetSentence ∈ T) : (∅ : ZFSet.{u}) ∈ M := by
  have hr := M.realize_of_mem h
  have key : ∃ x : ↥M.toMaterialCarrier, ∀ y : ↥M.toMaterialCarrier,
      (y : ZFSet.{u}) ∉ (x : ZFSet.{u}) := by
    simpa [emptySetSentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc] using hr
  obtain ⟨x, hx⟩ := key
  have hxe : (x : ZFSet.{u}) = ∅ := by
    refine (ZFSet.eq_empty _).2 fun z hz ↦ ?_
    exact hx ⟨z, mem_trans hz x.2⟩ hz
  exact hxe ▸ x.2

/-- **Closure under unordered pairs**, priced at the pairing axiom. -/
theorem insert_pair_mem (h : pairingSentence ∈ T) {x y : ZFSet.{u}} (hx : x ∈ M)
    (hy : y ∈ M) : ({x, y} : ZFSet.{u}) ∈ M := by
  have hr := M.realize_of_mem h
  have key : ∀ a b : ↥M.toMaterialCarrier, ∃ c : ↥M.toMaterialCarrier,
      ∀ z : ↥M.toMaterialCarrier, ((z : ZFSet.{u}) ∈ (c : ZFSet.{u}) ↔ z = a ∨ z = b) := by
    simpa [pairingSentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc] using hr
  obtain ⟨c, hc⟩ := key ⟨x, hx⟩ ⟨y, hy⟩
  have hce : (c : ZFSet.{u}) = {x, y} := by
    refine ZFSet.ext fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · have hzM : z ∈ M := mem_trans hz c.2
      rcases (hc ⟨z, hzM⟩).1 (by simpa using hz) with h1 | h1
      · exact ZFSet.mem_pair.2 (Or.inl (congrArg Subtype.val h1))
      · exact ZFSet.mem_pair.2 (Or.inr (congrArg Subtype.val h1))
    · rcases ZFSet.mem_pair.1 hz with rfl | rfl
      · simpa using (hc ⟨z, hx⟩).2 (Or.inl rfl)
      · simpa using (hc ⟨z, hy⟩).2 (Or.inr rfl)
  exact hce ▸ c.2

/-- **Closure under singletons**: the diagonal case of pairing. -/
theorem singleton_mem (h : pairingSentence ∈ T) {x : ZFSet.{u}} (hx : x ∈ M) :
    ({x} : ZFSet.{u}) ∈ M := by
  have hpair := M.insert_pair_mem h hx hx
  have hxx : ({x, x} : ZFSet.{u}) = {x} :=
    ZFSet.ext fun z ↦ by simp
  rwa [hxx] at hpair

/-- **Closure under binary unions**, priced at the binary-union axiom. -/
theorem union_mem (h : binaryUnionSentence ∈ T) {x y : ZFSet.{u}} (hx : x ∈ M)
    (hy : y ∈ M) : x ∪ y ∈ M := by
  have hr := M.realize_of_mem h
  have key : ∀ a b : ↥M.toMaterialCarrier, ∃ c : ↥M.toMaterialCarrier,
      ∀ z : ↥M.toMaterialCarrier, ((z : ZFSet.{u}) ∈ (c : ZFSet.{u}) ↔
        (z : ZFSet.{u}) ∈ (a : ZFSet.{u}) ∨ (z : ZFSet.{u}) ∈ (b : ZFSet.{u})) := by
    simpa [binaryUnionSentence, memFormula, Sentence.Realize, Formula.Realize, Fin.snoc]
      using hr
  obtain ⟨c, hc⟩ := key ⟨x, hx⟩ ⟨y, hy⟩
  have hce : (c : ZFSet.{u}) = x ∪ y := by
    refine ZFSet.ext fun z ↦ ⟨fun hz ↦ ?_, fun hz ↦ ?_⟩
    · exact ZFSet.mem_union.2 ((hc ⟨z, mem_trans hz c.2⟩).1 hz)
    · rcases ZFSet.mem_union.1 hz with h1 | h1
      · exact (hc ⟨z, mem_trans h1 hx⟩).2 (Or.inl h1)
      · exact (hc ⟨z, mem_trans h1 hy⟩).2 (Or.inr h1)
  exact hce ▸ c.2

/-- **Closure under general union**: the members of the members of `x` form a member of the
ground. This is the flattening step of the atomic recursion's row construction, where
Collection yields a set whose members are stage *sets* and the graph needs their entries. -/
theorem sUnion_mem (h : unionSentence ∈ T) {x : ZFSet.{u}} (hx : x ∈ M) :
    ZFSet.sUnion x ∈ M := by
  have hr := M.realize_of_mem h
  rw [unionSentence] at hr
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, realize_sUnionDef, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc] at hr
  obtain ⟨c, hc⟩ := hr ⟨x, hx⟩
  exact hc ▸ c.2

/-- **General Union subsumes the binary fragment**, given pairing: `a ∪ b = ⋃₀ {a, b}`. The
ledger keeps both sentences anyway, so that each theorem records the strength it actually
uses rather than the strongest available. -/
theorem union_mem_of_sUnion (hu : unionSentence ∈ T) (hp : pairingSentence ∈ T)
    {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) : x ∪ y ∈ M := by
  have hxy : ZFSet.sUnion ({x, y} : ZFSet.{u}) = x ∪ y :=
    ZFSet.ext fun z ↦ by
      simp only [ZFSet.mem_sUnion, ZFSet.mem_union, ZFSet.mem_insert_iff,
        ZFSet.mem_singleton]
      constructor
      · rintro ⟨w, rfl | rfl, hz⟩
        · exact Or.inl hz
        · exact Or.inr hz
      · rintro (hz | hz)
        · exact ⟨x, Or.inl rfl, hz⟩
        · exact ⟨y, Or.inr rfl, hz⟩
  exact hxy ▸ M.sUnion_mem hu (M.insert_pair_mem hp hx hy)

/-- **An inductive set lies in the ground** — the consequence of Infinity, and the only place
it is used. Stated against the shared `IsInductive`, so it cannot drift from the sentence. -/
theorem exists_inductive (h : infinitySentence ∈ T) :
    ∃ w : ZFSet.{u}, w ∈ M ∧ IsInductive w := by
  have hr := M.realize_of_mem h
  rw [infinitySentence] at hr
  simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_ex] at hr
  obtain ⟨w, hw⟩ := hr
  exact ⟨w, w.2, realize_inductiveDef.1 hw⟩

/-- **Closure under `insert`**: a singleton unioned on, priced at pairing and union. -/
theorem insert_mem (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T)
    {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) : insert x y ∈ M := by
  have hun := M.union_mem hu (M.singleton_mem hp hx) hy
  have hsu : ({x} : ZFSet.{u}) ∪ y = insert x y :=
    ZFSet.ext fun z ↦ by simp [ZFSet.mem_union, ZFSet.mem_singleton, ZFSet.mem_insert_iff]
  rwa [hsu] at hun

/-- **Closure under Kuratowski pairs** — three applications of pairing, and the only closure
the finite tagged-tree codings need. -/
theorem pair_mem (h : pairingSentence ∈ T) {x y : ZFSet.{u}} (hx : x ∈ M) (hy : y ∈ M) :
    ZFSet.pair x y ∈ M :=
  M.insert_pair_mem h (M.singleton_mem h hx) (M.insert_pair_mem h hx hy)

/-- **Closure under the von Neumann numerals** — the dependency-mining result: the successor
code is an `insert`, so numerals price at empty set, pairing, and union. Infinity is **not**
required: each individual numeral is built by finite recursion. -/
theorem natCode_mem {T : memLang.Theory} (M : MaterialGround.{u} T)
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) (hu : binaryUnionSentence ∈ T) :
    ∀ n : ℕ, natCode.{u} n ∈ M
  | 0 => M.empty_mem he
  | n + 1 => by
    rw [natCode_succ]
    exact M.insert_mem hp hu (M.natCode_mem he hp hu n) (M.natCode_mem he hp hu n)

end MaterialGround

end Forcing
