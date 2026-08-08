/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.Axioms
import Forcing.Material.NameCoding

/-!
# Assignment coding

The assignments layer of the internal-coding work. Assignments are coded **as tuples of
presentation codes** (`a : Fin n → N.Code`), not as tuples of external names: the name family
is only a range, so no canonical code for a name is available — decoding happens pointwise,
later, where assignments meet the forcing relation.

The encoding is the reversed snoc-list:

```text
code []          = ∅
code (snoc a i)  = pair (N.code i) (code a)
```

with the snoc law definitional up to `Fin.init_snoc` (`assignmentCode_snoc`).

**The price is exactly Empty Set and Pairing** — the first real exercise of the theory
interface. Each externally finite assignment is built by finite recursion, so only the finite
closure axioms are cited (`MaterialGround.empty_mem`, `MaterialGround.pair_mem`), each
through `realize_of_mem`. Neither Infinity, nor Union, nor Replacement appears. **The
distinction to keep**, which the formulas layer will meet again: an individual finite code
costs finite closure, while a single *internal collection* of all such codes is a
substantially more expensive demand — and no internal set of all assignments is constructed
here.

Faithfulness comes from pair injectivity plus the name-code faithfulness of
`InternalNameCoding`: equal assignment codes decode to pointwise-equal names
(`decode_eq_of_assignmentCode_eq`). As with names, codes may repeat, so the conclusion is
about the decoded names, not about the code indices.

Nothing here depends on forcing or formulas — and nothing depends on the **order** either:
the module takes `[Preorder P]` only where the condition presentation of the faithfulness
theorem requires it.

## Main definitions

* `Forcing.InternalNamePresentation.assignmentCode`: the reversed snoc-list code.

## Main results

* `Forcing.InternalNamePresentation.assignmentCode_snoc`: the extension law.
* `Forcing.InternalNamePresentation.assignmentCode_mem`: membership in the ground, priced at
  Empty Set and Pairing.
* `Forcing.InternalNamePresentation.decode_eq_of_assignmentCode_eq`: faithfulness.
-/

universe u

namespace Forcing

namespace InternalNamePresentation

open PName

variable {M : MaterialCarrier.{u}} {P : Type u}
variable (N : InternalNamePresentation M P)

/-- The code of an assignment of presentation codes: the reversed snoc-list. -/
def assignmentCode : ∀ {n : ℕ}, (Fin n → N.Code) → ZFSet.{u}
  | 0, _ => ∅
  | _ + 1, a => ZFSet.pair (N.code (a (Fin.last _))) (assignmentCode (Fin.init a))

@[simp] theorem assignmentCode_zero (a : Fin 0 → N.Code) : N.assignmentCode a = ∅ :=
  rfl

/-- **The extension law**: coding a snoc-extended assignment pairs the new name code onto the
code of the rest. -/
@[simp] theorem assignmentCode_snoc {n : ℕ} (a : Fin n → N.Code) (i : N.Code) :
    N.assignmentCode (Fin.snoc a i) = ZFSet.pair (N.code i) (N.assignmentCode a) := by
  rw [assignmentCode]
  simp [Fin.init_snoc]

variable {N}

/-- **Membership in the ground**, priced at exactly Empty Set and Pairing: each finite
assignment code is built by finite recursion, so no further axiom is cited. -/
theorem assignmentCode_mem {T : memLang.Theory} {G : MaterialGround.{u} T}
    {N : InternalNamePresentation G.toMaterialCarrier P}
    (he : emptySetSentence ∈ T) (hp : pairingSentence ∈ T) :
    ∀ {n : ℕ} (a : Fin n → N.Code), N.assignmentCode a ∈ G
  | 0, _ => G.empty_mem he
  | _ + 1, a => by
    rw [assignmentCode]
    exact G.pair_mem hp (N.code_mem _) (assignmentCode_mem he hp _)

/-- **Faithfulness**: equal assignment codes decode to pointwise-equal names. Pair
injectivity peels the tuple; name-code faithfulness converts codes to names. -/
theorem decode_eq_of_assignmentCode_eq [Preorder P]
    {Pres : InternalForcingPresentation M P} (h : InternalNameCoding Pres N) :
    ∀ {n : ℕ} (a b : Fin n → N.Code), N.assignmentCode a = N.assignmentCode b →
      ∀ i, N.decode (a i) = N.decode (b i)
  | 0, _, _, _, i => i.elim0
  | n + 1, a, b, hab, i => by
    rw [assignmentCode, assignmentCode] at hab
    obtain ⟨hlast, hinit⟩ := ZFSet.pair_inj.1 hab
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact h.decode_eq_of_code_eq _ _ hlast
    · have := decode_eq_of_assignmentCode_eq h (Fin.init a) (Fin.init b) hinit j
      simpa [Fin.init] using this

/-!
### Sanity examples

The code of the empty assignment is `∅`, and a one-element assignment is the pair of its
single name code with `∅` — the recursion bottoming out, with no collection of assignments
anywhere in sight.
-/

example (a : Fin 0 → N.Code) : N.assignmentCode a = ∅ :=
  rfl

example (i : N.Code) :
    N.assignmentCode (Fin.snoc (fun j : Fin 0 ↦ j.elim0) i) = ZFSet.pair (N.code i) ∅ := by
  simp

end InternalNamePresentation

end Forcing
