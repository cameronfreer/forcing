/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Material.AtomicFormula
import Forcing.Material.Lookup
import Forcing.Material.NameRecognition

/-!
# The formula-to-definition compiler

`forcesDef` sends a source formula `φ : memLang.BoundedFormula (Fin k) sn` to a membership-language
formula asserting that the condition coded by `p` forces `φ` under the assignment coded by `a`.

**Syntax only.** This file defines the compiler and certifies its *guards* — the three places where
a wrong orientation would typecheck. Structural-induction correctness against `ForcesFormula` is a
separate development; nothing here charges a theory sentence.

## The output context

The output is a `memLang.BoundedFormula α m` for an **ambient** `m`, with every parameter supplied
as a term in `α ⊕ Fin m`, so a compiled formula splices anywhere. This is the `lookupDef` and
`…Def` idiom, not a fixed variable layout.

Two designated arguments, in this order: the **condition** `p`, then the **assignment** `a`. Both
vary down the recursion — `p` at `.imp`, `a` at `.all` — which is why neither lives in
`CompilerParams`.

## The combined assignment

`ForcesFormula` evaluates terms at `Sum.elim v xs`, a valuation on `Fin k ⊕ Fin sn`. The compiled
form codes that as a **single** assignment of arity `k + sn` under `finSumFinEquiv`: free variables
first, bound variables after. `.all` extends it by `Fin.snoc`, which is why `assignmentCode`'s
reversed-snoc convention puts the newly bound name outermost, at peel zero.

## The three guards

Each is a relation the compiler asserts internally, and each would typecheck reversed:

| site | guard | law |
|---|---|---|
| `.imp` | `q ≤ p` as `pairMemDef q p orderCode` | `realize_forcesDef_imp` |
| `.all` | `a' = ⟨c, a⟩` as `pairDef c a a'` | `realize_forcesDef_all` |
| `.equal`, `.rel` | entry `i` at peel `k + sn - 1 - i` | `…_equal_of_assignmentCode` |

## Universal, not existential, at the extension sites

`.imp` and `.all` both introduce their bound object with `∀' (guard ⟹ …)` rather than
`∃' (guard ⊓ …)`. The guards are functional — `pairDef` determines `a'` outright — so the two agree
whenever the object exists in the carrier. The universal form is the one that asserts no existence,
and therefore charges no Pairing sentence into the *syntax*.

The consequence for correctness is **asymmetric**, and should stay that way rather than being
smoothed into a global hypothesis:

* external forcing → compiled `.all` needs no Pairing. Any `a'` satisfying the guard is handed to
  us, so there is nothing to construct.
* compiled `.all` → external forcing needs Pairing, to build the extended assignment code that the
  universal hypothesis is then applied to.

So the price is paid in one direction only, at one site.

## Main results

* `Forcing.forcesDef`: the compiler, five equations.
* `Forcing.realize_relabel_snoc`: the recognition splice, beneath the new binder.
* `Forcing.realize_forcesDef_imp`, `…_all`, `…_equal`, `…_rel`: the guards, realized.
* `Forcing.realize_forcesDef_all_recognition`: the spliced recognizer names exactly the
  range of `N.code`.
* `Forcing.realize_forcesDef_equal_of_assignmentCode`, `…_rel_of_assignmentCode`: the orientation
  guard, against a genuine coded assignment.
* `Forcing.realize_forcesDef_all_of_assignmentCode`: the extension guard, likewise, with
  `…_arity` pinning the combined arity.
-/

universe u v

namespace Forcing

open FirstOrder Language AtomicRecursion

/-! ### The parameter block -/

/-- The compiler's context-dependent parameters: the four fixed material codes, and the
recognizer's parameter positions.

Bundled because every one of them must be lifted at every binder, and lifting them in one place
is what keeps the bookkeeping checkable. `p` and `a` are deliberately *not* here: they vary with
the recursion rather than being carried through it. -/
structure CompilerParams (α : Type v) (arity m : ℕ) where
  /-- Code of the membership-witness tag. -/
  tagMem : memLang.Term (α ⊕ Fin m)
  /-- Code of the forced-equality tag. -/
  tagEq : memLang.Term (α ⊕ Fin m)
  /-- The coded set of conditions. -/
  condSet : memLang.Term (α ⊕ Fin m)
  /-- The coded order on conditions. -/
  orderCode : memLang.Term (α ⊕ Fin m)
  /-- Where the recognizer's parameters sit in the ambient context. -/
  recParams : Fin arity → α ⊕ Fin m

namespace CompilerParams

variable {α : Type v} {arity m : ℕ}

/-- Push a parameter block under one new binder. -/
def lift (Γ : CompilerParams α arity m) : CompilerParams α arity (m + 1) where
  tagMem := liftTerm Γ.tagMem
  tagEq := liftTerm Γ.tagEq
  condSet := liftTerm Γ.condSet
  orderCode := liftTerm Γ.orderCode
  recParams := fun i ↦ Sum.map id Fin.castSucc (Γ.recParams i)

end CompilerParams

/-! ### Source indices -/

/-- The position of a source variable in the combined assignment: free variables first, bound
variables after. `memLang` is function-free, so `var` is the only case that can occur. -/
def srcIndex {k sn : ℕ} : memLang.Term (Fin k ⊕ Fin sn) → Fin (k + sn)
  | .var i => finSumFinEquiv i
  | .func f _ => Empty.elim f

/-- How many second components to peel to reach a source variable's code. The arity is `k + sn`
and `assignmentCode` is reversed, so entry `i` sits under `k + sn - 1 - i` peels. -/
def srcPeel {k sn : ℕ} (t : memLang.Term (Fin k ⊕ Fin sn)) : ℕ :=
  k + sn - 1 - (srcIndex t : ℕ)

/-! ### The compiler -/

/-- **The compiler.** `forcesDef rec φ Γ p a` says: the condition coded by `p` forces `φ` under
the assignment coded by `a`.

`rec` is the name-code recognizer, a fixed unary formula spliced by `relabel` at `.all`; #218
settled that no substitution API is needed. The atomic cases consume the **uniform** seven-parameter
definitions, never the pair-relative `…DefOn A` layer. -/
def forcesDef {α : Type v} {k arity : ℕ} (rec : memLang.BoundedFormula (Fin arity) 1) :
    ∀ {sn m : ℕ}, memLang.BoundedFormula (Fin k) sn → CompilerParams α arity m →
      memLang.Term (α ⊕ Fin m) → memLang.Term (α ⊕ Fin m) → memLang.BoundedFormula α m
  | _, _, .falsum, _, _, _ => ⊥
  | _, m, .equal t₁ t₂, Γ, p, a =>
      ∃' ∃' (lookupDef (srcPeel t₁) (liftTerm (liftTerm a)) (&(Fin.castSucc (Fin.last m))) ⊓
        (lookupDef (srcPeel t₂) (liftTerm (liftTerm a)) (&(Fin.last (m + 1))) ⊓
          forcesEqDef Γ.lift.lift.tagMem Γ.lift.lift.tagEq Γ.lift.lift.condSet
            Γ.lift.lift.orderCode (liftTerm (liftTerm p))
            (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1)))))
  | _, m, .rel .mem ts, Γ, p, a =>
      ∃' ∃' (lookupDef (srcPeel (ts 0)) (liftTerm (liftTerm a)) (&(Fin.castSucc (Fin.last m))) ⊓
        (lookupDef (srcPeel (ts 1)) (liftTerm (liftTerm a)) (&(Fin.last (m + 1))) ⊓
          forcesMemDef Γ.lift.lift.tagMem Γ.lift.lift.tagEq Γ.lift.lift.condSet
            Γ.lift.lift.orderCode (liftTerm (liftTerm p))
            (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1)))))
  | _, m, .imp φ ψ, Γ, p, a =>
      ∀' (pairMemDef (&(Fin.last m)) (liftTerm p) Γ.lift.orderCode ⟹
        (forcesDef rec φ Γ.lift (&(Fin.last m)) (liftTerm a) ⟹
          forcesDef rec ψ Γ.lift (&(Fin.last m)) (liftTerm a)))
  | _, m, .all φ, Γ, p, a =>
      ∀' (rec.relabel Γ.recParams ⟹
        ∀' (pairDef (&(Fin.castSucc (Fin.last m))) (liftTerm (liftTerm a))
              (&(Fin.last (m + 1))) ⟹
          forcesDef rec φ Γ.lift.lift (liftTerm (liftTerm p)) (&(Fin.last (m + 1)))))

/-! ### The five constructor equations

Named rather than `@[simp]`, matching `ForcesFormula`'s unfolding laws. -/

section Equations

variable {α : Type v} {k arity sn m : ℕ} {rec : memLang.BoundedFormula (Fin arity) 1}
variable {Γ : CompilerParams α arity m} {p a : memLang.Term (α ⊕ Fin m)}

theorem forcesDef_falsum :
    forcesDef rec (.falsum : memLang.BoundedFormula (Fin k) sn) Γ p a = ⊥ :=
  rfl

theorem forcesDef_equal {t₁ t₂ : memLang.Term (Fin k ⊕ Fin sn)} :
    forcesDef rec (.equal t₁ t₂) Γ p a =
      ∃' ∃' (lookupDef (srcPeel t₁) (liftTerm (liftTerm a)) (&(Fin.castSucc (Fin.last m))) ⊓
        (lookupDef (srcPeel t₂) (liftTerm (liftTerm a)) (&(Fin.last (m + 1))) ⊓
          forcesEqDef Γ.lift.lift.tagMem Γ.lift.lift.tagEq Γ.lift.lift.condSet
            Γ.lift.lift.orderCode (liftTerm (liftTerm p))
            (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1))))) :=
  rfl

theorem forcesDef_rel {ts : Fin 2 → memLang.Term (Fin k ⊕ Fin sn)} :
    forcesDef rec (.rel .mem ts) Γ p a =
      ∃' ∃' (lookupDef (srcPeel (ts 0)) (liftTerm (liftTerm a)) (&(Fin.castSucc (Fin.last m))) ⊓
        (lookupDef (srcPeel (ts 1)) (liftTerm (liftTerm a)) (&(Fin.last (m + 1))) ⊓
          forcesMemDef Γ.lift.lift.tagMem Γ.lift.lift.tagEq Γ.lift.lift.condSet
            Γ.lift.lift.orderCode (liftTerm (liftTerm p))
            (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1))))) :=
  rfl

theorem forcesDef_imp {φ ψ : memLang.BoundedFormula (Fin k) sn} :
    forcesDef rec (φ.imp ψ) Γ p a =
      ∀' (pairMemDef (&(Fin.last m)) (liftTerm p) Γ.lift.orderCode ⟹
        (forcesDef rec φ Γ.lift (&(Fin.last m)) (liftTerm a) ⟹
          forcesDef rec ψ Γ.lift (&(Fin.last m)) (liftTerm a))) :=
  rfl

theorem forcesDef_all {φ : memLang.BoundedFormula (Fin k) (sn + 1)} :
    forcesDef rec φ.all Γ p a =
      ∀' (rec.relabel Γ.recParams ⟹
        ∀' (pairDef (&(Fin.castSucc (Fin.last m))) (liftTerm (liftTerm a))
              (&(Fin.last (m + 1))) ⟹
          forcesDef rec φ Γ.lift.lift (liftTerm (liftTerm p)) (&(Fin.last (m + 1))))) :=
  rfl

end Equations

/-! ### The guards, realized

Each theorem below pins one place where the compiler asserts a relation that would typecheck
reversed. No structural induction and no theory sentence: these certify the binder bookkeeping
and the orientations, so that correctness measures the compiler design rather than this. -/

section Guards

variable {α : Type v} {k arity sn m : ℕ} {M : MaterialCarrier.{u}}
variable {rec : memLang.BoundedFormula (Fin arity) 1}
variable {Γ : CompilerParams α arity m} {p a : memLang.Term (α ⊕ Fin m)}
variable {v : α → M} {xs : Fin m → M}

/-- **The recognition splice.** A fixed unary recognizer, relabelled into the ambient context,
realizes beneath the new binder exactly as the original does at the mapped parameters and the
newly bound element.

This is what #218 verified: `relabel` alone suffices, no substitution API. -/
theorem realize_relabel_snoc (rec : memLang.BoundedFormula (Fin arity) 1)
    (g : Fin arity → α ⊕ Fin m) (c : M) :
    (rec.relabel g).Realize v (Fin.snoc xs c) ↔
      rec.Realize (fun i ↦ Sum.elim v xs (g i)) ![c] := by
  have h1 : (Sum.elim v (Fin.snoc xs c ∘ Fin.castAdd 1) ∘ g) = fun i ↦ Sum.elim v xs (g i) := by
    funext i
    cases h : g i with
    | inl _ => simp [h]
    | inr j =>
      simp only [h, Sum.elim_inr, Function.comp_apply]
      have hc : (Fin.castAdd 1 j : Fin (m + 1)) = Fin.castSucc j := by ext; simp
      rw [hc, Fin.snoc_castSucc]
  have h2 : (Fin.snoc xs c ∘ Fin.natAdd m) = ![c] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have hn : Fin.natAdd m (0 : Fin 1) = Fin.last m := by ext; simp
    simp [hn]
  rw [BoundedFormula.realize_relabel, h1, h2]

/-- **The implication guard.** The strengthening is certified as `⟨q, p⟩ ∈ orderCode` — the
coded order, in that argument order. Reversing it would compile. -/
theorem realize_forcesDef_imp {φ ψ : memLang.BoundedFormula (Fin k) sn} :
    (forcesDef rec (φ.imp ψ) Γ p a).Realize v xs ↔
      ∀ q : ↥M, ZFSet.pair ((q : ↥M) : ZFSet.{u})
            ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u}) ∈
          ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u}) →
        ((forcesDef rec φ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v (Fin.snoc xs q) →
          (forcesDef rec ψ Γ.lift (&(Fin.last m)) (liftTerm a)).Realize v (Fin.snoc xs q)) := by
  simp only [forcesDef_imp, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_pairMemDef, CompilerParams.lift, Term.realize_var, Sum.elim_inr,
    Function.comp_apply, Fin.snoc_last, realize_liftTerm]

/-- **The universal guard.** The bound name code is recognized, and the extended assignment is
certified as `⟨c, a⟩` — new entry outermost, matching `assignmentCode`'s reversed-snoc law.
Swapping the pair's components would compile. -/
theorem realize_forcesDef_all {φ : memLang.BoundedFormula (Fin k) (sn + 1)} :
    (forcesDef rec φ.all Γ p a).Realize v xs ↔
      ∀ c : ↥M, rec.Realize (fun i ↦ Sum.elim v xs (Γ.recParams i)) ![c] →
        ∀ a' : ↥M, ((a' : ↥M) : ZFSet.{u}) = ZFSet.pair ((c : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) →
          (forcesDef rec φ Γ.lift.lift (liftTerm (liftTerm p))
            (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs c) a') := by
  simp only [forcesDef_all, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_pairDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]
  exact forall_congr' fun c ↦ imp_congr_left (realize_relabel_snoc rec Γ.recParams c)

/-- **The equality case.** Both source variables are looked up in the coded assignment, and the
uniform `forcesEqDef` — never the pair-relative `…DefOn A` layer — is applied to the results. -/
theorem realize_forcesDef_equal {t₁ t₂ : memLang.Term (Fin k ⊕ Fin sn)}
    (hm : ((Term.realize (Sum.elim v xs) Γ.tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) Γ.tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesDef rec (.equal t₁ t₂) Γ p a).Realize v xs ↔
      ∃ x y : ↥M,
        LookupAt (srcPeel t₁) ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u})
            ((x : ↥M) : ZFSet.{u}) ∧
        LookupAt (srcPeel t₂) ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u})
            ((y : ↥M) : ZFSet.{u}) ∧
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
            entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
  have hatom : ∀ x y : ↥M,
      (forcesEqDef Γ.lift.lift.tagMem Γ.lift.lift.tagEq Γ.lift.lift.condSet
        Γ.lift.lift.orderCode (liftTerm (liftTerm p))
        (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1)))).Realize v
          (Fin.snoc (Fin.snoc xs x) y) ↔
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
            entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
    intro x y
    rw [realize_forcesEqDef (by simpa [CompilerParams.lift, realize_liftTerm] using hm)
      (by simpa [CompilerParams.lift, realize_liftTerm] using hq)]
    simp [CompilerParams.lift, realize_liftTerm]
  simp only [forcesDef_equal, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_lookupDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]
  exact exists_congr fun x ↦ exists_congr fun y ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ hatom x y

/-- **The membership case.** Same shape, with `forcesMemDef` — density of the membership slice. -/
theorem realize_forcesDef_rel {ts : Fin 2 → memLang.Term (Fin k ⊕ Fin sn)}
    (hm : ((Term.realize (Sum.elim v xs) Γ.tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) Γ.tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesDef rec (.rel .mem ts) Γ p a).Realize v xs ↔
      ∃ x y : ↥M,
        LookupAt (srcPeel (ts 0)) ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u})
            ((x : ↥M) : ZFSet.{u}) ∧
        LookupAt (srcPeel (ts 1)) ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u})
            ((y : ↥M) : ZFSet.{u}) ∧
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
            DenseMem ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((R : ↥M) : ZFSet.{u}) ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) := by
  have hatom : ∀ x y : ↥M,
      (forcesMemDef Γ.lift.lift.tagMem Γ.lift.lift.tagEq Γ.lift.lift.condSet
        Γ.lift.lift.orderCode (liftTerm (liftTerm p))
        (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1)))).Realize v
          (Fin.snoc (Fin.snoc xs x) y) ↔
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
            DenseMem ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((R : ↥M) : ZFSet.{u}) ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) := by
    intro x y
    rw [realize_forcesMemDef (by simpa [CompilerParams.lift, realize_liftTerm] using hm)
      (by simpa [CompilerParams.lift, realize_liftTerm] using hq)]
    simp [CompilerParams.lift, realize_liftTerm]
  simp only [forcesDef_rel, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    realize_lookupDef, Term.realize_var, Sum.elim_inr, Function.comp_apply, Fin.snoc_last,
    Fin.snoc_castSucc, realize_liftTerm]
  exact exists_congr fun x ↦ exists_congr fun y ↦
    and_congr_right fun _ ↦ and_congr_right fun _ ↦ hatom x y

/-! ### Against a genuine name family

The guards above are stated for an arbitrary carrier element in the assignment position. These
specialize them to a real coded assignment and a real recognizer, which is where an off-by-one or
a swapped pair would actually show. -/

section Names

variable {α : Type v} {k arity sn m : ℕ} {M : MaterialCarrier.{u}} {P : Type u}
variable {N : InternalNamePresentation M P}
variable {rec : memLang.BoundedFormula (Fin arity) 1}
variable {Γ : CompilerParams α arity m} {p a : memLang.Term (α ⊕ Fin m)}
variable {v : α → M} {xs : Fin m → M}

/-- **The orientation guard, at the equality case.** Read against a genuine coded assignment,
the two lookups name exactly the codes of `asg (srcIndex t₁)` and `asg (srcIndex t₂)`.

`srcIndex` places free variables before bound ones and `assignmentCode` is reversed, so the peel
`k + sn - 1 - i` is forced: any other index arithmetic makes this unprovable. -/
theorem realize_forcesDef_equal_of_assignmentCode {t₁ t₂ : memLang.Term (Fin k ⊕ Fin sn)}
    (asg : Fin (k + sn) → N.Code)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) = N.assignmentCode asg)
    (hm : ((Term.realize (Sum.elim v xs) Γ.tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) Γ.tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesDef rec (.equal t₁ t₂) Γ p a).Realize v xs ↔
      ∃ x y : ↥M,
        ((x : ↥M) : ZFSet.{u}) = N.code (asg (srcIndex t₁)) ∧
        ((y : ↥M) : ZFSet.{u}) = N.code (asg (srcIndex t₂)) ∧
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
            entry eqTag ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) ∈ ((R : ↥M) : ZFSet.{u}) := by
  rw [realize_forcesDef_equal hm hq]
  exact exists_congr fun x ↦ exists_congr fun y ↦
    and_congr (ha ▸ lookupAt_assignmentCode_iff asg (srcIndex t₁) _)
      (and_congr_left fun _ ↦ ha ▸ lookupAt_assignmentCode_iff asg (srcIndex t₂) _)

/-- **The orientation guard, at the membership case.** -/
theorem realize_forcesDef_rel_of_assignmentCode {ts : Fin 2 → memLang.Term (Fin k ⊕ Fin sn)}
    (asg : Fin (k + sn) → N.Code)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) = N.assignmentCode asg)
    (hm : ((Term.realize (Sum.elim v xs) Γ.tagMem : ↥M) : ZFSet.{u}) = natCode memWitnessTag)
    (hq : ((Term.realize (Sum.elim v xs) Γ.tagEq : ↥M) : ZFSet.{u}) = natCode eqTag) :
    (forcesDef rec (.rel .mem ts) Γ p a).Realize v xs ↔
      ∃ x y : ↥M,
        ((x : ↥M) : ZFSet.{u}) = N.code (asg (srcIndex (ts 0))) ∧
        ((y : ↥M) : ZFSet.{u}) = N.code (asg (srcIndex (ts 1))) ∧
        ∃ A : ↥M, ((A : ↥M) : ZFSet.{u}).IsTransitive ∧
          ((x : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ((y : ↥M) : ZFSet.{u}) ∈ ((A : ↥M) : ZFSet.{u}) ∧
          ∃ R : ↥M, AtomicCoherentOn ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((A : ↥M) : ZFSet.{u}) ((R : ↥M) : ZFSet.{u}) ∧
            DenseMem ((Term.realize (Sum.elim v xs) Γ.condSet : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) Γ.orderCode : ↥M) : ZFSet.{u})
              ((R : ↥M) : ZFSet.{u}) ((Term.realize (Sum.elim v xs) p : ↥M) : ZFSet.{u})
              ((x : ↥M) : ZFSet.{u}) ((y : ↥M) : ZFSet.{u}) := by
  rw [realize_forcesDef_rel hm hq]
  exact exists_congr fun x ↦ exists_congr fun y ↦
    and_congr (ha ▸ lookupAt_assignmentCode_iff asg (srcIndex (ts 0)) _)
      (and_congr_left fun _ ↦ ha ▸ lookupAt_assignmentCode_iff asg (srcIndex (ts 1)) _)

/-- **The recognition pressure test.** Compiled against a supplied recognizer whose parameters
sit where `Γ.recParams` says, the universal case quantifies over exactly the codes of the name
family — the `∃ i : N.Code` that correctness will need in order to apply `N.decode`. -/
theorem realize_forcesDef_all_recognition (R : InternalNameRecognition N)
    {Γ : CompilerParams α R.arity m} {φ : memLang.BoundedFormula (Fin k) (sn + 1)}
    (hparams : ∀ i, Sum.elim v xs (Γ.recParams i) = R.params i) :
    (forcesDef R.formula φ.all Γ p a).Realize v xs ↔
      ∀ c : ↥M, (∃ i : N.Code, ((c : ↥M) : ZFSet.{u}) = N.code i) →
        ∀ a' : ↥M, ((a' : ↥M) : ZFSet.{u}) = ZFSet.pair ((c : ↥M) : ZFSet.{u})
              ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) →
          (forcesDef R.formula φ Γ.lift.lift (liftTerm (liftTerm p))
            (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs c) a') := by
  have hfun : (fun i ↦ Sum.elim v xs (Γ.recParams i)) = R.params := funext hparams
  rw [realize_forcesDef_all]
  exact forall_congr' fun c ↦ imp_congr_left (by rw [hfun]; exact R.realize_iff c)

/-- **The extension guard, against a genuine coded assignment.** The `a'` the compiler admits at
`.all` is exactly the code of the extended assignment `Fin.snoc asg i` — the new name last in the
`Fin.snoc`, hence outermost in the code, hence at peel zero for the newly bound variable.

Swapping the pair's components, or extending at the wrong end, breaks this and nothing else. Note
the arities line up definitionally: the source arity goes `sn ↦ sn + 1` while the combined arity
goes `k + sn ↦ k + (sn + 1)`, and `k + (sn + 1)` is `(k + sn) + 1`. -/
theorem realize_forcesDef_all_of_assignmentCode {ℓ : ℕ} (R : InternalNameRecognition N)
    {Γ : CompilerParams α R.arity m} {φ : memLang.BoundedFormula (Fin k) (sn + 1)}
    (asg : Fin ℓ → N.Code)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) = N.assignmentCode asg)
    (hparams : ∀ i, Sum.elim v xs (Γ.recParams i) = R.params i) :
    (forcesDef R.formula φ.all Γ p a).Realize v xs ↔
      ∀ (i : N.Code) (c a' : ↥M), ((c : ↥M) : ZFSet.{u}) = N.code i →
        ((a' : ↥M) : ZFSet.{u}) = N.assignmentCode (Fin.snoc asg i) →
          (forcesDef R.formula φ Γ.lift.lift (liftTerm (liftTerm p))
            (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs c) a') := by
  rw [realize_forcesDef_all_recognition R hparams]
  constructor
  · intro h i c a' hc ha'
    refine h c ⟨i, hc⟩ a' ?_
    rw [ha', InternalNamePresentation.assignmentCode_snoc, hc, ha]
  · rintro h c ⟨i, hc⟩ a' hpair
    refine h i c a' hc ?_
    rw [InternalNamePresentation.assignmentCode_snoc, ← hc, ← ha, hpair]

/-- **The combined arity, checked.** The same law with the assignment's arity pinned to `k + sn`,
producing the extended assignment at the type the recursive call's own guards consume: source
arity `sn + 1` means combined arity `k + (sn + 1)`.

`Fin.snoc asg i` has type `Fin ((k + sn) + 1) → N.Code`, so the binder for `asg'` typechecks only
because `k + (sn + 1)` and `(k + sn) + 1` are definitionally equal. That is the alignment the
module docstring claims, now checked by Lean rather than asserted in prose. -/
theorem realize_forcesDef_all_of_assignmentCode_arity (R : InternalNameRecognition N)
    {Γ : CompilerParams α R.arity m} {φ : memLang.BoundedFormula (Fin k) (sn + 1)}
    (asg : Fin (k + sn) → N.Code)
    (ha : ((Term.realize (Sum.elim v xs) a : ↥M) : ZFSet.{u}) = N.assignmentCode asg)
    (hparams : ∀ i, Sum.elim v xs (Γ.recParams i) = R.params i) :
    (forcesDef R.formula φ.all Γ p a).Realize v xs ↔
      ∀ (i : N.Code) (asg' : Fin (k + (sn + 1)) → N.Code), asg' = Fin.snoc asg i →
        ∀ c a' : ↥M, ((c : ↥M) : ZFSet.{u}) = N.code i →
          ((a' : ↥M) : ZFSet.{u}) = N.assignmentCode asg' →
            (forcesDef R.formula φ Γ.lift.lift (liftTerm (liftTerm p))
              (&(Fin.last (m + 1)))).Realize v (Fin.snoc (Fin.snoc xs c) a') := by
  rw [realize_forcesDef_all_of_assignmentCode R asg ha hparams]
  constructor
  · rintro h i asg' rfl c a' hc ha'
    exact h i c a' hc ha'
  · intro h i c a' hc ha'
    exact h i (Fin.snoc asg i) rfl c a' hc ha'

end Names

end Guards

end Forcing
