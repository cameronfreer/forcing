/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Forcing.Cohen.NewReal

/-!
# The headline axiom audit

Makes the README's trust claim executable for the declarations readers actually ask about:
each **headline declaration** must depend only on the three standard axioms. The audit runs
at every build of this module (an `#eval` that throws fails elaboration, hence the build and
CI), so the policy — "project policy forbids `sorry` and custom axioms" — is enforced rather
than stated for the headlines.

Scope discipline (from the audit's design review): a short named list of headline
declarations, extended at each milestone close — **not** a library-wide sweep, no counts, no
generated status artifact. The list and the allowlist live here and nowhere else.
-/

open Lean

namespace Forcing

/-- The allowlist: exactly the three standard axioms. -/
def axiomAllowlist : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The audited headline declarations. Extend at each milestone close. -/
def auditedHeadlines : List Name :=
  [``Forcing.Cohen.addsNewReal]

set_option linter.hashCommand false in
open Elab Command in
#eval show CommandElabM Unit from do
  for decl in auditedHeadlines do
    let axs ← collectAxioms decl
    for a in axs do
      unless axiomAllowlist.contains a do
        throwError "Axiom audit failed: {decl} depends on non-allowlisted axiom {a}"

end Forcing
