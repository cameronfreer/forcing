/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Basic

/-!
# Forcing

Placeholder file confirming that the project builds against mathlib.
-/

example {α : Type*} [PartialOrder α] {a b : α} (h : a < b) : a ≤ b := h.le
