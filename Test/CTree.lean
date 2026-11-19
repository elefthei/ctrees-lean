/- SPDX-License-Identifier: MIT -/
module

import CTree

namespace Test
open CTree
open ITree (Effect)

variable {E B : Effect.{0}} {R : Type}

/-! Phase 1: core definitions -/

example (k : Nat → CTree E B Nat) : ((.stuck : CTree E B Nat) >>= k) = .stuck := by simp

example : (CTree.step (pure 1) >>= fun x => pure (x + 1) : CTree E B Nat) = .step (pure 2) := by
  simp

example : CTree.spin ≠ (CTree.spinS : CTree E B Nat) := by
  intro h
  have := congrArg CTree.unfold h
  rw [unfold_spin, unfold_spinS] at this
  simp at this

end Test
