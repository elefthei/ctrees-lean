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

/-! Phase 2: coinduction tower -/

section Tower
open CTree.Coinduction

def constB (p : Prop) : Mon (Rel Nat Nat) := ⟨fun _ _ _ => p, fun _ _ _ h => h⟩

example (x y : Nat) : gfp (constB True) x y :=
  coinduction (b := constB True) (fun _ : Unit => x) (fun _ => y) (fun _ _ _ _ => trivial) ()

example (x y : Nat) : ¬ gfp (constB False) x y := fun h => gfp_pfp (b := constB False) _ _ h

end Tower

end Test
