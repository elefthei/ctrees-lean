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
open Coinduction

def constB (p : Prop) : Mon (Rel Nat Nat) := ⟨fun _ _ _ => p, fun _ _ _ h => h⟩

example (x y : Nat) : gfp (constB True) x y := by
  coinduction _ _ _
  trivial

example (x y : Nat) : ¬ gfp (constB False) x y := fun h => gfp_pfp (b := constB False) _ _ h

end Tower

/-! Phase 3: structural equality and the LTS -/

example (t u : CTree E B02 Nat) : trans .tau (CTree.brS2 t u) u := trans_brS2_r

example (x : Nat) : wtrans (.val x) (CTree.guard (CTree.step (pure x)) : CTree E B Nat) .stuck :=
  wcons (trans_guard (trans_step _)) (trans_wtrans (trans_ret x))

example : trans (.val 2) ((pure 1 : CTree E B Nat) >>= fun x => pure (x + 1)) .stuck :=
  trans_bind_r (trans_ret 1) (trans_ret 2)

example : isStuck (CTree.spin : CTree E B Nat) := spin_isStuck

example (l : Label E) (u : CTree E B Nat) (h : trans l (pure 3) u) : l = .val 3 :=
  (trans_ret_inv h).2

/-! Phases 4-5: simulations, bisimulations, traces, heads -/

example : (CTree.guard (pure 1) : CTree E B Nat) ~ (pure 1 : CTree E B Nat) := sb_guard _

example : (CTree.step (CTree.guard (pure 1)) : CTree E B Nat) ≈ pure 1 :=
  wbisim_trans (step_wb _) (guard_wb _)

example : traceq (CTree.guard (pure 1) : CTree E B Nat) (pure 1 : CTree E B Nat) :=
  sbisim_traceq (sb_guard _)

example : isPure (pure 1 : CTree E B Nat) := isPure_ret 1

example (t : CTree E B Nat) : t = head t >>= runHAction := get_run_haction t

example (u : CTree E B Nat) (h : trans .tau (CTree.step u) u) :
    trans (.val (HAction.step u)) (head (CTree.step u) : CTree E B (HAction E B Nat)) .stuck :=
  trans_head_tau h

/-! Phase 6: interpreters -/

example (h : (e : E.I) → CTree E B (E.O e)) (t : CTree E B Nat) (k : Nat → CTree E B Nat) :
    interp h (t >>= k) = interp h t >>= fun x => interp h (k x) := interp_bind h t k

example (h : (e : E.I) → StateT Nat (CTree E B) (E.O e)) :
    interp_state h (pure 1 : CTree E B Nat) 5 = (pure (1, 5) : CTree E B (Nat × Nat)) := by simp

example : CTree.burn 2 (CTree.guard (CTree.step (pure 1)) : CTree E B Nat) = pure 1 := by
  simp [CTree.burn]

end Test
