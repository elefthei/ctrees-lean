/- SPDX-License-Identifier: MIT -/
module

import Logic
import Lang

namespace Test.Logic
open Tisl Tisl.Notation
open ITree (Effect)

/-! Phase 1: generic logic on a toy Kripke structure without transitions -/

/-- Models that never step. -/
def Toy (_ _ : Effect.{0}) (X : Type) : Type := X

instance {E B : Effect.{0}} : Kripke Toy E B := ⟨fun _ _ _ _ => False, False.elim⟩

variable {E B : Effect.{0}} (t : Toy E B Nat) (w : World E)

example : ¬ entails (⊥ : TiclL E) t w := ticll_sound

example (p q : World E → Prop) :
    entails (.now p ∧ₜ .now q : TiclL E) t w ↔
      entails (.now p : TiclL E) t w ∧ entails (.now q) t w :=
  ticl_and _ _

/-- A non-stepping model satisfies no `AX`. -/
example (p : TiclL E) : ¬ entails (AX p) t w := fun ⟨_, ⟨_, _, h⟩, _⟩ => h

/-- `AF p` collapses to `p` when nothing steps. -/
example (p : TiclL E) (h : entails (AF p) t w) : entails p t w := by
  cases (h : Auc _ _ t w) with
  | matchA h => exact h
  | stepA _ hs _ => obtain ⟨_, _, h⟩ := hs; exact h.elim

/-! Phase 2: the ctree model -/
section CTreeModel
open CTree

example : entails (AX (ret= (1 : Nat) World.pure)) (CTree.step (pure 1) : CTree E B Nat) .pure :=
  an_step.2 ⟨(ticl_now _).2 ⟨trivial, .pure⟩, ret_ret .pure ⟨rfl, rfl⟩⟩

example (w : World E) : ¬ can_step (CTree.stuck : CTree E B Nat) w := can_step_stuck

end CTreeModel

/-! Phase 3: the round-robin scheduler picks slot 0 first and advances the cursor -/
section Scheduler
open CTree Tisl.Yield

example [Bn -< B] :
    (schedule_rr 2 #v[.vis (.inl ⟨⟩) fun _ => pure ⟨⟩, pure ⟨⟩] none 0 : Completed E B).unfold =
      .vis (.inr (0 : Nat)) fun _ =>
        schedule_rr 2 #v[.vis (.inl ⟨⟩) fun _ => pure ⟨⟩, pure ⟨⟩] (some 0) 1 :=
  schedule_rr_no_focus_nonempty 1 _ 0

end Scheduler

/-! Phase 5: CoCSL denotation of a pure bind -/
section CoCSL
open CTree CoCSL Tisl.CSL

example : denote_flow (.bind (.ret 1) fun x => .ret (x + 1)) =
    (pure (some 2) : CTree CEff Bn (Option Nat)) := by
  simp [denote_flow]

end CoCSL

end Test.Logic
