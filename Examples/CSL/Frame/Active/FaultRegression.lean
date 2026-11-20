/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Owned
public import Examples.Scheduling
public import Examples.CSL.Frame.Shared

/-!
# Active separation: fault regression

A write outside the writer's reservation gets stuck in the original runner, and the admission
condition already rejects it (← `examples/CSL/Frame/Active.v`, module `FaultRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.FaultRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm CoCSL Examples.Scheduling
open Examples.CSL.Frame.Shared

theorem invalid_write_stuck :
    finish_sample (@log_payload (CSLObs (Nat × Nat))) 1000 []
      (interp_schedule_nd sh 2 #v[denote (.write 1 4), denote (.ret ())] (some 0)
        (region 2 5, ([], 0))) = none := by
  have hs : schedule 2 #v[denote (.write 1 4), denote (.ret ())] (some 0) =
      .vis (.inl (.inl (.write 1 4))) fun x =>
        schedule 2 (#v[denote (.write 1 4), denote (.ret ())].set 0 (pure ⟨⟩)) (some 0) :=
    unfold_inj (by
      rw [schedule_focused_user_event 1 _ 0 (E := sE) (.inl (.write 1 4)) (fun _ => pure ⟨⟩)
        (by simp only [denote, source_raw_write_head]; rfl), unfold_vis]; rfl)
  have ht : interp_schedule_nd sh 2 #v[denote (.write 1 4), denote (.ret ())] (some 0)
      ((region 2 5 : ManagedHeap), (([] : Ctx), 0)) = .stuck := by
    simp only [interp_schedule_nd, hs, project_scheduled_user, interp_state_vis, sh, h_sum]
    rw [heap_handlerW_wr_none _ 1 _ _ _ 4 (by simp [region, hsingle]), stuck_bind]
  rw [ht]; rfl

theorem invalid_write_not_admissible :
    ¬ admissible (.write 1 4) (.ret ()) managed_empty (region 2 5) [] 0 := by
  rintro ⟨-, -, -, -, -, HC, -⟩
  have Hlocal : confined managed_empty (init_local .child (.write 1 4) managed_empty [] 0 false) :=
    confined_equ _ _ _ (project_init_child _ _ _ _ _ _) HC
  have Hselect : Star owned_next (init_local .child (.write 1 4) managed_empty [] 0 false)
      (init_local .child (.write 1 4) managed_empty [] 0 true) :=
    .single ⟨act .child .select, (init_local_select _ _ _ _ _ _ _).2 ⟨rfl, rfl⟩⟩
  exact Hlocal _ Hselect (denote (.write 1 4)) .child (.inl (.write 1 4)) (fun _ => pure ⟨⟩) rfl
    ⟨0, source_raw_write_head _ _ _⟩ rfl

end Examples.CSL.Frame.Active.FaultRegression
