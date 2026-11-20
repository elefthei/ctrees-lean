/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Allocator.LivenessRanks
public import Examples.CSL.Allocator.Replay
public import Examples.CSL.Queue.Program
public import Lang.CoCSL.Sequential
public import Logic.CTree.TraceRules
public import Logic.CTree.Bind
public import Logic.CTree.Yield

/-!
# Observable heap mutations: the allocator, initialization faults and recurrence controls

The allocator probe script and its exact snapshot prefix, partial and initialization fault
prefixes, the silent out-of-space allocation, the empty-log pool, and controls separating payload
recurrence from retained observations (← `examples/CSL/Frame/HeapObservations.v`, lines
1189-1457).
-/

@[expose] public section
namespace Examples.CSL.Frame.HeapObservations
open CTree Coinduction Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open Examples.CSL.Allocator.Layout Examples.CSL.Allocator.Program Examples.CSL.Allocator.Model
open Examples.CSL.Allocator.Execution Examples.CSL.Allocator.Liveness Examples.CSL.Allocator.Replay
open Examples.CSL.Queue.Layout Examples.CSL.Queue.Program
open Actor owner_pc remote_pc

def allocator_probe_script : List Actor :=
  [Owner, Owner, Owner, Owner, Owner, Remote1, Remote1, Remote1, Remote0, Remote0,
   Remote0, Remote0, Remote1, Owner, Owner, Owner, Owner, Owner, Owner]

def allocator_probe_mutations : List (CSLObs (Nat × Nat)) :=
  write_snapshots
    [(1, 0), (3, 0), (2, 8), (4, 6), (2, 0), (5, 8), (5, 0), (9, 2), (8, 0), (4, 0),
     (7, 1), (6, 0), (1, 6), (1, 0), (3, 6), (6, 0), (2, 6), (3, 0), (2, 0), (4, 6)]
    ((initial_state 2 0).aheap, upd hemp 1 (page_size 2))

def allocator_probe_turn (i : Nat) : List (CSLObs (Nat × Nat)) :=
  (match i with
   | 1 => allocator_probe_mutations.take 2
   | 3 => (allocator_probe_mutations.drop 2).take 2
   | 4 => (allocator_probe_mutations.drop 4).take 2
   | 5 => (allocator_probe_mutations.drop 6).take 2
   | 7 => (allocator_probe_mutations.drop 8).take 1
   | 8 => (allocator_probe_mutations.drop 9).take 2
   | 10 => (allocator_probe_mutations.drop 11).take 1
   | 11 => (allocator_probe_mutations.drop 12).take 1
   | 14 => (allocator_probe_mutations.drop 13).take 2
   | 15 => (allocator_probe_mutations.drop 15).take 3
   | 17 => (allocator_probe_mutations.drop 18).take 2
   | _ => []) ++
  (match i with
   | 3 => [.emit (stamp (tag_alloc, 6) 0)]
   | 4 => [.emit (stamp (tag_alloc, 8) 1)]
   | 11 => [.emit (stamp (tag_retire, 6) 2)]
   | 12 => [.emit (stamp (tag_retry, 8) 3)]
   | 15 => [.emit (stamp (tag_reclaim, 6) 4)]
   | 17 => [.emit (stamp (tag_alloc, 6) 5)]
   | _ => [])

def allocator_probe_logs : List (CSLObs (Nat × Nat)) :=
  ((List.range' 0 19).map allocator_probe_turn).flatten

/-- The probe replays the starvation prefix turn by turn. -/
private theorem probe_turn_table : allocator_probe_turn = starve_prefix_event 0 := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18
  | _ + 19 => rfl

theorem allocator_snapshot_prefix (ctx : Ctx) :
    (new_page_logs (A := Nat × Nat) 1 2 managed_empty).length = 8 ∧
    csl_emissions allocator_probe_logs =
      [stamp (tag_alloc, 6) 0, stamp (tag_alloc, 8) 1, stamp (tag_retire, 6) 2,
       stamp (tag_retry, 8) 3, stamp (tag_reclaim, 6) 4, stamp (tag_alloc, 6) 5] ∧
    (∀ i, i < 19 → ∃ middle logs next,
      run_turns (turn 1) (fun xs => xs) (allocator_probe_script.take i) (initial_state 2 0) =
        some (middle, logs) ∧
      turn 1 (allocator_probe_script.getD i Remote1) middle =
        some (next, allocator_probe_turn i)) ∧
    (∃ last labels residual,
      run_turns (turn 1) (fun xs => xs) allocator_probe_script (initial_state 2 0) =
        some (last, allocator_probe_logs) ∧
      label_logs labels = new_page_logs 1 2 managed_empty ++ allocator_probe_logs ∧
      label_taus labels = 19 ∧
      FiniteSteps (run_nd (allocator_program 2) (managed_empty, (ctx, 0))) labels residual ∧
      residual ~ (model_nd 2 actor_of_slot (turn 1) last :
        ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro i hi
    rw [probe_turn_table]
    exact ⟨_, _, _, starve_run 0 i (Nat.le_of_lt hi), starve_cert 0 i hi⟩
  · obtain ⟨last, hrun⟩ : ∃ last, run_turns (turn 1) (fun xs => xs) allocator_probe_script
        (initial_state 2 0) = some (last, allocator_probe_logs) := by
      rw [allocator_probe_logs, probe_turn_table]
      exact ⟨_, starve_run 0 19 (Nat.le_refl _)⟩
    obtain ⟨labels, residual, -, hlogs, htaus, hsteps, hres⟩ :=
      run_turns_realizes_source 2 ctx 0 allocator_probe_script last allocator_probe_logs hrun
    exact ⟨last, labels, residual, hrun, hlogs, htaus, hsteps, hres⟩

def allocator_partial_state : AState :=
  { aheap := hsingle 4 6, aallocs := hemp, acount := 0,
    owner_state := ORead, remote0_state := RPoll, remote1_state := RPoll }

theorem allocator_partial_fault_prefix :
    instr_flow_erased (client_round 1 false) ((hsingle 4 6, hemp), ([], 0)) ~
      (log (CSLObs.heap (upd (hsingle 4 6) 4 0, hemp) : CSLObs (Nat × Nat)) >>= fun _ =>
        (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option (Option Unit) × SSig))) ∧
    turn 1 Remote0 allocator_partial_state = none := by
  refine ⟨?_, rfl⟩
  refine sbisim_trans (instr_flow_read _ 6 _ _ rfl) ?_
  refine sbisim_trans (instr_flow_write _ _ _ _ (by decide)) ?_
  exact sbisim_bind_eq _ fun _ => instr_flow_write_missing _ _ _ _ rfl

theorem initialization_fault_prefix (ctx : Ctx) (c : Nat) :
    run_rr (.bind (new_queue [10, 20]) fun _ => .bind (.read 100) fun _ => .ret ())
        (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 [10, 20] managed_empty).map Sum.inl)
        (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_unfold]
  refine sbisim_trans (equ_sbisim _ _ (interp_rr_bind 0 #v[pure ⟨⟩] 0 (new_queue [10, 20])
    (fun _ => .bind (.read 100) fun _ => .ret ()) (fun _ => pure ⟨⟩) 0 _)) ?_
  refine sbisim_trans (interp_rr_new_queue_empty 0 _ 0 [10, 20] _ 0 ctx c) (emit_list_sbisim _ ?_)
  refine sbisim_trans (equ_sbisim _ _ (interp_rr_bind 0 _ 0 (.read 100) (fun _ => .ret ())
    (fun _ => pure ⟨⟩) 0 _)) ?_
  exact interp_rr_read_missing 0 _ 0 100 _ 0 _ _ ctx c rfl

theorem allocation_no_space_silent (ctx : Ctx) (c : Nat) :
    instr_flow_erased (.bind (.alloc 1) fun _ => .ret ()) ((fun _ => some 0, hemp), (ctx, c)) ~
      (CTree.spin : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) :=
  instr_flow_alloc_no_space 1 _ _ (by decide) fun _ _ H => nomatch H 0 (by decide)

def empty_log_thread : Thread sE Bn :=
  .vis (.inl ⟨⟩) fun _ => .guard empty_log_thread
partial_fixpoint

theorem empty_log_thread_unfold :
    empty_log_thread = .vis (.inl ⟨⟩) fun _ => .guard empty_log_thread := by
  rw (occs := .pos [1]) [empty_log_thread]

theorem empty_log_closed_turns :
    ClosedTurns sh #v[empty_log_thread] (fun (_ : Unit) (_ : SSig) => True) := by
  intro _ σ i _
  obtain rfl := fin1_eq i
  exact ⟨(), σ, [], ⟨.guard empty_log_thread,
    .equ empty_log_thread_unfold (.yield _ σ) rfl,
    guard_equ_left _ _ (guard_equ_equ _ _ rfl)⟩, trivial⟩

theorem empty_log_pool_invariance_nd_rr (s : SSig) (focus : Option (Fin 1)) (cursor : Nat)
    (w : World (writerE (CSLObs (Nat × Nat)))) (wr : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    NotDone w → NotDone wr →
      entails (AG ⊤) (interp_schedule_nd sh 1 #v[empty_log_thread] focus s) w ∧
      entails (AG ⊤) (interp_schedule_rr sh 1 #v[empty_log_thread] focus cursor s) wr := by
  intro hw hwr
  exact ⟨ag_pool_nd_invariance sh #v[empty_log_thread] _ ⊤ empty_log_closed_turns
      (fun _ _ _ hv _ => ticll_top hv) (fun _ _ _ _ _ hv => ticll_top hv) () s focus w trivial hw,
    ag_pool_rr_invariance sh #v[empty_log_thread] _ ⊤ empty_log_closed_turns
      (fun _ _ _ hv _ => ticll_top hv) (fun _ _ _ _ _ _ hv => ticll_top hv) () s focus cursor wr
      trivial hwr⟩

/-! ## Controls separating payload recurrence from retained observations -/

namespace EventRecurrenceControls

def repeat_emit_7 : ctreeW Nat Bn PUnit :=
  emit_batches (fun _ : PUnit => [7]) (fun x => x) ⟨⟩

def once_then_silent : ctreeW Nat Bn PUnit :=
  log 7 >>= fun _ => CTree.spinS

def emit_or_silent : ctreeW Nat Bn PUnit :=
  CTree.brSn 2 fun i => #v[repeat_emit_7, CTree.spinS][i]

/-- Labels logging the payload `7`. -/
def L : Label (writerE Nat) → Prop :=
  log_label (fun n : Nat => n = 7)

theorem repeat_plain_payload_recurrent : RecurrentLabel L repeat_emit_7 := by
  have eloop : repeat_emit_7 ~ (CTree.vis (E := writerE Nat) (7 : Nat) fun _ => repeat_emit_7) := by
    have h := emit_batches_unfold_sbisim (B := Bn) (X := PUnit) (fun _ : PUnit => [(7 : Nat)])
      (fun x => x) ⟨⟩
    simp only [emit_list_cons] at h
    exact h
  refine coinduction₁ (b := recurrentLabelF L)
    (ι := {t : ctreeW Nat Bn PUnit // t ~ repeat_emit_7}) (fun t => t.1) ?_
    ⟨repeat_emit_7, sbisim_refl _⟩
  rintro R - cih ⟨t, et⟩
  have evis := sbisim_trans et eloop
  refine ⟨eventually_label_sbisim L
    (CTree.vis (E := writerE Nat) (7 : Nat) fun _ => repeat_emit_7) t
    (sbisim_symm evis) ?_, fun l u tr => ?_⟩
  · exact eventually_label_intro ⟨_, _, trans_vis (E := writerE Nat) (B := Bn) (e := (7 : Nat))
      PUnit.unit fun _ => repeat_emit_7⟩ fun l u tr => by
      obtain ⟨_, -, rfl⟩ := trans_vis_inv tr
      exact .inl rfl
  · obtain ⟨_, u', tr', eu, rfl⟩ := (sbisim_unfold.1 evis).1 _ _ tr
    obtain ⟨_, rfl, rfl⟩ := trans_vis_inv tr'
    exact cih ⟨u, eu⟩

private theorem spinS_not_recurrent :
    ¬ RecurrentLabel L (CTree.spinS : ctreeW Nat Bn PUnit) := by
  intro h
  have key : ∀ t : ctreeW Nat Bn PUnit, EventuallyLabel L t → t = CTree.spinS → False := by
    intro t he
    induction he with
    | intro _ _ ih =>
      rintro rfl
      have tr := trans_step (CTree.spinS : ctreeW Nat Bn PUnit)
      rw [← unfold_spinS] at tr
      exact ih .tau _ tr id rfl
  exact key _ (recurrent_label_unfold.1 h).1 rfl

theorem retained_payload_not_recurrent :
    entails (AG (AF (visWₜ fun n : Nat => n = 7))) once_then_silent .pure ∧
    ¬ RecurrentLabel L once_then_silent := by
  refine ⟨ag_log_iff.2 ⟨af_log .pure (.matchA ((ticl_vis _).2 (.obs _ _ rfl))), ?_⟩, ?_⟩
  · refine coinduction (b := agcF (entails (AF (visWₜ fun n : Nat => n = 7))))
      (ι := Unit) (fun _ => (CTree.spinS : ctreeW Nat Bn PUnit))
      (fun _ => .obs (E := writerE Nat) (7 : Nat) ⟨⟩) ?_ ()
    rintro R - cih -
    refine ⟨.matchA ((ticl_vis _).2 (.obs _ _ rfl)),
      by rw [unfold_spinS]; exact can_step_step.2 (.obs _ _), ?_⟩
    intro t' w' tr
    rw [unfold_spinS] at tr
    obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
    exact cih ()
  · intro h
    refine spinS_not_recurrent
      ((recurrent_label_unfold.1 h).2 (.obs (E := writerE Nat) (7 : Nat) ⟨⟩) _ ?_)
    simp only [once_then_silent, log, vis_bind, pure_bind']
    exact trans_vis _ _

theorem universal_recurrence_rejects_silent_branch : ¬ RecurrentLabel L emit_or_silent :=
  fun h => spinS_not_recurrent ((recurrent_label_unfold.1 h).2 .tau _
    (trans_brS' (B₁ := Bn) (c := ⟨2⟩)
      (k := fun x : ULift (Fin 2) => #v[repeat_emit_7, CTree.spinS][x.down]) ⟨1⟩))

theorem event_recurrence_rejects_return :
    ¬ RecurrentLabel L (pure ⟨⟩ : ctreeW Nat Bn PUnit) := by
  intro h
  obtain ⟨he, -⟩ :=
    recurrent_label_unfold.1 ((recurrent_label_unfold.1 h).2 _ _ (trans_ret PUnit.unit))
  obtain ⟨hcan, -⟩ := he
  obtain ⟨_, _, tr⟩ := hcan
  exact trans_stuck_inv tr

end EventRecurrenceControls

end Examples.CSL.Frame.HeapObservations

-- Not ported: `allocator_probe_snapshots` (redundant with `CoCSL.write_snapshots`).
