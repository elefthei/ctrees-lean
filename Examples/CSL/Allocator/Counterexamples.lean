/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Allocator.LivenessRanks
public import Examples.CSL.Allocator.Replay

/-!
# Constructive counterexamples for the allocator's liveness premises

Two infinite executions of the actual model, each realized by the actual source program:
`fair_starvation_exists` (fair choices under which remote 1 holds block 8 forever and retries its
CAS infinitely often while block 6 cycles through retire, reclaim and allocation) and
`owner_stall_prevents_reclamation` (after turn 5 the owner is never selected, so block 6, retired
at turn 8, is never reclaimed) (← `examples/CSL/Allocator/Counterexamples.v`).

The periodic heaps are pointwise representatives only; every execution state is the actual result
of its preceding turns, never a reset.
-/

@[expose] public section
namespace Examples.CSL.Allocator.Counterexamples
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Allocator.Layout Examples.CSL.Allocator.Program Examples.CSL.Allocator.Model
open Examples.CSL.Allocator.Execution Examples.CSL.Allocator.Liveness Examples.CSL.Allocator.Replay
open Actor owner_pc remote_pc

/-- Snapshot slices carry no user emission. -/
private theorem slice_emissions (ws : List (Nat × Nat)) (memory : ManagedHeap)
    (start count : Nat) (rest : List (CSLObs (Nat × Nat))) :
    csl_emissions (snapshot_slice (write_snapshots ws memory) start count ++ rest) =
      csl_emissions rest := by
  obtain ⟨heaps, e⟩ := write_snapshots_heaps (A := Nat × Nat) ws memory
  rw [snapshot_slice, e, ← List.map_drop, ← List.map_take, csl_emissions_heap_prefix]

section Starvation

private theorem starve_prefix_run (c : Nat) : ∃ last,
    run_turns (turn 1) (fun xs => xs) starvation_prefix (initial_state 2 c) =
      some (last, starve_prefix_logs c) ∧
    state_equiv last (starve_boundary (6 + c)) := by
  refine ⟨_, starve_run c 19 (Nat.le_refl _), fun x => ?_, fun _ => rfl,
    show c + 1 + 1 + 1 + 1 + 1 + 1 = 6 + c by omega, rfl, rfl, rfl⟩
  match x with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | x + 10 => rfl

private theorem starve_cycle_run (c : Nat) : ∃ last,
    run_turns (turn 1) (fun xs => xs) starvation_cycle (starve_boundary c) =
      some (last, starve_cycle_logs c) ∧
    state_equiv last (starve_boundary (4 + c)) := by
  refine ⟨_, cycle_run c 13 (Nat.le_refl _), fun x => ?_, fun _ => rfl,
    show c + 1 + 1 + 1 + 1 = 4 + c by omega, rfl, rfl, rfl⟩
  match x with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | x + 10 => rfl

private theorem starve_cycle_run_actual (c : Nat) (s : AState) :
    state_equiv s (starve_boundary c) →
    ∃ last, run_turns (turn 1) (fun xs => xs) starvation_cycle s =
        some (last, starve_cycle_logs c) ∧
      state_equiv last (starve_boundary (4 + c)) := by
  intro hs
  obtain ⟨last, hrun, hlast⟩ := starve_cycle_run c
  obtain ⟨actual, hactual, heq⟩ := run_turns_some_compatible (turn 1) (fun xs => xs)
    state_equiv (turn_proper 1) starvation_cycle (starve_boundary c) s last _
    (state_equiv_sym _ _ hs) hrun
  exact ⟨actual, hactual, state_equiv_trans _ _ _ (state_equiv_sym _ _ heq) hlast⟩

private theorem starve_prefix_position (c i : Nat) : i < 19 →
    ∃ middle logs next,
      run_turns (turn 1) (fun xs => xs) (starvation_prefix.take i) (initial_state 2 c) =
        some (middle, logs) ∧
      turn 1 (starvation_prefix.getD i Remote1) middle = some (next, starve_prefix_event c i) :=
  fun hi => ⟨_, _, _, starve_run c i (Nat.le_of_lt hi), starve_cert c i hi⟩

private theorem starve_cycle_position (c i : Nat) : i < 13 →
    ∃ middle logs next,
      run_turns (turn 1) (fun xs => xs) (starvation_cycle.take i) (starve_boundary c) =
        some (middle, logs) ∧
      held middle.remote1_state = [8] ∧
      turn 1 (starvation_cycle.getD i Remote1) middle = some (next, starve_cycle_event c i) :=
  fun hi => ⟨_, _, _, cycle_run c i (Nat.le_of_lt hi), cycle_held c i hi, cycle_cert c i hi⟩

/-- The infinite execution follows the periodic script from the actual initial state. -/
private def starvation_choices : Nat → Actor :=
  periodic_choices starvation_prefix Remote1 starvation_cycle.tail

private def starvation_execution : Execution AState Actor (List (CSLObs (Nat × Nat))) :=
  allocator_execution 2 0 starvation_choices

private theorem starvation_execution_valid : allocator_valid 2 0 starvation_execution :=
  allocator_execution_valid 2 0 _

private theorem starve_prefix_script :
    (List.range' 0 starvation_prefix.length).map starvation_execution.selected =
      starvation_prefix :=
  periodic_prefix_script _ _ _

private theorem starve_selected_cycle (n i : Nat) : i < 13 →
    starvation_execution.selected (19 + 13 * n + i) = starvation_cycle.getD i Remote1 := by
  intro hi
  have := periodic_choices_round starvation_prefix Remote1 starvation_cycle.tail n i hi
  rwa [show starvation_prefix.length + n * (starvation_cycle.tail.length + 1) + i =
    19 + 13 * n + i by simp [starvation_prefix, starvation_cycle]; omega] at this

private theorem starve_cycle_script (n : Nat) :
    (List.range' (19 + 13 * n) starvation_cycle.length).map starvation_execution.selected =
      starvation_cycle :=
  map_seq_eq _ _ _ _ Remote1 rfl fun i hi => starve_selected_cycle n i hi

private theorem starve_initial_equiv :
    state_equiv (starvation_execution.states 0) (initial_state 2 0) := by
  rw [starvation_execution_valid.1]; exact state_equiv_refl _

private theorem starve_boundaries (n : Nat) :
    state_equiv (starvation_execution.states (19 + 13 * n)) (starve_boundary (6 + 4 * n)) := by
  have hcycles := execution_script_cycles (turn 1) (fun xs => xs)
    (fun s => s = initial_state 2 0) state_equiv (turn_proper 1) starvation_execution
    starvation_prefix starvation_cycle starve_boundary 6 (Nat.add 4) (initial_state 2 0)
    state_equiv_equivalence starvation_execution_valid starve_initial_equiv starve_prefix_script
    (by obtain ⟨last, hrun, hlast⟩ := starve_prefix_run 0; exact ⟨last, _, hrun, hlast⟩)
    (fun k => by
      rw [show starvation_prefix.length + k * starvation_cycle.length = 19 + 13 * k by
        simp [starvation_prefix, starvation_cycle]; omega]
      exact starve_cycle_script k)
    (fun c => by obtain ⟨last, hrun, hlast⟩ := starve_cycle_run c; exact ⟨last, _, hrun, hlast⟩) n
  rwa [nat_iter_add_const, show starvation_prefix.length + n * starvation_cycle.length =
    19 + 13 * n by simp [starvation_prefix, starvation_cycle]; omega,
    show n * 4 + 6 = 6 + 4 * n by omega] at hcycles

private theorem starve_cycle_emitted (n i : Nat) : i < 13 →
    starvation_execution.emitted (19 + 13 * n + i) = starve_cycle_event (6 + 4 * n) i := by
  intro hi
  obtain ⟨middle, logs, next, hrun, -, hturn⟩ := starve_cycle_position (6 + 4 * n) i hi
  exact (execution_script_emitted (turn 1) (fun xs => xs) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) starvation_execution (19 + 13 * n) starvation_cycle i Remote1
    (starve_boundary (6 + 4 * n)) middle logs next _ starvation_execution_valid
    (starve_boundaries n) (starve_cycle_script n) hi hrun hturn).2

private theorem starve_prefix_emitted (i : Nat) : i < 19 →
    starvation_execution.emitted i = starve_prefix_event 0 i := by
  intro hi
  obtain ⟨middle, logs, next, hrun, hturn⟩ := starve_prefix_position 0 i hi
  have := (execution_script_emitted (turn 1) (fun xs => xs) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) starvation_execution 0 starvation_prefix i Remote1
    (initial_state 2 0) middle logs next _ starvation_execution_valid starve_initial_equiv
    starve_prefix_script hi hrun hturn).2
  rwa [Nat.zero_add] at this

private theorem starve_index (k : Nat) : 19 ≤ k → ∃ n i, i < 13 ∧ k = 19 + 13 * n + i :=
  fun _ => ⟨(k - 19) / 13, (k - 19) % 13, Nat.mod_lt _ (by decide), by omega⟩

private theorem starve_fair : fair_choices starvation_execution.selected := by
  intro actor lo
  cases actor with
  | Owner => exact ⟨19 + 13 * lo + 7, by omega, starve_selected_cycle lo 7 (by decide)⟩
  | Remote0 => exact ⟨19 + 13 * lo + 2, by omega, starve_selected_cycle lo 2 (by decide)⟩
  | Remote1 => exact ⟨19 + 13 * lo + 0, by omega, starve_selected_cycle lo 0 (by decide)⟩

private theorem starve_held_forever (k : Nat) : 19 ≤ k →
    held (starvation_execution.states k).remote1_state = [8] := by
  intro hk
  obtain ⟨n, i, hi, rfl⟩ := starve_index k hk
  obtain ⟨middle, logs, next, hrun, hheld, hturn⟩ := starve_cycle_position (6 + 4 * n) i hi
  obtain ⟨-, -, -, -, -, hremote1⟩ := (execution_script_emitted (turn 1) (fun xs => xs)
    (fun s => s = initial_state 2 0) state_equiv (turn_proper 1) starvation_execution
    (19 + 13 * n) starvation_cycle i Remote1 (starve_boundary (6 + 4 * n)) middle logs next _
    starvation_execution_valid (starve_boundaries n) (starve_cycle_script n) hi hrun hturn).1
  rw [hremote1]; exact hheld

private theorem starve_prefix_event_emissions (c i : Nat) :
    csl_emissions (starve_prefix_event c i) = csl_emissions (starve_prefix_user_event c i) := by
  unfold starve_prefix_event; split <;> first | rfl | exact slice_emissions _ _ _ _ _

private theorem starve_cycle_event_emissions (c i : Nat) :
    csl_emissions (starve_cycle_event c i) = csl_emissions (starve_cycle_user_event c i) := by
  unfold starve_cycle_event; split <;> first | rfl | exact slice_emissions _ _ _ _ _

private theorem starve_prefix_never_retire8 (c i idx : Nat) : i < 19 →
    stamp (tag_retire, 8) idx ∉ csl_emissions (starve_prefix_event c i) := by
  intro _
  rw [starve_prefix_event_emissions]; unfold starve_prefix_user_event
  split <;> simp [csl_emissions, tag_retire, tag_alloc, tag_retry, tag_reclaim]

private theorem starve_cycle_never_retire8 (c i idx : Nat) : i < 13 →
    stamp (tag_retire, 8) idx ∉ csl_emissions (starve_cycle_event c i) := by
  intro _
  rw [starve_cycle_event_emissions]; unfold starve_cycle_user_event
  split <;> simp [csl_emissions, tag_retire, tag_alloc, tag_retry, tag_reclaim]

private theorem starve_never_retire8 (k : Nat) :
    ¬ block_event tag_retire 8 (starvation_execution.emitted k) := by
  rintro ⟨idx, hevent⟩
  rcases Nat.lt_or_ge k 19 with hprefix | hcycle
  · rw [starve_prefix_emitted k hprefix] at hevent
    exact starve_prefix_never_retire8 0 k idx hprefix hevent
  · obtain ⟨n, i, hi, rfl⟩ := starve_index k hcycle
    rw [starve_cycle_emitted n i hi] at hevent
    exact starve_cycle_never_retire8 (6 + 4 * n) i idx hi hevent

private theorem starve_infinitely_retry8 :
    infinitely fun k => block_event tag_retry 8 (starvation_execution.emitted k) :=
  fun lo => ⟨19 + 13 * lo + 6, by omega, 6 + 4 * lo + 1,
    by rw [starve_cycle_emitted lo 6 (by decide)]; exact .head _⟩

private theorem starve_infinitely_retire6 :
    infinitely fun k => block_event tag_retire 6 (starvation_execution.emitted k) :=
  fun lo => ⟨19 + 13 * lo + 5, by omega, 6 + 4 * lo,
    by rw [starve_cycle_emitted lo 5 (by decide)]; exact .head _⟩

private theorem starve_infinitely_reclaim6 :
    infinitely fun k => block_event tag_reclaim 6 (starvation_execution.emitted k) :=
  fun lo => ⟨19 + 13 * lo + 9, by omega, 6 + 4 * lo + 2,
    by rw [starve_cycle_emitted lo 9 (by decide)]; exact .head _⟩

private theorem starve_infinitely_alloc6 :
    infinitely fun k => block_event tag_alloc 6 (starvation_execution.emitted k) :=
  fun lo => ⟨19 + 13 * lo + 11, by omega, 6 + 4 * lo + 3,
    by rw [starve_cycle_emitted lo 11 (by decide)]; exact .head _⟩

theorem fair_starvation_exists : ∃ e,
    allocator_valid 2 0 e ∧ fair_choices e.selected ∧
    (∀ k, 19 ≤ k → held (e.states k).remote1_state = [8]) ∧
    infinitely (fun k => block_event tag_retry 8 (e.emitted k)) ∧
    (∀ k, ¬ block_event tag_retire 8 (e.emitted k)) ∧
    infinitely (fun k => block_event tag_retire 6 (e.emitted k)) ∧
    infinitely (fun k => block_event tag_reclaim 6 (e.emitted k)) ∧
    infinitely (fun k => block_event tag_alloc 6 (e.emitted k)) ∧
    realizes (prepend_chunk
      ((new_page_logs 1 2 managed_empty).map fun o => .obs (E := writerE _) o ⟨⟩)
      (fun j => turn_labels (e.emitted j))) 0
      (run_nd (allocator_program 2) (managed_empty, (([] : Ctx), 0))) :=
  ⟨starvation_execution, starvation_execution_valid, starve_fair, starve_held_forever,
    starve_infinitely_retry8, starve_never_retire8, starve_infinitely_retire6,
    starve_infinitely_reclaim6, starve_infinitely_alloc6,
    valid_execution_realizes_source 2 [] 0 _ starvation_execution_valid⟩

/-- The first cycle, chained from the ACTUAL prefix result, is a finite source trace with one
genuine scheduler tau per turn. -/
theorem starvation_chained_cycle_actual_source : ∃ last labels residual,
    run_turns (turn 1) (fun xs => xs) (starvation_prefix ++ starvation_cycle)
        (initial_state 2 0) = some (last, starve_prefix_logs 0 ++ starve_cycle_logs 6) ∧
    label_logs labels = new_page_logs 1 2 managed_empty ++
      (starve_prefix_logs 0 ++ starve_cycle_logs 6) ∧
    label_taus labels = 32 ∧
    FiniteSteps (run_nd (allocator_program 2) (managed_empty, (([] : Ctx), 0))) labels residual ∧
    residual ~ (model_nd 2 actor_of_slot (turn 1) last
      : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  obtain ⟨first, hprefix, hfirst⟩ := starve_prefix_run 0
  obtain ⟨last, hcycle, -⟩ := starve_cycle_run_actual 6 first hfirst
  have hrun := run_turns_compose (turn 1) (fun xs => xs) starvation_prefix starvation_cycle
    (initial_state 2 0) first last _ _ hprefix hcycle
  obtain ⟨labels, residual, -, hlogs, htaus, hsteps, htail⟩ :=
    run_turns_realizes_source 2 [] 0 _ last _ hrun
  exact ⟨last, labels, residual, hrun, hlogs, htaus, hsteps, htail⟩

end Starvation

section OwnerStall

private def owner_stall_cycle : List Actor := [Remote0, Remote1]

def owner_stall_choices : Nat → Actor :=
  periodic_choices owner_stall_prefix Remote0 [Remote1]

private theorem stalled_prefix_run (c : Nat) : ∃ last,
    run_turns (turn 1) (fun xs => xs) owner_stall_prefix (initial_state 2 c) =
      some (last, stalled_prefix_logs c) ∧
    state_equiv last (stalled_boundary (c + 4)) := by
  refine ⟨_, stall_run c 13 (Nat.le_refl _), fun x => ?_, fun _ => rfl, rfl, rfl, rfl, rfl⟩
  match x with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | x + 10 => rfl

private theorem stalled_polling_turn (c : Nat) (who : Actor) :
    who = Remote0 ∨ who = Remote1 →
      turn 1 who (stalled_boundary c) = some (stalled_boundary c, []) := by
  rintro (rfl | rfl)
  · exact turn_remote_poll_empty 1 false _ rfl rfl
  · exact turn_remote_poll_empty 1 true _ rfl rfl

private theorem stalled_prefix_position (k : Nat) : k < 13 →
    ∃ before after logs,
      run_turns (turn 1) (fun xs => xs) (owner_stall_prefix.take k) (initial_state 2 0) =
        some (before, logs) ∧
      turn 1 (owner_stall_prefix.getD k Remote0) before =
        some (after, stalled_prefix_event 0 k) :=
  fun hk => ⟨_, _, _, stall_run 0 k (Nat.le_of_lt hk), stall_cert 0 k hk⟩

/-- The infinite execution follows the periodic script from the actual initial state. -/
def owner_stall_execution : Execution AState Actor (List (CSLObs (Nat × Nat))) :=
  allocator_execution 2 0 owner_stall_choices

private theorem owner_stall_execution_valid : allocator_valid 2 0 owner_stall_execution :=
  allocator_execution_valid 2 0 _

private theorem stalled_prefix_script :
    (List.range' 0 owner_stall_prefix.length).map owner_stall_execution.selected =
      owner_stall_prefix :=
  periodic_prefix_script _ _ _

private theorem stalled_initial_equiv :
    state_equiv (owner_stall_execution.states 0) (initial_state 2 0) := by
  rw [owner_stall_execution_valid.1]; exact state_equiv_refl _

private theorem stalled_prefix_state :
    state_equiv (owner_stall_execution.states 13) (stalled_boundary 4) := by
  obtain ⟨last, hrun, hlast⟩ := stalled_prefix_run 0
  exact state_equiv_trans _ _ _ (execution_script_state (turn 1) (fun xs => xs)
    (fun s => s = initial_state 2 0) state_equiv (turn_proper 1) owner_stall_execution 0
    owner_stall_prefix (initial_state 2 0) last _ owner_stall_execution_valid
    stalled_initial_equiv stalled_prefix_script hrun) hlast

private theorem stalled_prefix_observation (k : Nat) : k < 13 →
    owner_stall_execution.emitted k = stalled_prefix_event 0 k := by
  intro hk
  obtain ⟨before, after, logs, hrun, hturn⟩ := stalled_prefix_position k hk
  have := (execution_script_emitted (turn 1) (fun xs => xs) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) owner_stall_execution 0 owner_stall_prefix k Remote0
    (initial_state 2 0) before logs after _ owner_stall_execution_valid stalled_initial_equiv
    stalled_prefix_script hk hrun hturn).2
  rwa [Nat.zero_add] at this

private theorem stalled_retire6 :
    owner_stall_execution.emitted 8 = snapshot_slice stalled_prefix_snapshots 9 1 ++
      [.emit (stamp (tag_retire, 6) 2)] :=
  stalled_prefix_observation 8 (by decide)

private theorem stalled_tail_choices (n : Nat) :
    owner_stall_execution.selected (13 + n) = owner_stall_cycle.getD (n % 2) Remote0 :=
  periodic_choices_nth owner_stall_prefix Remote0 [Remote1] n

private theorem stalled_tail_client (n : Nat) :
    owner_stall_execution.selected (13 + n) = Remote0 ∨
      owner_stall_execution.selected (13 + n) = Remote1 := by
  rw [stalled_tail_choices]
  have := Nat.mod_lt n (show 2 > 0 by decide)
  rcases h : n % 2 with _ | _ | r
  · exact .inl rfl
  · exact .inr rfl
  · omega

private theorem stalled_cycle_selection (n i : Nat) : i < 2 →
    owner_stall_execution.selected (13 + n * 2 + i) = owner_stall_cycle.getD i Remote0 :=
  periodic_choices_round owner_stall_prefix Remote0 [Remote1] n i

private theorem stalled_no_owner (k : Nat) : 5 ≤ k → owner_stall_execution.selected k ≠ Owner := by
  intro hfive
  rcases Nat.lt_or_ge k 13 with hprefix | htail
  · have key : ∀ k, k < 13 → 5 ≤ k → owner_stall_prefix.getD k Remote0 ≠ Owner := by decide
    show periodic_choices owner_stall_prefix Remote0 [Remote1] k ≠ Owner
    rw [periodic_choices_before _ _ _ _ hprefix]
    exact key k hprefix hfive
  · obtain ⟨j, rfl⟩ : ∃ j, k = 13 + j := ⟨k - 13, by omega⟩
    rcases stalled_tail_client j with h | h <;> rw [h] <;> nofun

private theorem stalled_remote0_infinitely :
    infinitely fun k => owner_stall_execution.selected k = Remote0 :=
  fun n => ⟨13 + n * 2, by omega, stalled_cycle_selection n 0 (by decide)⟩

private theorem stalled_remote1_infinitely :
    infinitely fun k => owner_stall_execution.selected k = Remote1 :=
  fun n => ⟨13 + n * 2 + 1, by omega, stalled_cycle_selection n 1 (by decide)⟩

private theorem stalled_suffix_state (n : Nat) :
    state_equiv (owner_stall_execution.states (13 + n)) (stalled_boundary 4) :=
  execution_stutters_from (turn 1) (fun s => s = initial_state 2 0) state_equiv (turn_proper 1)
    owner_stall_execution 13 (stalled_boundary 4) owner_stall_execution_valid stalled_prefix_state
    (fun k => ⟨[], stalled_polling_turn 4 _ (stalled_tail_client k)⟩) n

private theorem stalled_suffix_silent (n : Nat) : owner_stall_execution.emitted (13 + n) = [] := by
  obtain ⟨next, hnext, -⟩ := execution_turn_observation (turn 1) (fun s => s = initial_state 2 0)
    state_equiv (turn_proper 1) owner_stall_execution (13 + n) (stalled_boundary 4)
    owner_stall_execution_valid (stalled_suffix_state n)
  rw [stalled_polling_turn 4 _ (stalled_tail_client n)] at hnext
  simp only [Option.some.injEq, Prod.mk.injEq] at hnext
  exact hnext.2.symm

private theorem stalled_no_reclaim (k block : Nat) :
    ¬ block_event tag_reclaim block (owner_stall_execution.emitted k) := by
  rintro ⟨idx, hobs⟩
  rcases Nat.lt_or_ge k 13 with hprefix | htail
  · rw [stalled_prefix_observation k hprefix] at hobs
    have key : ∀ k, k < 13 → ∀ x ∈ csl_emissions (stalled_prefix_event 0 k),
        x.value.1 ≠ tag_reclaim := by decide
    exact key k hprefix _ hobs rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = 13 + j := ⟨k - 13, by omega⟩
    rw [stalled_suffix_silent] at hobs
    simp [csl_emissions] at hobs

theorem stalled_prefix_source : ∃ last labels residual,
    run_turns (turn 1) (fun xs => xs) owner_stall_prefix (initial_state 2 0) =
      some (last, stalled_prefix_logs 0) ∧
    state_equiv last (stalled_boundary 4) ∧
    label_logs labels = new_page_logs 1 2 managed_empty ++ stalled_prefix_logs 0 ∧
    label_taus labels = 13 ∧
    FiniteSteps (run_nd (allocator_program 2) (managed_empty, (([] : Ctx), 0))) labels residual ∧
    residual ~ (model_nd 2 actor_of_slot (turn 1) last
      : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  obtain ⟨last, hrun, hstate⟩ := stalled_prefix_run 0
  obtain ⟨labels, residual, -, hlogs, htaus, hsteps, hresidual⟩ :=
    run_turns_realizes_source 2 [] 0 owner_stall_prefix last _ hrun
  exact ⟨last, labels, residual, hrun, hstate, hlogs, htaus, hsteps, hresidual⟩

/-- Every silent polling choice still consumes one real scheduler tau. -/
theorem stalled_tail_source_tau (n : Nat) (t : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) :
    realizes (fun j => turn_labels (owner_stall_execution.emitted j)) (13 + n) t →
    ∃ next, FiniteSteps t [.tau] next ∧
      realizes (fun j => turn_labels (owner_stall_execution.emitted j)) (13 + n + 1) next := by
  intro h
  obtain ⟨next, -, hsteps, hrest⟩ := realizes_unfold.1 h
  refine ⟨next, ?_, hrest⟩
  rw [stalled_suffix_silent] at hsteps
  exact hsteps

theorem owner_stall_prevents_reclamation : ∃ e,
    allocator_valid 2 0 e ∧
    (∀ k, 5 ≤ k → e.selected k ≠ Owner) ∧
    infinitely (fun k => e.selected k = Remote0) ∧
    infinitely (fun k => e.selected k = Remote1) ∧
    e.emitted 8 = snapshot_slice stalled_prefix_snapshots 9 1 ++
      [.emit (stamp (tag_retire, 6) 2)] ∧
    (∀ k, ¬ block_event tag_reclaim 6 (e.emitted k)) ∧
    realizes (prepend_chunk
      ((new_page_logs 1 2 managed_empty).map fun o => .obs (E := writerE _) o ⟨⟩)
      (fun j => turn_labels (e.emitted j))) 0
      (run_nd (allocator_program 2) (managed_empty, (([] : Ctx), 0))) :=
  ⟨owner_stall_execution, owner_stall_execution_valid, stalled_no_owner,
    stalled_remote0_infinitely, stalled_remote1_infinitely, stalled_retire6,
    fun k => stalled_no_reclaim k 6,
    valid_execution_realizes_source 2 [] 0 _ owner_stall_execution_valid⟩

end OwnerStall

end Examples.CSL.Allocator.Counterexamples

-- Not ported: `mutation_snapshots` (redundant with `CoCSL.write_snapshots`); the unused
-- emission cross-checks `starve_prefix_user_table`, `starve_cycle_user_table`,
-- `stalled_prefix_user_table`, `stalled_prefix_user_turn_table` with their data
-- `starve_prefix_user_logs`, `starve_cycle_user_logs`, `stalled_prefix_user_logs`,
-- `stalled_prefix_user_observations`, `stalled_prefix_observations` (redundant with
-- `Replay.stalled_prefix_event`). The scripts, boundaries and observation tables keep their
-- Rocq names in `Examples.CSL.Allocator.Replay`; section `Let`s referenced (also transitively,
-- as the module system requires) by a public statement are public `def`s.
