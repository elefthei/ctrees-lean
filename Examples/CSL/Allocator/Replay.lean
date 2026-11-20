/- SPDX-License-Identifier: MIT -/
module
-- Lean-only module, no Rocq counterpart.

public import Examples.CSL.Allocator.Model
public import Lang.CoCSL.Sequential

/-!
# Replay tables of the allocator's concrete scripts

The concrete scripts and per-turn observation tables of the counterexamples and of the ABA
scenario (Rocq `Let`s of `examples/CSL/Allocator/Counterexamples.v` and `Liveness.v`, moved here
under their Rocq names), each paired with an explicit state table. Turn `i` of a table maps its
pre-state by a step function read off one phase equation of `turn`, and the certificate of turn
`i` is that phase equation: nothing here or downstream evaluates `turn` itself.
-/

@[expose] public section
namespace Examples.CSL.Allocator.Replay
open Tisl Tisl.Heap Tisl.CSL CoCSL
open Examples.CSL.Allocator.Layout Examples.CSL.Allocator.Model
open Actor owner_pc remote_pc

/-- The states visited from `s0` when turn `i` maps its pre-state by `step i`. -/
def replay_states (step : Nat → AState → AState) (s0 : AState) : Nat → AState
  | 0 => s0
  | i + 1 => step i (replay_states step s0 i)

def snapshot_slice (logs : List (CSLObs (Nat × Nat))) (start count : Nat) :
    List (CSLObs (Nat × Nat)) :=
  (logs.drop start).take count

/-! ## Starvation: scripts and observation tables -/

def starvation_cycle : List Actor :=
  [Remote1, Remote1, Remote0, Remote0, Remote0, Remote0, Remote1,
   Owner, Owner, Owner, Owner, Owner, Owner]

def starvation_prefix : List Actor :=
  [Owner, Owner, Owner, Owner, Owner, Remote1] ++ starvation_cycle

/-- A pointwise representative only: the infinite witness always retains the actual heap returned
by its preceding turn. -/
def starve_boundary_heap : Heap := fun x =>
  match x with
  | 1 => some 0 | 2 => some 0 | 3 => some 0 | 4 => some 6
  | 5 => some 0 | 6 => some 0 | 7 => some 1 | 8 => some 0
  | 9 => some 2 | _ => none

def starve_boundary (c : Nat) : AState where
  aheap := starve_boundary_heap
  aallocs := upd hemp 1 (page_size 2)
  acount := c
  owner_state := ORead
  remote0_state := RPoll
  remote1_state := RRead 8

/-- The observation of each individual turn, including every silent turn. -/
def starve_prefix_user_event (c i : Nat) : List (CSLObs (Nat × Nat)) :=
  match i with
  | 3 => [.emit (stamp (tag_alloc, 6) c)]
  | 4 => [.emit (stamp (tag_alloc, 8) (c + 1))]
  | 11 => [.emit (stamp (tag_retire, 6) (c + 2))]
  | 12 => [.emit (stamp (tag_retry, 8) (c + 3))]
  | 15 => [.emit (stamp (tag_reclaim, 6) (c + 4))]
  | 17 => [.emit (stamp (tag_alloc, 6) (c + 5))]
  | _ => []

def starve_cycle_user_event (c i : Nat) : List (CSLObs (Nat × Nat)) :=
  match i with
  | 5 => [.emit (stamp (tag_retire, 6) c)]
  | 6 => [.emit (stamp (tag_retry, 8) (c + 1))]
  | 9 => [.emit (stamp (tag_reclaim, 6) (c + 2))]
  | 11 => [.emit (stamp (tag_alloc, 6) (c + 3))]
  | _ => []

def starve_prefix_snapshots : List (CSLObs (Nat × Nat)) :=
  write_snapshots
    [(1, 0), (3, 0), (2, 8), (4, 6), (2, 0), (5, 8), (5, 0), (9, 2),
     (8, 0), (4, 0), (7, 1), (6, 0), (1, 6), (1, 0), (3, 6),
     (6, 0), (2, 6), (3, 0), (2, 0), (4, 6)]
    ((initial_state 2 0).aheap, upd hemp 1 (page_size 2))

def starve_cycle_snapshots : List (CSLObs (Nat × Nat)) :=
  write_snapshots
    [(8, 0), (4, 0), (7, 1), (6, 0), (1, 6), (1, 0), (3, 6),
     (6, 0), (2, 6), (3, 0), (2, 0), (4, 6)]
    (starve_boundary_heap, upd hemp 1 (page_size 2))

def starve_prefix_event (c i : Nat) : List (CSLObs (Nat × Nat)) :=
  (match i with
   | 1 => snapshot_slice starve_prefix_snapshots 0 2
   | 3 => snapshot_slice starve_prefix_snapshots 2 2
   | 4 => snapshot_slice starve_prefix_snapshots 4 2
   | 5 => snapshot_slice starve_prefix_snapshots 6 2
   | 7 => snapshot_slice starve_prefix_snapshots 8 1
   | 8 => snapshot_slice starve_prefix_snapshots 9 2
   | 10 => snapshot_slice starve_prefix_snapshots 11 1
   | 11 => snapshot_slice starve_prefix_snapshots 12 1
   | 14 => snapshot_slice starve_prefix_snapshots 13 2
   | 15 => snapshot_slice starve_prefix_snapshots 15 3
   | 17 => snapshot_slice starve_prefix_snapshots 18 2
   | _ => []) ++ starve_prefix_user_event c i

def starve_cycle_event (c i : Nat) : List (CSLObs (Nat × Nat)) :=
  (match i with
   | 1 => snapshot_slice starve_cycle_snapshots 0 1
   | 2 => snapshot_slice starve_cycle_snapshots 1 2
   | 4 => snapshot_slice starve_cycle_snapshots 3 1
   | 5 => snapshot_slice starve_cycle_snapshots 4 1
   | 8 => snapshot_slice starve_cycle_snapshots 5 2
   | 9 => snapshot_slice starve_cycle_snapshots 7 3
   | 11 => snapshot_slice starve_cycle_snapshots 10 2
   | _ => []) ++ starve_cycle_user_event c i

def starve_prefix_logs (c : Nat) : List (CSLObs (Nat × Nat)) :=
  ((List.range' 0 19).map (starve_prefix_event c)).flatten

def starve_cycle_logs (c : Nat) : List (CSLObs (Nat × Nat)) :=
  ((List.range' 0 13).map (starve_cycle_event c)).flatten

/-! ## Starvation: state tables -/

/-- Turn `i` of `starvation_cycle`: remote 1 links block 8 against the empty head, remote 0
retires block 6, remote 1's CAS fails, and the owner reclaims and reallocates block 6. -/
def cycle_step : Nat → AState → AState
  | 0, s => set_remote_pc true (RLink 8 0) s
  | 1, s => { set_remote_pc true (RCAS 8 0) s with aheap := upd s.aheap 8 0 }
  | 2, s => { set_remote_pc false (RRead 6) s with aheap := upd (upd s.aheap 4 0) 7 1 }
  | 3, s => set_remote_pc false (RLink 6 0) s
  | 4, s => { set_remote_pc false (RCAS 6 0) s with aheap := upd s.aheap 6 0 }
  | 5, s => { set_remote_pc false RPoll s with aheap := upd s.aheap 1 6, acount := s.acount + 1 }
  | 6, s => { set_remote_pc true (RRead 8) s with acount := s.acount + 1 }
  | 7, s => { s with owner_state := OCAS 6 }
  | 8, s => { s with owner_state := ODrain, aheap := upd (upd s.aheap 1 0) 3 6 }
  | 9, s => { s with aheap := upd (upd (upd s.aheap 6 0) 2 6) 3 0, acount := s.acount + 1 }
  | 10, s => { s with owner_state := OOffer false }
  | 11, s =>
    { s with
      owner_state := OOffer true, aheap := upd (upd s.aheap 2 0) 4 6, acount := s.acount + 1 }
  | 12, s => { s with owner_state := ORead }
  | _, s => s

/-- Turn `i` of `starvation_prefix`: the owner initializes and hands out blocks 6 and 8, remote 1
picks up block 8, then one cycle. -/
def starve_step : Nat → AState → AState
  | 0, s => { s with owner_state := OCAS 0 }
  | 1, s => { s with owner_state := ODrain, aheap := upd (upd s.aheap 1 0) 3 0 }
  | 2, s => { s with owner_state := OOffer false }
  | 3, s =>
    { s with
      owner_state := OOffer true, aheap := upd (upd s.aheap 2 8) 4 6, acount := s.acount + 1 }
  | 4, s =>
    { s with owner_state := ORead, aheap := upd (upd s.aheap 2 0) 5 8, acount := s.acount + 1 }
  | 5, s => { set_remote_pc true (RRead 8) s with aheap := upd (upd s.aheap 5 0) 9 2 }
  | i + 6, s => cycle_step i s

def starve_state (c : Nat) : Nat → AState := replay_states starve_step (initial_state 2 c)

def cycle_state (c : Nat) : Nat → AState := replay_states cycle_step (starve_boundary c)

theorem starve_cert (c : Nat) : ∀ i, i < 19 →
    turn 1 (starvation_prefix.getD i Remote1) (starve_state c i) =
      some (starve_state c (i + 1), starve_prefix_event c i)
  | 0, _ => turn_owner_read 1 _ 0 rfl rfl
  | 1, _ => turn_owner_cas_success 1 _ 0 _ rfl rfl rfl
  | 2, _ => turn_owner_drain_empty 1 _ rfl rfl
  | 3, _ => turn_owner_offer_block 1 false _ 6 8 rfl rfl rfl (by decide) rfl
  | 4, _ => turn_owner_offer_block 1 true _ 8 0 rfl rfl rfl (by decide) rfl
  | 5, _ => turn_remote_poll_pickup 1 true _ 8 _ rfl rfl (by decide) rfl
  | 6, _ => turn_remote_read 1 true _ 8 0 rfl rfl
  | 7, _ => turn_remote_link 1 true _ 8 0 _ rfl rfl
  | 8, _ => turn_remote_poll_pickup 1 false _ 6 _ rfl rfl (by decide) rfl
  | 9, _ => turn_remote_read 1 false _ 6 0 rfl rfl
  | 10, _ => turn_remote_link 1 false _ 6 0 _ rfl rfl
  | 11, _ => turn_remote_cas_success 1 false _ 6 0 rfl rfl
  | 12, _ => turn_remote_cas_retry 1 true _ 8 0 6 rfl rfl (by decide)
  | 13, _ => turn_owner_read 1 _ 6 rfl rfl
  | 14, _ => turn_owner_cas_success 1 _ 6 _ rfl rfl rfl
  | 15, _ => turn_owner_drain_block 1 _ 6 0 0 rfl rfl (by decide) rfl rfl
  | 16, _ => turn_owner_drain_empty 1 _ rfl rfl
  | 17, _ => turn_owner_offer_block 1 false _ 6 0 rfl rfl rfl (by decide) rfl
  | 18, _ => turn_owner_offer_skip 1 true _ 0 rfl rfl (.inr rfl)
  | _ + 19, h => absurd h (by omega)

theorem cycle_cert (c : Nat) : ∀ i, i < 13 →
    turn 1 (starvation_cycle.getD i Remote1) (cycle_state c i) =
      some (cycle_state c (i + 1), starve_cycle_event c i)
  | 0, _ => turn_remote_read 1 true _ 8 0 rfl rfl
  | 1, _ => turn_remote_link 1 true _ 8 0 _ rfl rfl
  | 2, _ => turn_remote_poll_pickup 1 false _ 6 _ rfl rfl (by decide) rfl
  | 3, _ => turn_remote_read 1 false _ 6 0 rfl rfl
  | 4, _ => turn_remote_link 1 false _ 6 0 _ rfl rfl
  | 5, _ => turn_remote_cas_success 1 false _ 6 0 rfl rfl
  | 6, _ => turn_remote_cas_retry 1 true _ 8 0 6 rfl rfl (by decide)
  | 7, _ => turn_owner_read 1 _ 6 rfl rfl
  | 8, _ => turn_owner_cas_success 1 _ 6 _ rfl rfl rfl
  | 9, _ => turn_owner_drain_block 1 _ 6 0 0 rfl rfl (by decide) rfl rfl
  | 10, _ => turn_owner_drain_empty 1 _ rfl rfl
  | 11, _ => turn_owner_offer_block 1 false _ 6 0 rfl rfl rfl (by decide) rfl
  | 12, _ => turn_owner_offer_skip 1 true _ 0 rfl rfl (.inr rfl)
  | _ + 13, h => absurd h (by omega)

/-- Remote 1 holds block 8 throughout the cycle. -/
theorem cycle_held (c : Nat) : ∀ i, i < 13 → held (cycle_state c i).remote1_state = [8]
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ => rfl
  | _ + 13, h => absurd h (by omega)

theorem starve_run (c i : Nat) (hi : i ≤ starvation_prefix.length) :
    run_turns (turn 1) (fun xs => xs) (starvation_prefix.take i) (initial_state 2 c) =
      some (starve_state c i, ((List.range' 0 i).map (starve_prefix_event c)).flatten) :=
  run_turns_table (turn 1) (fun xs => xs) starvation_prefix Remote1 (starve_state c)
    (starve_prefix_event c) (starve_cert c) i hi

theorem cycle_run (c i : Nat) (hi : i ≤ starvation_cycle.length) :
    run_turns (turn 1) (fun xs => xs) (starvation_cycle.take i) (starve_boundary c) =
      some (cycle_state c i, ((List.range' 0 i).map (starve_cycle_event c)).flatten) :=
  run_turns_table (turn 1) (fun xs => xs) starvation_cycle Remote1 (cycle_state c)
    (starve_cycle_event c) (cycle_cert c) i hi

/-! ## Owner stall and ABA: scripts and observation tables -/

def owner_stall_prefix : List Actor :=
  List.replicate 5 Owner ++ List.replicate 4 Remote0 ++ List.replicate 4 Remote1

def aba_before_reuse : List Actor :=
  List.replicate 5 Owner ++ List.replicate 4 Remote0 ++ List.replicate 3 Remote1

def aba_before_commit : List Actor :=
  aba_before_reuse ++ List.replicate 6 Owner ++ List.replicate 4 Remote0

def aba_script : List Actor := aba_before_commit ++ [Remote1]

def stalled_prefix_snapshots : List (CSLObs (Nat × Nat)) :=
  write_snapshots
    [(1, 0), (3, 0), (2, 8), (4, 6), (2, 0), (5, 8), (4, 0), (7, 1),
     (6, 0), (1, 6), (5, 0), (9, 2), (8, 6), (1, 8)]
    ((initial_state 2 0).aheap, upd hemp 1 (page_size 2))

def stalled_prefix_event (c i : Nat) : List (CSLObs (Nat × Nat)) :=
  (match i with
   | 1 => snapshot_slice stalled_prefix_snapshots 0 2
   | 3 => snapshot_slice stalled_prefix_snapshots 2 2
   | 4 => snapshot_slice stalled_prefix_snapshots 4 2
   | 5 => snapshot_slice stalled_prefix_snapshots 6 2
   | 7 => snapshot_slice stalled_prefix_snapshots 8 1
   | 8 => snapshot_slice stalled_prefix_snapshots 9 1
   | 9 => snapshot_slice stalled_prefix_snapshots 10 2
   | 11 => snapshot_slice stalled_prefix_snapshots 12 1
   | 12 => snapshot_slice stalled_prefix_snapshots 13 1
   | _ => []) ++
  match i with
  | 3 => [.emit (stamp (tag_alloc, 6) c)]
  | 4 => [.emit (stamp (tag_alloc, 8) (c + 1))]
  | 8 => [.emit (stamp (tag_retire, 6) (c + 2))]
  | 12 => [.emit (stamp (tag_retire, 8) (c + 3))]
  | _ => []

def stalled_prefix_logs (c : Nat) : List (CSLObs (Nat × Nat)) :=
  ((List.range' 0 13).map (stalled_prefix_event c)).flatten

/-- Only a pointwise representative of the returned heap. The execution always runs the actual
preceding turn. -/
def stalled_boundary_heap : Heap := fun x =>
  match x with
  | 1 => some 8 | 2 => some 0 | 3 => some 0 | 4 => some 0
  | 5 => some 0 | 6 => some 0 | 7 => some 1 | 8 => some 6
  | 9 => some 2 | _ => none

def stalled_boundary (c : Nat) : AState where
  aheap := stalled_boundary_heap
  aallocs := upd hemp 1 (page_size 2)
  acount := c
  owner_state := ORead
  remote0_state := RPoll
  remote1_state := RPoll

/-- The observation of each turn of `aba_script` (Lean-only). -/
def aba_snapshots : List (CSLObs (Nat × Nat)) :=
  write_snapshots
    [(1, 0), (3, 0), (2, 8), (4, 6), (2, 0), (5, 8), (4, 0), (7, 1),
     (6, 0), (1, 6), (5, 0), (9, 2), (8, 6), (1, 0), (3, 6), (6, 0),
     (2, 6), (3, 0), (2, 0), (4, 6), (4, 0), (7, 1), (6, 0), (1, 6), (1, 8)]
    ((initial_state 2 0).aheap, upd hemp 1 (page_size 2))

def aba_event (c i : Nat) : List (CSLObs (Nat × Nat)) :=
  (match i with
   | 1 => snapshot_slice aba_snapshots 0 2
   | 3 => snapshot_slice aba_snapshots 2 2
   | 4 => snapshot_slice aba_snapshots 4 2
   | 5 => snapshot_slice aba_snapshots 6 2
   | 7 => snapshot_slice aba_snapshots 8 1
   | 8 => snapshot_slice aba_snapshots 9 1
   | 9 => snapshot_slice aba_snapshots 10 2
   | 11 => snapshot_slice aba_snapshots 12 1
   | 13 => snapshot_slice aba_snapshots 13 2
   | 14 => snapshot_slice aba_snapshots 15 3
   | 16 => snapshot_slice aba_snapshots 18 2
   | 18 => snapshot_slice aba_snapshots 20 2
   | 20 => snapshot_slice aba_snapshots 22 1
   | 21 => snapshot_slice aba_snapshots 23 1
   | 22 => snapshot_slice aba_snapshots 24 1
   | _ => []) ++
  match i with
  | 3 => [.emit (stamp (tag_alloc, 6) c)]
  | 4 => [.emit (stamp (tag_alloc, 8) (c + 1))]
  | 8 => [.emit (stamp (tag_retire, 6) (c + 2))]
  | 14 => [.emit (stamp (tag_reclaim, 6) (c + 3))]
  | 16 => [.emit (stamp (tag_alloc, 6) (c + 4))]
  | 21 => [.emit (stamp (tag_retire, 6) (c + 5))]
  | 22 => [.emit (stamp (tag_retire, 8) (c + 6))]
  | _ => []

/-! ## Owner stall and ABA: state tables -/

/-- Turn `i` of `aba_script`: after the owner's start, remote 0 retires block 6 and remote 1
snapshots head 6 for block 8; the owner reclaims and reallocates block 6, remote 0 retires it
again, and remote 1's stale CAS commits. -/
def aba_step : Nat → AState → AState
  | 5, s => { set_remote_pc false (RRead 6) s with aheap := upd (upd s.aheap 4 0) 7 1 }
  | 6, s => set_remote_pc false (RLink 6 0) s
  | 7, s => { set_remote_pc false (RCAS 6 0) s with aheap := upd s.aheap 6 0 }
  | 8, s => { set_remote_pc false RPoll s with aheap := upd s.aheap 1 6, acount := s.acount + 1 }
  | 9, s => { set_remote_pc true (RRead 8) s with aheap := upd (upd s.aheap 5 0) 9 2 }
  | 10, s => set_remote_pc true (RLink 8 6) s
  | 11, s => { set_remote_pc true (RCAS 8 6) s with aheap := upd s.aheap 8 6 }
  | 12, s => cycle_step 7 s
  | 13, s => cycle_step 8 s
  | 14, s => cycle_step 9 s
  | 15, s => cycle_step 10 s
  | 16, s => cycle_step 11 s
  | 17, s => cycle_step 12 s
  | 18, s => cycle_step 2 s
  | 19, s => cycle_step 3 s
  | 20, s => cycle_step 4 s
  | 21, s => cycle_step 5 s
  | 22, s => { set_remote_pc true RPoll s with aheap := upd s.aheap 1 8, acount := s.acount + 1 }
  | i, s => starve_step i s

/-- `owner_stall_prefix` shares the first twelve turns of `aba_script`; its last turn commits
remote 1's CAS at once. -/
def stall_step : Nat → AState → AState
  | 12, s => aba_step 22 s
  | i, s => aba_step i s

def aba_state (c : Nat) : Nat → AState := replay_states aba_step (initial_state 2 c)

def stall_state (c : Nat) : Nat → AState := replay_states stall_step (initial_state 2 c)

theorem aba_cert (c : Nat) : ∀ i, i < 23 →
    turn 1 (aba_script.getD i Owner) (aba_state c i) =
      some (aba_state c (i + 1), aba_event c i)
  | 0, _ => turn_owner_read 1 _ 0 rfl rfl
  | 1, _ => turn_owner_cas_success 1 _ 0 _ rfl rfl rfl
  | 2, _ => turn_owner_drain_empty 1 _ rfl rfl
  | 3, _ => turn_owner_offer_block 1 false _ 6 8 rfl rfl rfl (by decide) rfl
  | 4, _ => turn_owner_offer_block 1 true _ 8 0 rfl rfl rfl (by decide) rfl
  | 5, _ => turn_remote_poll_pickup 1 false _ 6 _ rfl rfl (by decide) rfl
  | 6, _ => turn_remote_read 1 false _ 6 0 rfl rfl
  | 7, _ => turn_remote_link 1 false _ 6 0 _ rfl rfl
  | 8, _ => turn_remote_cas_success 1 false _ 6 0 rfl rfl
  | 9, _ => turn_remote_poll_pickup 1 true _ 8 _ rfl rfl (by decide) rfl
  | 10, _ => turn_remote_read 1 true _ 8 6 rfl rfl
  | 11, _ => turn_remote_link 1 true _ 8 6 _ rfl rfl
  | 12, _ => turn_owner_read 1 _ 6 rfl rfl
  | 13, _ => turn_owner_cas_success 1 _ 6 _ rfl rfl rfl
  | 14, _ => turn_owner_drain_block 1 _ 6 0 0 rfl rfl (by decide) rfl rfl
  | 15, _ => turn_owner_drain_empty 1 _ rfl rfl
  | 16, _ => turn_owner_offer_block 1 false _ 6 0 rfl rfl rfl (by decide) rfl
  | 17, _ => turn_owner_offer_skip 1 true _ 0 rfl rfl (.inr rfl)
  | 18, _ => turn_remote_poll_pickup 1 false _ 6 _ rfl rfl (by decide) rfl
  | 19, _ => turn_remote_read 1 false _ 6 0 rfl rfl
  | 20, _ => turn_remote_link 1 false _ 6 0 _ rfl rfl
  | 21, _ => turn_remote_cas_success 1 false _ 6 0 rfl rfl
  | 22, _ => turn_remote_cas_success 1 true _ 8 6 rfl rfl
  | _ + 23, h => absurd h (by omega)

theorem stall_cert (c : Nat) : ∀ i, i < 13 →
    turn 1 (owner_stall_prefix.getD i Remote0) (stall_state c i) =
      some (stall_state c (i + 1), stalled_prefix_event c i)
  | 0, _ => turn_owner_read 1 _ 0 rfl rfl
  | 1, _ => turn_owner_cas_success 1 _ 0 _ rfl rfl rfl
  | 2, _ => turn_owner_drain_empty 1 _ rfl rfl
  | 3, _ => turn_owner_offer_block 1 false _ 6 8 rfl rfl rfl (by decide) rfl
  | 4, _ => turn_owner_offer_block 1 true _ 8 0 rfl rfl rfl (by decide) rfl
  | 5, _ => turn_remote_poll_pickup 1 false _ 6 _ rfl rfl (by decide) rfl
  | 6, _ => turn_remote_read 1 false _ 6 0 rfl rfl
  | 7, _ => turn_remote_link 1 false _ 6 0 _ rfl rfl
  | 8, _ => turn_remote_cas_success 1 false _ 6 0 rfl rfl
  | 9, _ => turn_remote_poll_pickup 1 true _ 8 _ rfl rfl (by decide) rfl
  | 10, _ => turn_remote_read 1 true _ 8 6 rfl rfl
  | 11, _ => turn_remote_link 1 true _ 8 6 _ rfl rfl
  | 12, _ => turn_remote_cas_success 1 true _ 8 6 rfl rfl
  | _ + 13, h => absurd h (by omega)

theorem aba_run (c i : Nat) (hi : i ≤ aba_script.length) :
    run_turns (turn 1) (fun xs => xs) (aba_script.take i) (initial_state 2 c) =
      some (aba_state c i, ((List.range' 0 i).map (aba_event c)).flatten) :=
  run_turns_table (turn 1) (fun xs => xs) aba_script Owner (aba_state c) (aba_event c)
    (aba_cert c) i hi

theorem stall_run (c i : Nat) (hi : i ≤ owner_stall_prefix.length) :
    run_turns (turn 1) (fun xs => xs) (owner_stall_prefix.take i) (initial_state 2 c) =
      some (stall_state c i, ((List.range' 0 i).map (stalled_prefix_event c)).flatten) :=
  run_turns_table (turn 1) (fun xs => xs) owner_stall_prefix Remote0 (stall_state c)
    (stalled_prefix_event c) (stall_cert c) i hi

end Examples.CSL.Allocator.Replay
