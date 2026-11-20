/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.HeapObservations.Loops
public import Examples.CSL.Queue

/-!
# Framed heap observations

The mutation loop under a passive heap frame, frame stability of heap versus emission prefixes,
a two-log iterator, allocation faults, and exact queue snapshots
(← `examples/CSL/Frame/HeapObservations.v`, lines 688-1188).
-/

@[expose] public section
namespace Examples.CSL.Frame.HeapObservations
open CTree Tisl Tisl.Heap Tisl.Pcm Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Operations Examples.CSL.Queue.Layout
open Examples.CSL.Queue.Trace Examples.CSL.Queue.Program Examples.CSL.Queue.Shared
open ITree (Effect)

/-! ## A passively framed mutation loop -/

/-- The passive frame: cell `2` holding `7`. -/
def mutation_frame : ManagedHeap := region 2 7

/-- The loop's own cell `1` joined with the frame. -/
def mutation_framed_memory : ManagedHeap := region 1 0 ⊎ mutation_frame

theorem mutation_framed_initial :
    mutation_framed_memory.1 1 ≠ none ∧ mutation_framed_memory.1 2 = some 7 := by
  decide

/-- The batch model keeps the frame cell while recurrently showing either requested value. -/
theorem mutation_framed_batches_agaf {X : Type} (memory : ManagedHeap)
    (w : World (writerE (CSLObs (Nat × Nat)))) (value : Nat) :
    (value = 1 ∨ value = 2) → memory.1 1 ≠ none → memory.1 2 = some 7 → NotDone w →
    entails (AG (AF (visWₜ (csl_heap fun m => m.1 1 = some value ∧ m.1 2 = some 7))))
      (emit_batches mutation_logs mutation_next memory : ctreeW (CSLObs (Nat × Nat)) Bn X) w := by
  intro V H1 H2 Hw
  refine emit_batches_agaf mutation_logs mutation_next
    (fun m => m.1 1 ≠ none ∧ m.1 2 = some 7) (fun _ => 0)
    (csl_heap fun m => m.1 1 = some value ∧ m.1 2 = some 7)
    (fun m H => ⟨mutation_next_present m, by simp [mutation_next, mutation_store, upd, H.2]⟩)
    (fun _ _ => nofun) (fun m H => .inl ?_) memory w ⟨H1, H2⟩ Hw
  rcases V with rfl | rfl
  · exact ⟨_, .head _, by simp [csl_heap, mutation_store, upd, H.2]⟩
  · exact ⟨_, .tail _ (.head _), by simp [csl_heap, mutation_next, mutation_store, upd, H.2]⟩

/-- The framed loop recurrently shows each requested value while the frame cell stays `7`. -/
theorem mutation_loop_framed_nd (value : Nat) (ctx : Ctx) (c : Nat) : (value = 1 ∨ value = 2) →
    entails (AG (AF (visWₜ (csl_heap fun m => m.1 1 = some value ∧ m.1 2 = some 7))))
      (run_nd mutation_loop (frame_state mutation_frame (own 1 0 ctx c))) .pure := fun V =>
  (proper_entails_meq _ (mutation_loop_batches_nd mutation_framed_memory ctx c
    mutation_framed_initial.1)).2 (mutation_framed_batches_agaf _ _ value V
      mutation_framed_initial.1 mutation_framed_initial.2 .pure)

/-- The round-robin framed loop: program snapshots under `.inl`, picks never match. -/
theorem mutation_loop_framed_rr (value : Nat) (ctx : Ctx) (c : Nat) : (value = 1 ∨ value = 2) →
    entails
      (AG (AF (visWₜ (fair_obs (csl_heap fun m => m.1 1 = some value ∧ m.1 2 = some 7)))))
      (run_rr mutation_loop (frame_state mutation_frame (own 1 0 ctx c))) .pure := by
  intro V
  refine (proper_entails_meq _ (mutation_loop_batches_rr mutation_framed_memory ctx c
    mutation_framed_initial.1)).2 ?_
  refine emit_batches_agaf (fun m => (mutation_logs m).map Sum.inl) mutation_next
    (fun m => m.1 1 ≠ none ∧ m.1 2 = some 7) (fun _ => 0)
    (fair_obs (csl_heap fun m => m.1 1 = some value ∧ m.1 2 = some 7))
    (fun m H => ⟨mutation_next_present m, by simp [mutation_next, mutation_store, upd, H.2]⟩)
    (fun _ _ => nofun) (fun m H => .inl ?_) _ _ mutation_framed_initial .pure
  rcases V with rfl | rfl
  · exact ⟨_, .head _, by simp [fair_obs, csl_heap, mutation_store, upd, H.2]⟩
  · exact ⟨_, .tail _ (.head _),
      by simp [fair_obs, csl_heap, mutation_next, mutation_store, upd, H.2]⟩

/-- A framed write records its post-memory before returning; the framed postcondition unpacks to
the joined region. -/
theorem mutation_return_framed (ctx : Ctx) (c : Nat) (w : World (writerE (CSLObs (Nat × Nat)))) :
    NotDone w →
    entails (AX (.ret (frame_post mutation_frame (Qwrite 1 ctx c))))
      (instr_flow_erased (.write 1 1) (frame_state mutation_frame (own 1 0 ctx c))) w ∧
    (∀ s' r w', frame_post mutation_frame (Qwrite 1 ctx c) (r, s') w' →
      r = some () ∧ csl_memory s' ≈ region 1 1 ⊎ mutation_frame ∧ s'.2 = (ctx, c) ∧
      w' = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (csl_memory s')) ⟨⟩) :=
  fun Hw => ⟨write_ax_ret_framed 1 2 0 7 ctx c _ w Hw
      (frame_rel_state _ _ (region_frame_inv 1 2 0 7 ctx c (by decide))),
    fun s' r w' h => frame_post_write 1 2 7 ctx c s' r w' h⟩

/-! ## Heap-prefix stability -/

/-- The latest heap snapshot has no cell `2`. -/
def heap_cell2_absent : World (writerE (CSLObs (Nat × Nat))) → Prop :=
  fun w => ∃ memory, w = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap memory) ⟨⟩ ∧
    memory.1 2 = none

/-- Exact heap observations are not frame-stable: the frame fills the absent cell. -/
theorem exact_heap_prefix_not_stable :
    ¬ prefix_stable (frameER mutation_frame) (frameRV (X := Unit) mutation_frame)
      (.now heap_cell2_absent) := by
  intro H
  have HR : frameER (A := Nat × Nat) mutation_frame (CSLObs.heap (region 1 1))
      (CSLObs.heap (region 1 1 ⊎ mutation_frame)) :=
    ⟨region_disj 1 2 1 7 (by decide), managed_wf_preallocated _, peq_refl _⟩
  obtain ⟨memory, E, Hnone⟩ := (prefix_stable_now _ _ _).1 H _ _ (.obs _ _)
    (.obs _ _ _ _ HR HEq.rfl) ⟨region 1 1, rfl, hsingle_neq 1 2 1 (by decide)⟩
  cases E
  revert Hnone; decide

/-- Indexed emissions are frame-stable, so their `AG AF` recurrence transports. -/
theorem emission_prefix_stable (fr : ManagedHeap) (P : Indexed (Nat × Nat) → Prop) :
    prefix_stable (frameER fr) (frameRV (X := Unit) fr)
      (AG (AF (visWₜ fun o =>
        match o with | CSLObs.emit emission => P emission | _ => False))) := by
  refine ⟨fun _ _ _ _ _ => trivial, fun w w' _ HW HP => ?_⟩
  obtain ⟨o, _, HP⟩ := HP
  cases o with
  | heap => exact HP.elim
  | ctx => exact HP.elim
  | emit emission => rw [frame_emit_world fr emission w' HW]; exact .obs _ _ HP

/-- A finish world transports its framed heap predecessor; the two snapshots differ. -/
theorem finish_heap_predecessor_framed (ctx : Ctx) (c : Nat) :
    simW (frameER (A := Nat × Nat) mutation_frame) (frameRV (X := Option Unit) mutation_frame)
      (.finish (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 1 1)) ⟨⟩
        (some (), own 1 1 ctx c))
      (.finish (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 1 1 ⊎ mutation_frame)) ⟨⟩
        (some (), frame_state mutation_frame (own 1 1 ctx c))) ∧
    DoneWith (frame_post mutation_frame (Qwrite 1 ctx c))
      (.finish (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 1 1 ⊎ mutation_frame)) ⟨⟩
        (some (), frame_state mutation_frame (own 1 1 ctx c))) ∧
    region 1 1 ≠ region 1 1 ⊎ mutation_frame := by
  have HI : frame_inv mutation_frame (own 1 1 ctx c) := region_frame_inv 1 2 1 7 ctx c (by decide)
  have HF : simW (frameER (A := Nat × Nat) mutation_frame)
      (frameRV (X := Option Unit) mutation_frame)
      (.finish (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 1 1)) ⟨⟩
        (some (), own 1 1 ctx c))
      (.finish (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 1 1 ⊎ mutation_frame)) ⟨⟩
        (some (), frame_state mutation_frame (own 1 1 ctx c))) :=
    .finish _ _ _ _ _ _ ⟨HI.1, HI.2, peq_refl _⟩ HEq.rfl ⟨rfl, frame_rel_state _ _ HI⟩
  refine ⟨HF, sim_done_with _ _ (Qwrite 1 ctx c) _ _ HF (.finish _ _ _ ⟨rfl, peq_refl _, rfl, rfl⟩),
    fun E => ?_⟩
  have := congrArg (fun m : ManagedHeap => m.1 2) E
  revert this; decide

/-! ## A two-log iterator -/

/-- One iteration logs `true`, then `false`, and continues. -/
def two_log_body (_ : Unit) : CTree (stateE Bool) Bn (Unit ⊕ Unit) :=
  CTree.put true >>= fun _ => CTree.put false >>= fun _ => pure (.inl ())

theorem two_log_body_run (σ : Bool) :
    interp_state (h_stateW (B := Bn)) (two_log_body ()) σ ~
      (emit_list [true, false] (pure (.inl (), false)) :
        ctreeW Bool Bn ((Unit ⊕ Unit) × Bool)) := by
  unfold two_log_body
  rw [interp_state_bind]
  refine sbisim_trans (sbisim_clo_bind_eq (interp_state_put _ _) fun _ => sbisim_refl _) ?_
  simp only [log, vis_bind, pure_bind', emit_list_cons]
  refine sb_vis _ fun _ => ?_
  rw [interp_state_bind]
  refine sbisim_trans (sbisim_clo_bind_eq (interp_state_put _ _) fun _ => sbisim_refl _) ?_
  simp only [log, vis_bind, pure_bind', emit_list_nil, interp_state_ret]
  exact sb_vis _ fun _ => sbisim_refl _

/-- Every visible suffix of the iterator eventually logs `true`. -/
theorem two_log_iterator_recurrence (σ : Bool) (w : World (writerE Bool)) : NotDone w →
    entails (AG (AF (visWₜ fun value : Bool => value = true)))
      (interp_state (h_stateW (B := Bn)) (CTree.iter two_log_body ()) σ) w := by
  intro Hw
  refine ag_state_iter_logs (h := h_stateW (B := Bn)) (X := Unit) (I := Unit)
    (fun _ _ => True) (k := two_log_body) (φ := AF (visWₜ fun value : Bool => value = true))
    (fun _ _ _ => ⟨(), false, [true, false], nofun, two_log_body_run _, trivial⟩)
    (fun o t v Hv H => by rw [← log_vis o t]; exact af_log Hv H)
    (fun _ _ v _ Hv => ?_) () σ w trivial Hw
  rw [interp_state_unfold_iter]
  refine (proper_entails_meq _
    (sbisim_clo_bind_eq (two_log_body_run _) fun _ => sbisim_refl _)).2 ?_
  rw [emit_list_ret_bind]
  exact af_emit_list_member _ _ v _ true Hv (.head _) rfl

/-- A detached `false` suffix never logs `true`. -/
theorem two_log_detached_suffix_no_target :
    ¬ entails (EF (visWₜ fun value : Bool => value = true))
      (log false >>= fun _ => pure ((), false) : ctreeW Bool Bn (Unit × Bool)) .pure := by
  rw [log_vis]
  intro H
  rcases eu_vis.2 H with H | ⟨_, _, H⟩
  · exact not_visWith_pure ((ticl_vis _).1 H)
  · rcases eu_ret.2 H with H | H
    · cases (ticl_vis _).1 H with | obs _ _ h => exact absurd h (by decide)
    · exact en_ret H

/-! ## Allocation faults -/

/-- An invalid free and a double free are stuck after their exact heap prefixes. -/
theorem invalid_and_double_free_prefix (ctx : Ctx) (c : Nat) :
    let allocated := managed_alloc managed_empty 1 2
    let freed : ManagedHeap := (hfree_block 1 2 allocated.1, hfree 1 allocated.2)
    (instr_flow_erased (.bind (.free 2) fun _ => .ret ()) (allocated, (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.alloc 2) fun base =>
        .bind (.free base) fun _ => .bind (.free base) fun _ => .ret ())
        (managed_empty, (ctx, c)) ~
      emit_list [CSLObs.heap allocated, .heap freed]
        (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) := by
  intro allocated freed
  refine ⟨instr_flow_free_invalid _ _ _ rfl, ?_⟩
  refine sbisim_trans (instr_flow_alloc_first 2 1 _ _ (by decide) (by decide)
    (fun _ _ => rfl) (fun _ h h' => by omega)) ?_
  simp only [emit_list_cons, emit_list_nil, log_vis]
  refine sb_vis _ fun _ => ?_
  refine sbisim_trans (instr_flow_free 1 _ _ freed rfl) ?_
  simp only [log_vis]
  exact sb_vis _ fun _ => instr_flow_free_invalid _ _ _ rfl

/-! ## Queue snapshots -/

def queue_probe_heap : Heap := new_queue_heap 1 [10, 20] hemp
def queue_probe_allocs : AllocationTable := upd hemp 1 6

/-- The header and node cells of a heap snapshot. -/
def queue_probe_view (o : CSLObs (Nat × Nat)) :
    Option (Option Nat × Option Nat × Option Nat × Option Nat) :=
  match o with
  | .heap memory => some (memory.1 1, memory.1 2, memory.1 4, memory.1 6)
  | _ => none

/-- The shared queue's allocation prefix and the first two round-robin turns, exactly. -/
theorem queue_snapshot_prefix (ctx : Ctx) (c : Nat) :
    run_rr (allocated_shared_queue [10, 20]) (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 [10, 20] managed_empty).map Sum.inl)
        (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 0) fun _ =>
          emit_list ((queue_turn_logs (.emit (stamp (2, 10) c))
              1 3 5 5 (queue_probe_heap, queue_probe_allocs)).map Sum.inl)
            (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 1) fun _ =>
              emit_list ((queue_turn_logs (.emit (stamp (1, 20) (c + 1)))
                  1 5 3 3 (qstep 1 [3, 5] queue_probe_heap, queue_probe_allocs)).map Sum.inl)
                (run_rr_pool #v[worker 2 1, worker 1 1] none 2
                  ((qstepN 1 2 [3, 5] queue_probe_heap, queue_probe_allocs),
                    (ctx, c + 2))))) ∧
    (new_queue_logs (A := Nat × Nat) 1 [10, 20] managed_empty).length = 7 ∧
    (new_queue_logs 1 [10, 20] managed_empty).map queue_probe_view =
      [some (some 0, some 0, some 0, some 0),
       some (some 5, some 0, some 0, some 0),
       some (some 5, some 3, some 0, some 0),
       some (some 5, some 3, some 0, some 0),
       some (some 5, some 3, some 5, some 0),
       some (some 5, some 3, some 5, some 0),
       some (some 5, some 3, some 5, some 0)] ∧
    (queue_turn_logs (.emit (stamp (2, 10) c)) 1 3 5 5
        (queue_probe_heap, queue_probe_allocs)).map queue_probe_view =
      [none, some (some 5, some 5, some 5, some 0),
       some (some 5, some 5, some 5, some 3),
       some (some 5, some 5, some 0, some 3),
       some (some 3, some 5, some 0, some 3)] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  refine sbisim_trans (run_rr_allocated_shared_queue [10, 20] ctx c) (emit_list_sbisim _ ?_)
  have Hq0 : qrep 1 [3, 5] [10, 20] queue_probe_heap := allocated_shared_queue_rep [10, 20]
  have Hq1 : qrep 1 [5, 3] [20, 10] (qstep 1 [3, 5] queue_probe_heap) :=
    qstep_qrep 1 [3, 5] [10, 20] queue_probe_heap Hq0 nofun
  have T0 := exact_worker_turn 2 1 3 [5] 10 [20] queue_probe_heap queue_probe_allocs ctx c Hq0
  have T1 := exact_worker_turn 1 1 5 [3] 20 [10] (qstep 1 [3, 5] queue_probe_heap)
    queue_probe_allocs ctx (c + 1) Hq1
  have g0 : (csl_pool #v[worker 2 1, worker 1 1])[0] = denote (worker 2 1) := by simp [csl_pool]
  have g1 : (csl_pool #v[worker 2 1, worker 1 1])[1] = denote (worker 1 1) := by simp [csl_pool]
  rw [← g0] at T0
  rw [← g1] at T1
  refine sbisim_trans (run_rr_two_forks (worker 1 1) (worker 2 1) _) ?_
  refine sbisim_trans (run_rr_pool_select #v[worker 2 1, worker 1 1] 0 _) ?_
  rw [rr_pick_even (n := 0) rfl]
  refine sb_vis _ fun _ => ?_
  refine sbisim_trans (run_rr_pool_turn #v[worker 2 1, worker 1 1] 0 1 _ _ _ T0)
    (emit_list_sbisim _ ?_)
  refine sbisim_trans (run_rr_pool_select #v[worker 2 1, worker 1 1] 1 _) ?_
  rw [rr_pick_odd (n := 1) rfl]
  exact sb_vis _ fun _ => run_rr_pool_turn #v[worker 2 1, worker 1 1] 1 2 _ _ _ T1

-- Not ported: none (every Rocq declaration in lines 688-1188 is ported under its name).

end Examples.CSL.Frame.HeapObservations
