/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Program
public import Logic.Yield.Fair
public import Logic.CTree.TraceRules

/-!
# Shared: one finite heap queue rotated forever by two spawned workers

Both workers of `shared_queue` rotate the SAME queue. Each scheduled turn of either worker is an
exact first-yield segment logging one pop and four post-write snapshots, then rotating the queue
once (`exact_worker_turn`). The certificate `shared_worker_turn` is the queue's standard rank
argument, stated per worker slot so that it is independent of which worker the scheduler selects
(← `examples/CSL/Queue/Shared.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Shared
open CTree Tisl Tisl.Notation Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Operations Examples.CSL.Queue.Layout
open Examples.CSL.Queue.Trace Examples.CSL.Queue.Frame Examples.CSL.Queue.Program
open ITree (Effect)

/-! ## One worker turn as an exact source segment -/

theorem exact_worker_turn (tag hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    qrep hdr (a :: ns) (v :: vs) h →
    segment_to sh csl_equ (denote (worker tag hdr)) ((h, allocs), (ctx, c))
      (queue_turn_logs (.emit (stamp (tag, v) c)) hdr a (ns.headD 0) ((a :: ns).getLastD 0)
        (h, allocs))
      (denote (worker tag hdr))
      ((rot_heap hdr a (ns.headD 0) (zof hdr ns) h, allocs), (ctx, c + 1)) := by
  intro hq
  have hzdom := qrep_zof_dom _ _ _ _ _ _ hq
  obtain ⟨hwf, hhd, htl, hch, -, hfp⟩ := hq
  obtain ⟨ha, hsa, -⟩ := (chain_cons _ _ _ _ _ _).1 hch
  obtain ⟨-, -, -, -, hhshdr⟩ := qwf_neqs _ _ _ hwf
  have hhdrdom : h hdr ≠ none := hfp _ (.head _)
  have hsadom : h (a + 1) ≠ none := by rw [hsa]; simp
  have hshdrdom : h (hdr + 1) ≠ none := by rw [hhd]; simp
  have hread_hdr : upd h (hdr + 1) (ns.headD 0) hdr = some ((a :: ns).getLastD 0) := by
    rw [upd_neq _ _ _ _ hhshdr]; exact htl
  rw [← zof_compute hdr a ns hwf] at hzdom ⊢
  simp only [queue_turn_logs, denote, worker]
  apply exact_source_until
  apply exact_source_bind
  unfold rotate_once
  apply exact_source_bind; refine exact_source_read _ _ _ _ _ _ _ _ _ _ hhd ?_; dsimp only
  apply exact_source_bind; refine exact_source_read _ _ _ _ _ _ _ _ _ _ ha ?_; dsimp only
  apply exact_source_bind; refine exact_source_emit _ _ _ _ _ _ _ _ _ ?_; dsimp only
  apply exact_source_bind; refine exact_source_read _ _ _ _ _ _ _ _ _ _ hsa ?_; dsimp only
  apply exact_source_bind; refine exact_source_write _ _ _ _ _ _ _ _ _ _ hshdrdom ?_
  dsimp only
  apply exact_source_bind; refine exact_source_read _ _ _ _ _ _ _ _ _ _ hread_hdr ?_
  dsimp only
  apply exact_source_bind
  refine exact_source_write _ _ _ _ _ _ _ _ _ _ (upd_mono _ _ _ _ hzdom) ?_; dsimp only
  apply exact_source_bind
  refine exact_source_write _ _ _ _ _ _ _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ hsadom)) ?_
  dsimp only
  refine exact_source_write _ _ _ _ _ _ _ _ _ _
    (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ hhdrdom))) ?_
  dsimp only
  apply exact_source_bind; apply exact_source_yield; dsimp only
  rw [source_raw_ret]
  exact guard_equ_left _ _ (guard_equ_equ _ _ rfl)

/-! ## Observation targets and the shared-queue invariant -/

def shared_pop (nl : Nat) : CSLObs (Nat × Nat) → Prop :=
  csl_indexed fun o => o.value.2 = nl

def shared_pop_after (nl k : Nat) : CSLObs (Nat × Nat) → Prop :=
  csl_indexed (indexed_after (fun p => p.2 = nl) k)

def SharedInv (hdr nl k : Nat) (g : Nat × Nat) (s : SSig) : Prop :=
  ∃ ns vs d, qrep hdr ns vs (csl_memory s).1 ∧ find_index Nat.beq nl vs = some d ∧
    g = (k - csl_counter s, d)

/-- Either worker's turn preserves the invariant and either meets the target or strictly
decreases the rank `(k - counter, position of nl)`. -/
theorem shared_worker_turn (tag hdr nl k : Nat) (g : Nat × Nat) (s : SSig) :
    SharedInv hdr nl k g s →
    ∃ g' s' logs,
      segment_to sh csl_equ (denote (worker tag hdr)) s logs (denote (worker tag hdr)) s' ∧
      SharedInv hdr nl k g' s' ∧ ((∃ o ∈ logs, shared_pop_after nl k o) ∨ lexnat g' g) := by
  rintro ⟨ns, vs, d, hq, hf, rfl⟩
  obtain ⟨⟨h, allocs⟩, ctx, c⟩ := s
  simp only [csl_memory, csl_counter] at hq ⊢
  match vs, ns, hq, hf with
  | [], _, _, hf => simp [find_index] at hf
  | _ :: _, [], hq, _ => have := qrep_len _ _ _ _ hq; simp at this
  | v :: vs', a :: ns', hq, hf =>
    have hstep : ∀ d', find_index Nat.beq nl (vs' ++ [v]) = some d' →
        SharedInv hdr nl k (k - (c + 1), d')
          ((rot_heap hdr a (ns'.headD 0) (zof hdr ns') h, allocs), (ctx, c + 1)) :=
      fun d' hd' => ⟨ns' ++ [a], vs' ++ [v], d', (rot_heap_spec hdr a ns' v vs' h hq).1, hd', rfl⟩
    have hturn := exact_worker_turn tag hdr a ns' v vs' h allocs ctx c hq
    obtain ⟨d', hd', ⟨rfl, hle⟩ | hrank⟩ :=
      find_index_rotation_progress Nat.beq (fun _ _ => Nat.beq_eq.to_iff) nl v vs' d hf k c
    · exact ⟨_, _, _, hturn, hstep d' hd', .inl ⟨_, .head _, rfl, hle⟩⟩
    · exact ⟨_, _, _, hturn, hstep d' hd', .inr (Prod.lex_def.2 hrank)⟩

/-! ## The two-worker pool and its turn certificates

After both forks the parent has terminated and the pool is `#v[worker 2 hdr, worker 1 hdr]`.
Either slot closes a turn from every invariant state, so neither the nondeterministic nor the
round-robin proof needs a fairness or phase argument. -/

theorem shared_ranked (hdr nl k : Nat) :
    RankedTurns sh (csl_pool #v[worker 2 hdr, worker 1 hdr]) (SharedInv hdr nl k) (fun g => g)
      lexnat (shared_pop_after nl k) := by
  intro g s i hinv
  rw [csl_pool_pair]
  match i with
  | 0 => exact shared_worker_turn 2 hdr nl k g s hinv
  | 1 => exact shared_worker_turn 1 hdr nl k g s hinv

theorem shared_pool_agaf_nd (hdr nl k : Nat) (g : Nat × Nat) (s : SSig)
    (w0 : World (writerE (CSLObs (Nat × Nat)))) (P : CSLObs (Nat × Nat) → Prop) :
    RankedTurns sh (csl_pool #v[worker 2 hdr, worker 1 hdr]) (SharedInv hdr nl k) (fun g => g)
      lexnat P →
    SharedInv hdr nl k g s → NotDone w0 →
    entails (AG (AF (visWₜ P))) (run_nd_pool #v[worker 2 hdr, worker 1 hdr] none s) w0 :=
  fun hr hinv hw0 =>
    ag_csl_nd_invariance _ (SharedInv hdr nl k) _ (ranked_turns_closed sh _ _ _ _ _ hr)
      (fun o t w hw hφ => by have := af_log (s := o) (k := t) hw hφ; rwa [log_vis] at this)
      (fun g0 s0 focus w hinv0 hw =>
        aul_csl_nd_eventually _ _ (fun g => g) lexnat P lexnat_wf hr g0 s0 focus w hinv0 hw)
      g s none w0 hinv hw0

/-- Under ANY fair policy: both slots close a turn that hits the target or drops the rank, so
every slot is helpful; slot `0` is picked arbitrarily. -/
theorem shared_pool_agaf_fair (sch : Scheduler) [FairScheduler sch] (hdr nl k : Nat)
    (g : Nat × Nat) (s : SSig) (focus : Option (Fin 2)) (st : sch.sched_state)
    (w0 : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) (P : CSLObs (Nat × Nat) → Prop) :
    RankedTurns sh (csl_pool #v[worker 2 hdr, worker 1 hdr]) (SharedInv hdr nl k) (fun g => g)
      lexnat P →
    SharedInv hdr nl k g s → NotDone w0 →
    entails (AG (AF (visWₜ (fair_obs P))))
      (run_fair_pool sch #v[worker 2 hdr, worker 1 hdr] focus st s) w0 := by
  intro hr hinv hw0
  refine agaf_fair_turns sh sch _ 0 (SharedInv hdr nl k) (fun g => g) lexnat P lexnat_wf ?_
    g s focus st w0 hinv hw0
  intro g0 s0 j hinv0
  obtain ⟨g', s', logs, hseg, hinv', hcase⟩ := hr g0 s0 j hinv0
  exact ⟨g', s', logs, hseg, hinv', hcase.imp id .inl⟩

/-- Round robin is the logged fair-policy specialisation. -/
theorem shared_pool_agaf_rr (hdr nl k : Nat) (g : Nat × Nat) (s : SSig) (cursor : Nat)
    (w0 : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) (P : CSLObs (Nat × Nat) → Prop) :
    RankedTurns sh (csl_pool #v[worker 2 hdr, worker 1 hdr]) (SharedInv hdr nl k) (fun g => g)
      lexnat P →
    SharedInv hdr nl k g s → NotDone w0 →
    entails (AG (AF (visWₜ (fair_obs P))))
      (run_rr_pool #v[worker 2 hdr, worker 1 hdr] none cursor s) w0 :=
  shared_pool_agaf_fair rr_scheduler hdr nl k g s none cursor w0 P

/-! ## Recurrence of the actual shared program from a represented queue -/

private theorem pop_after_zero (nl : Nat) (o : CSLObs (Nat × Nat)) :
    shared_pop_after nl 0 o → shared_pop nl o := by
  cases o <;> simp [shared_pop_after, shared_pop, csl_indexed, indexed_after]

theorem shared_rotate_agaf_pop_nd_fresh (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d k : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (shared_pop_after nl k))))
      (run_nd (shared_queue hdr) ((h, allocs), (ctx, c))) .pure := fun hq hf =>
  (proper_entails_meq _ (run_nd_two_forks _ _ _)).2
    (shared_pool_agaf_nd hdr nl k (k - c, d) _ _ _ (shared_ranked hdr nl k)
      ⟨ns, vs, d, hq, hf, rfl⟩ .pure)

theorem shared_rotate_agaf_pop_rr_fresh (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d k : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop_after nl k)))))
      (run_rr (shared_queue hdr) ((h, allocs), (ctx, c))) .pure := fun hq hf =>
  (proper_entails_meq _ (run_rr_two_forks _ _ _)).2
    (shared_pool_agaf_rr hdr nl k (k - c, d) _ _ _ _ (shared_ranked hdr nl k)
      ⟨ns, vs, d, hq, hf, rfl⟩ .pure)

theorem shared_rotate_agaf_pop_fair_fresh (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d k : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop_after nl k)))))
      (run_fair sch (shared_queue hdr) st ((h, allocs), (ctx, c))) .pure := fun hq hf =>
  (proper_entails_meq _ (run_fair_two_forks _ _ _ _ _)).2
    (shared_pool_agaf_fair sch hdr nl k (k - c, d) _ _ _ _ _ (shared_ranked hdr nl k)
      ⟨ns, vs, d, hq, hf, rfl⟩ .pure)

theorem shared_rotate_agaf_pop_nd (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (shared_pop nl))))
      (run_nd (shared_queue hdr) ((h, allocs), (ctx, c))) .pure := fun hq hf =>
  (proper_entails_meq _ (run_nd_two_forks _ _ _)).2
    (shared_pool_agaf_nd hdr nl 0 (0 - c, d) _ _ _
      (ranked_turns_mono sh _ _ _ _ _ _ (pop_after_zero nl) (shared_ranked hdr nl 0))
      ⟨ns, vs, d, hq, hf, rfl⟩ .pure)

theorem shared_rotate_agaf_pop_rr (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop nl)))))
      (run_rr (shared_queue hdr) ((h, allocs), (ctx, c))) .pure := fun hq hf =>
  (proper_entails_meq _ (run_rr_two_forks _ _ _)).2
    (shared_pool_agaf_rr hdr nl 0 (0 - c, d) _ _ _ _
      (ranked_turns_mono sh _ _ _ _ _ _ (pop_after_zero nl) (shared_ranked hdr nl 0))
      ⟨ns, vs, d, hq, hf, rfl⟩ .pure)

theorem shared_rotate_agaf_pop_fair (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (hdr nl : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns vs : List Nat) (d : Nat) :
    qrep hdr ns vs h → find_index Nat.beq nl vs = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop nl)))))
      (run_fair sch (shared_queue hdr) st ((h, allocs), (ctx, c))) .pure := fun hq hf =>
  (proper_entails_meq _ (run_fair_two_forks _ _ _ _ _)).2
    (shared_pool_agaf_fair sch hdr nl 0 (0 - c, d) _ _ _ _ _
      (ranked_turns_mono sh _ _ _ _ _ _ (pop_after_zero nl) (shared_ranked hdr nl 0))
      ⟨ns, vs, d, hq, hf, rfl⟩ .pure)

/-! ## The allocated program -/

theorem allocated_shared_queue_rep (values : List Nat) :
    qrep 1 (queue_nodes 1 values.length) values (new_queue_heap 1 values hemp) := by
  have hq := qheap_queue_nodes_rep 1 values (by omega)
  have hagree := new_queue_heap_agrees 1 values hemp (by omega) (fun _ _ => rfl)
  refine qrep_agree_fp 1 _ _ _ _ hq (fun x _ => ?_) ?_
  · rw [hagree x]; unfold hunion hemp; split <;> simp_all
  · rw [hagree 0]; unfold hunion; rw [qrep_null _ _ _ _ hq]; rfl

theorem shared_rotate_agaf_pop_alloc_nd (values : List Nat) (nl : Nat) (ctx : Ctx) (c d : Nat) :
    find_index Nat.beq nl values = some d →
    entails (AG (AF (visWₜ (shared_pop nl))))
      (run_nd (allocated_shared_queue values) (managed_empty, (ctx, c))) .pure := fun hf =>
  (proper_entails_meq _ (run_nd_allocated_shared_queue values ctx c)).2
    (agaf_emit_list _ _ _ _ .pure ((proper_entails_meq _ (run_nd_two_forks _ _ _)).2
      (shared_pool_agaf_nd 1 nl 0 (0 - c, d) _ _ _
        (ranked_turns_mono sh _ _ _ _ _ _ (pop_after_zero nl) (shared_ranked 1 nl 0))
        ⟨_, values, d, allocated_shared_queue_rep values, hf, rfl⟩
        (after_logs_not_done _ .pure))))

theorem shared_rotate_agaf_pop_alloc_rr (values : List Nat) (nl : Nat) (ctx : Ctx) (c d : Nat) :
    find_index Nat.beq nl values = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop nl)))))
      (run_rr (allocated_shared_queue values) (managed_empty, (ctx, c))) .pure := fun hf =>
  (proper_entails_meq _ (run_rr_allocated_shared_queue values ctx c)).2
    (agaf_emit_list _ _ _ _ .pure ((proper_entails_meq _ (run_rr_two_forks _ _ _)).2
      (shared_pool_agaf_rr 1 nl 0 (0 - c, d) _ _ _ _
        (ranked_turns_mono sh _ _ _ _ _ _ (pop_after_zero nl) (shared_ranked 1 nl 0))
        ⟨_, values, d, allocated_shared_queue_rep values, hf, rfl⟩
        (after_logs_not_done _ .pure))))

theorem shared_rotate_agaf_pop_alloc_fair (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (values : List Nat) (nl : Nat) (ctx : Ctx) (c d : Nat) :
    find_index Nat.beq nl values = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop nl)))))
      (run_fair sch (allocated_shared_queue values) st (managed_empty, (ctx, c))) .pure :=
  fun hf =>
  (proper_entails_meq _ (run_fair_allocated_shared_queue sch values st ctx c)).2
    (agaf_emit_list _ _ _ _ .pure ((proper_entails_meq _ (run_fair_two_forks _ _ _ _ _)).2
      (shared_pool_agaf_fair sch 1 nl 0 (0 - c, d) _ _ _ _ _
        (ranked_turns_mono sh _ _ _ _ _ _ (pop_after_zero nl) (shared_ranked 1 nl 0))
        ⟨_, values, d, allocated_shared_queue_rep values, hf, rfl⟩
        (after_logs_not_done _ .pure))))

theorem shared_rotate_agaf_pop_alloc_fair_fresh (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (values : List Nat) (nl : Nat) (ctx : Ctx) (c d k : Nat) :
    find_index Nat.beq nl values = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop_after nl k)))))
      (run_fair sch (allocated_shared_queue values) st (managed_empty, (ctx, c))) .pure :=
  fun hf =>
  (proper_entails_meq _ (run_fair_allocated_shared_queue sch values st ctx c)).2
    (agaf_emit_list _ _ _ _ .pure ((proper_entails_meq _ (run_fair_two_forks _ _ _ _ _)).2
      (shared_pool_agaf_fair sch 1 nl k (k - c, d) _ _ _ _ _ (shared_ranked 1 nl k)
        ⟨_, values, d, allocated_shared_queue_rep values, hf, rfl⟩
        (after_logs_not_done _ .pure))))

theorem shared_rotate_agaf_pop_alloc_nd_fresh (values : List Nat) (nl : Nat) (ctx : Ctx)
    (c d k : Nat) :
    find_index Nat.beq nl values = some d →
    entails (AG (AF (visWₜ (shared_pop_after nl k))))
      (run_nd (allocated_shared_queue values) (managed_empty, (ctx, c))) .pure := fun hf =>
  (proper_entails_meq _ (run_nd_allocated_shared_queue values ctx c)).2
    (agaf_emit_list _ _ _ _ .pure ((proper_entails_meq _ (run_nd_two_forks _ _ _)).2
      (shared_pool_agaf_nd 1 nl k (k - c, d) _ _ _ (shared_ranked 1 nl k)
        ⟨_, values, d, allocated_shared_queue_rep values, hf, rfl⟩
        (after_logs_not_done _ .pure))))

theorem shared_rotate_agaf_pop_alloc_rr_fresh (values : List Nat) (nl : Nat) (ctx : Ctx)
    (c d k : Nat) :
    find_index Nat.beq nl values = some d →
    entails (AG (AF (visWₜ (fair_obs (shared_pop_after nl k)))))
      (run_rr (allocated_shared_queue values) (managed_empty, (ctx, c))) .pure := fun hf =>
  (proper_entails_meq _ (run_rr_allocated_shared_queue values ctx c)).2
    (agaf_emit_list _ _ _ _ .pure ((proper_entails_meq _ (run_rr_two_forks _ _ _)).2
      (shared_pool_agaf_rr 1 nl k (k - c, d) _ _ _ _ (shared_ranked 1 nl k)
        ⟨_, values, d, allocated_shared_queue_rep values, hf, rfl⟩
        (after_logs_not_done _ .pure))))

/-! ## Concrete execution

The first three complete rotations of the allocated program under round robin: worker 2 runs
first (the parent is gone and the cursor is still `0`), then worker 1, then worker 2 again, each
rotating the same queue once and logging one pop and four snapshots. Every scheduling decision
logs its slot via `.inr` (`run_rr_pool_select`). -/

theorem shared_queue_rr_prefix3 :
    let h0 := new_queue_heap 1 [10, 20, 30] hemp
    let h3 := qstepN 1 3 [3, 5, 7] h0
    run_rr (allocated_shared_queue [10, 20, 30]) (managed_empty, ([], 0)) ~
      emit_list ((new_queue_logs 1 [10, 20, 30] managed_empty).map .inl)
      (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 0) fun _ =>
      emit_list ((queue_turn_logs (.emit (stamp (2, 10) 0)) 1 3 5 7 (h0, upd hemp 1 8)).map .inl)
      (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 1) fun _ =>
      emit_list ((queue_turn_logs (.emit (stamp (1, 20) 1)) 1 5 7 3
        (qstep 1 [3, 5, 7] h0, upd hemp 1 8)).map .inl)
      (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 0) fun _ =>
      emit_list ((queue_turn_logs (.emit (stamp (2, 30) 2)) 1 7 3 5
        (qstep 1 [5, 7, 3] (qstep 1 [3, 5, 7] h0), upd hemp 1 8)).map .inl)
      (run_rr_pool #v[worker 2 1, worker 1 1] none 3 ((h3, upd hemp 1 8), ([], 3)))))) := by
  intro h0 h3
  have hq0 : qrep 1 [3, 5, 7] [10, 20, 30] h0 := allocated_shared_queue_rep [10, 20, 30]
  have hq1 : qrep 1 [5, 7, 3] [20, 30, 10] (qstep 1 [3, 5, 7] h0) :=
    qstep_qrep 1 _ _ h0 hq0 (by simp)
  have hq2 : qrep 1 [7, 3, 5] [30, 10, 20] (qstep 1 [5, 7, 3] (qstep 1 [3, 5, 7] h0)) :=
    qstep_qrep 1 _ _ _ hq1 (by simp)
  refine sbisim_trans (run_rr_allocated_shared_queue _ _ _) (emit_list_sbisim _ ?_)
  refine sbisim_trans (run_rr_two_forks _ _ _) ?_
  -- worker 2
  refine sbisim_trans (run_rr_pool_select _ 0 _) (sb_vis _ fun _ => ?_)
  refine sbisim_trans (run_rr_pool_turn _ 0 1 _ ((qstep 1 [3, 5, 7] h0, upd hemp 1 8), ([], 1))
    _ ?_) (emit_list_sbisim _ ?_)
  · rw [csl_pool_pair]
    exact exact_worker_turn 2 1 3 [5, 7] 10 [20, 30] h0 (upd hemp 1 8) [] 0 hq0
  -- worker 1
  refine sbisim_trans (run_rr_pool_select _ 1 _) (sb_vis _ fun _ => ?_)
  refine sbisim_trans (run_rr_pool_turn _ 1 2 _
    ((qstep 1 [5, 7, 3] (qstep 1 [3, 5, 7] h0), upd hemp 1 8), ([], 2)) _ ?_)
    (emit_list_sbisim _ ?_)
  · rw [csl_pool_pair]
    exact exact_worker_turn 1 1 5 [7, 3] 20 [30, 10] _ (upd hemp 1 8) [] 1 hq1
  -- worker 2 again
  refine sbisim_trans (run_rr_pool_select _ 2 _) (sb_vis _ fun _ => ?_)
  refine sbisim_trans (run_rr_pool_turn _ 0 3 _ ((h3, upd hemp 1 8), ([], 3)) _ ?_)
    (emit_list_sbisim _ ?_)
  · rw [csl_pool_pair]
    exact exact_worker_turn 2 1 7 [3, 5] 30 [10, 20] _ (upd hemp 1 8) [] 2 hq2
  exact sbisim_refl _

/-! ## The empty queue faults

An allocated empty queue has a null head pointer and the null cell is unallocated: after the
scheduler's logged pick, the first worker turn reads it and the whole run is stuck, so no `AG`
formula holds. -/

theorem allocated_shared_queue_empty_stuck (ctx : Ctx) (c : Nat) :
    run_rr (allocated_shared_queue []) (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 [] managed_empty).map .inl)
        (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 0) fun _ =>
          (CTree.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig))) := by
  refine sbisim_trans (run_rr_allocated_shared_queue _ _ _) (emit_list_sbisim _ ?_)
  refine sbisim_trans (run_rr_two_forks _ _ _) ?_
  refine sbisim_trans (run_rr_pool_select _ 0 _) (sb_vis _ fun _ => ?_)
  have hpool : csl_pool #v[worker 2 1, worker 1 1] =
      (#v[pure ⟨⟩, denote (worker 1 1)] : Pool sE Bn 2).set ((0 : Fin 2) : Nat)
        (denote_flow (worker 2 1) >>= fun _ => pure ⟨⟩) := by
    simp [csl_pool, denote]
  unfold run_rr_pool
  rw [hpool, rr_pick_even (n := 0) rfl]
  unfold worker
  rw [interp_rr_until_none, interp_rr_bind]
  unfold rotate_once
  rw [interp_rr_bind]
  refine sbisim_trans (interp_rr_read_value _ _ _ _ 0 _ _ _ _ _ _ (by decide)) ?_
  dsimp only
  rw [interp_rr_bind]
  exact interp_rr_read_missing _ _ _ _ _ _ _ _ _ _ (by decide)

theorem allocated_shared_queue_empty_no_ag (ctx : Ctx) (c : Nat)
    (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    ¬ entails (AG φ) (run_rr (allocated_shared_queue []) (managed_empty, (ctx, c))) w := by
  rw [proper_entails_meq _ (allocated_shared_queue_empty_stuck ctx c)]
  intro h
  have h' := (ag_vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (e := .inr 0) PUnit.unit).2
    (ag_emit_list_suffix _ _ _ _ h)
  exact ag_stuck (h'.2 PUnit.unit)

end Examples.CSL.Queue.Shared
