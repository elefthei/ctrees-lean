/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Composition

/-!
# Fair recurrence for two queues rotated by `parallel_queues`

Under any `FairScheduler`, every element of either queue is popped again and again (`AG AF`),
starting from represented disjoint queues, from owned queues, or from freshly allocated ones; the
`_fresh` variants also require the pop to be newer than any bound `k`. Without allocation the
program faults (`AG` fails) (← `examples/CSL/Queue/Ticl.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Ticl
open CTree Tisl Tisl.Notation Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Layout
open Examples.CSL.Queue.Separation Examples.CSL.Queue.Program Examples.CSL.Queue.Composition
open ITree (Effect)

/-- `parallel_queues u v` forks `worker 2 v` and continues as `worker 1 u`: the fair pool is
`#v[worker 2 v, worker 1 u]` focused on the parent. -/
theorem run_fair_parallel_queues (sch : Scheduler) (u v : Nat) (st : sch.sched_state)
    (s : SSig) :
    run_fair sch (parallel_queues u v) st s ~
      run_fair_pool sch #v[worker 2 v, worker 1 u] (some 1) st s := by
  rw [run_fair_pool, csl_pool_pair]
  exact run_fair_fork_bind sch _ _ st s

/-! ## From represented disjoint queues -/

theorem rotate_agaf_pop_fair (sch : Scheduler) [FairScheduler sch] (st : sch.sched_state)
    (u v nl1 nl2 : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) (ns1 vs1 ns2 vs2 : List Nat)
    (d1 d2 : Nat) :
    qrep u ns1 vs1 h → qrep v ns2 vs2 h → Disj u ns1 v ns2 →
    find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed fun o : Indexed (Nat × Nat) =>
        o.value = (1, nl1))))))
      (run_fair sch (parallel_queues u v) st ((h, allocs), (ctx, c))) .pure :=
  fun H1 H2 Hd F1 F2 => (proper_entails_meq _ (run_fair_parallel_queues sch u v st _)).2
    (fair_agaf_q1_gen sch u v nl1 nl2 0 _ (fun _ _ => rfl) _ st h allocs ctx c ns1 vs1 ns2 vs2
      d1 d2 .pure H1 H2 Hd F1 F2 .pure)

theorem rotate_agaf_pop_fair_q2 (sch : Scheduler) [FairScheduler sch] (st : sch.sched_state)
    (u v nl1 nl2 : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) (ns1 vs1 ns2 vs2 : List Nat)
    (d1 d2 : Nat) :
    qrep u ns1 vs1 h → qrep v ns2 vs2 h → Disj u ns1 v ns2 →
    find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed fun o : Indexed (Nat × Nat) =>
        o.value = (2, nl2))))))
      (run_fair sch (parallel_queues u v) st ((h, allocs), (ctx, c))) .pure :=
  fun H1 H2 Hd F1 F2 => (proper_entails_meq _ (run_fair_parallel_queues sch u v st _)).2
    (fair_agaf_q2_gen sch u v nl1 nl2 0 _ (fun _ _ => rfl) _ st h allocs ctx c ns1 vs1 ns2 vs2
      d1 d2 .pure H1 H2 Hd F1 F2 .pure)

theorem rotate_agaf_pop_fair_fresh (sch : Scheduler) [FairScheduler sch] (st : sch.sched_state)
    (u v nl1 nl2 k : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) (ns1 vs1 ns2 vs2 : List Nat)
    (d1 d2 : Nat) :
    qrep u ns1 vs1 h → qrep v ns2 vs2 h → Disj u ns1 v ns2 →
    find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed (indexed_after (· = (1, nl1)) k))))))
      (run_fair sch (parallel_queues u v) st ((h, allocs), (ctx, c))) .pure :=
  fun H1 H2 Hd F1 F2 => (proper_entails_meq _ (run_fair_parallel_queues sch u v st _)).2
    (fair_agaf_q1_gen sch u v nl1 nl2 k _ (fun _ hj => show _ ∧ _ from ⟨rfl, hj⟩) _ st h
      allocs ctx c ns1 vs1 ns2 vs2 d1 d2 .pure H1 H2 Hd F1 F2 .pure)

theorem rotate_agaf_pop_fair_q2_fresh (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (u v nl1 nl2 k : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat)
    (ns1 vs1 ns2 vs2 : List Nat) (d1 d2 : Nat) :
    qrep u ns1 vs1 h → qrep v ns2 vs2 h → Disj u ns1 v ns2 →
    find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed (indexed_after (· = (2, nl2)) k))))))
      (run_fair sch (parallel_queues u v) st ((h, allocs), (ctx, c))) .pure :=
  fun H1 H2 Hd F1 F2 => (proper_entails_meq _ (run_fair_parallel_queues sch u v st _)).2
    (fair_agaf_q2_gen sch u v nl1 nl2 k _ (fun _ hj => show _ ∧ _ from ⟨rfl, hj⟩) _ st h
      allocs ctx c ns1 vs1 ns2 vs2 d1 d2 .pure H1 H2 Hd F1 F2 .pure)

/-- From an owned (separating-conjunction) precondition. -/
theorem rotate_agaf_pop_fair_owned (sch : Scheduler) [FairScheduler sch] (st : sch.sched_state)
    (u v nl1 nl2 : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) (ns1 vs1 ns2 vs2 : List Nat)
    (d1 d2 : Nat) :
    owned_queues u ns1 vs1 v ns2 vs2 h →
    find_index Nat.beq nl1 vs1 = some d1 → find_index Nat.beq nl2 vs2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed fun o : Indexed (Nat × Nat) =>
        o.value = (1, nl1))))))
      (run_fair sch (parallel_queues u v) st ((h, allocs), (ctx, c))) .pure := fun Hown F1 F2 =>
  have ⟨H1, H2, Hd⟩ := owned_queues_sound u ns1 vs1 v ns2 vs2 h Hown
  rotate_agaf_pop_fair sch st u v nl1 nl2 h allocs ctx c ns1 vs1 ns2 vs2 d1 d2 H1 H2 Hd F1 F2

/-! ## From freshly allocated queues -/

/-- Shared allocation prefix: after `allocated_parallel_queues`, both workers run on owned
queues, so any per-queue `AG AF` result from `fair_agaf_q*_gen` transports through the logs. -/
private theorem alloc_agaf (sch : Scheduler) (st : sch.sched_state)
    (values1 values2 : List Nat) (ctx : Ctx) (c : Nat) (P : Indexed (Nat × Nat) → Prop)
    (hgen : ∀ u v h allocs w, qrep u (queue_nodes u values1.length) values1 h →
      qrep v (queue_nodes v values2.length) values2 h →
      Disj u (queue_nodes u values1.length) v (queue_nodes v values2.length) → NotDone w →
      entails (AG (AF (visWₜ (fair_obs (csl_indexed P)))))
        (run_fair_pool sch #v[worker 2 v, worker 1 u] (some 1) st ((h, allocs), (ctx, c))) w) :
    entails (AG (AF (visWₜ (fair_obs (csl_indexed P)))))
      (run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty, (ctx, c)))
      .pure := by
  obtain ⟨u, v, h, allocs, -, hown, hrun⟩ :=
    run_fair_allocated_parallel sch values1 values2 st ctx c
  obtain ⟨H1, H2, Hd⟩ := owned_queues_sound _ _ _ _ _ _ _ hown
  refine (proper_entails_meq _ hrun).2 (agaf_emit_list _ _ _ _ .pure ?_)
  exact (proper_entails_meq _ (run_fair_parallel_queues sch u v st _)).2
    (hgen u v h allocs _ H1 H2 Hd (after_logs_not_done _ .pure))

theorem rotate_agaf_pop_alloc (sch : Scheduler) [FairScheduler sch] (st : sch.sched_state)
    (values1 values2 : List Nat) (nl1 nl2 : Nat) (ctx : Ctx) (c d1 d2 : Nat) :
    find_index Nat.beq nl1 values1 = some d1 → find_index Nat.beq nl2 values2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed fun o : Indexed (Nat × Nat) =>
        o.value = (1, nl1))))))
      (run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty, (ctx, c)))
      .pure := fun F1 F2 =>
  alloc_agaf sch st values1 values2 ctx c _ fun u v h allocs w H1 H2 Hd hw =>
    fair_agaf_q1_gen sch u v nl1 nl2 0 _ (fun _ _ => rfl) _ st h allocs ctx c _ _ _ _
      d1 d2 w H1 H2 Hd F1 F2 hw

theorem rotate_agaf_pop_alloc_q2 (sch : Scheduler) [FairScheduler sch] (st : sch.sched_state)
    (values1 values2 : List Nat) (nl1 nl2 : Nat) (ctx : Ctx) (c d1 d2 : Nat) :
    find_index Nat.beq nl1 values1 = some d1 → find_index Nat.beq nl2 values2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed fun o : Indexed (Nat × Nat) =>
        o.value = (2, nl2))))))
      (run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty, (ctx, c)))
      .pure := fun F1 F2 =>
  alloc_agaf sch st values1 values2 ctx c _ fun u v h allocs w H1 H2 Hd hw =>
    fair_agaf_q2_gen sch u v nl1 nl2 0 _ (fun _ _ => rfl) _ st h allocs ctx c _ _ _ _
      d1 d2 w H1 H2 Hd F1 F2 hw

theorem rotate_agaf_pop_alloc_fresh (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (values1 values2 : List Nat) (nl1 nl2 k : Nat) (ctx : Ctx)
    (c d1 d2 : Nat) :
    find_index Nat.beq nl1 values1 = some d1 → find_index Nat.beq nl2 values2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed (indexed_after (· = (1, nl1)) k))))))
      (run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty, (ctx, c)))
      .pure := fun F1 F2 =>
  alloc_agaf sch st values1 values2 ctx c _ fun u v h allocs w H1 H2 Hd hw =>
    fair_agaf_q1_gen sch u v nl1 nl2 k _ (fun _ hj => show _ ∧ _ from ⟨rfl, hj⟩) _ st h allocs
      ctx c _ _ _ _ d1 d2 w H1 H2 Hd F1 F2 hw

theorem rotate_agaf_pop_alloc_q2_fresh (sch : Scheduler) [FairScheduler sch]
    (st : sch.sched_state) (values1 values2 : List Nat) (nl1 nl2 k : Nat) (ctx : Ctx)
    (c d1 d2 : Nat) :
    find_index Nat.beq nl1 values1 = some d1 → find_index Nat.beq nl2 values2 = some d2 →
    entails (AG (AF (visWₜ (fair_obs (csl_indexed (indexed_after (· = (2, nl2)) k))))))
      (run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty, (ctx, c)))
      .pure := fun F1 F2 =>
  alloc_agaf sch st values1 values2 ctx c _ fun u v h allocs w H1 H2 Hd hw =>
    fair_agaf_q2_gen sch u v nl1 nl2 k _ (fun _ hj => show _ ∧ _ from ⟨rfl, hj⟩) _ st h allocs
      ctx c _ _ _ _ d1 d2 w H1 H2 Hd F1 F2 hw

/-! ## Without allocation the program faults -/

theorem parallel_queues_hemp_no_ag (u v : Nat) (ctx : Ctx) (c : Nat)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    ¬ entails (AG φ) (run_rr (parallel_queues u v) (managed_empty, (ctx, c))) w := by
  rw [proper_entails_meq _ (parallel_queues_hemp_stuck u v ctx c)]
  exact ag_stuck

theorem allocated_parallel_queues_empty_no_ag (values : List Nat) (ctx : Ctx) (c : Nat)
    (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat)))
    (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    ¬ entails (AG φ) (run_rr (allocated_parallel_queues [] values) (managed_empty, (ctx, c)))
      w := by
  obtain ⟨u, v, hrun⟩ := allocated_parallel_queues_empty_stuck values ctx c
  rw [proper_entails_meq _ hrun]
  exact ag_emit_list_stuck _ _ _

end Examples.CSL.Queue.Ticl
