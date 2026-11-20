/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Lang.CoCSL.Sequential
public import Examples.CSL.Queue.Alternating
public import Examples.CSL.Queue.Separation

/-!
# The queue as a CoCSL program

The rotating queue written in the source language: one rotation `rotate_once`, a yielding
`worker` loop, two forked workers `parallel_queues`, and the allocating constructors `new_queue`,
`allocated_parallel_queues`, `allocated_shared_queue`. Under the source round-robin scheduler the
two-worker pool is bisimilar to the reference alternating scheduler `srun`; allocation and
initialization are exact under every policy (← `examples/CSL/Queue/Program.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Program
open CTree Tisl Tisl.Heap Tisl.Pcm Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Layout Examples.CSL.Queue.Operations
open Examples.CSL.Queue.Alternating Examples.CSL.Queue.Trace Examples.CSL.Queue.Frame
open Examples.CSL.Queue.Separation
open ITree (Effect)

/-! ## Programs -/

/-- One rotation of the queue at `hdr`, emitting the popped payload with tag `q`. -/
def rotate_once (q hdr : Nat) : CProg Unit :=
  .bind (.read (hdr + 1)) fun a =>
  .bind (.read a) fun v =>
  .bind (.emit q v) fun _ =>
  .bind (.read (a + 1)) fun n =>
  .bind (.write (hdr + 1) n) fun _ =>
  .bind (.read hdr) fun z0 =>
  .bind (.write ((if n == 0 then hdr else z0) + 1) a) fun _ =>
  .bind (.write (a + 1) 0) fun _ =>
  .write hdr a

def worker (q hdr : Nat) : CProg Unit :=
  .untilNone (.bind (rotate_once q hdr) fun _ => .bind .yield fun _ => .ret (some ()))

def parallel_queues (u v : Nat) : CProg Unit :=
  .bind (.fork (worker 2 v)) fun _ => worker 1 u

def fill_nodes (first : Nat) (values : List Nat) : CProg Unit :=
  write_list (node_writes (node_addrs first values.length) values)

def init_queue (hdr : Nat) (values : List Nat) : CProg Unit :=
  let ns := queue_nodes hdr values.length
  .bind (.write hdr (ns.getLastD 0)) fun _ =>
  .bind (.write (hdr + 1) (ns.headD 0)) fun _ =>
  fill_nodes (hdr + 2) values

def new_queue (values : List Nat) : CProg Nat :=
  .bind (.alloc (2 * (values.length + 1))) fun hdr =>
  .bind (init_queue hdr values) fun _ => .ret hdr

def fill_nodes_logs {A : Type} (first : Nat) (values : List Nat) (memory : ManagedHeap) :
    List (CSLObs A) :=
  write_snapshots (node_writes (node_addrs first values.length) values) memory

def init_queue_logs {A : Type} (hdr : Nat) (values : List Nat) (memory : ManagedHeap) :
    List (CSLObs A) :=
  let ns := queue_nodes hdr values.length
  let h1 := upd memory.1 hdr (ns.getLastD 0)
  let h2 := upd h1 (hdr + 1) (ns.headD 0)
  .heap (h1, memory.2) :: .heap (h2, memory.2) :: fill_nodes_logs (hdr + 2) values (h2, memory.2)

def new_queue_logs {A : Type} (hdr : Nat) (values : List Nat) (memory : ManagedHeap) :
    List (CSLObs A) :=
  let allocated := managed_alloc memory hdr (2 * (values.length + 1))
  .heap allocated :: init_queue_logs hdr values allocated

theorem fill_nodes_logs_after {A : Type} (first : Nat) (values : List Nat)
    (memory : ManagedHeap) :
    after_logs (fill_nodes_logs (A := A) first values memory)
        (.obs (E := writerE (CSLObs A)) (.heap memory) ⟨⟩) =
      .obs (E := writerE (CSLObs A)) (.heap (fill_nodes_heap first values memory.1, memory.2)) ⟨⟩ :=
  write_snapshots_after _ _

theorem init_queue_logs_after {A : Type} (hdr : Nat) (values : List Nat) (memory : ManagedHeap)
    (w : World (writerE (CSLObs A))) :
    after_logs (init_queue_logs (A := A) hdr values memory) w =
      .obs (E := writerE (CSLObs A)) (.heap (init_queue_heap hdr values memory.1, memory.2)) ⟨⟩ :=
  fill_nodes_logs_after (hdr + 2) values _

theorem new_queue_logs_after {A : Type} (hdr : Nat) (values : List Nat) (memory : ManagedHeap)
    (w : World (writerE (CSLObs A))) :
    after_logs (new_queue_logs (A := A) hdr values memory) w =
      .obs (E := writerE (CSLObs A)) (.heap (new_queue_heap hdr values memory.1,
        upd memory.2 hdr (2 * (values.length + 1)))) ⟨⟩ :=
  init_queue_logs_after hdr values _ w

/-- A logged run retains the complete constructor prefix and its final heap snapshot on the
program-observation side of the sum. -/
theorem new_queue_logs_afterW {A : Type} (hdr : Nat) (values : List Nat) (memory : ManagedHeap)
    (w : World (writerE (CSLObs A ⊕ Nat))) :
    after_logs ((new_queue_logs (A := A) hdr values memory).map Sum.inl) w =
      .obs (E := writerE (CSLObs A ⊕ Nat)) (.inl (.heap (new_queue_heap hdr values memory.1,
        upd memory.2 hdr (2 * (values.length + 1))))) ⟨⟩ :=
  after_logs_map Sum.inl _ _ _ (init_queue_logs_after hdr values _ _)

theorem fill_nodes_logs_length {A : Type} (first : Nat) (values : List Nat)
    (memory : ManagedHeap) :
    (fill_nodes_logs (A := A) first values memory).length = 2 * values.length := by
  rw [fill_nodes_logs, write_snapshots_length, ← List.length_map (f := Prod.fst),
    node_writes_cells _ _ (node_addrs_length _ _), cells_length, node_addrs_length]

theorem init_queue_logs_length {A : Type} (hdr : Nat) (values : List Nat)
    (memory : ManagedHeap) :
    (init_queue_logs (A := A) hdr values memory).length = 2 + 2 * values.length := by
  simp only [init_queue_logs, List.length_cons, fill_nodes_logs_length]; omega

theorem new_queue_logs_length {A : Type} (hdr : Nat) (values : List Nat)
    (memory : ManagedHeap) :
    (new_queue_logs (A := A) hdr values memory).length = 3 + 2 * values.length := by
  simp only [new_queue_logs, List.length_cons, init_queue_logs_length]; omega

def allocated_parallel_queues (values1 values2 : List Nat) : CProg Unit :=
  .bind (new_queue values1) fun u => .bind (new_queue values2) fun v => parallel_queues u v

def shared_queue (hdr : Nat) : CProg Unit :=
  .bind (.fork (worker 1 hdr)) fun _ => .bind (.fork (worker 2 hdr)) fun _ => .ret ()

def allocated_shared_queue (values : List Nat) : CProg Unit :=
  .bind (new_queue values) shared_queue

/-- The two-worker pool of `parallel_queues`, each slot optionally behind its loop guard. -/
def queue_workers (u v : Nat) (g2 g1 : Bool) : Pool sE Bn 2 :=
  #v[if g2 then .guard (denote (worker 2 v)) else denote (worker 2 v),
    if g1 then .guard (denote (worker 1 u)) else denote (worker 1 u)]

/-! ## Denotations -/

theorem denote_rotate_once (q hdr : Nat) :
    denote_flow (rotate_once q hdr) =
      (heap_read (E := CEff) (B := Bn) (hdr + 1) >>= fun a =>
       heap_read (E := CEff) (B := Bn) a >>= fun v =>
       CTree.trigger (E := CEff) (B := Bn) (.inr (.inr (.inr (.inr (q, v))))) >>= fun _ =>
       heap_read (E := CEff) (B := Bn) (a + 1) >>= fun n =>
       heap_write (E := CEff) (B := Bn) (hdr + 1) n >>= fun _ =>
       heap_read (E := CEff) (B := Bn) hdr >>= fun z0 =>
       heap_write (E := CEff) (B := Bn) ((if n == 0 then hdr else z0) + 1) a >>= fun _ =>
       heap_write (E := CEff) (B := Bn) (a + 1) 0 >>= fun _ =>
       heap_write (E := CEff) (B := Bn) hdr a >>= fun _ =>
       pure (some ())) := by
  simp only [rotate_once, denote_flow, bind_assoc, pure_bind']

private theorem denote_rotate_once_bind {X : Type} (q hdr : Nat)
    (K : Option Unit → CTree CEff Bn X) :
    (denote_flow (rotate_once q hdr) >>= K) =
      (denote (rotate_once q hdr) >>= fun _ => K (some ())) := by
  simp only [denote, denote_rotate_once, bind_assoc, pure_bind']

theorem denote_worker (q hdr : Nat) :
    denote (worker q hdr) =
      (denote (rotate_once q hdr) >>= fun _ =>
        source_yield >>= fun _ => .guard (denote (worker q hdr))) := by
  conv => lhs; rw [denote, worker, denote_flow, unfold_iter]
  simp only [denote, worker, denote_flow, denote_rotate_once, bind_assoc, source_yield,
    vis_bind, pure_bind', guard_bind]

theorem denote_parallel_queues (u v : Nat) :
    denote (parallel_queues u v) =
      .vis (.inr (.inl ⟨⟩)) fun child : Bool =>
        if child then denote (worker 2 v) else denote (worker 1 u) :=
  denote_fork_bind _ _

/-! ## The two-worker pool under round robin -/

/-- One source instruction of a rotation: expose it under the focused round-robin runner and
under the lifted `interp_state sh`, and continue with identical prefixes. -/
local macro "rotate_effect " law:term : tactic => `(tactic| (
  rw [interp_rr_bind]
  refine sbisim_trans $law ?_
  rw [interp_state_bind, translate_bind, bind_assoc]
  refine sbisim_clo_bind_eq (sbisim_refl _) fun p => ?_
  dsimp only))

theorem interp_rr_rotate_once (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (q hdr : Nat) (K : Option Unit → Thread sE Bn) (m : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (rotate_once q hdr) >>= K)) (some i) m
        s ~
      (translate relabel_log (interp_state sh (turn q hdr) s) >>= fun p =>
        interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m p.2) := by
  unfold rotate_once turn turnk queue_turn
  rotate_effect (interp_rr_read _ _ _ _ _ _ _)
  rotate_effect (interp_rr_read _ _ _ _ _ _ _)
  rotate_effect (interp_rr_emit _ _ _ _ _ _ _ _)
  rotate_effect (interp_rr_read _ _ _ _ _ _ _)
  rotate_effect (interp_rr_write _ _ _ _ _ _ _ _)
  rotate_effect (interp_rr_read _ _ _ _ _ _ _)
  rotate_effect (interp_rr_write _ _ _ _ _ _ _ _)
  rotate_effect (interp_rr_write _ _ _ _ _ _ _ _)
  refine sbisim_trans (interp_rr_write _ _ _ _ _ _ _ _) ?_
  rw [interp_state_bind, translate_bind, bind_assoc]
  refine sbisim_clo_bind_eq (sbisim_refl _) fun p => ?_
  simp only [interp_state_ret, translate_ret, pure_bind']
  exact sbisim_refl _

theorem queue_pick_next (n : Nat) : rr_pick 1 n = queue_slot (n + 1) := by
  unfold queue_slot
  split <;> (apply Fin.ext; simp only [rr_pick]; simp; omega)

private theorem interp_rr_worker (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (q hdr m : Nat) (s : SSig) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote (worker q hdr))) (some i) m s ~
      (translate relabel_log (interp_state sh (turn q hdr) s) >>= fun p =>
        interp_schedule_rr sh (n + 1) (ts.set i (.guard (denote (worker q hdr)))) none m p.2) := by
  show interp_schedule_rr sh (n + 1)
    (ts.set i (denote_flow (.untilNone _) >>= fun _ => pure ⟨⟩)) (some i) m s ~ _
  rw [interp_rr_until_none, interp_rr_bind]
  refine sbisim_trans (interp_rr_rotate_once n ts i q hdr _ m s)
    (sbisim_clo_bind_eq (sbisim_refl _) fun p => ?_)
  dsimp only
  rw [interp_rr_bind]
  refine sbisim_trans (interp_rr_yield _ _ _ _ _ _) ?_
  dsimp only
  rw [source_raw_ret]
  exact sbisim_refl _

/-- One pool turn: the focused worker rotates, then the scheduler's logged pick
(`interp_schedule_rr_select`) moves to the other slot. -/
theorem queue_pool_turn (u v n : Nat) (g2 g1 : Bool) (s : SSig) :
    interp_schedule_rr sh 2 (queue_workers u v g2 g1) (some (queue_slot n)) n s ~
      (translate relabel_log (interp_state sh (turn (tagof n) (hdrof u v n)) s) >>= fun p =>
        .vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr (slot_index (queue_slot (n + 1))))
          fun _ => interp_schedule_rr sh 2
            (queue_workers u v (if n % 2 = 0 then g2 else true) (if n % 2 = 0 then true else g1))
            (some (queue_slot (n + 1))) (n + 1) p.2) := by
  by_cases hn : n % 2 = 0
  · have hs : queue_slot n = 1 := by simp [queue_slot, hn]
    rw [hs, tagof_even n hn, hdrof_even u v n hn]
    simp only [hn, ↓reduceIte]
    have hg : interp_schedule_rr sh 2 (queue_workers u v g2 g1) (some 1) n s ~
        interp_schedule_rr sh 2 ((queue_workers u v g2 false).set 1 (denote (worker 1 u)))
          (some 1) n s := by
      cases g1
      · exact sbisim_refl _
      · exact interp_schedule_rr_guard sh 1 _ 1 _ n s rfl
    refine sbisim_trans hg (sbisim_trans (interp_rr_worker 1 _ 1 1 u n s)
      (sbisim_clo_bind_eq (sbisim_refl _) fun p => ?_))
    refine sbisim_trans (interp_schedule_rr_select sh 1 _ n p.2) ?_
    rw [queue_pick_next]
    exact sbisim_refl _
  · have hs : queue_slot n = 0 := by simp [queue_slot, hn]
    rw [hs, tagof_odd n (by omega), hdrof_odd u v n (by omega)]
    simp only [hn, ↓reduceIte]
    have hg : interp_schedule_rr sh 2 (queue_workers u v g2 g1) (some 0) n s ~
        interp_schedule_rr sh 2 ((queue_workers u v false g1).set 0 (denote (worker 2 v)))
          (some 0) n s := by
      cases g2
      · exact sbisim_refl _
      · exact interp_schedule_rr_guard sh 1 _ 0 _ n s rfl
    refine sbisim_trans hg (sbisim_trans (interp_rr_worker 1 _ 0 2 v n s)
      (sbisim_clo_bind_eq (sbisim_refl _) fun p => ?_))
    refine sbisim_trans (interp_schedule_rr_select sh 1 _ n p.2) ?_
    rw [queue_pick_next]
    exact sbisim_refl _

/-- The two-worker pool under the source round-robin scheduler is the reference alternating
scheduler: both factor every turn through the lifted `interp_state sh (turn _ _)` and end with
the same logged pick. -/
theorem queue_pool_bisim (u v n : Nat) (g2 g1 : Bool) (s : SSig) :
    interp_schedule_rr sh 2 (queue_workers u v g2 g1) (some (queue_slot n)) n s ~ srun u v n s :=
  sbisim_log_family
    (fun x : Nat × Bool × Bool × SSig =>
      interp_schedule_rr sh 2 (queue_workers u v x.2.1 x.2.2.1) (some (queue_slot x.1)) x.1
        x.2.2.2)
    (fun x => srun u v x.1 x.2.2.2)
    (fun x => translate relabel_log (interp_state sh (turn (tagof x.1) (hdrof u v x.1)) x.2.2.2))
    (fun x => .inr (slot_index (queue_slot (x.1 + 1))))
    (fun x p => (x.1 + 1, if x.1 % 2 = 0 then x.2.1 else true,
      if x.1 % 2 = 0 then true else x.2.2.1, p.2))
    (fun _ => True)
    (fun x _ => queue_pool_turn u v x.1 x.2.1 x.2.2.1 x.2.2.2)
    (fun x _ => srun_turn u v x.1 x.2.2.2)
    (fun _ _ _ => trivial) (n, g2, g1, s) trivial

theorem run_rr_parallel_bisim (u v : Nat) (s : SSig) :
    run_rr (parallel_queues u v) s ~ srun u v 0 s :=
  sbisim_trans (run_rr_fork_bind _ _ s) (queue_pool_bisim u v 0 false false s)

/-- One whole rotation of the reference scheduler, read off `turnk_spec`: one pop and four
snapshots, the logged scheduling pick, the rotated heap. -/
theorem srun_pop (u v n hdr tag a : Nat) (ns : List Nat) (pv : Nat) (vs : List Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    hdrof u v n = hdr → tagof n = tag → qrep hdr (a :: ns) (pv :: vs) h →
    srun u v n ((h, allocs), (ctx, c)) ~
      emit_list ((queue_turn_logs (.emit (stamp (tag, pv) c)) hdr a (ns.headD 0)
          ((a :: ns).getLastD 0) (h, allocs)).map Sum.inl)
        (log (Sum.inr (slot_index (queue_slot (n + 1))) : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
          srun u v (n + 1) ((qstep hdr (a :: ns) h, allocs), (ctx, c + 1))) := by
  rintro rfl rfl hq
  refine sbisim_trans (srun_turn u v n _) ?_
  unfold turn
  refine sbisim_trans (sbisim_clo_bind_eq (translate_sbisim relabel_log
    (turnk_spec (tagof n) (hdrof u v n) a ns pv vs h allocs ctx c (pure ⟨⟩ : CTree sE Bn PUnit)
      hq)) fun _ => sbisim_refl _) ?_
  rw [translate_emit_list, emit_list_bind]
  refine emit_list_sbisim _ ?_
  rw [interp_state_ret, translate_ret, pure_bind', log_vis]
  exact sbisim_refl _

/-- The first four pops of two disjoint queues under the shared source round-robin scheduler:
queue 1 rotates `[a, b]`, queue 2 its singleton `[d]`, alternating, with the observation counter
advancing once per pop and one logged scheduling pick between consecutive pops (slots
`0, 1, 0, 1`). -/
theorem parallel_queues_four_pop_bisim (u a b v d : Nat) (h allocs : Heap) (x y z : Nat)
    (ctx : Ctx) (c : Nat) :
    qrep u [a, b] [x, y] h → qrep v [d] [z] h → Disj u [a, b] v [d] →
    let h1 := qstep u [a, b] h
    let h2 := qstep v [d] h1
    let h3 := qstep u [b, a] h2
    let h4 := qstep v [d] h3
    run_rr (parallel_queues u v) ((h, allocs), (ctx, c)) ~
      emit_list ((queue_turn_logs (.emit (stamp (1, x) c)) u a b b (h, allocs)).map Sum.inl)
       (log (Sum.inr 0 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        emit_list ((queue_turn_logs (.emit (stamp (2, z) (c + 1))) v d 0 d (h1, allocs)).map
          Sum.inl)
       (log (Sum.inr 1 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        emit_list ((queue_turn_logs (.emit (stamp (1, y) (c + 2))) u b a a (h2, allocs)).map
          Sum.inl)
       (log (Sum.inr 0 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        emit_list ((queue_turn_logs (.emit (stamp (2, z) (c + 3))) v d 0 d (h3, allocs)).map
          Sum.inl)
       (log (Sum.inr 1 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ =>
        srun u v 4 ((h4, allocs), (ctx, c + 4)))))) := by
  intro H1 H2 Hd h1 h2 h3 h4
  have H1a : qrep u [b, a] [y, x] (qstep u [a, b] h) := qstep_qrep u [a, b] [x, y] h H1 (by simp)
  have H2a := foreign_pres u [a, b] [x, y] v [d] [z] h H1 (by simp) H2 Hd
  have Hda : Disj u [b, a] v [d] := Disj_rotl_l u [a, b] v [d] (by simp) Hd
  have H1b := foreign_pres v [d] [z] u [b, a] [y, x] (qstep u [a, b] h) H2a (by simp) H1a
    (Disj_sym u [b, a] v [d] Hda)
  have H2b : qrep v [d] [z] (qstep v [d] (qstep u [a, b] h)) :=
    qstep_qrep v [d] [z] _ H2a (by simp)
  have H2c := foreign_pres u [b, a] [y, x] v [d] [z] (qstep v [d] (qstep u [a, b] h)) H1b
    (by simp) H2b Hda
  refine sbisim_trans (run_rr_parallel_bisim u v _) ?_
  refine sbisim_trans (srun_pop u v 0 u 1 a [b] x [y] h allocs ctx c rfl rfl H1) ?_
  refine emit_list_sbisim _ (sbisim_clo_bind_eq (sbisim_refl _) fun _ => ?_)
  refine sbisim_trans (srun_pop u v 1 v 2 d [] z [] _ allocs ctx (c + 1) rfl rfl H2a) ?_
  refine emit_list_sbisim _ (sbisim_clo_bind_eq (sbisim_refl _) fun _ => ?_)
  refine sbisim_trans (srun_pop u v 2 u 1 b [a] y [x] _ allocs ctx (c + 2) rfl rfl H1b) ?_
  refine emit_list_sbisim _ (sbisim_clo_bind_eq (sbisim_refl _) fun _ => ?_)
  refine sbisim_trans (srun_pop u v 3 v 2 d [] z [] _ allocs ctx (c + 3) rfl rfl H2c) ?_
  exact emit_list_sbisim _ (sbisim_clo_bind_eq (sbisim_refl _) fun _ => sbisim_refl _)

/-- Queue 1 takes the first source turn; a fault there faults the whole run. -/
private theorem parallel_queues_first_turn_stuck (u v : Nat) (s : SSig) :
    interp_state sh (turn 1 u) s ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) →
    run_rr (parallel_queues u v) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  intro hf
  refine sbisim_trans (run_rr_fork_bind _ _ s) ?_
  refine sbisim_trans (queue_pool_turn u v 0 false false s) ?_
  refine sbisim_trans (sbisim_clo_bind_eq (translate_sbisim relabel_log hf)
    fun _ => sbisim_refl _) ?_
  rw [translate_stuck, stuck_bind]
  exact sbisim_refl _

theorem parallel_queues_hemp_stuck (u v : Nat) (ctx : Ctx) (c : Nat) :
    run_rr (parallel_queues u v) (managed_empty, (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  apply parallel_queues_first_turn_stuck
  unfold turn turnk queue_turn
  exact interp_heapW_rd_missing CSLObs.heap (h_sum csl_context_handler csl_emit_handler) (u + 1)
    hemp hemp (ctx, c) _ rfl

/-! ## Exact initialization under the nondeterministic runner -/

theorem interp_nd_fill_nodes (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (first : Nat)
    (values : List Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    (∀ offset, offset < 2 * values.length → h (first + offset) ≠ none) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (fill_nodes first values) >>= K))
        (some i) ((h, allocs), (ctx, c)) ~
      emit_list (fill_nodes_logs first values (h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          ((fill_nodes_heap first values h, allocs), (ctx, c))) := by
  intro hall
  refine interp_nd_write_list n ts i _ K h allocs (ctx, c) fun a w hin => ?_
  obtain ⟨hlo, hhi⟩ := (node_cells_range _ _ _).1
    (node_writes_keys_subset _ _ a (List.mem_map.2 ⟨(a, w), hin, rfl⟩))
  have := hall (a - first) (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

theorem interp_nd_init_queue (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1)) (hdr : Nat)
    (values : List Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    (∀ offset, offset < 2 * (values.length + 1) → h (hdr + offset) ≠ none) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (init_queue hdr values) >>= K))
        (some i) ((h, allocs), (ctx, c)) ~
      emit_list (init_queue_logs hdr values (h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          ((init_queue_heap hdr values h, allocs), (ctx, c))) := by
  intro hall
  dsimp only [init_queue]
  rw [interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_write_present n ts i _ _ _ h allocs ctx c
    (by simpa using hall 0 (by omega))) ?_
  simp only [init_queue_logs, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_write_present n ts i _ _ _ _ allocs ctx c
    (upd_mono _ _ _ _ (hall 1 (by omega)))) ?_
  rw [log_vis]
  refine sb_vis _ fun _ => ?_
  dsimp only
  refine interp_nd_fill_nodes n ts i (hdr + 2) values K _ allocs ctx c fun offset ho => ?_
  refine upd_mono _ _ _ _ (upd_mono _ _ _ _ ?_)
  have := hall (2 + offset) (by omega)
  rwa [← Nat.add_assoc] at this

theorem interp_nd_new_queue_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (values : List Nat) (hdr : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    0 < hdr → block_free h hdr (2 * (values.length + 1)) →
    (∀ j, 0 < j → j < hdr → ¬ block_free h j (2 * (values.length + 1))) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      emit_list (new_queue_logs hdr values (h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some hdr))) (some i)
          ((new_queue_heap hdr values h, upd allocs hdr (2 * (values.length + 1))), (ctx, c))) := by
  intro hpos hfree hfirst
  rw [new_queue, interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_alloc_first n ts i _ hdr _ h allocs ctx c (by omega)
    hpos hfree hfirst) ?_
  simp only [new_queue_logs, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_nd_source_bind]
  refine sbisim_trans (interp_nd_init_queue n ts i hdr values _
    (hunion (hblock hdr (2 * (values.length + 1))) h) _ ctx c fun offset ho => ?_) ?_
  · simp [hunion, hblock_in hdr _ offset ho]
  · refine emit_list_sbisim _ ?_
    dsimp only
    rw [interp_nd_source_ret]
    exact sbisim_refl _

theorem interp_nd_new_queue_empty (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (values : List Nat) (K : Option Nat → Thread sE Bn) (ctx : Ctx) (c : Nat) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K)) (some i)
        (managed_empty, (ctx, c)) ~
      emit_list (new_queue_logs 1 values managed_empty)
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some 1))) (some i)
          ((new_queue_heap 1 values hemp, upd hemp 1 (2 * (values.length + 1))), (ctx, c))) :=
  interp_nd_new_queue_first n ts i values 1 K hemp hemp ctx c (by omega) (fun _ _ => rfl)
    (fun _ hj hj1 => absurd hj1 (by omega))

private theorem set_single (a b : Thread sE Bn) (i : Fin 1) : #v[a].set i b = #v[b] := by
  match i with
  | ⟨0, _⟩ => rfl

theorem run_nd_allocated_shared_queue (values : List Nat) (ctx : Ctx) (c : Nat) :
    run_nd (allocated_shared_queue values) (managed_empty, (ctx, c)) ~
      emit_list (new_queue_logs 1 values managed_empty)
        (run_nd (shared_queue 1)
          ((new_queue_heap 1 values hemp, upd hemp 1 (2 * (values.length + 1))), (ctx, c))) := by
  rw [run_nd_unfold, run_nd_unfold, ← set_single (pure ⟨⟩) (denote (allocated_shared_queue _)) 0,
    denote, allocated_shared_queue, interp_nd_source_bind]
  exact interp_nd_new_queue_empty 0 _ 0 values _ ctx c

/-! ## Exact initialization under any scheduling policy

The outer injection preserves the distinction between CSL logs and scheduler observations. -/

theorem interp_fair_fill_nodes (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (first : Nat) (values : List Nat) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * values.length → h (first + offset) ≠ none) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (fill_nodes first values) >>= K))
        (some i) st ((h, allocs), (ctx, c)) ~
      emit_list ((fill_nodes_logs first values (h, allocs)).map Sum.inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          ((fill_nodes_heap first values h, allocs), (ctx, c))) := by
  intro hall
  refine interp_fair_write_list sch n ts i _ K st h allocs (ctx, c) fun a w hin => ?_
  obtain ⟨hlo, hhi⟩ := (node_cells_range _ _ _).1
    (node_writes_keys_subset _ _ a (List.mem_map.2 ⟨(a, w), hin, rfl⟩))
  have := hall (a - first) (by omega)
  rwa [Nat.add_sub_cancel' hlo] at this

theorem interp_fair_init_queue (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (hdr : Nat) (values : List Nat) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * (values.length + 1) → h (hdr + offset) ≠ none) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (init_queue hdr values) >>= K))
        (some i) st ((h, allocs), (ctx, c)) ~
      emit_list ((init_queue_logs hdr values (h, allocs)).map Sum.inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          ((init_queue_heap hdr values h, allocs), (ctx, c))) := by
  intro hall
  dsimp only [init_queue]
  rw [interp_fair_bind]
  refine sbisim_trans (interp_fair_write_present sch n ts i _ _ _ st h allocs ctx c
    (by simpa using hall 0 (by omega))) ?_
  simp only [init_queue_logs, List.map_cons, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_fair_bind]
  refine sbisim_trans (interp_fair_write_present sch n ts i _ _ _ st _ allocs ctx c
    (upd_mono _ _ _ _ (hall 1 (by omega)))) ?_
  rw [log_vis]
  refine sb_vis _ fun _ => ?_
  refine interp_fair_fill_nodes sch n ts i (hdr + 2) values K st _ allocs ctx c
    fun offset ho => ?_
  refine upd_mono _ _ _ _ (upd_mono _ _ _ _ ?_)
  have := hall (2 + offset) (by omega)
  rwa [← Nat.add_assoc] at this

theorem interp_fair_new_queue_first (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (values : List Nat) (hdr : Nat) (K : Option Nat → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    0 < hdr → block_free h hdr (2 * (values.length + 1)) →
    (∀ j, 0 < j → j < hdr → ¬ block_free h j (2 * (values.length + 1))) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K))
        (some i) st ((h, allocs), (ctx, c)) ~
      emit_list ((new_queue_logs hdr values (h, allocs)).map Sum.inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some hdr))) (some i) st
          ((new_queue_heap hdr values h, upd allocs hdr (2 * (values.length + 1))), (ctx, c))) := by
  intro hpos hfree hfirst
  rw [new_queue, interp_fair_bind]
  refine sbisim_trans (interp_fair_alloc_first sch n ts i _ hdr _ st h allocs ctx c (by omega)
    hpos hfree hfirst) ?_
  simp only [new_queue_logs, List.map_cons, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_fair_bind]
  refine sbisim_trans (interp_fair_init_queue sch n ts i hdr values _ st
    (hunion (hblock hdr (2 * (values.length + 1))) h) _ ctx c fun offset ho => ?_) ?_
  · simp [hunion, hblock_in hdr _ offset ho]
  · refine emit_list_sbisim _ ?_
    rw [interp_fair_ret]
    exact sbisim_refl _

theorem interp_fair_new_queue_empty (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (values : List Nat) (K : Option Nat → Thread sE Bn)
    (st : sch.sched_state) (ctx : Ctx) (c : Nat) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K))
        (some i) st (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 values managed_empty).map Sum.inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some 1))) (some i) st
          ((new_queue_heap 1 values hemp, upd hemp 1 (2 * (values.length + 1))), (ctx, c))) :=
  interp_fair_new_queue_first sch n ts i values 1 K st hemp hemp ctx c (by omega)
    (fun _ _ => rfl) (fun _ hj hj1 => absurd hj1 (by omega))

theorem run_fair_allocated_shared_queue (sch : Scheduler) (values : List Nat)
    (st : sch.sched_state) (ctx : Ctx) (c : Nat) :
    run_fair sch (allocated_shared_queue values) st (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 values managed_empty).map Sum.inl)
        (run_fair sch (shared_queue 1) st
          ((new_queue_heap 1 values hemp, upd hemp 1 (2 * (values.length + 1))), (ctx, c))) := by
  rw [run_fair_unfold, run_fair_unfold,
    ← set_single (pure ⟨⟩) (denote (allocated_shared_queue _)) 0, denote, allocated_shared_queue,
    interp_fair_bind]
  exact interp_fair_new_queue_empty sch 0 _ 0 values _ st ctx c

theorem interp_fair_new_queue (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (values : List Nat) (K : Option Nat → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    heap_finite h →
    ∃ hdr, 0 < hdr ∧ block_free h hdr (2 * (values.length + 1)) ∧
      heap_finite (new_queue_heap hdr values h) ∧
      asep (qrepX hdr (queue_nodes hdr values.length) values) (fun frame => heq frame h)
        (new_queue_heap hdr values h) ∧
      interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K))
          (some i) st ((h, allocs), (ctx, c)) ~
        emit_list ((new_queue_logs hdr values (h, allocs)).map Sum.inl)
          (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some hdr))) (some i) st
            ((new_queue_heap hdr values h, upd allocs hdr (2 * (values.length + 1))),
              (ctx, c))) := by
  intro hfin
  obtain ⟨hdr, hpos, hfree, hfirst⟩ := first_fit_exists h (2 * (values.length + 1)) hfin
    (by omega)
  exact ⟨hdr, hpos, hfree, new_queue_heap_finite hdr values h hfin,
    new_queue_heap_owned hdr values h hpos hfree,
    interp_fair_new_queue_first sch n ts i values hdr K st h allocs ctx c hpos hfree hfirst⟩

private theorem sb_of_eq {W X : Type} {t u : ctreeW W Bn X} (h : t = u) : t ~ u :=
  h ▸ sbisim_refl _

theorem run_fair_allocated_parallel (sch : Scheduler) (values1 values2 : List Nat)
    (st : sch.sched_state) (ctx : Ctx) (c : Nat) :
    ∃ u v h allocs, heap_finite h ∧
      asep (qrepX u (queue_nodes u values1.length) values1)
        (qrepX v (queue_nodes v values2.length) values2) h ∧
      run_fair sch (allocated_parallel_queues values1 values2) st (managed_empty, (ctx, c)) ~
        emit_list ((new_queue_logs u values1 managed_empty ++
            new_queue_logs v values2
              (new_queue_heap u values1 hemp, upd hemp u (2 * (values1.length + 1)))).map
            Sum.inl)
          (run_fair sch (parallel_queues u v) st ((h, allocs), (ctx, c))) := by
  obtain ⟨u, upos, ufree, fin1, -, run1⟩ := interp_fair_new_queue sch 0 #v[pure ⟨⟩] 0 values1
    (fun r => match r with
      | none => pure ⟨⟩
      | some u => denote_flow (.bind (new_queue values2) fun v => parallel_queues u v) >>=
          fun _ => pure ⟨⟩) st hemp hemp ctx c heap_finite_hemp
  obtain ⟨v, vpos, vfree, fin2, -, run2⟩ := interp_fair_new_queue sch 0 #v[pure ⟨⟩] 0 values2
    (fun r => match r with
      | none => pure ⟨⟩
      | some v => denote_flow (parallel_queues u v) >>= fun _ => pure ⟨⟩) st
    (new_queue_heap u values1 hemp) (upd hemp u (2 * (values1.length + 1))) ctx c fin1
  refine ⟨u, v, new_queue_heap v values2 (new_queue_heap u values1 hemp),
    upd (upd hemp u (2 * (values1.length + 1))) v (2 * (values2.length + 1)), fin2, ?_, ?_⟩
  · have E1 : heq (new_queue_heap u values1 hemp)
        (qheap u (queue_nodes u values1.length) values1) := fun x => by
      rw [new_queue_heap_agrees u values1 hemp upos ufree x]
      simp only [hunion, hemp]
      split <;> simp_all
    have D21 : hdisj (qheap v (queue_nodes v values2.length) values2)
        (qheap u (queue_nodes u values1.length) values1) :=
      hdisj_resp _ _ _ _ (heq_refl _) E1 (new_queue_heap_disjoint v values2 _ vfree)
    refine ⟨_, _, hdisj_sym _ _ D21, ?_, ⟨qheap_queue_nodes_rep u values1 upos, qheap_qex _ _ _⟩,
      ⟨qheap_queue_nodes_rep v values2 vpos, qheap_qex _ _ _⟩⟩
    exact heq_trans _ _ _ (new_queue_heap_agrees v values2 _ vpos vfree)
      (heq_trans _ _ _ (hunion_resp _ _ _ _ (heq_refl _) E1) (hunion_comm _ _ D21))
  · rw [run_fair_unfold sch (allocated_parallel_queues values1 values2),
      ← set_single (pure ⟨⟩) (denote (allocated_parallel_queues values1 values2)) 0, denote,
      allocated_parallel_queues, interp_fair_bind]
    -- `interp_fair_bind` and `run1`/`run2` phrase one continuation with different matchers
    refine sbisim_trans (sb_of_eq ?_) (sbisim_trans run1 ?_)
    · congr 3; funext r; cases r <;> rfl
    rw [List.map_append, emit_list_app]
    refine emit_list_sbisim _ ?_
    dsimp only
    rw [interp_fair_bind]
    refine sbisim_trans (sb_of_eq ?_) (sbisim_trans run2 (emit_list_sbisim _ ?_))
    · congr 3; funext r; cases r <;> rfl
    rw [run_fair_unfold, ← set_single (pure ⟨⟩) _ 0]
    exact sbisim_refl _

/-! ## Round robin: instances of the policy-generic rules

Round-robin initialization preserves every snapshot via `Sum.inl`. -/

theorem interp_rr_fill_nodes (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (first : Nat) (values : List Nat) (K : Option Unit → Thread sE Bn) (m : Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * values.length → h (first + offset) ≠ none) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (fill_nodes first values) >>= K))
        (some i) m ((h, allocs), (ctx, c)) ~
      emit_list ((fill_nodes_logs first values (h, allocs)).map Sum.inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          ((fill_nodes_heap first values h, allocs), (ctx, c))) :=
  interp_fair_fill_nodes rr_scheduler n ts i first values K m h allocs ctx c

theorem interp_rr_init_queue (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (hdr : Nat) (values : List Nat) (K : Option Unit → Thread sE Bn) (m : Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * (values.length + 1) → h (hdr + offset) ≠ none) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (init_queue hdr values) >>= K))
        (some i) m ((h, allocs), (ctx, c)) ~
      emit_list ((init_queue_logs hdr values (h, allocs)).map Sum.inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          ((init_queue_heap hdr values h, allocs), (ctx, c))) :=
  interp_fair_init_queue rr_scheduler n ts i hdr values K m h allocs ctx c

theorem interp_rr_new_queue_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (values : List Nat) (hdr : Nat) (K : Option Nat → Thread sE Bn) (m : Nat)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    0 < hdr → block_free h hdr (2 * (values.length + 1)) →
    (∀ j, 0 < j → j < hdr → ¬ block_free h j (2 * (values.length + 1))) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      emit_list ((new_queue_logs hdr values (h, allocs)).map Sum.inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some hdr))) (some i) m
          ((new_queue_heap hdr values h, upd allocs hdr (2 * (values.length + 1))), (ctx, c))) :=
  interp_fair_new_queue_first rr_scheduler n ts i values hdr K m h allocs ctx c

theorem interp_rr_new_queue_empty (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (values : List Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (ctx : Ctx) (c : Nat) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K)) (some i) m
        (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 values managed_empty).map Sum.inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some 1))) (some i) m
          ((new_queue_heap 1 values hemp, upd hemp 1 (2 * (values.length + 1))), (ctx, c))) :=
  interp_fair_new_queue_empty rr_scheduler n ts i values K m ctx c

theorem run_rr_allocated_shared_queue (values : List Nat) (ctx : Ctx) (c : Nat) :
    run_rr (allocated_shared_queue values) (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs 1 values managed_empty).map Sum.inl)
        (run_rr (shared_queue 1)
          ((new_queue_heap 1 values hemp, upd hemp 1 (2 * (values.length + 1))), (ctx, c))) :=
  run_fair_allocated_shared_queue rr_scheduler values (0 : Nat) ctx c

theorem interp_rr_new_queue (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (values : List Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    heap_finite h →
    ∃ hdr, 0 < hdr ∧ block_free h hdr (2 * (values.length + 1)) ∧
      heap_finite (new_queue_heap hdr values h) ∧
      asep (qrepX hdr (queue_nodes hdr values.length) values) (fun frame => heq frame h)
        (new_queue_heap hdr values h) ∧
      interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (new_queue values) >>= K)) (some i) m
          ((h, allocs), (ctx, c)) ~
        emit_list ((new_queue_logs hdr values (h, allocs)).map Sum.inl)
          (interp_schedule_rr sh (n + 1) (ts.set i (K (some hdr))) (some i) m
            ((new_queue_heap hdr values h, upd allocs hdr (2 * (values.length + 1))),
              (ctx, c))) :=
  interp_fair_new_queue rr_scheduler n ts i values K m h allocs ctx c

theorem run_rr_allocated_parallel (values1 values2 : List Nat) (ctx : Ctx) (c : Nat) :
    ∃ u v h allocs, heap_finite h ∧
      asep (qrepX u (queue_nodes u values1.length) values1)
        (qrepX v (queue_nodes v values2.length) values2) h ∧
      run_rr (allocated_parallel_queues values1 values2) (managed_empty, (ctx, c)) ~
        emit_list ((new_queue_logs u values1 managed_empty ++
            new_queue_logs v values2
              (new_queue_heap u values1 hemp, upd hemp u (2 * (values1.length + 1)))).map
            Sum.inl)
          (run_rr (parallel_queues u v) ((h, allocs), (ctx, c))) :=
  run_fair_allocated_parallel rr_scheduler values1 values2 (0 : Nat) ctx c

/-- An allocated empty first queue has head pointer `0`, and the null cell is unallocated: the
first source turn faults, whatever the second queue is. -/
theorem allocated_parallel_queues_empty_stuck (values : List Nat) (ctx : Ctx) (c : Nat) :
    ∃ u v, run_rr (allocated_parallel_queues [] values) (managed_empty, (ctx, c)) ~
      emit_list ((new_queue_logs u [] managed_empty ++
          new_queue_logs v values (new_queue_heap u [] hemp, upd hemp u 2)).map Sum.inl)
        (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  obtain ⟨u, v, h, allocs, -, owned, run⟩ := run_rr_allocated_parallel [] values ctx c
  obtain ⟨⟨-, hhead, -, -, hnull, -⟩, -, -⟩ := owned_queues_sound _ _ _ _ _ _ _ owned
  refine ⟨u, v, sbisim_trans run (emit_list_sbisim _ ?_)⟩
  apply parallel_queues_first_turn_stuck
  unfold turn turnk queue_turn
  refine sbisim_trans (interp_heapW_rd CSLObs.heap (h_sum csl_context_handler csl_emit_handler)
    (u + 1) h allocs (ctx, c) 0 _ hhead) ?_
  exact interp_heapW_rd_missing CSLObs.heap (h_sum csl_context_handler csl_emit_handler) 0
    h allocs (ctx, c) _ hnull

-- Not ported: the Ltacs `rotate_state_bind`, `rotate_effect` (replaced by the local macro
-- `rotate_effect`) and `queue_fault` (inlined as `interp_heapW_rd_missing`).

end Examples.CSL.Queue.Program
