/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Lang.CoCSL.Frame
public import Lang.CoCSL.Sequential
public import Logic.Yield.Execution
public import Logic.Utils.Execution
public import Examples.CSL.Queue.Representation
public import Examples.CSL.Allocator.Layout
public import Examples.CSL.Allocator.Program
public import Examples.CSL.Allocator.Model

/-!
# The allocator's source pool and its pool-simulation certificate

Residual source threads for every model phase, the exact snapshot-preserving initialization of the
page under the ND, round-robin and generic policy runners, the exact first-yield segment of every
model turn, and the `PoolSimulation` instance relating the source pool to the turn model
(← `examples/CSL/Allocator/Execution.v`).
-/

@[expose] public section
namespace Examples.CSL.Allocator.Execution
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Allocator.Layout Examples.CSL.Allocator.Program Examples.CSL.Allocator.Model
open Actor owner_pc remote_pc

/-! ## Residual source threads of every model phase -/

def client_next (base : Nat) (client : Bool) : Option (Option Unit) → Thread sE Bn :=
  until_tail (client_round base client) fun _ => pure ⟨⟩

def remote_after_free (base : Nat) (client : Bool) (flow : Option Unit) : Thread sE Bn :=
  match flow with
  | none => client_next base client none
  | some _ =>
    denote_flow (.bind .yield fun _ => .ret (some () : Option Unit)) >>= client_next base client

def remote_cas_tail (base block old : Nat) : CProg (Option Unit) :=
  .bind (.cas (.lit (remote_head base)) (.lit old) (.lit block)) fun success =>
    if success then
      .bind (.emit tag_retire block) fun _ => .ret none
    else
      .bind (.emit tag_retry block) fun _ =>
      .bind .yield fun _ => .ret (some ())

def remote_link_tail (base block old : Nat) : CProg (Option Unit) :=
  .bind (.write block old) fun _ =>
  .bind .yield fun _ => remote_cas_tail base block old

def remote_residual (base : Nat) (client : Bool) (pc : remote_pc) : Thread sE Bn :=
  match pc with
  | RPoll => denote (remote_client base client)
  | RRead block => denote_flow (remote_free base block) >>= remote_after_free base client
  | RLink block old => denote_flow (remote_link_tail base block old) >>=
      until_tail (remote_attempt base block) (remote_after_free base client)
  | RCAS block old => denote_flow (remote_cas_tail base block old) >>=
      until_tail (remote_attempt base block) (remote_after_free base client)

def owner_next (base : Nat) : Option (Option Unit) → Thread sE Bn :=
  until_tail (owner_round base) fun _ => pure ⟨⟩

def owner_offer_tail (base : Nat) (client : Bool) : CProg (Option Unit) :=
  if client then
    .bind (offer_block base true) fun _ => .ret (some ())
  else
    .bind (offer_block base false) fun _ =>
    .bind (offer_block base true) fun _ => .ret (some ())

def owner_after_collect (base : Nat) (flow : Option Unit) : Thread sE Bn :=
  match flow with
  | none => owner_next base none
  | some _ => denote_flow (owner_offer_tail base false) >>= owner_next base

def owner_after_detach (base : Nat) (flow : Option Unit) : Thread sE Bn :=
  match flow with
  | none => owner_after_collect base none
  | some _ => denote_flow (.untilNone (reclaim_step base)) >>= owner_after_collect base

def detach_cas_tail (base old : Nat) : CProg (Option Unit) :=
  .bind (.cas (.lit (remote_head base)) (.lit old) (.lit 0)) fun success =>
    if success then
      .bind (.write (drain_head base) old) fun _ =>
      .bind .yield fun _ => .ret none
    else .bind .yield fun _ => .ret (some ())

def owner_residual (base : Nat) (pc : owner_pc) : Thread sE Bn :=
  match pc with
  | ORead => denote (.untilNone (owner_round base))
  | OCAS old => denote_flow (detach_cas_tail base old) >>=
      until_tail (detach_attempt base) (owner_after_detach base)
  | ODrain => denote_flow (.untilNone (reclaim_step base)) >>= owner_after_collect base
  | OOffer client => denote_flow (owner_offer_tail base client) >>= owner_next base

/-- Physical slot order `[client1, client0, owner]`. -/
def allocator_pool (base : Nat) (s : AState) : Pool sE Bn 3 :=
  #v[remote_residual base true s.remote1_state, remote_residual base false s.remote0_state,
    owner_residual base s.owner_state]

def source_pool0 (base : Nat) : Pool sE Bn 3 :=
  #v[denote (remote_client base true), denote (remote_client base false),
    denote (.untilNone (owner_round base))]

def state_agrees (sigma : SSig) (s : AState) : Prop :=
  heq sigma.1.1 s.aheap ∧ heq sigma.1.2 s.aallocs ∧ csl_counter sigma = s.acount

def source_reheap (sigma : SSig) (s : AState) : AState where
  aheap := sigma.1.1
  aallocs := sigma.1.2
  acount := csl_counter sigma
  owner_state := s.owner_state
  remote0_state := s.remote0_state
  remote1_state := s.remote1_state

theorem state_agrees_reheap (sigma : SSig) (s : AState) :
    state_agrees sigma s → state_equiv s (source_reheap sigma s) :=
  fun ⟨hh, ha, hc⟩ => ⟨heq_sym _ _ hh, heq_sym _ _ ha, hc.symm, rfl, rfl, rfl⟩

theorem source_pool0_initial (capacity c : Nat) :
    pool_equ (source_pool0 1) (allocator_pool 1 (initial_state capacity c)) :=
  pool_equ_refl _

/-! ## Snapshot-preserving page initialization -/

theorem init_links_yield_fork_free (first count : Nat) : yield_fork_free (init_links first count) :=
  write_list_yield_fork_free _

theorem init_page_yield_fork_free (base capacity : Nat) :
    yield_fork_free (init_page base capacity) :=
  ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ =>
    init_links_yield_fork_free _ _⟩⟩⟩⟩⟩

def init_links_logs {A : Type} (first count : Nat) (memory : ManagedHeap) : List (CSLObs A) :=
  write_snapshots (link_updates first count) memory

def init_page_logs {A : Type} (base capacity : Nat) (memory : ManagedHeap) : List (CSLObs A) :=
  let al := memory.2
  let h1 := upd memory.1 (remote_head base) 0
  let h2 := upd h1 (drain_head base) 0
  let h3 := upd h2 (mailbox base false) 0
  let h4 := upd h3 (mailbox base true) 0
  let h5 := upd h4 (local_head base) (match capacity with | 0 => 0 | _ + 1 => base + 5)
  [.heap (h1, al), .heap (h2, al), .heap (h3, al), .heap (h4, al), .heap (h5, al)] ++
    init_links_logs (base + 5) capacity (h5, al)

def new_page_logs {A : Type} (base capacity : Nat) (memory : ManagedHeap) : List (CSLObs A) :=
  let allocated := managed_alloc memory base (page_size capacity)
  .heap allocated :: init_page_logs base capacity allocated

theorem init_links_logs_length {A : Type} (first count : Nat) (memory : ManagedHeap) :
    (init_links_logs (A := A) first count memory).length = count := by
  simp [init_links_logs, write_snapshots_length]

theorem init_page_logs_length {A : Type} (base capacity : Nat) (memory : ManagedHeap) :
    (init_page_logs (A := A) base capacity memory).length = 5 + capacity := by
  simp [init_page_logs, init_links_logs_length]; omega

theorem new_page_logs_length {A : Type} (base capacity : Nat) (memory : ManagedHeap) :
    (new_page_logs (A := A) base capacity memory).length = 6 + capacity := by
  simp [new_page_logs, init_page_logs_length]; omega

theorem instr_flow_init_links (first count : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * count → h (first + offset) ≠ none) →
    instr_flow_erased (init_links first count) ((h, allocs), (ctx, c)) ~
      emit_list (init_links_logs first count (h, allocs))
        (pure (some (), ((init_links_heap first count h, allocs), (ctx, c))) :
          ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) := by
  intro hal
  refine instr_flow_write_list _ h allocs (ctx, c) fun a v hin => ?_
  have ha : a ∈ node_addrs first count := by
    rw [← link_updates_keys]; exact List.mem_map_of_mem (f := Prod.fst) hin
  obtain ⟨j, hj, rfl⟩ := (node_addrs_in _ _ _).1 ha
  exact hal _ (by omega)

/-- A checked write exposes its post-memory snapshot before the standalone continuation. -/
private theorem instr_flow_write_vis {A : Type} (a v : Nat) (k : Unit → CProg A)
    (m : ManagedHeap) (aux : Ctx × Nat) :
    m.1 a ≠ none →
    instr_flow_erased (.bind (.write a v) k) (m, aux) ~
      .vis (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (upd m.1 a v, m.2)) fun _ =>
        instr_flow_erased (k ()) ((upd m.1 a v, m.2), aux) := fun hv => by
  refine sbisim_trans (instr_flow_write a v k (m, aux) hv) ?_
  rw [log_vis]; exact sbisim_refl _

theorem instr_flow_init_page (base capacity : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    instr_flow_erased (init_page base capacity)
        ((hunion (hblock base (page_size capacity)) h, allocs), (ctx, c)) ~
      emit_list (init_page_logs base capacity (hunion (hblock base (page_size capacity)) h, allocs))
        (pure (some (), ((page_heap base capacity h, allocs), (ctx, c))) :
          ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) := by
  have hb : ∀ x, base ≤ x → x < base + page_size capacity →
      hunion (hblock base (page_size capacity)) h x ≠ none := fun x h1 h2 => by
    rw [page_backing_in _ _ _ _ ⟨h1, h2⟩]; simp
  have hsz : 5 ≤ page_size capacity := by unfold page_size; omega
  simp only [init_page_logs, List.cons_append, List.nil_append, emit_list_cons]
  refine sbisim_trans (instr_flow_write_vis _ _ _ _ _ ?_) (sb_vis _ fun _ => ?_)
  · exact hb _ (by simp [remote_head]) (by simp [remote_head]; omega)
  refine sbisim_trans (instr_flow_write_vis _ _ _ _ _ ?_) (sb_vis _ fun _ => ?_)
  · exact upd_mono _ _ _ _ (hb _ (by simp [drain_head]) (by simp [drain_head]; omega))
  refine sbisim_trans (instr_flow_write_vis _ _ _ _ _ ?_) (sb_vis _ fun _ => ?_)
  · exact upd_mono _ _ _ _ (upd_mono _ _ _ _
      (hb _ (by simp [mailbox]) (by simp [mailbox]; omega)))
  refine sbisim_trans (instr_flow_write_vis _ _ _ _ _ ?_) (sb_vis _ fun _ => ?_)
  · exact upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _
      (hb _ (by simp only [mailbox, ↓reduceIte]; omega)
        (by simp only [mailbox, ↓reduceIte]; omega))))
  refine sbisim_trans (instr_flow_write_vis _ _ _ _ _ ?_) (sb_vis _ fun _ => ?_)
  · exact upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _
      (hb _ (by simp [local_head]) (by simp [local_head]; omega)))))
  refine instr_flow_init_links _ _ _ _ _ _ fun offset ho => ?_
  exact upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _ (upd_mono _ _ _ _
    (hb _ (by omega) (by unfold page_size at *; omega))))))

theorem interp_rr_init_links (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (first count : Nat) (K : Option Unit → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    (∀ offset, offset < 2 * count → h (first + offset) ≠ none) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (init_links first count) >>= K)) (some i)
        m ((h, allocs), (ctx, c)) ~
      emit_list ((init_links_logs first count (h, allocs)).map .inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          ((init_links_heap first count h, allocs), (ctx, c))) := fun hal =>
  interp_fair_sequential rr_scheduler n ts i _ K m _ _ _ _ (init_links_yield_fork_free _ _)
    (instr_flow_init_links first count h allocs ctx c hal)

theorem interp_nd_init_links (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (first count : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * count → h (first + offset) ≠ none) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (init_links first count) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      emit_list (init_links_logs first count (h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          ((init_links_heap first count h, allocs), (ctx, c))) := fun hal => by
  refine sbisim_trans (run_nd_prefix n ts i _ K _ (init_links_yield_fork_free _ _)) ?_
  refine sbisim_trans (sbisim_clo_bind_eq (instr_flow_init_links first count h allocs ctx c hal)
    fun _ => sbisim_refl _) ?_
  rw [emit_list_ret_bind]; exact sbisim_refl _

/-- The starting heap is the actual allocation overlay: the five metadata writes and every link
write are checked against allocated cells, and untouched payloads keep the allocation's zeroes. -/
theorem interp_rr_init_page (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base capacity : Nat) (K : Option Unit → Thread sE Bn) (m : Nat) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (init_page base capacity) >>= K))
        (some i) m ((hunion (hblock base (page_size capacity)) h, allocs), (ctx, c)) ~
      emit_list ((init_page_logs base capacity
          (hunion (hblock base (page_size capacity)) h, allocs)).map .inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) m
          ((page_heap base capacity h, allocs), (ctx, c))) :=
  interp_fair_sequential rr_scheduler n ts i _ K m _ _ _ _ (init_page_yield_fork_free _ _)
    (instr_flow_init_page base capacity h allocs ctx c)

theorem interp_nd_init_page (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (base capacity : Nat) (K : Option Unit → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (init_page base capacity) >>= K))
        (some i) ((hunion (hblock base (page_size capacity)) h, allocs), (ctx, c)) ~
      emit_list (init_page_logs base capacity (hunion (hblock base (page_size capacity)) h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          ((page_heap base capacity h, allocs), (ctx, c))) := by
  refine sbisim_trans (run_nd_prefix n ts i _ K _ (init_page_yield_fork_free _ _)) ?_
  refine sbisim_trans (sbisim_clo_bind_eq (instr_flow_init_page base capacity h allocs ctx c)
    fun _ => sbisim_refl _) ?_
  rw [emit_list_ret_bind]; exact sbisim_refl _

/-- First fit at a known fresh base, separated from the finite-heap existence proof; the
allocation records the page's whole extent in the allocation table. -/
theorem interp_rr_new_page_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity base : Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    0 < base → block_free h base (page_size capacity) →
    (∀ j, 0 < j → j < base → ¬ block_free h j (page_size capacity)) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K)) (some i) m
        ((h, allocs), (ctx, c)) ~
      emit_list ((new_page_logs base capacity (h, allocs)).map .inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some base))) (some i) m
          ((page_heap base capacity h, upd allocs base (page_size capacity)), (ctx, c))) := by
  intro hpos hfree hfirst
  rw [new_page, interp_rr_bind]
  refine sbisim_trans (interp_rr_alloc_first n ts i _ base _ m h allocs ctx c
    (page_size_positive _) hpos hfree hfirst) ?_
  simp only [new_page_logs, List.map_cons, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_rr_bind]
  refine sbisim_trans (interp_rr_init_page n ts i base capacity _ m h
    (upd allocs base (page_size capacity)) ctx c) (emit_list_sbisim _ ?_)
  rw [interp_rr_ret]; exact sbisim_refl _

theorem interp_nd_new_page_first (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity base : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    0 < base → block_free h base (page_size capacity) →
    (∀ j, 0 < j → j < base → ¬ block_free h j (page_size capacity)) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K)) (some i)
        ((h, allocs), (ctx, c)) ~
      emit_list (new_page_logs base capacity (h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
          ((page_heap base capacity h, upd allocs base (page_size capacity)), (ctx, c))) := by
  intro hpos hfree hfirst
  rw [new_page, interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_alloc_first n ts i _ base _ h allocs ctx c
    (page_size_positive _) hpos hfree hfirst) ?_
  simp only [new_page_logs, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_nd_source_bind]
  refine sbisim_trans (interp_nd_init_page n ts i base capacity _ h
    (upd allocs base (page_size capacity)) ctx c) (emit_list_sbisim _ ?_)
  rw [interp_nd_source_ret]; exact sbisim_refl _

theorem interp_rr_new_page (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (h allocs : Heap) (ctx : Ctx)
    (c : Nat) :
    heap_finite h →
    ∃ base, 0 < base ∧ block_free h base (page_size capacity) ∧
      (∀ j, 0 < j → j < base → ¬ block_free h j (page_size capacity)) ∧
      heap_finite (page_heap base capacity h) ∧
      (∀ x, h x ≠ none → page_heap base capacity h x = h x) ∧
      interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K)) (some i) m
          ((h, allocs), (ctx, c)) ~
        emit_list ((new_page_logs base capacity (h, allocs)).map .inl)
          (interp_schedule_rr sh (n + 1) (ts.set i (K (some base))) (some i) m
            ((page_heap base capacity h, upd allocs base (page_size capacity)), (ctx, c))) := by
  intro hfin
  obtain ⟨base, hpos, hfree, hfirst⟩ :=
    first_fit_exists h (page_size capacity) hfin (page_size_positive _)
  exact ⟨base, hpos, hfree, hfirst, page_heap_finite _ _ _ hfin, page_heap_old_frame _ _ _ hfree,
    interp_rr_new_page_first n ts i capacity base K m h allocs ctx c hpos hfree hfirst⟩

theorem interp_nd_new_page (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (K : Option Nat → Thread sE Bn) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    heap_finite h →
    ∃ base, 0 < base ∧ block_free h base (page_size capacity) ∧
      (∀ j, 0 < j → j < base → ¬ block_free h j (page_size capacity)) ∧
      heap_finite (page_heap base capacity h) ∧
      (∀ x, h x ≠ none → page_heap base capacity h x = h x) ∧
      interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K)) (some i)
          ((h, allocs), (ctx, c)) ~
        emit_list (new_page_logs base capacity (h, allocs))
          (interp_schedule_nd sh (n + 1) (ts.set i (K (some base))) (some i)
            ((page_heap base capacity h, upd allocs base (page_size capacity)), (ctx, c))) := by
  intro hfin
  obtain ⟨base, hpos, hfree, hfirst⟩ :=
    first_fit_exists h (page_size capacity) hfin (page_size_positive _)
  exact ⟨base, hpos, hfree, hfirst, page_heap_finite _ _ _ hfin, page_heap_old_frame _ _ _ hfree,
    interp_nd_new_page_first n ts i capacity base K h allocs ctx c hpos hfree hfirst⟩

/-! Empty heaps accept the very first candidate, even at capacity zero: the request always
covers the five metadata cells. -/

theorem interp_rr_new_page_hemp (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (ctx : Ctx) (c : Nat) :
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K)) (some i) m
        (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some 1))) (some i) m
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) :=
  interp_rr_new_page_first n ts i capacity 1 K m hemp hemp ctx c Nat.one_pos (fun _ _ => rfl)
    fun _ _ h2 => absurd h2 (by omega)

theorem interp_nd_new_page_hemp (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (K : Option Nat → Thread sE Bn) (ctx : Ctx) (c : Nat) :
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K)) (some i)
        (managed_empty, (ctx, c)) ~
      emit_list (new_page_logs 1 capacity managed_empty)
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some 1))) (some i)
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) :=
  interp_nd_new_page_first n ts i capacity 1 K hemp hemp ctx c Nat.one_pos (fun _ _ => rfl)
    fun _ _ h2 => absurd h2 (by omega)

/-! Source read probes after dynamic initialization: instantiating `address` with metadata, link
or payload addresses combines these with the `page_heap_*` lookup laws, without a fixture. -/

theorem interp_rr_new_page_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (address : Nat → Nat) (value : Nat) (K : Option Nat → Thread sE Bn)
    (m : Nat) (ctx : Ctx) (c : Nat) :
    page_heap 1 capacity hemp (address 1) = some value →
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.bind (new_page capacity) fun base => .read (address base)) >>= K))
        (some i) m (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some value))) (some i) m
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) := by
  intro hl
  rw [interp_rr_bind]
  exact sbisim_trans (interp_rr_new_page_hemp n ts i capacity _ m ctx c)
    (emit_list_sbisim _ (interp_rr_read_value n ts i (address 1) value K m _ _ ctx c hl))

theorem interp_nd_new_page_read (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (address : Nat → Nat) (value : Nat) (K : Option Nat → Thread sE Bn)
    (ctx : Ctx) (c : Nat) :
    page_heap 1 capacity hemp (address 1) = some value →
    interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.bind (new_page capacity) fun base => .read (address base)) >>= K))
        (some i) (managed_empty, (ctx, c)) ~
      emit_list (new_page_logs 1 capacity managed_empty)
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some value))) (some i)
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) := by
  intro hl
  rw [interp_nd_source_bind]
  exact sbisim_trans (interp_nd_new_page_hemp n ts i capacity _ ctx c)
    (emit_list_sbisim _ (interp_nd_source_read_value n ts i (address 1) value K _ _ ctx c hl))

theorem interp_rr_new_page_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (address : Nat → Nat) (K : Option Nat → Thread sE Bn) (m : Nat) (ctx : Ctx)
    (c : Nat) :
    page_heap 1 capacity hemp (address 1) = none →
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.bind (new_page capacity) fun base => .read (address base)) >>= K))
        (some i) m (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  intro hl
  rw [interp_rr_bind]
  exact sbisim_trans (interp_rr_new_page_hemp n ts i capacity _ m ctx c)
    (emit_list_sbisim _ (interp_rr_read_missing n ts i (address 1) K m _ _ ctx c hl))

theorem interp_nd_new_page_read_missing (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (capacity : Nat) (address : Nat → Nat) (K : Option Nat → Thread sE Bn) (ctx : Ctx) (c : Nat) :
    page_heap 1 capacity hemp (address 1) = none →
    interp_schedule_nd sh (n + 1)
        (ts.set i (denote_flow (.bind (new_page capacity) fun base => .read (address base)) >>= K))
        (some i) (managed_empty, (ctx, c)) ~
      emit_list (new_page_logs 1 capacity managed_empty)
        (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  intro hl
  rw [interp_nd_source_bind]
  exact sbisim_trans (interp_nd_new_page_hemp n ts i capacity _ ctx c)
    (emit_list_sbisim _ (interp_nd_source_read_missing n ts i (address 1) K _ _ ctx c hl))

/-- The children are the actual scoped-fork children: their `none` branch terminates instead of
running the parent's remaining initialization; the parent's focus advances twice but its cursor is
unchanged until selection. All initialization snapshots are retained under `.inl`. -/
theorem run_rr_allocator_initialized (capacity : Nat) (ctx : Ctx) (c : Nat) :
    run_rr (allocator_program capacity) (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (interp_schedule_rr sh 3 (source_pool0 1) none 0
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) := by
  rw [run_rr_unfold]
  show interp_schedule_rr sh (0 + 1) (#v[(pure ⟨⟩ : Thread sE Bn)].set (0 : Fin 1)
    (denote_flow (allocator_program capacity) >>= fun _ => pure ⟨⟩)) (some 0) 0 _ ~ _
  rw [allocator_program, interp_rr_bind]
  refine sbisim_trans (interp_rr_new_page_hemp 0 _ 0 capacity _ 0 ctx c) (emit_list_sbisim _ ?_)
  rw [interp_rr_bind]
  refine sbisim_trans (interp_rr_fork 0 _ 0 _ _ 0 _) ?_
  show interp_schedule_rr sh (1 + 1) (#v[denote (remote_client 1 false), pure ⟨⟩].set (1 : Fin 2)
    (denote_flow (.bind (.fork (remote_client 1 true)) fun _ => owner 1) >>= fun _ => pure ⟨⟩))
    (some 1) 0 _ ~ _
  rw [interp_rr_bind]
  refine sbisim_trans (interp_rr_fork 1 _ 1 _ _ 0 _) ?_
  show interp_schedule_rr sh (2 + 1) (#v[denote (remote_client 1 true),
    denote (remote_client 1 false), pure ⟨⟩].set (2 : Fin 3)
    (denote_flow (owner 1) >>= fun _ => pure ⟨⟩)) (some 2) 0 _ ~ _
  rw [owner, interp_rr_bind]
  exact interp_rr_yield 2 _ 2 _ 0 _

/-! The same snapshot-preserving startup for any instrumented scheduler. -/

theorem interp_fair_init_links (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (first count : Nat) (K : Option Unit → Thread sE Bn) (st : sch.sched_state)
    (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    (∀ offset, offset < 2 * count → h (first + offset) ≠ none) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (init_links first count) >>= K))
        (some i) st ((h, allocs), (ctx, c)) ~
      emit_list ((init_links_logs first count (h, allocs)).map .inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          ((init_links_heap first count h, allocs), (ctx, c))) := fun hal =>
  interp_fair_sequential sch n ts i _ K st _ _ _ _ (init_links_yield_fork_free _ _)
    (instr_flow_init_links first count h allocs ctx c hal)

theorem interp_fair_init_page (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (base capacity : Nat) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (init_page base capacity) >>= K))
        (some i) st ((hunion (hblock base (page_size capacity)) h, allocs), (ctx, c)) ~
      emit_list ((init_page_logs base capacity
          (hunion (hblock base (page_size capacity)) h, allocs)).map .inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          ((page_heap base capacity h, allocs), (ctx, c))) :=
  interp_fair_sequential sch n ts i _ K st _ _ _ _ (init_page_yield_fork_free _ _)
    (instr_flow_init_page base capacity h allocs ctx c)

theorem interp_fair_new_page_first (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (capacity base : Nat) (K : Option Nat → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    0 < base → block_free h base (page_size capacity) →
    (∀ j, 0 < j → j < base → ¬ block_free h j (page_size capacity)) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K))
        (some i) st ((h, allocs), (ctx, c)) ~
      emit_list ((new_page_logs base capacity (h, allocs)).map .inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some base))) (some i) st
          ((page_heap base capacity h, upd allocs base (page_size capacity)), (ctx, c))) := by
  intro hpos hfree hfirst
  rw [new_page, interp_fair_bind]
  refine sbisim_trans (interp_fair_alloc_first sch n ts i _ base _ st h allocs ctx c
    (page_size_positive _) hpos hfree hfirst) ?_
  simp only [new_page_logs, List.map_cons, emit_list_cons, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_fair_bind]
  refine sbisim_trans (interp_fair_init_page sch n ts i base capacity _ st h
    (upd allocs base (page_size capacity)) ctx c) (emit_list_sbisim _ ?_)
  rw [interp_fair_ret]; exact sbisim_refl _

theorem interp_fair_new_page_hemp (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (capacity : Nat) (K : Option Nat → Thread sE Bn) (st : sch.sched_state)
    (ctx : Ctx) (c : Nat) :
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (new_page capacity) >>= K))
        (some i) st (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some 1))) (some i) st
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) :=
  interp_fair_new_page_first sch n ts i capacity 1 K st hemp hemp ctx c Nat.one_pos
    (fun _ _ => rfl) fun _ _ h2 => absurd h2 (by omega)

theorem run_fair_allocator_initialized (sch : Scheduler) (capacity : Nat) (st : sch.sched_state)
    (ctx : Ctx) (c : Nat) :
    run_fair sch (allocator_program capacity) st (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (interp_schedule_fair sch sh 3 (source_pool0 1) none st
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) := by
  rw [run_fair_unfold]
  show interp_schedule_fair sch sh (0 + 1) (#v[(pure ⟨⟩ : Thread sE Bn)].set (0 : Fin 1)
    (denote_flow (allocator_program capacity) >>= fun _ => pure ⟨⟩)) (some 0) st _ ~ _
  rw [allocator_program, interp_fair_bind]
  refine sbisim_trans (interp_fair_new_page_hemp sch 0 _ 0 capacity _ st ctx c)
    (emit_list_sbisim _ ?_)
  rw [interp_fair_bind]
  refine sbisim_trans (interp_fair_fork sch 0 _ 0 _ _ st _) ?_
  show interp_schedule_fair sch sh (1 + 1) (#v[denote (remote_client 1 false), pure ⟨⟩].set
    (1 : Fin 2)
    (denote_flow (.bind (.fork (remote_client 1 true)) fun _ => owner 1) >>= fun _ => pure ⟨⟩))
    (some 1) st _ ~ _
  rw [interp_fair_bind]
  refine sbisim_trans (interp_fair_fork sch 1 _ 1 _ _ st _) ?_
  show interp_schedule_fair sch sh (2 + 1) (#v[denote (remote_client 1 true),
    denote (remote_client 1 false), pure ⟨⟩].set (2 : Fin 3)
    (denote_flow (owner 1) >>= fun _ => pure ⟨⟩)) (some 2) st _ ~ _
  rw [owner, interp_fair_bind]
  exact interp_fair_yield sch 2 _ 2 _ st _

theorem run_nd_allocator_initialized (capacity : Nat) (ctx : Ctx) (c : Nat) :
    run_nd (allocator_program capacity) (managed_empty, (ctx, c)) ~
      emit_list (new_page_logs 1 capacity managed_empty)
        (interp_schedule_nd sh 3 (source_pool0 1) none
          ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))) := by
  rw [run_nd_unfold]
  show interp_schedule_nd sh (0 + 1) (#v[(pure ⟨⟩ : Thread sE Bn)].set (0 : Fin 1)
    (denote_flow (allocator_program capacity) >>= fun _ => pure ⟨⟩)) (some 0) _ ~ _
  rw [allocator_program, interp_nd_source_bind]
  refine sbisim_trans (interp_nd_new_page_hemp 0 _ 0 capacity _ ctx c) (emit_list_sbisim _ ?_)
  rw [interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_fork 0 _ 0 _ _ _) ?_
  show interp_schedule_nd sh (1 + 1) (#v[denote (remote_client 1 false), pure ⟨⟩].set (1 : Fin 2)
    (denote_flow (.bind (.fork (remote_client 1 true)) fun _ => owner 1) >>= fun _ => pure ⟨⟩))
    (some 1) _ ~ _
  rw [interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_fork 1 _ 1 _ _ _) ?_
  show interp_schedule_nd sh (2 + 1) (#v[denote (remote_client 1 true),
    denote (remote_client 1 false), pure ⟨⟩].set (2 : Fin 3)
    (denote_flow (owner 1) >>= fun _ => pure ⟨⟩)) (some 2) _ ~ _
  rw [owner, interp_nd_source_bind]
  exact interp_nd_source_yield 2 _ 2 _ _

/-! ## Exact first-yield segments of every model turn

The checked model branches provide precisely the successful heap reads; repeated checked writes stay
allocated even if addresses coincide. No heap extensionality, freshness or unchecked CAS is used.
The Rocq Ltacs `allocator_segment_steps`/`allocator_residual_raw` become the local tactics below:
`seg_step` walks one exact-segment rule, `res_close` closes the trailing guard equivalence. -/

private theorem seg_ite_pos {A : Type} {c : Prop} [Decidable c] (a b : CProg A)
    (K : Option A → Thread sE Bn) (σ : SSig) (logs : List (CSLObs (Nat × Nat)))
    (target : Thread sE Bn) (σ' : SSig) :
    c → segment_to sh csl_equ (denote_flow a >>= K) σ logs target σ' →
    segment_to sh csl_equ (denote_flow (if c then a else b) >>= K) σ logs target σ' := by
  intro hc h; simp only [hc, ↓reduceIte]; exact h

private theorem seg_ite_neg {A : Type} {c : Prop} [Decidable c] (a b : CProg A)
    (K : Option A → Thread sE Bn) (σ : SSig) (logs : List (CSLObs (Nat × Nat)))
    (target : Thread sE Bn) (σ' : SSig) :
    ¬ c → segment_to sh csl_equ (denote_flow b >>= K) σ logs target σ' →
    segment_to sh csl_equ (denote_flow (if c then a else b) >>= K) σ logs target σ' := by
  intro hc h; simp only [hc, ↓reduceIte]; exact h

local syntax "cell_ok" : tactic
macro_rules
  | `(tactic| cell_ok) => `(tactic| first | focus (simp [*]; done) | (apply upd_mono; cell_ok))

local macro "side_ok" : tactic => `(tactic| first | rfl | assumption | focus (simp_all; done))

local macro "seg_step" : tactic => `(tactic| first
  | apply exact_source_yield
  | apply exact_source_bind
  | apply exact_source_until
  | apply exact_source_ret
  | (apply exact_source_read; assumption)
  | (apply exact_source_write; cell_ok)
  | apply exact_source_emit
  | (apply exact_source_cas_success; assumption)
  | (apply exact_source_cas_failure; assumption; side_ok)
  | (apply seg_ite_pos; side_ok)
  | (apply seg_ite_neg; side_ok)
  | dsimp only [until_tail, client_next, remote_after_free, owner_next,
      owner_after_collect, owner_after_detach])

local syntax "raw_close" : tactic
macro_rules | `(tactic| raw_close) => `(tactic| first
  | exact rfl
  | (dsimp only [until_tail, owner_after_detach, owner_after_collect, remote_after_free,
      client_next, owner_next, owner_residual, remote_residual]; raw_close)
  | (split <;> raw_close)
  | (congr 1 <;> first | exact rfl | (funext flow; cases flow <;> raw_close)))

theorem source_owner_read (base : Nat) :
    owner_residual base ORead =
      (denote_flow (detach_remote base) >>= owner_after_detach base) := by
  simp only [owner_residual, denote, source_raw_until]
  unfold owner_round collect_remote
  rw [source_raw_bind, source_raw_bind]
  raw_close

local macro "res_close" : tactic => `(tactic| (
  simp only [owner_residual, remote_residual, source_raw_ret, until_tail, owner_after_detach,
    owner_after_collect, remote_after_free]
  first
  | exact guard_equ_equ _ _ rfl
  | (apply guard_equ_equ; raw_close)
  | (apply guard_equ_left; apply guard_equ_equ; raw_close)
  | (apply guard_equ_equ; rw [source_raw_bind]; raw_close)
  | exact guard_equ_left _ _ (guard_equ_equ _ _ (source_owner_read _).symm)))

local macro "turn_cases " T:ident : tactic => `(tactic|
  (simp only [turn, Bool.false_eq_true, ↓reduceIte] at $T:ident <;> (repeat' split at $T:ident) <;>
    simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at $T:ident <;>
    obtain ⟨rfl, rfl⟩ := $T <;>
    simp only [beq_iff_eq] at * <;> subst_vars <;>
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil] <;>
    (repeat seg_step) <;> res_close))

/-- A successful model turn records the exact managed-memory snapshots of its source segment,
carrying its own allocation table throughout. -/
theorem turn_source_exact_segment (base : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) (ctx : Ctx) :
    turn base who s = some (t, event) →
    ∃ residual,
      ThreadSegment sh csl_equ (allocator_pool base s)[slot_of_actor who]
        ((s.aheap, s.aallocs), (ctx, s.acount)) event residual
        ((t.aheap, t.aallocs), (ctx, t.acount)) ∧
      guard_equ residual (allocator_pool base t)[slot_of_actor who] := by
  obtain ⟨h, al, c, op, r0, r1⟩ := s
  intro T
  cases who
  · show segment_to sh csl_equ (owner_residual base op) _ _ (owner_residual base t.owner_state) _
    rcases op with _ | _ | _ | ⟨_ | _⟩ <;> turn_cases T
  · show segment_to sh csl_equ (remote_residual base false r0) _ _
      (remote_residual base false t.remote0_state) _
    rcases r0 with _ | _ | _ | _ <;> turn_cases T
  · show segment_to sh csl_equ (remote_residual base true r1) _ _
      (remote_residual base true t.remote1_state) _
    rcases r1 with _ | _ | _ | _ <;> turn_cases T

theorem turn_other_slots (base : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) :
    turn base who s = some (t, event) →
    ∀ j, j ≠ slot_of_actor who → (allocator_pool base s)[j] = (allocator_pool base t)[j] := by
  obtain ⟨h, al, c, op, r0, r1⟩ := s
  intro T j hj
  have hfr : (who = Owner → t.remote0_state = r0 ∧ t.remote1_state = r1) ∧
      (who = Remote0 → t.owner_state = op ∧ t.remote1_state = r1) ∧
      (who = Remote1 → t.owner_state = op ∧ t.remote0_state = r0) := by
    cases who
    · rcases op with _ | _ | _ | ⟨_ | _⟩ <;>
        simp only [turn, Bool.false_eq_true, ↓reduceIte] at T <;> (repeat' split at T) <;>
        simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at T <;>
        obtain ⟨rfl, rfl⟩ := T <;> simp
    · rcases r0 with _ | _ | _ | _ <;>
        simp only [turn, Bool.false_eq_true, ↓reduceIte] at T <;> (repeat' split at T) <;>
        simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at T <;>
        obtain ⟨rfl, rfl⟩ := T <;> simp
    · rcases r1 with _ | _ | _ | _ <;>
        simp only [turn, ↓reduceIte] at T <;> (repeat' split at T) <;>
        simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at T <;>
        obtain ⟨rfl, rfl⟩ := T <;> simp
  obtain ⟨j, hj3⟩ := j
  cases who <;> simp only [forall_const, reduceCtorEq, false_implies, and_true, true_and] at hfr <;>
    obtain ⟨e1, e2⟩ := hfr <;>
    (match j, hj3 with
     | 0, _ | 1, _ | 2, _ => simp_all [allocator_pool, slot_of_actor, Fin.ext_iff])

theorem allocator_pool_state_equiv (base : Nat) (s t : AState) :
    state_equiv s t → pool_equ (allocator_pool base s) (allocator_pool base t) := fun e =>
  state_equiv_eq s t e ▸ pool_equ_refl _

/-! ## The allocator's pool-simulation certificate -/

/-- One instantiation of `PoolSimulation`; the scheduling-equivalence theorems it unlocks are the
library's, so no allocator copy of the ND coinduction or the RR guard alignment remains. -/
theorem allocator_simulation (base capacity : Nat) :
    PoolSimulation 2 sh slot_of_actor (turn base) (allocator_pool base) state_agrees
      (allocator_inv base capacity) where
  simulation_total who s hinv :=
    let ⟨t, event, ht⟩ := turn_total base capacity who s hinv
    ⟨t, event, ht, turn_preserves_inv base capacity who s t event hinv ht⟩
  simulation_segment who s s' event σ _ hagree hturn := by
    obtain ⟨⟨h, al⟩, ctx, c⟩ := σ
    obtain ⟨hh, ha, hc⟩ := hagree
    obtain rfl : h = s.aheap := funext hh
    obtain rfl : al = s.aallocs := funext ha
    obtain rfl : c = s.acount := hc
    obtain ⟨residual, hseg, htail⟩ := turn_source_exact_segment base who s s' event ctx hturn
    exact ⟨residual, _, hseg, ⟨heq_refl _, heq_refl _, rfl⟩, htail,
      turn_other_slots base who s s' event hturn⟩

private theorem source_replace_turn (base : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) (residual : Thread sE Bn) :
    turn base who s = some (t, event) →
    pool_equ ((allocator_pool base s).set (slot_of_actor who) residual)
      ((allocator_pool base t).set (slot_of_actor who) residual) := by
  intro hturn j
  by_cases hj : j = slot_of_actor who
  · subst hj; simp
  · have hv : (slot_of_actor who : Nat) ≠ j := fun e => hj (Fin.ext e).symm
    simp only [Fin.getElem_fin, Vector.getElem_set_ne _ _ hv]
    exact turn_other_slots base who s t event hturn j hj

/-- Every phase-table branch at once. The result keeps the actual residual at `none` focus; at the
canonical state the post-turn handler state is exactly the model's heap and counter. -/
theorem turn_interp_nd (base capacity : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) (ctx : Ctx) :
    allocator_inv base capacity s → turn base who s = some (t, event) →
    ∃ residual, guard_equ residual (allocator_pool base t)[slot_of_actor who] ∧
      interp_schedule_nd sh 3 (allocator_pool base s) (some (slot_of_actor who))
          ((s.aheap, s.aallocs), (ctx, s.acount)) ~
        emit_list event
          (interp_schedule_nd sh 3 ((allocator_pool base t).set (slot_of_actor who) residual)
            none ((t.aheap, t.aallocs), (ctx, t.acount))) := by
  intro _ hturn
  obtain ⟨residual, hseg, htail⟩ := turn_source_exact_segment base who s t event ctx hturn
  refine ⟨residual, htail, sbisim_trans (segment_interp_nd sh csl_equ
    (fun _ _ _ e => e ▸ sbisim_refl _) 2 _ _ _ _ _ _ hseg) ?_⟩
  rw [interp_schedule_nd_equ (handler := sh) 3 _ _ none _
    (source_replace_turn base who s t event residual hturn)]
  exact sbisim_refl _

theorem turn_interp_rr (base capacity : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) (ctx : Ctx) (cursor : Nat) :
    allocator_inv base capacity s → turn base who s = some (t, event) →
    ∃ residual, guard_equ residual (allocator_pool base t)[slot_of_actor who] ∧
      interp_schedule_rr sh 3 (allocator_pool base s) (some (slot_of_actor who)) cursor
          ((s.aheap, s.aallocs), (ctx, s.acount)) ~
        emit_list (event.map .inl)
          (interp_schedule_rr sh 3 ((allocator_pool base t).set (slot_of_actor who) residual)
            none cursor ((t.aheap, t.aallocs), (ctx, t.acount))) := by
  intro _ hturn
  obtain ⟨residual, hseg, htail⟩ := turn_source_exact_segment base who s t event ctx hturn
  refine ⟨residual, htail, sbisim_trans (segment_interp_fair rr_scheduler sh csl_equ
    (fun _ _ _ e => e ▸ sbisim_refl _) 2 _ _ cursor _ _ _ _ hseg) ?_⟩
  rw [← interp_schedule_rr_equ (h := sh) 3 _ _ none _ _
    (source_replace_turn base who s t event residual hturn)]
  exact sbisim_refl _

/-- At an arbitrary aligned pool and store the final handler state is only relationally
determined, by the library segment of `allocator_simulation`. -/
theorem selected_turn_interp_nd (base capacity : Nat) (ts : Pool sE Bn 3) (sigma : SSig)
    (s : AState) (who : Actor) (t : AState) (event : List (CSLObs (Nat × Nat))) :
    pool_guard_equ ts (allocator_pool base s) → state_agrees sigma s →
    allocator_inv base capacity s → turn base who s = some (t, event) →
    ∃ residual sigma', state_agrees sigma' t ∧
      guard_equ residual (allocator_pool base t)[slot_of_actor who] ∧
      interp_schedule_nd sh 3 ts (some (slot_of_actor who)) sigma ~
        emit_list event (interp_schedule_nd sh 3 (ts.set (slot_of_actor who) residual) none sigma')
    := by
  intro hpool hagree hinv hturn
  obtain ⟨residual, sigma', hstate, hnext, hinterp⟩ := pool_simulation_turn_nd
    (allocator_simulation base capacity) ts s who t event sigma hinv hagree hpool hturn
  have htail := hnext (slot_of_actor who)
  simp only [Fin.getElem_fin, Vector.getElem_set_self] at htail
  exact ⟨residual, sigma', hstate, htail, hinterp⟩

theorem selected_turn_interp_rr (base capacity : Nat) (ts : Pool sE Bn 3) (sigma : SSig)
    (s : AState) (who : Actor) (t : AState) (event : List (CSLObs (Nat × Nat))) (cursor : Nat) :
    pool_guard_equ ts (allocator_pool base s) → state_agrees sigma s →
    allocator_inv base capacity s → turn base who s = some (t, event) →
    ∃ residual sigma', state_agrees sigma' t ∧
      guard_equ residual (allocator_pool base t)[slot_of_actor who] ∧
      interp_schedule_rr sh 3 ts (some (slot_of_actor who)) cursor sigma ~
        emit_list (event.map .inl)
          (interp_schedule_rr sh 3 (ts.set (slot_of_actor who) residual) none cursor sigma') := by
  intro hpool hagree hinv hturn
  obtain ⟨residual, sigma', hseg, hstate, hnext⟩ := selected_turn_segment
    (allocator_simulation base capacity) ts s who t event sigma hinv hagree hpool hturn
  have htail := hnext (slot_of_actor who)
  simp only [Fin.getElem_fin, Vector.getElem_set_self] at htail
  exact ⟨residual, sigma', hstate, htail, segment_interp_fair rr_scheduler sh csl_equ
    (fun _ _ _ e => e ▸ sbisim_refl _) 2 ts _ cursor sigma event residual sigma' hseg⟩

theorem selected_turn_exact_segment (base : Nat) (ts : Pool sE Bn 3) (s : AState) (who : Actor)
    (t : AState) (event : List (CSLObs (Nat × Nat))) (ctx : Ctx) :
    pool_guard_equ ts (allocator_pool base s) → turn base who s = some (t, event) →
    ∃ residual,
      ThreadSegment sh csl_equ ts[slot_of_actor who] ((s.aheap, s.aallocs), (ctx, s.acount))
        event residual ((t.aheap, t.aallocs), (ctx, t.acount)) ∧
      guard_equ residual (allocator_pool base t)[slot_of_actor who] := by
  intro hpool hturn
  obtain ⟨residual, hseg, htail⟩ := turn_source_exact_segment base who s t event ctx hturn
  exact ⟨residual, (guard_equ_segment_iff sh csl_equ _ _ (hpool (slot_of_actor who)) _ _ _ _).2
    hseg, htail⟩

theorem run_rr_allocator_bisim (capacity : Nat) (ctx : Ctx) (c : Nat) :
    run_rr (allocator_program capacity) (managed_empty, (ctx, c)) ~
      emit_list ((new_page_logs 1 capacity managed_empty).map .inl)
        (model_rr 2 actor_of_slot (turn 1) (initial_state capacity c) 0 :
          ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  sbisim_trans (run_rr_allocator_initialized capacity ctx c) (emit_list_sbisim _
    (pool_simulation_rr_bisim actor_of_slot slot_of_actor_of_slot
      (allocator_simulation 1 capacity) (initial_state capacity c) (source_pool0 1)
      ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c)) 0
      (initial_state_inv capacity c) ⟨heq_refl _, heq_refl _, rfl⟩
      (pool_equ_guard _ _ (source_pool0_initial capacity c))))

theorem run_nd_allocator_bisim (capacity : Nat) (ctx : Ctx) (c : Nat) :
    run_nd (allocator_program capacity) (managed_empty, (ctx, c)) ~
      emit_list (new_page_logs 1 capacity managed_empty)
        (model_nd 2 actor_of_slot (turn 1) (initial_state capacity c) :
          ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) :=
  sbisim_trans (run_nd_allocator_initialized capacity ctx c) (emit_list_sbisim _
    (pool_simulation_nd_bisim (allocator_simulation 1 capacity) actor_of_slot
      slot_of_actor_of_slot (initial_state capacity c) (source_pool0 1)
      ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c))
      (initial_state_inv capacity c) ⟨heq_refl _, heq_refl _, rfl⟩
      (pool_equ_guard _ _ (source_pool0_initial capacity c))))

/-- The one program-specific validity entry point for raw source executions: the library's pool
validity at the allocator handler, slot map, initial source pool, and initialized page with its
recorded extent. -/
def allocator_source_valid (capacity : Nat) (ctx : Ctx) (c : Nat)
    (se : Execution (Pool sE Bn 3 × SSig) Actor (List (CSLObs (Nat × Nat)))) : Prop :=
  pool_execution_valid 2 sh slot_of_actor (source_pool0 1)
    ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c)) se

-- Not ported: the Ltacs `allocator_residual_raw` and `allocator_segment_steps` (replaced by the
-- local tactics `seg_step`/`raw_close`/`res_close`/`turn_cases` above); `Local Opaque`/
-- `Local Transparent` directives (Lean's `simp only` lists control unfolding instead).

end Examples.CSL.Allocator.Execution
