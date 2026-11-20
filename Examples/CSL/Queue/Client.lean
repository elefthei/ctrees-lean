/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Program
public import Examples.CSL.Queue.Shared

/-!
# An allocated queue client: passive framing and runner-safe source reuse

The source split changes neither effect order nor yield boundaries. Its finite helper equation
is lifted structurally before applying the round-robin runner. The recurrent proof reuses
`SharedInv` and the ranked-turn certificate, then applies the generic semantic frame rule to the
initialized owned resource (← `examples/CSL/Queue/Client.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Client
open CTree Tisl Tisl.Notation Tisl.Heap Tisl.Pcm Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Layout Examples.CSL.Queue.Operations
open Examples.CSL.Queue.Trace Examples.CSL.Queue.Frame Examples.CSL.Queue.Program
open Examples.CSL.Queue.Shared
open ITree (Effect)

def read_queue_head (hdr : Nat) : CProg (Nat × Nat) :=
  .bind (.read (hdr + 1)) fun a =>
  .bind (.read a) fun v => .ret (a, v)

def rotate_captured (tag hdr a v : Nat) : CProg Unit :=
  .bind (.emit tag v) fun _ =>
  .bind (.read (a + 1)) fun n =>
  .bind (.write (hdr + 1) n) fun _ =>
  .bind (.read hdr) fun z0 =>
  .bind (.write ((if n == 0 then hdr else z0) + 1) a) fun _ =>
  .bind (.write (a + 1) 0) fun _ => .write hdr a

def rotate_once_split (tag hdr : Nat) : CProg Unit :=
  .bind (read_queue_head hdr) fun av => rotate_captured tag hdr av.1 av.2

def worker_split (tag hdr : Nat) : CProg Unit :=
  .untilNone (.bind (rotate_once_split tag hdr) fun _ => .bind .yield fun _ => .ret (some ()))

def shared_queue_split (hdr : Nat) : CProg Unit :=
  .bind (.fork (worker_split 1 hdr)) fun _ =>
  .bind (.fork (worker_split 2 hdr)) fun _ => .ret ()

def allocated_shared_queue_split (values : List Nat) : CProg Unit :=
  .bind (new_queue values) shared_queue_split

/-! ## Source equivalence

Finite source unfolding and monad laws remove the captured-pair return; no iteration or
scheduler is unfolded. Rocq `≅` is `=`. -/

private theorem rotate_once_split_cps_equ {X : Type} (tag hdr : Nat)
    (K : Option Unit → CTree CEff Bn X) :
    (denote_flow (rotate_once_split tag hdr) >>= K) =
      (denote_flow (rotate_once tag hdr) >>= K) := by
  simp only [rotate_once_split, read_queue_head, rotate_captured, rotate_once, denote_flow,
    bind_assoc, pure_bind']

theorem rotate_once_split_cps (tag hdr : Nat) (K : Option Unit → Thread sE Bn) :
    (denote_flow (rotate_once_split tag hdr) >>= K) =
      (denote_flow (rotate_once tag hdr) >>= K) :=
  rotate_once_split_cps_equ tag hdr K

private theorem rotate_once_split_equ (tag hdr : Nat) :
    denote_flow (rotate_once_split tag hdr) = denote_flow (rotate_once tag hdr) := by
  simp only [rotate_once_split, read_queue_head, rotate_captured, rotate_once, denote_flow,
    bind_assoc, pure_bind']

theorem denote_flow_worker_split (tag hdr : Nat) :
    denote_flow (worker_split tag hdr) = denote_flow (worker tag hdr) := by
  have hu : ∀ b b' : CProg (Option Unit), denote_flow b = denote_flow b' →
      denote_flow (.untilNone b) = denote_flow (.untilNone b') := by
    intro b b' h; rw [denote_flow, denote_flow, h]
  exact hu _ _ (denote_flow_bind_equ _ _ _ _ (rotate_once_split_equ tag hdr) fun _ => rfl)

theorem denote_worker_split (tag hdr : Nat) :
    denote (worker_split tag hdr) = denote (worker tag hdr) :=
  denote_equ _ _ (denote_flow_worker_split tag hdr)

theorem worker_split_pool_rr (hdr : Nat) (focus : Option (Fin 2)) (cursor : Nat) (s : SSig) :
    run_rr_pool #v[worker_split 2 hdr, worker_split 1 hdr] focus cursor s ~
      run_rr_pool #v[worker 2 hdr, worker 1 hdr] focus cursor s := by
  have h : csl_pool #v[worker_split 2 hdr, worker_split 1 hdr] =
      csl_pool #v[worker 2 hdr, worker 1 hdr] := by
    simp [csl_pool, denote_worker_split]
  unfold run_rr_pool; rw [h]; exact sbisim_refl _

theorem shared_queue_split_rr (hdr : Nat) (s : SSig) :
    run_rr (shared_queue_split hdr) s ~ run_rr (shared_queue hdr) s :=
  sbisim_trans (run_rr_two_forks _ _ s)
    (sbisim_trans (worker_split_pool_rr hdr none 0 s) (sbisim_symm (run_rr_two_forks _ _ s)))

private theorem shared_queue_split_equ (hdr : Nat) :
    denote_flow (shared_queue_split hdr) = denote_flow (shared_queue hdr) :=
  denote_flow_bind_equ _ _ _ _
    (denote_flow_fork_equ _ _ (denote_flow_worker_split 1 hdr)) fun _ =>
  denote_flow_bind_equ _ _ _ _
    (denote_flow_fork_equ _ _ (denote_flow_worker_split 2 hdr)) fun _ => rfl

theorem allocated_shared_queue_split_rr (values : List Nat) (s : SSig) :
    run_rr (allocated_shared_queue_split values) s ~ run_rr (allocated_shared_queue values) s := by
  have h : denote (allocated_shared_queue_split values) = denote (allocated_shared_queue values) :=
    denote_equ _ _ (denote_flow_bind_equ _ _ _ _ rfl shared_queue_split_equ)
  rw [run_rr_unfold, run_rr_unfold, h]
  exact sbisim_refl _

/-! ## Initialization contract -/

theorem qheap_managed_wf (hdr : Nat) (values : List Nat) :
    0 < hdr →
      managed_wf (qheap hdr (queue_nodes hdr values.length) values,
        upd hemp hdr (2 * (values.length + 1))) := by
  intro hpos
  refine ⟨fun base size hrec => ?_, fun b1 n1 b2 n2 h1 h2 hne => ?_⟩
  · simp only [upd, hemp] at hrec
    split at hrec
    · cases hrec; subst base
      refine ⟨hpos, by omega, fun x hx => ?_⟩
      exact qrep_fp _ _ _ _ (qheap_queue_nodes_rep hdr values hpos) x
        ((queue_cells_range hdr values.length x).2 hx)
    · cases hrec
  · simp only [upd, hemp] at h1 h2
    split at h1 <;> split at h2 <;> simp_all

theorem initialized_queue_frame_rel (hdr : Nat) (values : List Nat) (f : Heap) (ctx : Ctx)
    (c : Nat) :
    0 < hdr → block_free f hdr (2 * (values.length + 1)) →
      frame_rel (f, hemp)
        ((qheap hdr (queue_nodes hdr values.length) values,
          upd hemp hdr (2 * (values.length + 1))), (ctx, c))
        ((new_queue_heap hdr values f, upd hemp hdr (2 * (values.length + 1))), (ctx, c)) := by
  intro hpos hfree
  refine ⟨⟨⟨new_queue_heap_disjoint hdr values f hfree, hdisj_sym _ _ (hdisj_hemp _)⟩,
    qheap_managed_wf hdr values hpos⟩, rfl, new_queue_heap_agrees hdr values f hpos hfree,
    fun x => ?_⟩
  show upd hemp hdr _ x = hunion (upd hemp hdr _) hemp x
  simp only [hunion]; split <;> simp_all [hemp]

/-- Focusing a singleton pool replaces its only thread. -/
private theorem pool_set_single (x : Thread sE Bn) :
    #v[(pure ⟨⟩ : Thread sE Bn)].set ((0 : Fin (0 + 1)) : Nat) x = #v[x] := by
  simp

/-- The allocated shared queue is the new-queue flow followed by the shared program. -/
private theorem denote_allocated (values : List Nat) :
    denote (allocated_shared_queue values) =
      (denote_flow (new_queue values) >>= fun flow => match flow with
        | none => pure ⟨⟩
        | some hdr => denote (shared_queue hdr)) := by
  rw [denote, allocated_shared_queue, source_raw_bind]
  congr 1; funext flow; cases flow <;> rfl

theorem allocated_shared_queue_rr_contract (values : List Nat) (f : Heap) (ctx : Ctx) (c : Nat) :
    heap_finite f →
    ∃ hdr,
      0 < hdr ∧ block_free f hdr (2 * (values.length + 1)) ∧
      asep (qrepX hdr (queue_nodes hdr values.length) values) (fun frame => heq frame f)
        (new_queue_heap hdr values f) ∧
      frame_rel (f, hemp)
        ((qheap hdr (queue_nodes hdr values.length) values,
          upd hemp hdr (2 * (values.length + 1))), (ctx, c))
        ((new_queue_heap hdr values f, upd hemp hdr (2 * (values.length + 1))), (ctx, c)) ∧
      run_rr (allocated_shared_queue values) ((f, hemp), (ctx, c)) ~
        emit_list ((new_queue_logs hdr values (f, hemp)).map .inl)
          (run_rr (shared_queue hdr)
            ((new_queue_heap hdr values f, upd hemp hdr (2 * (values.length + 1))), (ctx, c))) := by
  intro hfin
  obtain ⟨hdr, hpos, hfree, -, howned, hrun⟩ := interp_rr_new_queue 0 #v[pure ⟨⟩] 0 values
    (fun flow => match flow with
      | none => pure ⟨⟩
      | some hdr => denote (shared_queue hdr)) 0 f hemp ctx c hfin
  refine ⟨hdr, hpos, hfree, howned, initialized_queue_frame_rel hdr values f ctx c hpos hfree, ?_⟩
  rw [pool_set_single, pool_set_single] at hrun
  rw [run_rr_unfold, denote_allocated, run_rr_unfold]
  exact hrun

/-! ## Passive framing of the recurrent emission -/

private theorem shared_queue_alloc_free (hdr : Nat) : alloc_free (shared_queue hdr) := by
  simp [alloc_free, shared_queue, worker, rotate_once, prog_ok, okE_thread, okE_lift,
    no_alloc_sE]

/-- Passive framing preserves indexed user emissions through `.inl`, while heap snapshots gain
the passive frame and `.inr` selections stay equal. -/
private theorem shared_pop_after_stable (fr : ManagedHeap) (nl k : Nat) :
    prefix_stable (frameERW fr) (frameRV (X := PUnit) fr)
      (AG (AF (visWₜ (fair_obs (shared_pop_after nl k))))) := by
  simp only [prefix_stable_cg, prefix_stable_cu, prefix_stable_now]
  refine ⟨fun _ _ _ _ _ => trivial, fun w w' hw hW hP => ?_⟩
  cases hP with
  | obs e v hP =>
    rcases e with ((_ | _ | e) | _) <;> simp only [fair_obs, shared_pop_after, csl_indexed] at hP
    have hS : simW (frameERW fr) (frameRV (X := PUnit) fr) (.obs (.inl (.emit e)) v)
        (.obs (.inl (.emit e)) v) := .obs _ _ _ _ (frameERW_emit fr e) .rfl
    rw [simW_not_done_right_unique _ _ (frameERW_right_unique fr) _ _ _ hw hW hS]
    exact .obs _ _ hP

theorem allocated_shared_queue_passive_fresh_rr (values : List Nat) (nl d : Nat) (f : Heap)
    (ctx : Ctx) :
    heap_finite f → find_index Nat.beq nl values = some d →
      run_rr_recurrently_emits (allocated_shared_queue values) (f, hemp) ctx
        (fun output => output.2 = nl) := by
  intro hfin hmem c
  refine csl_fresh_implies_recurrent_emissionW _ (fun _ => inferInstance) _ .pure fun k => ?_
  obtain ⟨hdr, hpos, hfree, -, hrel, hrun⟩ := allocated_shared_queue_rr_contract values f ctx c hfin
  refine (proper_entails_meq _ hrun).2 (agaf_emit_list _ _ _ _ .pure ?_)
  rw [new_queue_logs_afterW]
  let owned_memory : ManagedHeap :=
    (qheap hdr (queue_nodes hdr values.length) values, upd hemp hdr (2 * (values.length + 1)))
  refine ticl_csl_frameW_stable (f, hemp) _ _ _ (run_rr_framable _ (shared_queue_alloc_free hdr))
    hrel _ (.obs (.inl (.heap owned_memory)) ⟨⟩) _ (shared_pop_after_stable _ nl k)
    (.obs _ _ _ _ (frameERW_heap (f, hemp) _ _ hrel) .rfl) ?_
  show entails _ (run_rr (shared_queue hdr) (owned_memory, (ctx, c))) _
  refine (proper_entails_meq _ (run_rr_two_forks _ _ _)).2 ?_
  exact shared_pool_agaf_rr hdr nl k (k - c, d) _ 0 _ _ (shared_ranked hdr nl k)
    ⟨queue_nodes hdr values.length, values, d, qheap_queue_nodes_rep hdr values hpos, hmem, rfl⟩
    (.obs _ _)

theorem allocated_shared_queue_split_passive_fresh_rr (values : List Nat) (nl d : Nat) (f : Heap)
    (ctx : Ctx) :
    heap_finite f → find_index Nat.beq nl values = some d →
      run_rr_recurrently_emits (allocated_shared_queue_split values) (f, hemp) ctx
        (fun output => output.2 = nl) := fun hfin hmem c =>
  recurrent_label_sbisim _ _ _ (sbisim_symm (allocated_shared_queue_split_rr values _))
    (allocated_shared_queue_passive_fresh_rr values nl d f ctx hfin hmem c)

theorem client_passive_10 :
    run_rr_recurrently_emits (allocated_shared_queue [10, 20, 30]) (upd hemp 100 7, hemp) []
      (fun output => output.2 = 10) :=
  allocated_shared_queue_passive_fresh_rr _ _ 0 _ _ (heap_finite_upd _ _ _ heap_finite_hemp) rfl

theorem client_split_passive_10 :
    run_rr_recurrently_emits (allocated_shared_queue_split [10, 20, 30]) (upd hemp 100 7, hemp) []
      (fun output => output.2 = 10) :=
  allocated_shared_queue_split_passive_fresh_rr _ _ 0 _ _
    (heap_finite_upd _ _ _ heap_finite_hemp) rfl

/-! ## A concrete client run -/

def client_heap : Heap := new_queue_heap 1 [10, 20, 30] (upd hemp 100 7)

private theorem client_block_free : block_free (upd hemp 100 7) 1 8 := by
  intro offset h; simp only [upd, hemp]; split <;> first | rfl | omega

private theorem client_heap_rep : qrep 1 [3, 5, 7] [10, 20, 30] client_heap := by
  have owned := qheap_queue_nodes_rep 1 [10, 20, 30] (by omega)
  refine qrep_agree_fp _ _ _ _ _ owned (fun x hx => ?_) rfl
  rw [client_heap, new_queue_heap_agrees 1 [10, 20, 30] (upd hemp 100 7) (by omega)
    client_block_free x]
  exact hunion_eq _ _ _ (qrep_fp _ _ _ _ owned x hx)

private theorem client_initialization :
    run_rr (allocated_shared_queue [10, 20, 30]) ((upd hemp 100 7, hemp), ([], 0)) ~
      emit_list ((new_queue_logs 1 [10, 20, 30] (upd hemp 100 7, hemp)).map .inl)
        (run_rr (shared_queue 1) ((client_heap, upd hemp 1 8), ([], 0))) := by
  rw [run_rr_unfold, denote_allocated, run_rr_unfold]
  exact interp_rr_new_queue_first 0 #v[pure ⟨⟩] 0 [10, 20, 30] 1
    (fun flow => match flow with
      | none => pure ⟨⟩
      | some hdr => denote (shared_queue hdr)) 0 (upd hemp 100 7) hemp [] 0
    (by omega) client_block_free (fun _ _ _ => by omega)

/-- Three logged scheduler picks, each followed by a complete constructor-backed turn; the
suffix records the actual cursor. -/
theorem client_split_prefix3 :
    run_rr (allocated_shared_queue_split [10, 20, 30]) ((upd hemp 100 7, hemp), ([], 0)) ~
      emit_list ((new_queue_logs 1 [10, 20, 30] (upd hemp 100 7, hemp)).map .inl)
      (.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr 0) fun _ =>
        emit_list ((queue_turn_logs (.emit (stamp (2, 10) 0))
          1 3 5 7 (client_heap, upd hemp 1 8)).map .inl)
      (.vis (.inr 1) fun _ =>
        emit_list ((queue_turn_logs (.emit (stamp (1, 20) 1))
          1 5 7 3 (qstep 1 [3, 5, 7] client_heap, upd hemp 1 8)).map .inl)
      (.vis (.inr 0) fun _ =>
        emit_list ((queue_turn_logs (.emit (stamp (2, 30) 2))
          1 7 3 5 (qstep 1 [5, 7, 3] (qstep 1 [3, 5, 7] client_heap), upd hemp 1 8)).map .inl)
        (run_rr_pool #v[worker 2 1, worker 1 1] none 3
          ((qstepN 1 3 [3, 5, 7] client_heap, upd hemp 1 8), ([], 3)))))) := by
  refine sbisim_trans (allocated_shared_queue_split_rr _ _)
    (sbisim_trans client_initialization (emit_list_sbisim _ ?_))
  refine sbisim_trans (run_rr_two_forks _ _ _) ?_
  have hq0 := client_heap_rep
  have hq1 : qrep 1 [5, 7, 3] [20, 30, 10] (qstep 1 [3, 5, 7] client_heap) :=
    qstep_qrep 1 [3, 5, 7] [10, 20, 30] client_heap hq0 (by simp)
  have hq2 : qrep 1 [7, 3, 5] [30, 10, 20] (qstep 1 [5, 7, 3] (qstep 1 [3, 5, 7] client_heap)) :=
    qstep_qrep 1 [5, 7, 3] [20, 30, 10] _ hq1 (by simp)
  have turn : ∀ (i : Fin 2) (tag cursor : Nat) (s s' : SSig) logs,
      (csl_pool #v[worker 2 1, worker 1 1])[i] = denote (worker tag 1) →
      segment_to sh csl_equ (denote (worker tag 1)) s logs (denote (worker tag 1)) s' →
      run_rr_pool #v[worker 2 1, worker 1 1] (some i) cursor s ~
        emit_list (logs.map .inl) (run_rr_pool #v[worker 2 1, worker 1 1] none cursor s') :=
    fun i _ cursor s s' logs hi h => run_rr_pool_turn _ i cursor s s' logs (hi ▸ h)
  refine sbisim_trans (run_rr_pool_select _ 0 _) ?_
  rw [rr_pick_even (n := 0) rfl]
  refine sb_vis _ fun _ => sbisim_trans (turn 0 2 1 _ _ _ (by simp [csl_pool])
    (exact_worker_turn 2 1 3 [5, 7] 10 [20, 30] client_heap (upd hemp 1 8) [] 0 hq0))
    (emit_list_sbisim _ ?_)
  refine sbisim_trans (run_rr_pool_select _ 1 _) ?_
  rw [rr_pick_odd (n := 1) rfl]
  refine sb_vis _ fun _ => sbisim_trans (turn 1 1 2 _ _ _ (by simp [csl_pool])
    (exact_worker_turn 1 1 5 [7, 3] 20 [30, 10] (qstep 1 [3, 5, 7] client_heap) (upd hemp 1 8)
      [] 1 hq1))
    (emit_list_sbisim _ ?_)
  refine sbisim_trans (run_rr_pool_select _ 2 _) ?_
  rw [rr_pick_even (n := 2) rfl]
  refine sb_vis _ fun _ => sbisim_trans (turn 0 2 3 _ _ _ (by simp [csl_pool])
    (exact_worker_turn 2 1 7 [3, 5] 30 [10, 20] (qstep 1 [5, 7, 3] (qstep 1 [3, 5, 7] client_heap))
      (upd hemp 1 8) [] 2 hq2))
    (emit_list_sbisim _ ?_)
  exact sbisim_refl _

theorem client_frame_preserved (n : Nat) : qstepN 1 n [3, 5, 7] client_heap 100 = some 7 := by
  have hout : 100 ∉ qcells 1 [3, 5, 7] := by decide
  have frame := frame_preserved n 1 [3, 5, 7] [10, 20, 30] client_heap client_heap_rep (by simp) 100
  rw [qfrm_out _ _ _ _ hout, qfrm_out _ _ _ _ hout] at frame
  rw [← frame]; rfl

theorem client_heap_cycle3 : heq (qstepN 1 3 [3, 5, 7] client_heap) client_heap := by
  intro x
  by_cases hin : x ∈ qcells 1 [3, 5, 7]
  · have : x ∈ [1, 2, 3, 4, 5, 6, 7, 8] := hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · exact qstepN_agree 3 1 [3, 5, 7] [10, 20, 30] client_heap client_heap_rep (by simp) x hin

end Examples.CSL.Queue.Client
