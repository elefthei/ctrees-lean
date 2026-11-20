/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Shared
public import Logic.CTree.TraceRules

/-!
# Observable heap mutations of the actual CoCSL interpreter: probes and loops

A straight-line mutation probe, the exact standalone snapshots of same-value mutations and faults,
the two-write mutation loop as a batch loop (exact prefixes and `AG AF` heap observations under
ND and RR), and the silent spin loop (← `examples/CSL/Frame/HeapObservations.v`, lines 1-686).
-/

@[expose] public section
namespace Examples.CSL.Frame.HeapObservations
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared (rr_obs)
open ITree (Effect)

/-! ## Programs and snapshots -/

def mutation_probe : CProg Unit :=
  .bind (.write 1 9) fun _ =>
  .bind (.cas (.lit 1) (.lit 9) (.lit 11)) fun _ =>
  .bind (.cas (.lit 1) (.lit 9) (.lit 12)) fun _ =>
  .bind (.read 1) fun value =>
  .bind (.emit 7 value) fun _ =>
  .bind (.free 0) fun _ =>
  .bind (.alloc 2) fun base =>
  .bind (.free base) fun _ => .ret ()

def mutation_body : CProg (Option Unit) :=
  .bind (.write 1 1) fun _ => .bind (.write 1 2) fun _ => .ret (some ())
def mutation_loop : CProg Unit := .untilNone mutation_body
def mutation_spin : CProg Unit :=
  .untilNone (.bind .yield fun _ => .ret (some () : Option Unit))

def mutation_store (memory : ManagedHeap) (value : Nat) : ManagedHeap :=
  (upd memory.1 1 value, memory.2)
def mutation_next (memory : ManagedHeap) : ManagedHeap :=
  mutation_store (mutation_store memory 1) 2
def mutation_logs (memory : ManagedHeap) : List (CSLObs (Nat × Nat)) :=
  [.heap (mutation_store memory 1), .heap (mutation_next memory)]

def probe_written : ManagedHeap := (upd (hsingle 1 0) 1 9, hemp)
def probe_cas : ManagedHeap := (upd probe_written.1 1 11, hemp)
def probe_allocated : ManagedHeap := managed_alloc probe_cas 2 2
def probe_freed : ManagedHeap :=
  (hfree_block 2 2 probe_allocated.1, hfree 2 probe_allocated.2)
def probe_logs : List (CSLObs (Nat × Nat)) :=
  [.heap probe_written, .heap probe_cas, .emit (stamp (7, 11) 5), .heap probe_allocated,
   .heap probe_freed]

/-- Counted snapshots follow chronological standard iteration. -/
def mutation_round_logs (n : Nat) (memory : ManagedHeap) : List (CSLObs (Nat × Nat)) :=
  (List.range' 0 n).flatMap fun j => mutation_logs (Nat.repeat mutation_next j memory)
def mutation_after (n : Nat) (memory : ManagedHeap) : ManagedHeap :=
  Nat.repeat mutation_next n memory

def spin_rr_at (cursor : Nat) (s : SSig) : ctreeW rr_obs Bn (PUnit × SSig) :=
  interp_schedule_rr sh 1 #v[denote mutation_spin] (some 0) cursor s

/-! ## Exact standalone snapshots -/

/-- Split a shared leading log. -/
local macro "log_step" : tactic => `(tactic|
  (simp only [emit_list_cons, emit_list_nil, log_vis]; refine sb_vis _ fun _ => ?_))

theorem mutation_probe_spec (ctx : Ctx) :
    instr_flow_erased mutation_probe ((hsingle 1 0, hemp), (ctx, 5)) ~
      (emit_list probe_logs (pure (some (), (probe_freed, (ctx, 6)))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) ∧
    probe_logs.length = 5 ∧
    probe_written.1 1 = some 9 ∧ probe_cas.1 1 = some 11 ∧
    probe_allocated.1 1 = some 11 ∧ probe_allocated.1 2 = some 0 ∧
    probe_allocated.1 3 = some 0 ∧ probe_allocated.2 2 = some 2 ∧
    probe_freed.1 1 = some 11 ∧ probe_freed.1 2 = none ∧
    probe_freed.1 3 = none ∧ heq probe_freed.2 hemp ∧
    block_free probe_cas.1 2 2 ∧
    (∀ j, 0 < j → j < 2 → ¬ block_free probe_cas.1 j 2) := by
  have F : block_free probe_cas.1 2 2 := by
    intro offset h
    simp only [probe_cas, probe_written, upd, hsingle]
    split <;> (try split) <;> first | rfl | omega
  have First : ∀ j, 0 < j → j < 2 → ¬ block_free probe_cas.1 j 2 := by
    intro j hj hlt H
    obtain rfl : j = 1 := by omega
    have := H 0 (by omega)
    simp [probe_cas, upd] at this
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, F, First⟩
  · simp only [mutation_probe, probe_logs]
    refine sbisim_trans (instr_flow_write 1 9 _ _ (by simp [csl_memory, hsingle])) ?_
    log_step
    refine sbisim_trans (instr_flow_cas_value 1 9 11 9 _ _ (by simp [csl_memory])) ?_
    rw [ite_eq_left rfl]
    log_step
    refine sbisim_trans (instr_flow_cas_value 1 9 12 11 _ _ (by simp [csl_memory])) ?_
    rw [ite_eq_right (by decide)]
    refine sbisim_trans (instr_flow_read 1 11 _ _ (by simp [csl_memory])) ?_
    refine sbisim_trans (instr_flow_emit _ _ _ _) ?_
    log_step
    refine sbisim_trans (instr_flow_free 0 _ _ probe_cas rfl) ?_
    refine sbisim_trans (instr_flow_alloc_first 2 2 _ _ (by decide) (by decide) F First) ?_
    log_step
    refine sbisim_trans (instr_flow_free 2 _ _ probe_freed rfl) ?_
    log_step
    rw [instr_flow_ret]
    exact sbisim_refl _
  · intro a
    simp only [probe_freed, probe_allocated, managed_alloc, probe_cas, hfree, upd, hemp]
    split <;> (try split) <;> first | rfl | omega

theorem same_value_mutations_visible (memory : ManagedHeap) (ctx : Ctx) (c a value : Nat) :
    memory.1 a = some value →
    (instr_flow_erased (.bind (.write a value) fun _ => .ret ()) (memory, (ctx, c)) ~
      (emit_list [.heap (upd memory.1 a value, memory.2)]
        (pure (some (), ((upd memory.1 a value, memory.2), (ctx, c)))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.cas (.lit a) (.lit value) (.lit value)) fun _ => .ret ())
        (memory, (ctx, c)) ~
      (emit_list [.heap (upd memory.1 a value, memory.2)]
        (pure (some (), ((upd memory.1 a value, memory.2), (ctx, c)))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.cas (.lit a) (.lit (value + 1)) (.lit value)) fun _ => .ret ())
        (memory, (ctx, c)) ~
      (pure (some (), (memory, (ctx, c))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.read a) fun _ => .bind (.free 0) fun _ => .ret ())
        (memory, (ctx, c)) ~
      (pure (some (), (memory, (ctx, c))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) := by
  intro H
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine sbisim_trans (instr_flow_write a value _ _ (by simp [csl_memory, H])) ?_
    log_step
    rw [instr_flow_ret]; exact sbisim_refl _
  · refine sbisim_trans (instr_flow_cas_value a value value value _ _ H) ?_
    rw [ite_eq_left rfl]
    log_step
    rw [instr_flow_ret]; exact sbisim_refl _
  · refine sbisim_trans (instr_flow_cas_value a (value + 1) value value _ _ H) ?_
    rw [ite_eq_right (by omega), instr_flow_ret]; exact sbisim_refl _
  · refine sbisim_trans (instr_flow_read a value _ _ H) ?_
    refine sbisim_trans (instr_flow_free 0 _ _ memory rfl) ?_
    rw [instr_flow_ret]; exact sbisim_refl _

theorem fault_prefix_preserved (ctx : Ctx) (c : Nat) :
    (instr_flow_erased (.bind (.read 2) fun _ => .ret ()) ((hsingle 1 0, hemp), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.write 2 1) fun _ => .ret ()) ((hsingle 1 0, hemp), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.cas (.lit 2) (.lit 0) (.lit 1)) fun _ => .ret ())
        ((hsingle 1 0, hemp), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.alloc 0) fun _ => .ret ()) ((hsingle 1 0, hemp), (ctx, c)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (∀ base, base ≠ 0 →
      instr_flow_erased (.bind (.free base) fun _ => .ret ()) ((hsingle 1 0, hemp), (ctx, c)) ~
        (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) ∧
    (instr_flow_erased (.bind (.write 1 9) fun _ => .bind (.read 2) fun _ => .ret ())
        ((hsingle 1 0, hemp), (ctx, c)) ~
      (log (CSLObs.heap probe_written) >>= fun _ =>
        (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)))) := by
  have Missing : hsingle 1 0 2 = none := hsingle_neq 1 2 0 (by decide)
  refine ⟨instr_flow_read_missing _ _ _ Missing, instr_flow_write_missing _ _ _ _ Missing,
    instr_flow_cas_missing _ _ _ _ _ Missing, instr_flow_alloc_zero _ _,
    fun base N => instr_flow_free_invalid _ _ _ (by simp [managed_free, csl_memory, N, hemp]),
    ?_⟩
  refine sbisim_trans (instr_flow_write 1 9 _ _ (by simp [csl_memory, hsingle])) ?_
  rw [log_vis, log_vis]; refine sb_vis _ fun _ => ?_
  exact instr_flow_read_missing _ _ _ (by simp [csl_memory, upd, hsingle])

/-! ## The mutation loop as a batch loop -/

theorem mutation_loop_round_nd (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    memory.1 1 ≠ none →
    run_nd mutation_loop (memory, (ctx, c)) ~
      emit_list (mutation_logs memory)
        (run_nd mutation_loop (mutation_next memory, (ctx, c))) := by
  obtain ⟨h, al⟩ := memory
  intro H
  rw [run_nd_focus, mutation_loop, interp_nd_source_until_none, mutation_body,
    interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_write_present 0 _ 0 1 1 _ h al ctx c H) ?_
  simp only [mutation_logs, mutation_next, mutation_store, emit_list_cons, emit_list_nil, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_nd_source_bind]
  refine sbisim_trans
    (interp_nd_source_write_present 0 _ 0 1 2 _ (upd h 1 1) al ctx c (by simp)) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  rw [interp_nd_source_ret]
  dsimp only
  refine sbisim_trans (interp_schedule_nd_guard sh 0 _ 0
    (denote_flow (.untilNone (.bind (.write 1 1) fun _ => .bind (.write 1 2) fun _ =>
      .ret (some ()))) >>= fun _ => pure ⟨⟩) _ (by simp)) ?_
  rw [Vector.set_set, run_nd_focus]
  exact sbisim_refl _

theorem mutation_loop_round_rr (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    memory.1 1 ≠ none →
    run_rr mutation_loop (memory, (ctx, c)) ~
      emit_list ((mutation_logs memory).map .inl)
        (run_rr mutation_loop (mutation_next memory, (ctx, c))) := by
  obtain ⟨h, al⟩ := memory
  intro H
  rw [run_rr_focus, mutation_loop, interp_rr_until_none, mutation_body, interp_rr_bind]
  refine sbisim_trans (interp_rr_write_present 0 _ 0 1 1 _ 0 h al ctx c H) ?_
  simp only [mutation_logs, mutation_next, mutation_store, List.map_cons, List.map_nil,
    emit_list_cons, emit_list_nil, log_vis]
  refine sb_vis _ fun _ => ?_
  rw [interp_rr_bind]
  refine sbisim_trans
    (interp_rr_write_present 0 _ 0 1 2 _ 0 (upd h 1 1) al ctx c (by simp)) ?_
  rw [log_vis]; refine sb_vis _ fun _ => ?_
  rw [interp_rr_ret]
  dsimp only
  refine sbisim_trans (interp_schedule_rr_guard sh 0 _ 0
    (denote_flow (.untilNone (.bind (.write 1 1) fun _ => .bind (.write 1 2) fun _ =>
      .ret (some ()))) >>= fun _ => pure ⟨⟩) _ _ (by simp)) ?_
  rw [Vector.set_set, run_rr_focus]
  exact sbisim_refl _

theorem mutation_next_present (memory : ManagedHeap) : (mutation_next memory).1 1 ≠ none := by
  simp [mutation_next, mutation_store]

theorem mutation_round_logs_length (n : Nat) (memory : ManagedHeap) :
    (mutation_round_logs n memory).length = 2 * n := by
  rw [mutation_round_logs, flat_map_fixed_length _ _ 2 fun _ _ => rfl, List.length_range']

/-- Every iterate of a heap with cell `1` keeps cell `1` (Rocq `Nat.iter_invariant`). -/
private theorem repeat_present (n : Nat) (memory : ManagedHeap) (H : memory.1 1 ≠ none) :
    (Nat.repeat mutation_next n memory).1 1 ≠ none :=
  match n with
  | 0 => H
  | _ + 1 => mutation_next_present _

theorem mutation_loop_batches_nd (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    memory.1 1 ≠ none →
    run_nd mutation_loop (memory, (ctx, c)) ~
      (emit_batches mutation_logs mutation_next memory :
        ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) :=
  emit_batches_bisim mutation_logs mutation_next (fun m => m.1 1 ≠ none)
    (fun m => run_nd mutation_loop (m, (ctx, c))) (fun m _ => mutation_next_present m)
    (fun _ _ => List.cons_ne_nil _ _) (fun m hm => mutation_loop_round_nd m ctx c hm) memory

theorem mutation_loop_batches_rr (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    memory.1 1 ≠ none →
    run_rr mutation_loop (memory, (ctx, c)) ~
      (emit_batches (fun m => (mutation_logs m).map Sum.inl) mutation_next memory :
        ctreeW rr_obs Bn (PUnit × SSig)) :=
  emit_batches_bisim (fun m => (mutation_logs m).map Sum.inl) mutation_next
    (fun m => m.1 1 ≠ none) (fun m => run_rr mutation_loop (m, (ctx, c)))
    (fun m _ => mutation_next_present m) (fun _ _ => List.cons_ne_nil _ _)
    (fun m hm => mutation_loop_round_rr m ctx c hm) memory

theorem mutation_loop_prefix_nd (n : Nat) (ctx : Ctx) (c : Nat) :
    run_nd mutation_loop ((hsingle 1 0, hemp), (ctx, c)) ~
      emit_list (mutation_round_logs n (hsingle 1 0, hemp))
        (run_nd mutation_loop (mutation_after n (hsingle 1 0, hemp), (ctx, c))) ∧
    (mutation_round_logs n (hsingle 1 0, hemp)).length = 2 * n := by
  have H0 : (hsingle 1 0, hemp).1 1 ≠ none := by simp [hsingle]
  refine ⟨sbisim_trans (mutation_loop_batches_nd _ ctx c H0) (sbisim_trans
    (emit_batches_prefix_sbisim _ _ n _) (emit_list_sbisim _ (sbisim_symm
      (mutation_loop_batches_nd _ ctx c (repeat_present n _ H0))))),
    mutation_round_logs_length n _⟩

theorem mutation_loop_prefix_rr (n : Nat) (ctx : Ctx) (c : Nat) :
    run_rr mutation_loop ((hsingle 1 0, hemp), (ctx, c)) ~
      emit_list ((mutation_round_logs n (hsingle 1 0, hemp)).map Sum.inl)
        (run_rr mutation_loop (mutation_after n (hsingle 1 0, hemp), (ctx, c))) ∧
    (mutation_round_logs n (hsingle 1 0, hemp)).length = 2 * n := by
  have H0 : (hsingle 1 0, hemp).1 1 ≠ none := by simp [hsingle]
  refine ⟨?_, mutation_round_logs_length n _⟩
  rw [mutation_round_logs, List.map_flatMap]
  exact sbisim_trans (mutation_loop_batches_rr _ ctx c H0) (sbisim_trans
    (emit_batches_prefix_sbisim _ _ n _) (emit_list_sbisim _ (sbisim_symm
      (mutation_loop_batches_rr _ ctx c (repeat_present n _ H0)))))

/-! ## Recurrent heap observations -/

theorem mutation_batches_agaf {X : Type} (memory : ManagedHeap)
    (w : World (writerE (CSLObs (Nat × Nat)))) (value : Nat) :
    (value = 1 ∨ value = 2) → memory.1 1 ≠ none → NotDone w →
    entails (AG (AF (visWₜ (csl_heap fun m => m.1 1 = some value))))
      (emit_batches mutation_logs mutation_next memory :
        ctreeW (CSLObs (Nat × Nat)) Bn X) w := fun V H Hw =>
  emit_batches_agaf mutation_logs mutation_next (fun m => m.1 1 ≠ none) (fun _ => 0) _
    (fun m _ => mutation_next_present m) (fun _ _ => List.cons_ne_nil _ _)
    (fun m _ => .inl (by
      rcases V with rfl | rfl
      · exact ⟨.heap (mutation_store m 1), .head _, by simp [csl_heap, mutation_store]⟩
      · exact ⟨.heap (mutation_next m), .tail _ (.head _),
          by simp [csl_heap, mutation_next, mutation_store]⟩))
    memory w H Hw

/-- Proved through the batch loop (`mutation_loop_batches_nd` + `mutation_batches_agaf`) instead
of Rocq's source loop rules. -/
theorem mutation_loop_agaf_nd (value : Nat) (ctx : Ctx) (c : Nat) :
    (value = 1 ∨ value = 2) →
    entails (AG (AF (visWₜ (csl_heap fun m => m.1 1 = some value))))
      (run_nd mutation_loop ((hsingle 1 0, hemp), (ctx, c))) .pure := fun V =>
  have H0 : (hsingle 1 0, hemp).1 1 ≠ none := by simp [hsingle]
  (proper_entails_meq _ (mutation_loop_batches_nd _ ctx c H0)).2
    (mutation_batches_agaf _ _ value V H0 .pure)

/-- Proved through the batch loop (`mutation_loop_batches_rr` + `emit_batches_agaf`). -/
theorem mutation_loop_agaf_rr (value : Nat) (ctx : Ctx) (c : Nat) :
    (value = 1 ∨ value = 2) →
    entails (AG (AF (visWₜ (fair_obs (csl_heap fun m => m.1 1 = some value)))))
      (run_rr mutation_loop ((hsingle 1 0, hemp), (ctx, c))) .pure := fun V =>
  have H0 : (hsingle 1 0, hemp).1 1 ≠ none := by simp [hsingle]
  (proper_entails_meq _ (mutation_loop_batches_rr _ ctx c H0)).2
    (emit_batches_agaf (fun m => (mutation_logs m).map Sum.inl) mutation_next
      (fun m => m.1 1 ≠ none) (fun _ => 0) _ (fun m _ => mutation_next_present m)
      (fun _ _ => List.cons_ne_nil _ _)
      (fun m _ => .inl (by
        rcases V with rfl | rfl
        · exact ⟨.inl (.heap (mutation_store m 1)), .head _,
            by simp [fair_obs, csl_heap, mutation_store]⟩
        · exact ⟨.inl (.heap (mutation_next m)), .tail _ (.head _),
            by simp [fair_obs, csl_heap, mutation_next, mutation_store]⟩))
      _ .pure H0 .pure)

/-! ## The silent spin loop -/

theorem mutation_spin_round_rr (cursor : Nat) (s : SSig) :
    spin_rr_at cursor s ~
      .vis (E := writerE rr_obs) (.inr 0) fun _ => spin_rr_at (cursor + 1) s := by
  show interp_schedule_rr sh 1 ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
    (denote_flow mutation_spin >>= fun _ => pure ⟨⟩)) (some 0) cursor s ~ _
  rw [mutation_spin, interp_rr_until_none, interp_rr_bind]
  refine sbisim_trans (interp_rr_yield 0 _ 0 _ cursor s) ?_
  dsimp only
  refine sbisim_trans (interp_schedule_rr_select sh 0 _ cursor s) ?_
  rw [rr_pick_0]
  refine sb_vis _ fun _ => ?_
  rw [interp_rr_ret]
  dsimp only
  refine sbisim_trans (interp_schedule_rr_guard sh 0 _ 0
    (denote_flow (.untilNone (.bind .yield fun _ => .ret (some () : Option Unit))) >>=
      fun _ => pure ⟨⟩) _ _ (by simp)) ?_
  rw [Vector.set_set]
  exact sbisim_refl _

theorem mutation_spin_round_nd (s : SSig) :
    run_nd mutation_spin s ~ .step (run_nd mutation_spin s) := by
  conv => lhs; rw [run_nd_focus, mutation_spin, interp_nd_source_until_none,
    interp_nd_source_bind]
  refine sbisim_trans (interp_nd_source_yield 0 _ 0 _ s) ?_
  dsimp only
  refine sbisim_trans (interp_schedule_nd_select sh 0 _ s) ?_
  simp only [CTree.brSn, CTree.brS', CTree.br']
  refine sb_br_l _ ((ITree.Subeffect.map (E₁ := Bn) (E₂ := Bn) ⟨1⟩).2 ⟨0⟩) _ _ fun x => ?_
  refine sb_step ?_
  generalize (ITree.Subeffect.map (E₁ := Bn) (E₂ := Bn) ⟨1⟩).2 x = y
  obtain ⟨y⟩ := y
  obtain rfl : y = 0 := fin1_eq y
  rw [interp_nd_source_ret]
  dsimp only
  refine sbisim_trans (interp_schedule_nd_guard sh 0 _ 0
    (denote_flow (.untilNone (.bind .yield fun _ => .ret (some () : Option Unit))) >>=
      fun _ => pure ⟨⟩) _ (by simp)) ?_
  rw [Vector.set_set, run_nd_focus]
  exact sbisim_refl _

section SilentSteps
variable {J X : Type} (root : J → ctreeW (CSLObs (Nat × Nat)) Bn X) (next : J → J)
  (Hstep : ∀ i, root i ~ .step (root (next i)))
include Hstep

theorem step_only_ag (i : J) (w : World (writerE (CSLObs (Nat × Nat)))) :
    NotDone w → entails (AG ⊤) (root i) w :=
  ag_step_family root next Hstep i w

theorem step_only_no_heap (i : J) :
    ¬ entails (EF (visWₜ (csl_heap fun _ => True))) (root i) .pure :=
  step_family_no_ef_visible root next Hstep _ i

end SilentSteps

theorem mutation_spin_no_heap_nd (ctx : Ctx) (c : Nat) :
    entails (AG ⊤) (run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c))) .pure ∧
    ¬ entails (EF (visWₜ (csl_heap fun _ => True)))
      (run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c))) .pure :=
  ⟨step_only_ag (fun _ : Unit => run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c)))
      id (fun _ => mutation_spin_round_nd _) () .pure .pure,
    step_only_no_heap (fun _ : Unit => run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c)))
      id (fun _ => mutation_spin_round_nd _) ()⟩

theorem mutation_spin_no_heap_rr (ctx : Ctx) (c : Nat) :
    entails (AG ⊤) (run_rr mutation_spin ((hsingle 1 0, hemp), (ctx, c))) .pure ∧
    ¬ entails (EF (visWₜ (fair_obs (csl_heap fun _ => True))))
      (run_rr mutation_spin ((hsingle 1 0, hemp), (ctx, c))) .pure := by
  rw [run_rr_unfold]
  exact
  ⟨ag_log_family (fun cursor => spin_rr_at cursor ((hsingle 1 0, hemp), (ctx, c))) (· + 1)
      (fun _ => .inr 0) (fun cursor => mutation_spin_round_rr cursor _) 0 .pure .pure,
    log_family_no_ef_visible (fun cursor => spin_rr_at cursor ((hsingle 1 0, hemp), (ctx, c)))
      (· + 1) (fun _ => .inr 0) (fun cursor => mutation_spin_round_rr cursor _)
      (fair_obs (csl_heap fun _ => True)) (fun _ h => h) 0⟩

theorem empty_log_pool_selection (ctx : Ctx) (c : Nat) :
    run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c)) ~
      .step (run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c))) ∧
    turn_labels ([] : List (CSLObs (Nat × Nat))) = [.tau] ∧
    entails (AG ⊤) (run_nd mutation_spin ((hsingle 1 0, hemp), (ctx, c))) .pure :=
  ⟨mutation_spin_round_nd _, rfl, (mutation_spin_no_heap_nd ctx c).1⟩

theorem mutation_observation_replaced (ctx : Ctx) (c : Nat) :
    (∀ t : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig),
      ¬ entails (visWₜ (csl_heap fun _ => True)) t .pure) ∧
    (∀ t : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig),
      entails (visWₜ (csl_heap fun m => m.1 1 = some 9)) t
        (.obs (E := writerE (CSLObs (Nat × Nat))) (.heap probe_written) ⟨⟩)) ∧
    (∀ t : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig),
      ¬ entails (visWₜ (csl_heap fun _ => True)) t
        (.obs (E := writerE (CSLObs (Nat × Nat))) (.emit (stamp (7, 9) c)) ⟨⟩)) ∧
    instr_flow_erased (.bind (.write 1 9) fun _ => .bind (.emit 7 9) fun _ => .ret ())
        ((hsingle 1 0, hemp), (ctx, c)) ~
      (emit_list [.heap probe_written, .emit (stamp (7, 9) c)]
        (pure (some (), (probe_written, (ctx, c + 1)))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) := by
  refine ⟨fun _ H => (nomatch H.1), fun _ => ⟨.obs _ _ (by simp [csl_heap, probe_written]),
    .obs _ _⟩, fun _ H => ?_, ?_⟩
  · cases H.1 with | obs _ _ h => exact h
  · refine sbisim_trans (instr_flow_write 1 9 _ _ (by simp [csl_memory, hsingle])) ?_
    log_step
    refine sbisim_trans (instr_flow_emit _ _ _ _) ?_
    log_step
    rw [instr_flow_ret]
    exact sbisim_refl _

end Examples.CSL.Frame.HeapObservations

-- Not ported: nothing; every Rocq declaration of lines 1-686 is above. Rocq's stdlib
-- `Nat.iter_invariant` use is the private `repeat_present`.
