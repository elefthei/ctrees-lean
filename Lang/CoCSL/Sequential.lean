/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Frame
public import Logic.Yield.Sequential

/-!
# Cooperative prefixes of CoCSL source programs

Yield/fork-free code executes its standalone checked prefix and rejoins the actual pool with the
resulting state. Round-robin and fair prefixes preserve scheduler state and relabel program
observations under `.inl`. Chronological write plans retain repeated snapshots and stop at the
first missing address (← `Lang/CoCSL/Sequential.v`).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx
open ITree (Effect)

/-- No yield, fork, or variable read (`.var` itself yields). -/
def yield_fork_free {A : Type} (p : CProg A) : Prop := prog_ok (user_only (E := sE)) p

/-- A yield/fork-free program denotes a sequential raw thread. -/
theorem denote_flow_sequential {A : Type} (p : CProg A) :
    yield_fork_free p → Sequential (denote_flow p) := fun H =>
  ⟨denote_flow_branchfree p, denote_flow_framable _ p H⟩

/-- Chronological checked writes. Every occurrence performs a write, including repeated keys; a
missing cell stops the source program at that occurrence. -/
def write_list : List (Nat × Nat) → CProg Unit
  | [] => .ret ()
  | (a, v) :: rest => .bind (.write a v) fun _ => write_list rest

/-- Heap observations retain the allocation table and do not stamp an event or advance the
source counter. The list includes every intermediate memory. -/
def write_snapshots {A : Type} : List (Nat × Nat) → ManagedHeap → List (CSLObs A)
  | [], _ => []
  | (a, v) :: rest, memory =>
    let next := (upd memory.1 a v, memory.2)
    .heap next :: write_snapshots rest next

theorem write_list_yield_fork_free (ws : List (Nat × Nat)) : yield_fork_free (write_list ws) := by
  induction ws with
  | nil => exact trivial
  | cons p rest ih => obtain ⟨a, v⟩ := p; exact ⟨trivial, fun _ => ih⟩

theorem write_list_alloc_free (ws : List (Nat × Nat)) : alloc_free (write_list ws) := by
  induction ws with
  | nil => exact trivial
  | cons p rest ih => obtain ⟨a, v⟩ := p; exact ⟨trivial, fun _ => ih⟩

theorem write_snapshots_length {A : Type} (ws : List (Nat × Nat)) (memory : ManagedHeap) :
    (write_snapshots (A := A) ws memory).length = ws.length := by
  induction ws generalizing memory with
  | nil => rfl
  | cons p rest ih => obtain ⟨a, v⟩ := p; simp [write_snapshots, ih]

/-- Write snapshots are heap observations only. -/
theorem write_snapshots_heaps {A : Type} (ws : List (Nat × Nat)) (memory : ManagedHeap) :
    ∃ heaps : List ManagedHeap, write_snapshots (A := A) ws memory = heaps.map CSLObs.heap := by
  induction ws generalizing memory with
  | nil => exact ⟨[], rfl⟩
  | cons p rest ih =>
    obtain ⟨heaps, e⟩ := ih (upd memory.1 p.1 p.2, memory.2)
    exact ⟨(upd memory.1 p.1 p.2, memory.2) :: heaps, by simp [write_snapshots, e]⟩

theorem write_snapshots_app {A : Type} (xs ys : List (Nat × Nat)) (memory : ManagedHeap) :
    write_snapshots (A := A) (xs ++ ys) memory =
      write_snapshots xs memory ++ write_snapshots ys (apply_writes xs memory.1, memory.2) := by
  induction xs generalizing memory with
  | nil => rfl
  | cons p rest ih => obtain ⟨a, v⟩ := p; simp [write_snapshots, ih]

theorem write_snapshots_last_heap {A : Type} (ws : List (Nat × Nat)) (memory : ManagedHeap) :
    (write_snapshots (A := A) ws memory).getLastD (.heap memory) =
      .heap (apply_writes ws memory.1, memory.2) := by
  induction ws generalizing memory with
  | nil => rfl
  | cons p rest ih => obtain ⟨a, v⟩ := p; rw [write_snapshots, List.getLastD_cons, ih]; rfl

theorem write_snapshots_after {A : Type} (ws : List (Nat × Nat)) (memory : ManagedHeap) :
    after_logs (write_snapshots (A := A) ws memory)
        (.obs (E := writerE (CSLObs A)) (.heap memory) ⟨⟩) =
      .obs (E := writerE (CSLObs A)) (.heap (apply_writes ws memory.1, memory.2)) ⟨⟩ := by
  induction ws generalizing memory with
  | nil => rfl
  | cons p rest ih => obtain ⟨a, v⟩ := p; exact ih _

/-- Native source return has no observation or state effect. -/
theorem instr_flow_ret {A : Type} (value : A) (s : SSig) :
    instr_flow_erased (.ret value) s =
      (pure (some value, s) : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  simp only [instr_flow_erased, denote_flow]
  exact interp_state_thread_ret sh _ s

/-! ## One-step equations of the standalone erased run -/

/-- A user-event head runs its handler, then the standalone erased continuation. -/
theorem instr_flow_head {A : Type} (p : CProg A) (e : sE.I)
    (k : sE.O e → CTree CEff Bn (Option A)) (s : SSig) :
    denote_flow p = .vis (.inr (.inr e)) k →
    instr_flow_erased p s ~
      (sh e s >>= fun r => interp_state sh (interp_thread (k r.1)) r.2) := by
  intro Hp
  simp only [instr_flow_erased, Hp]
  exact interp_state_thread_user sh e k s

/-- Read an owned cell and continue with its value in the standalone erased run. -/
theorem instr_flow_read {A : Type} (a v : Nat) (k : Nat → CProg A) (s : SSig) :
    (csl_memory s).1 a = some v →
    instr_flow_erased (.bind (.read a) k) s ~ instr_flow_erased (k v) s := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.read a)) (fun v => denote_flow (k v)) s
    (by simp [denote_flow, heap_read, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_rd_some _ a h al aux v Hv, pure_bind']
  exact sbisim_refl _

/-- Write an owned cell and continue in the updated standalone state. -/
theorem instr_flow_write {A : Type} (a v : Nat) (k : Unit → CProg A) (s : SSig) :
    (csl_memory s).1 a ≠ none →
    instr_flow_erased (.bind (.write a v) k) s ~
      (log (CSLObs.heap (upd (csl_memory s).1 a v, (csl_memory s).2) : CSLObs (Nat × Nat))
        >>= fun _ =>
        instr_flow_erased (k ()) ((upd (csl_memory s).1 a v, (csl_memory s).2), s.2)) := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.write a v)) (fun _ => denote_flow (k ())) s
    (by simp [denote_flow, heap_write, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [csl_memory] at Hv ⊢
  obtain ⟨old, Hh⟩ := Option.ne_none_iff_exists'.1 Hv
  simp only [sh, h_sum]
  rw [heap_handlerW_wr_some _ a h al aux v old Hh]
  simp only [bind_assoc, pure_bind']
  exact sbisim_refl _

/-- A standalone write logs its post-memory, then returns `some ()`. -/
theorem instr_flow_write_single (a v : Nat) (s : SSig) :
    (csl_memory s).1 a ≠ none →
    instr_flow_erased (.write a v) s ~
      (log (CSLObs.heap (upd (csl_memory s).1 a v, (csl_memory s).2) : CSLObs (Nat × Nat))
        >>= fun _ => (pure (some (), ((upd (csl_memory s).1 a v, (csl_memory s).2), s.2)) :
          ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.write a v)) (fun _ => pure (some ())) s
    (by simp [denote_flow, heap_write, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [csl_memory] at Hv ⊢
  obtain ⟨old, Hh⟩ := Option.ne_none_iff_exists'.1 Hv
  simp only [sh, h_sum]
  rw [heap_handlerW_wr_some _ a h al aux v old Hh]
  simp only [bind_assoc, pure_bind', interp_state_thread_ret]
  exact sbisim_refl _

/-! Each primitive exposes its checked outcome before the source continuation. -/

theorem instr_flow_read_missing {A : Type} (a : Nat) (k : Nat → CProg A) (s : SSig) :
    (csl_memory s).1 a = none →
    instr_flow_erased (.bind (.read a) k) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.read a)) (fun v => denote_flow (k v)) s
    (by simp [denote_flow, heap_read, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_rd_none _ a h al aux Hv, stuck_bind]
  exact sbisim_refl _

theorem instr_flow_write_missing {A : Type} (a v : Nat) (k : Unit → CProg A) (s : SSig) :
    (csl_memory s).1 a = none →
    instr_flow_erased (.bind (.write a v) k) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.write a v)) (fun _ => denote_flow (k ())) s
    (by simp [denote_flow, heap_write, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_wr_none _ a h al aux v Hv, stuck_bind]
  exact sbisim_refl _

/-- A checked finite prefix keeps the allocation table, context and event counter unchanged.
Allocated keys may repeat and may include address zero. -/
theorem instr_flow_write_list (ws : List (Nat × Nat)) (h allocs : Heap) (aux : Ctx × Nat) :
    (∀ a v, (a, v) ∈ ws → h a ≠ none) →
    instr_flow_erased (write_list ws) ((h, allocs), aux) ~
      emit_list (write_snapshots ws (h, allocs))
        (pure (some (), ((apply_writes ws h, allocs), aux)) :
          ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) := by
  induction ws generalizing h with
  | nil => intro _; rw [write_list, instr_flow_ret]; exact sbisim_refl _
  | cons p rest ih =>
    obtain ⟨a, v⟩ := p
    intro Hall
    refine sbisim_trans (instr_flow_write a v (fun _ => write_list rest) _
      (Hall a v List.mem_cons_self)) ?_
    simp only [csl_memory, write_snapshots, emit_list_cons, apply_writes_cons, log, vis_bind,
      pure_bind']
    exact sb_vis _ fun _ => ih _ fun x value Hin =>
      upd_mono h a v x (Hall x value (List.mem_cons_of_mem _ Hin))

/-- Stop at the first missing address, retaining exactly the preceding snapshots and never
evaluating the remaining writes. -/
theorem instr_flow_write_list_fault (ws pre : List (Nat × Nat)) (a v : Nat)
    (post : List (Nat × Nat)) (h allocs : Heap) (aux : Ctx × Nat) :
    ws = pre ++ (a, v) :: post →
    (∀ x value, (x, value) ∈ pre → h x ≠ none) →
    apply_writes pre h a = none →
    instr_flow_erased (write_list ws) ((h, allocs), aux) ~
      emit_list (write_snapshots pre (h, allocs))
        (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) := by
  rintro rfl
  induction pre generalizing h with
  | nil => intro _ Hmissing; exact instr_flow_write_missing a v _ _ Hmissing
  | cons p pre ih =>
    obtain ⟨x, value⟩ := p
    intro Hall Hmissing
    refine sbisim_trans (instr_flow_write x value (fun _ => write_list (pre ++ (a, v) :: post)) _
      (Hall x value List.mem_cons_self)) ?_
    simp only [csl_memory, write_snapshots, emit_list_cons, log, vis_bind, pure_bind']
    exact sb_vis _ fun _ => ih _ (fun y val Hin =>
      upd_mono h x value y (Hall y val (List.mem_cons_of_mem _ Hin))) Hmissing

theorem instr_flow_cas_value {A : Type} (a expected desired current : Nat) (k : Bool → CProg A)
    (s : SSig) :
    (csl_memory s).1 a = some current →
    instr_flow_erased (.bind (.cas (.lit a) (.lit expected) (.lit desired)) k) s ~
      if current = expected then
        log (CSLObs.heap (upd (csl_memory s).1 a desired, (csl_memory s).2) : CSLObs (Nat × Nat))
          >>= fun _ => instr_flow_erased (k true)
            ((upd (csl_memory s).1 a desired, (csl_memory s).2), s.2)
      else instr_flow_erased (k false) s := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.cas a expected desired))
    (fun b => denote_flow (k b)) s
    (by simp [denote_flow, denote_exp, heap_cas, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [csl_memory] at Hv ⊢
  simp only [sh, h_sum]
  by_cases HC : current = expected
  · subst HC
    rw [heap_handlerW_cas_success _ a current desired h al aux Hv]
    simp only [↓reduceIte, bind_assoc, pure_bind']
    exact sbisim_refl _
  · rw [heap_handlerW_cas_failure _ a expected desired current h al aux Hv HC]
    simp only [HC, ↓reduceIte, pure_bind']
    exact sbisim_refl _

theorem instr_flow_cas_missing {A : Type} (a expected desired : Nat) (k : Bool → CProg A)
    (s : SSig) :
    (csl_memory s).1 a = none →
    instr_flow_erased (.bind (.cas (.lit a) (.lit expected) (.lit desired)) k) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  intro Hv
  refine sbisim_trans (instr_flow_head _ (.inl (.cas a expected desired))
    (fun b => denote_flow (k b)) s
    (by simp [denote_flow, denote_exp, heap_cas, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_cas_missing _ a expected desired h al aux Hv, stuck_bind]
  exact sbisim_refl _

theorem instr_flow_free {A : Type} (base : Nat) (k : Unit → CProg A) (s : SSig)
    (memory' : ManagedHeap) :
    managed_free (csl_memory s) base = some memory' →
    instr_flow_erased (.bind (.free base) k) s ~
      match base with
      | 0 => instr_flow_erased (k ()) (memory', s.2)
      | _ + 1 => log (CSLObs.heap memory' : CSLObs (Nat × Nat)) >>= fun _ =>
        instr_flow_erased (k ()) (memory', s.2) := by
  intro HF
  refine sbisim_trans (instr_flow_head _ (.inl (.free base)) (fun _ => denote_flow (k ())) s
    (by simp [denote_flow, heap_free, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨memory, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_free _ base memory memory' aux HF]
  cases base with
  | zero => simp only [pure_bind']; exact sbisim_refl _
  | succ _ => simp only [bind_assoc, pure_bind']; exact sbisim_refl _

theorem instr_flow_free_invalid {A : Type} (base : Nat) (k : Unit → CProg A) (s : SSig) :
    managed_free (csl_memory s) base = none →
    instr_flow_erased (.bind (.free base) k) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  intro HF
  refine sbisim_trans (instr_flow_head _ (.inl (.free base)) (fun _ => denote_flow (k ())) s
    (by simp [denote_flow, heap_free, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨memory, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_free_invalid _ base memory aux HF, stuck_bind]
  exact sbisim_refl _

theorem instr_flow_alloc_first {A : Type} (size base : Nat) (k : Nat → CProg A) (s : SSig) :
    0 < size → 0 < base → block_free (csl_memory s).1 base size →
    (∀ j, 0 < j → j < base → ¬ block_free (csl_memory s).1 j size) →
    instr_flow_erased (.bind (.alloc size) k) s ~
      (log (CSLObs.heap (managed_alloc (csl_memory s) base size) : CSLObs (Nat × Nat)) >>=
        fun _ => instr_flow_erased (k base) (managed_alloc (csl_memory s) base size, s.2)) := by
  intro Pos Base Free First
  refine sbisim_trans (instr_flow_head _ (.inl (.alloc size)) (fun a => denote_flow (k a)) s
    (by simp [denote_flow, heap_alloc, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  refine sbisim_trans (sbisim_clo_bind_eq (heap_handlerW_alloc_first _ h al size base aux
    Pos Base Free First) fun _ => sbisim_refl _) ?_
  simp only [bind_assoc, pure_bind']
  exact sbisim_refl _

theorem instr_flow_alloc_zero {A : Type} (k : Nat → CProg A) (s : SSig) :
    instr_flow_erased (.bind (.alloc 0) k) s ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  refine sbisim_trans (instr_flow_head _ (.inl (.alloc 0)) (fun a => denote_flow (k a)) s
    (by simp [denote_flow, heap_alloc, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_alloc_zero _ h al aux, stuck_bind]
  exact sbisim_refl _

theorem instr_flow_alloc_no_space {A : Type} (size : Nat) (k : Nat → CProg A) (s : SSig) :
    0 < size → (∀ j, 0 < j → ¬ block_free (csl_memory s).1 j size) →
    instr_flow_erased (.bind (.alloc size) k) s ~
      (CTree.spin : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) := by
  intro Pos Full
  refine sbisim_trans (instr_flow_head _ (.inl (.alloc size)) (fun a => denote_flow (k a)) s
    (by simp [denote_flow, heap_alloc, CTree.trigger', CTree.vis']; rfl)) ?_
  obtain ⟨⟨h, al⟩, aux⟩ := s
  simp only [sh, h_sum]
  rw [heap_handlerW_alloc_no_space _ h al size aux Pos Full, bind_spin]
  exact sbisim_refl _

theorem instr_flow_emit {A : Type} (tag value : Nat) (k : Unit → CProg A) (s : SSig) :
    instr_flow_erased (.bind (.emit tag value) k) s ~
      (log (CSLObs.emit (stamp (tag, value) (csl_counter s))) >>= fun _ =>
        instr_flow_erased (k ()) (csl_memory s, (csl_context s, csl_counter s + 1))) := by
  refine sbisim_trans (instr_flow_head _ (.inr (.inr (tag, value))) (fun _ => denote_flow (k ())) s
    (by simp [denote_flow, CTree.trigger])) ?_
  obtain ⟨memory, ctx, c⟩ := s
  simp only [sh, h_sum, csl_emit_handler_log, bind_assoc, pure_bind']
  exact sbisim_refl _

/-! ## Pool-level prefix equations -/

/-- Join principle: a focused yield/fork-free segment runs standalone, then its round-robin pool
continues. -/
theorem run_rr_prefix {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (K : Option A → Thread sE Bn) (m : Nat) (σ : SSig) :
    yield_fork_free p →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow p >>= K)) (some i) m σ ~
      (translate relabel_log (instr_flow_erased p σ) >>= fun r =>
        interp_schedule_rr sh (n + 1) (ts.set i (K r.1)) (some i) m r.2) := fun Hp =>
  interp_schedule_rr_prefix_bind sh n ts i _ K m σ (denote_flow_sequential p Hp)

/-- The relabelled standalone run is the standalone run under the policy handler, with its events
embedded on the left. -/
theorem instr_flow_sched_interp {A : Type} (p : CProg A) (σ : SSig) :
    translate relabel_log (instr_flow_erased p σ) =
      interp_state (policy_handler sh)
        (translate
          (fun e => (⟨.inl e, id⟩ : (f : (sE ⊕ₑ schedE).I) × ((sE ⊕ₑ schedE).O f → sE.O e)))
          (interp_thread (denote_flow p))) σ :=
  (interp_state_policy_translate sh _ σ).symm

/-- Join principle: a focused yield/fork-free segment runs standalone, then its nondeterministic
pool continues. -/
theorem run_nd_prefix {A : Type} (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (p : CProg A) (K : Option A → Thread sE Bn) (σ : SSig) :
    yield_fork_free p →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow p >>= K)) (some i) σ ~
      (instr_flow_erased p σ >>= fun r =>
        interp_schedule_nd sh (n + 1) (ts.set i (K r.1)) (some i) r.2) := fun Hp =>
  interp_schedule_nd_prefix_bind sh n ts i _ K σ (denote_flow_sequential p Hp)

/-- The fair policy is untouched until the focused source prefix completes. -/
theorem run_fair_prefix {A : Type} (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (p : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (sigma : SSig) :
    yield_fork_free p →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow p >>= K)) (some i) st sigma ~
      (translate relabel_log (instr_flow_erased p sigma) >>= fun r =>
        interp_schedule_fair sch sh (n + 1) (ts.set i (K r.1)) (some i) st r.2) := fun Hp =>
  interp_schedule_fair_prefix_bind sch sh n ts i _ K st sigma (denote_flow_sequential p Hp)

/-- Any standalone finite sequential return prefix lifts to the instrumented scheduler, retaining
its precise state and source return value. -/
theorem interp_fair_sequential {A : Type} (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (p : CProg A) (K : Option A → Thread sE Bn) (st : sch.sched_state)
    (sigma : SSig) (logs : List (CSLObs (Nat × Nat))) (sigma' : SSig) (result : Option A) :
    yield_fork_free p →
    instr_flow_erased p sigma ~
      emit_list logs (pure (result, sigma') : ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig)) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow p >>= K)) (some i) st sigma ~
      emit_list (logs.map .inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K result)) (some i) st sigma') := by
  intro Hp Hprefix
  refine sbisim_trans (run_fair_prefix sch n ts i p K st sigma Hp) ?_
  have Hlabels := translate_sbisim relabel_log Hprefix
  rw [translate_emit_list, translate_ret] at Hlabels
  refine sbisim_trans (sbisim_clo_bind_eq Hlabels fun _ => sbisim_refl _) ?_
  rw [emit_list_ret_bind]
  exact sbisim_refl _

theorem interp_nd_write_list (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ws : List (Nat × Nat)) (K : Option Unit → Thread sE Bn) (h allocs : Heap)
    (aux : Ctx × Nat) :
    (∀ a v, (a, v) ∈ ws → h a ≠ none) →
    interp_schedule_nd sh (n + 1) (ts.set i (denote_flow (write_list ws) >>= K)) (some i)
        ((h, allocs), aux) ~
      emit_list (write_snapshots ws (h, allocs))
        (interp_schedule_nd sh (n + 1) (ts.set i (K (some ()))) (some i)
          ((apply_writes ws h, allocs), aux)) := by
  intro Hall
  refine sbisim_trans (run_nd_prefix n ts i _ K _ (write_list_yield_fork_free ws)) ?_
  refine sbisim_trans (sbisim_clo_bind_eq (instr_flow_write_list ws h allocs aux Hall)
    fun _ => sbisim_refl _) ?_
  rw [emit_list_ret_bind]
  exact sbisim_refl _

theorem interp_rr_write_list (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (ws : List (Nat × Nat)) (K : Option Unit → Thread sE Bn) (cursor : Nat) (h allocs : Heap)
    (aux : Ctx × Nat) :
    (∀ a v, (a, v) ∈ ws → h a ≠ none) →
    interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (write_list ws) >>= K)) (some i)
        cursor ((h, allocs), aux) ~
      emit_list ((write_snapshots ws (h, allocs)).map .inl)
        (interp_schedule_rr sh (n + 1) (ts.set i (K (some ()))) (some i) cursor
          ((apply_writes ws h, allocs), aux)) := fun Hall =>
  interp_fair_sequential rr_scheduler n ts i _ K cursor _ _ _ _
    (write_list_yield_fork_free ws) (instr_flow_write_list ws h allocs aux Hall)

theorem interp_fair_write_list (sch : Scheduler) (n : Nat) (ts : Pool sE Bn (n + 1))
    (i : Fin (n + 1)) (ws : List (Nat × Nat)) (K : Option Unit → Thread sE Bn)
    (st : sch.sched_state) (h allocs : Heap) (aux : Ctx × Nat) :
    (∀ a v, (a, v) ∈ ws → h a ≠ none) →
    interp_schedule_fair sch sh (n + 1) (ts.set i (denote_flow (write_list ws) >>= K)) (some i)
        st ((h, allocs), aux) ~
      emit_list ((write_snapshots ws (h, allocs)).map .inl)
        (interp_schedule_fair sch sh (n + 1) (ts.set i (K (some ()))) (some i) st
          ((apply_writes ws h, allocs), aux)) := fun Hall =>
  interp_fair_sequential sch n ts i _ K st _ _ _ _
    (write_list_yield_fork_free ws) (instr_flow_write_list ws h allocs aux Hall)

/-- A nondeterministic fork starts the child and continues with the parent focused. -/
theorem run_nd_fork_bind (p : CProg Unit) (next : Unit → CProg Unit) (s : SSig) :
    run_nd (.bind (.fork p) next) s ~
      interp_schedule_nd sh 2 #v[denote p, denote (next ())] (some 1) s := by
  rw [run_nd_unfold]
  refine sbisim_trans (interp_schedule_nd_fork sh 0 _ 0
    (fun child : Bool => if child then denote p else denote (next ())) s
    (by show (denote (.bind (.fork p) next)).unfold = _; rw [denote_fork_bind]; simp)) ?_
  exact sbisim_refl _

-- Not ported: the `flow_head` Ltac (each head equation is proved by `simp` on the denotation).

end CoCSL
