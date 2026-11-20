/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Queue.Sequential

/-!
# Trace: the state trajectory of the rotating queue

Shared between the two proof families; nothing here is a separation-logic notion. `qstepN` is the
heap after `n` rotations, and `run_stepN` exposes the corresponding `5 * n` observations, including
intermediate post-write snapshots (← `examples/CSL/Queue/Trace.v`).
-/

@[expose] public section
namespace Examples.CSL.Queue.Trace
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL
open Examples.CSL.Queue.Representation Examples.CSL.Queue.Operations
open Examples.CSL.Queue.Sequential

/-- One completed rotation exposes its payload and four post-write heaps; the administrative
iteration guard is discharged by `sb_guard`. -/
theorem run_step (hdr a : Nat) (ns : List Nat) (v : Nat) (vs : List Nat) (h allocs : Heap)
    (ctx : Ctx) (c : Nat) :
    qrep hdr (a :: ns) (v :: vs) h →
    run hdr ((h, allocs), (ctx, c)) ~
      emit_list (queue_turn_logs (.emit (stamp v c)) hdr a (ns.headD 0) ((a :: ns).getLastD 0)
        (h, allocs))
        (run hdr ((rot_heap hdr a (ns.headD 0) (zof hdr ns) h, allocs), (ctx, c + 1))) := by
  intro hq
  unfold run rotate
  rw [interp_state_unfold_iter]
  refine sbisim_trans (sbisim_clo_bind_eq (rot_body_spec hdr a ns v vs h allocs ctx c hq)
    fun _ => sbisim_refl _) ?_
  rw [emit_list_ret_bind]
  exact emit_list_sbisim _ (sb_guard _)

/-- The heap after one rotation. -/
def qstep (hdr : Nat) (ns : List Nat) (h : Heap) : Heap :=
  match ns with
  | [] => h
  | a :: ns' => rot_heap hdr a (ns'.headD 0) (zof hdr ns') h

/-- The heap after `n` rotations. -/
def qstepN (hdr n : Nat) (ns : List Nat) (h : Heap) : Heap :=
  (Nat.repeat (fun (p : List Nat × Heap) => (rotl p.1, qstep hdr p.1 p.2)) n (ns, h)).2

/-- The observation prefix of `n` rotations as a flat sequence of chronological batches; the
continuation `k` follows the final snapshot without an administrative bind. -/
def runN (hdr n : Nat) (ns vs : List Nat) (memory : ManagedHeap) (c : Nat)
    (k : ctreeW (CSLObs Nat) Bn (PUnit × SSig)) : ctreeW (CSLObs Nat) Bn (PUnit × SSig) :=
  emit_list
    ((List.range' 0 n).flatMap fun j =>
      let s := Nat.repeat
        (fun (s : List Nat × List Nat × ManagedHeap × Nat) =>
          (rotl s.1, rotl s.2.1, (qstep hdr s.1 s.2.2.1.1, s.2.2.1.2), s.2.2.2 + 1))
        j (ns, vs, memory, c)
      queue_turn_logs (.emit (stamp (s.2.1.headD 0) s.2.2.2)) hdr (s.1.headD 0)
        (s.1.tail.headD 0) (s.1.getLastD 0) s.2.2.1)
    k

private theorem qstep_iter (hdr n : Nat) (ns : List Nat) (h : Heap) :
    Nat.repeat (fun (p : List Nat × Heap) => (rotl p.1, qstep hdr p.1 p.2)) n (ns, h) =
      (rotlN n ns, qstepN hdr n ns h) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, qstepN, rotlN] at ih ⊢; rw [ih]

/-- Unfolding `qstepN` by one rotation (Lean-only helper). -/
theorem qstepN_succ (hdr n : Nat) (ns : List Nat) (h : Heap) :
    qstepN hdr (n + 1) ns h = qstep hdr (rotlN n ns) (qstepN hdr n ns h) := by
  show (Nat.repeat _ (n + 1) (ns, h)).2 = _
  simp only [Nat.repeat]; rw [qstep_iter]

private theorem runN_iter (hdr j : Nat) (ns vs : List Nat) (memory : ManagedHeap) (c : Nat) :
    Nat.repeat
        (fun (s : List Nat × List Nat × ManagedHeap × Nat) =>
          (rotl s.1, rotl s.2.1, (qstep hdr s.1 s.2.2.1.1, s.2.2.1.2), s.2.2.2 + 1))
        j (ns, vs, memory, c) =
      (rotlN j ns, rotlN j vs, (qstepN hdr j ns memory.1, memory.2), c + j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Nat.repeat] at ih ⊢; rw [ih, qstepN_succ]
    simp only [rotlN, Nat.repeat, Nat.add_assoc]

theorem qstep_qrep (hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ns ≠ [] → qrep hdr (rotl ns) (rotl vs) (qstep hdr ns h) := by
  intro hq hne
  match ns, vs, hq with
  | [], _, _ => exact absurd rfl hne
  | a :: ns', [], hq => exact absurd (qrep_len _ _ _ _ hq) (by simp)
  | a :: ns', v :: vs', hq => exact (rot_heap_spec hdr a ns' v vs' h hq).1

theorem qstepN_qrep (n hdr : Nat) (ns vs : List Nat) (h : Heap) :
    qrep hdr ns vs h → ns ≠ [] →
      qrep hdr (rotlN n ns) (rotlN n vs) (qstepN hdr n ns h) ∧ rotlN n ns ≠ [] := by
  intro hq hne
  induction n with
  | zero => exact ⟨hq, hne⟩
  | succ n ih =>
    rw [qstepN_succ]
    exact ⟨qstep_qrep _ _ _ _ ih.1 ih.2, rotl_nonnil _ ih.2⟩

/-- `n` rotations expose all five observations per turn before the run from the `n`-times-rotated
heap. -/
theorem run_stepN (n hdr : Nat) (ns vs : List Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    qrep hdr ns vs h → ns ≠ [] →
    run hdr ((h, allocs), (ctx, c)) ~
      runN hdr n ns vs (h, allocs) c (run hdr ((qstepN hdr n ns h, allocs), (ctx, c + n))) := by
  intro hq hne
  induction n with
  | zero => exact sbisim_refl _
  | succ n ih =>
    refine sbisim_trans ih ?_
    unfold runN
    rw [List.range'_concat, List.flatMap_append, emit_list_app]
    refine emit_list_sbisim _ ?_
    obtain ⟨hqn, hnen⟩ := qstepN_qrep n hdr ns vs h hq hne
    simp only [Nat.zero_add, Nat.one_mul, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      runN_iter]
    rw [qstepN_succ, ← Nat.add_assoc]
    generalize rotlN n ns = nodes at hqn hnen ⊢
    generalize rotlN n vs = values at hqn ⊢
    match nodes, values, hqn with
    | [], _, _ => exact absurd rfl hnen
    | a :: ns', [], hq' => exact absurd (qrep_len _ _ _ _ hq') (by simp)
    | a :: ns', v :: vs', hq' => exact run_step hdr a ns' v vs' _ allocs ctx (c + n) hq'

end Examples.CSL.Queue.Trace
