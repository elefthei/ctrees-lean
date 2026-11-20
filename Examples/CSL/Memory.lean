/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Logic.CTree.Trace

/-!
# Malloc/free lifecycle of the canonical CSL language

Concrete single-thread programs run through the real round-robin interpreter. They pin the
observable allocation discipline: first-fit zero-initialized malloc with recorded extents,
whole-block free, reuse of a released block, the null-free no-op, and faults on
interior-pointer, double, and use-after-free accesses. Every heap snapshot and indexed program
observation is logged under `.inl`; selections use `.inr slot` (← `examples/CSL/Memory.v`).
-/

@[expose] public section
namespace Examples.CSL.Memory
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open ITree (Effect)

/-! ## Fixtures -/

def lifecycle : CProg Unit :=
  .bind (.alloc 3) fun first =>
  .bind (.alloc 2) fun second =>
  .bind (.write first 7) fun _ =>
  .bind (.write (first + 2) 9) fun _ =>
  .bind (.write second 11) fun _ =>
  .bind (.cas (.lit first) (.lit 7) (.lit 8)) fun succeeded =>
  .bind (.cas (.lit first) (.lit 7) (.lit 99)) fun failed =>
  .bind (.emit 80 (if succeeded then 1 else 0)) fun _ =>
  .bind (.emit 81 (if failed then 1 else 0)) fun _ =>
  .bind (.free first) fun _ =>
  .bind (.read second) fun value =>
  .bind (.emit 82 value) fun _ => .ret ()

def reallocate : CProg Unit :=
  .bind (.alloc 3) fun first =>
  .bind (.free first) fun _ =>
  .bind (.alloc 3) fun next =>
  .bind (.emit 83 next) fun _ => .ret ()

def invalid_interior : CProg Unit :=
  .bind (.alloc 3) fun base => .free (base + 1)

def invalid_double : CProg Unit :=
  .bind (.alloc 3) fun base =>
  .bind (.free base) fun _ => .free base

def use_after_free_read : CProg Unit :=
  .bind (.alloc 3) fun base =>
  .bind (.free base) fun _ =>
  .bind (.read (base + 2)) fun _ => .ret ()

def use_after_free_write : CProg Unit :=
  .bind (.alloc 3) fun base =>
  .bind (.free base) fun _ => .write (base + 2) 17

def use_after_free_cas : CProg Unit :=
  .bind (.alloc 3) fun base =>
  .bind (.free base) fun _ =>
  .bind (.cas (.lit (base + 2)) (.lit 0) (.lit 17)) fun _ => .ret ()

/-! ## Driving the single-thread round-robin run

Each step applies one source execution rule of `Lang.CoCSL` at the focused thread; concrete
heap facts are discharged by computation. -/

/-- A first-fit side condition from a computable check of every lower candidate. -/
private theorem no_lower_fit (h : Heap) (base size : Nat)
    (hc : ∀ j, j < base → 0 < j → block_freeb h j size = false) :
    ∀ j, 0 < j → j < base → ¬ block_free h j size := fun j h0 hj hf => by
  have := hc j hj h0
  rw [(block_freeb_spec h j size).2 hf] at this
  exact Bool.noConfusion this

/-- The returned thread is removed and the empty pool returns the final state. -/
private theorem rr_finish (m : Nat) (σ : SSig) :
    interp_schedule_rr sh 1 ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1) (pure ⟨⟩)) (some 0) m
      σ ~
      (pure (⟨⟩, σ) : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  sbisim_trans (interp_schedule_rr_ret sh 0 _ 0 m σ rfl) (interp_schedule_rr_empty sh _ m σ)

/-- Rewrite the focused thread by one source rule, then normalize its continuation. -/
local macro "rr_by " t:term : tactic => `(tactic| (refine sbisim_trans $t ?_; try dsimp only))

/-- Unfold a source `bind` at the focused thread. -/
local macro "rr_bind" : tactic => `(tactic| (rw [interp_rr_bind]; try dsimp only))

/-- Split a shared leading observation. -/
local macro "rr_log" : tactic => `(tactic| (rw [log_vis]; refine sb_vis _ fun _ => ?_))

/-- First-fit allocation at the explicit `base`. -/
local macro "rr_alloc " base:term : tactic => `(tactic|
  rr_by interp_rr_alloc_first _ _ _ _ $base _ _ _ _ _ _ (by decide) (by decide)
    ((block_freeb_spec _ _ _).1 (by decide)) (no_lower_fit _ _ _ (by decide)))

/-! ## Behavior -/

/-- Both CAS outcomes, the adjacent allocation, release of the whole first extent, and the
observation stamps. -/
theorem lifecycle_scope :
    let m1 := managed_alloc managed_empty 1 3
    let m2 := managed_alloc m1 4 2
    let m3 : ManagedHeap := (upd m2.1 1 7, m2.2)
    let m4 : ManagedHeap := (upd m3.1 3 9, m3.2)
    let m5 : ManagedHeap := (upd m4.1 4 11, m4.2)
    let m6 : ManagedHeap := (upd m5.1 1 8, m5.2)
    let m7 : ManagedHeap := (hfree_block 1 3 m6.1, hfree 1 m6.2)
    ∃ memory : ManagedHeap,
      run_rr lifecycle (managed_empty, (([] : Ctx), 0)) ~
        (emit_list (List.map Sum.inl
          [CSLObs.heap m1, .heap m2, .heap m3, .heap m4, .heap m5, .heap m6,
           .emit (stamp (80, 1) 0), .emit (stamp (81, 0) 1), .heap m7,
           .emit (stamp (82, 11) 2)])
          (pure (⟨⟩, (memory, (([] : Ctx), 3))))
          : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) ∧
      memory.1 1 = none ∧ memory.1 2 = none ∧ memory.1 3 = none ∧
      memory.1 4 = some 11 ∧ memory.1 5 = some 0 ∧
      memory.2 1 = none ∧ memory.2 4 = some 2 := by
  intro m1 m2 m3 m4 m5 m6 m7
  refine ⟨m7, ?_, hfree_block_in 1 3 m6.1 1 (by decide), hfree_block_in 1 3 m6.1 2 (by decide),
    hfree_block_in 1 3 m6.1 3 (by decide), (hfree_block_out 1 3 m6.1 4 (by decide)).trans rfl,
    (hfree_block_out 1 3 m6.1 5 (by decide)).trans rfl, rfl, rfl⟩
  rw [run_rr_focus, lifecycle]
  simp only [List.map_cons, List.map_nil, emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_alloc 4; rr_log
  -- Three checked writes and the successful CAS each record their post-memory.
  rr_bind; rr_by interp_rr_write_present _ _ _ _ _ _ _ _ _ _ _ (by decide); rr_log
  rr_bind; rr_by interp_rr_write_present _ _ _ _ _ _ _ _ _ _ _ (by decide); rr_log
  rr_bind; rr_by interp_rr_write_present _ _ _ _ _ _ _ _ _ _ _ (by decide); rr_log
  rr_bind; rr_by interp_rr_cas_value _ _ _ _ _ _ 7 _ _ _ _ _ _ (by decide)
  rw [ite_eq_left rfl]; rr_log
  -- The failed CAS is silent; each explicit emission advances the counter.
  rr_bind; rr_by interp_rr_cas_value _ _ _ _ _ _ 8 _ _ _ _ _ _ (by decide)
  rw [ite_eq_right (by decide)]
  rr_bind; rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _; rr_log
  rr_bind; rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _; rr_log
  -- Release the first block, read the adjacent one, and emit the value.
  rr_bind; rr_by interp_rr_free _ _ _ _ _ _ _ _ _ _ (by rfl); rr_log
  rr_bind; rr_by interp_rr_read_value _ _ _ _ 11 _ _ _ _ _ _ (by decide)
  rr_bind; rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _; rr_log
  rw [interp_rr_ret]
  exact rr_finish _ _

/-- A released block is reused by the next first-fit malloc, with its whole extent recorded and
zero-initialized again. -/
theorem reuse_first_fit :
    let allocated := managed_alloc managed_empty 1 3
    let released : ManagedHeap := (hfree_block 1 3 allocated.1, hfree 1 allocated.2)
    let allocated_again := managed_alloc released 1 3
    ∃ memory : ManagedHeap,
      run_rr reallocate (managed_empty, (([] : Ctx), 0)) ~
        (emit_list (List.map Sum.inl
          [CSLObs.heap allocated, .heap released, .heap allocated_again,
           .emit (stamp (83, 1) 0)])
          (pure (⟨⟩, (memory, (([] : Ctx), 1))))
          : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) ∧
      memory.2 1 = some 3 ∧
      memory.1 1 = some 0 ∧ memory.1 2 = some 0 ∧ memory.1 3 = some 0 := by
  intro allocated released allocated_again
  refine ⟨allocated_again, ?_, upd_eq released.2 1 3,
    hunion_some (hblock 1 3) released.1 1 0 (hblock_in 1 3 0 (by decide)),
    hunion_some (hblock 1 3) released.1 2 0 (hblock_in 1 3 1 (by decide)),
    hunion_some (hblock 1 3) released.1 3 0 (hblock_in 1 3 2 (by decide))⟩
  rw [run_rr_focus, reallocate]
  simp only [List.map_cons, List.map_nil, emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_by interp_rr_free _ _ _ _ _ _ _ _ _ _ (by rfl); rr_log
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _; rr_log
  rw [interp_rr_ret]
  exact rr_finish _ _

/-- Freeing null leaves every component of the state unchanged. -/
theorem free_null_unchanged (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    run_rr (.free 0) (memory, (ctx, c)) ~
      (pure (⟨⟩, (memory, (ctx, c))) : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus]
  rr_by interp_rr_free 0 _ 0 0 _ 0 memory memory ctx c rfl
  exact rr_finish _ _

/-! ## Faults -/

theorem invalid_interior_stuck :
    run_rr invalid_interior (managed_empty, (([] : Ctx), 0)) ~
      (emit_list [.inl (CSLObs.heap (managed_alloc managed_empty 1 3))] .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, invalid_interior]
  simp only [emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  exact interp_rr_free_invalid _ _ _ _ _ _ _ _ _ (by decide)

theorem invalid_double_stuck :
    run_rr invalid_double (managed_empty, (([] : Ctx), 0)) ~
      (emit_list (List.map Sum.inl [CSLObs.heap (managed_alloc managed_empty 1 3),
          .heap (hfree_block 1 3 (managed_alloc managed_empty 1 3).1,
                 hfree 1 (managed_alloc managed_empty 1 3).2)]) .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, invalid_double]
  simp only [List.map_cons, List.map_nil, emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_by interp_rr_free _ _ _ _ _ _ _ _ _ _ (by rfl); rr_log
  exact interp_rr_free_invalid _ _ _ _ _ _ _ _ _ (by simp [managed_free, hfree])

theorem use_after_free_read_stuck :
    run_rr use_after_free_read (managed_empty, (([] : Ctx), 0)) ~
      (emit_list (List.map Sum.inl [CSLObs.heap (managed_alloc managed_empty 1 3),
          .heap (hfree_block 1 3 (managed_alloc managed_empty 1 3).1,
                 hfree 1 (managed_alloc managed_empty 1 3).2)]) .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, use_after_free_read]
  simp only [List.map_cons, List.map_nil, emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_by interp_rr_free _ _ _ _ _ _ _ _ _ _ (by rfl); rr_log
  rr_bind
  exact interp_rr_read_missing _ _ _ _ _ _ _ _ _ _ (hfree_block_in 1 3 _ 3 (by decide))

theorem use_after_free_write_stuck :
    run_rr use_after_free_write (managed_empty, (([] : Ctx), 0)) ~
      (emit_list (List.map Sum.inl [CSLObs.heap (managed_alloc managed_empty 1 3),
          .heap (hfree_block 1 3 (managed_alloc managed_empty 1 3).1,
                 hfree 1 (managed_alloc managed_empty 1 3).2)]) .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, use_after_free_write]
  simp only [List.map_cons, List.map_nil, emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_by interp_rr_free _ _ _ _ _ _ _ _ _ _ (by rfl); rr_log
  exact interp_rr_write_missing _ _ _ _ _ _ _ _ _ _ _ (hfree_block_in 1 3 _ 3 (by decide))

theorem use_after_free_cas_stuck :
    run_rr use_after_free_cas (managed_empty, (([] : Ctx), 0)) ~
      (emit_list (List.map Sum.inl [CSLObs.heap (managed_alloc managed_empty 1 3),
          .heap (hfree_block 1 3 (managed_alloc managed_empty 1 3).1,
                 hfree 1 (managed_alloc managed_empty 1 3).2)]) .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, use_after_free_cas]
  simp only [List.map_cons, List.map_nil, emit_list_cons, emit_list_nil]
  rr_bind; rr_alloc 1; rr_log
  rr_bind; rr_by interp_rr_free _ _ _ _ _ _ _ _ _ _ (by rfl); rr_log
  rr_bind
  exact interp_rr_cas_missing _ _ _ _ _ _ _ _ _ _ _ _ (hfree_block_in 1 3 _ 3 (by decide))

-- Not ported: the Ltac `first_fit`, `rr_log`, `block_is_free`, `rr_step`, `rr_alloc` and
-- `rr_finish` (proof automation; replaced by the local macros `rr_by`, `rr_bind`, `rr_log`,
-- `rr_alloc` and the private lemmas `no_lower_fit`, `rr_finish`); `run_rr_focus` (redundant with
-- `CoCSL.run_rr_focus`).

end Examples.CSL.Memory
