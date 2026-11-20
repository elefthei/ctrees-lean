/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Lang.CoCSL.Frame
public import Lang.CoCSL.Sequential
public import Logic.CTree.Trace

/-!
# Control behavior of the combined Yield+CSL source language
-/

@[expose] public section
namespace Examples.CSL.Control
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open ITree (Effect)

def ctx0 : Ctx := []
def state0 : SSig := (managed_empty, (ctx0, 0))

/-! ## Driving the scheduled runs -/

/-- Every replacement in a singleton pool is the literal replacement of slot `0`. -/
private theorem set1 (ts : Pool sE Bn (0 + 1)) (i : Fin (0 + 1)) (t : Thread sE Bn) :
    ts.set i t = (#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1) t := by
  obtain rfl : i = 0 := fin1_eq i
  ext j hj
  obtain rfl : j = 0 := by omega
  simp

/-- Expose the focused slot as an explicit replacement. -/
private theorem rr_focus {N : Nat} (ts : Pool sE Bn (N + 1)) (i : Fin (N + 1)) (m : Nat)
    (s : SSig) :
    interp_schedule_rr sh (N + 1) ts (some i) m s =
      interp_schedule_rr sh (N + 1) (ts.set i ts[i]) (some i) m s := by
  simp

private theorem nd_focus {N : Nat} (ts : Pool sE Bn (N + 1)) (i : Fin (N + 1)) (s : SSig) :
    interp_schedule_nd sh (N + 1) ts (some i) s =
      interp_schedule_nd sh (N + 1) (ts.set i ts[i]) (some i) s := by
  simp

/-- Normalize concrete pools to literals. -/
local macro "rr_norm" : tactic => `(tactic|
  simp only [Fin.isValue, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_succ, List.getElem_cons_zero, Vector.set_mk, List.set_toArray,
    List.set_cons_succ, List.set_cons_zero, Vector.eraseIdx_mk, List.eraseIdx_toArray,
    List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, Vector.cons, Vector.toArray_mk,
    List.append_toArray, List.cons_append, List.nil_append, Fin.val_one, Fin.val_zero,
    Fin.val_two, Nat.reduceAdd, Nat.reduceSub, Fin.succ_zero_eq_one])

private theorem vget1 (a : Thread sE Bn) : (#v[a])[(0 : Fin 1)] = a := rfl
private theorem vget2_0 (a b : Thread sE Bn) : (#v[a, b])[(0 : Fin 2)] = a := rfl
private theorem vget2_1 (a b : Thread sE Bn) : (#v[a, b])[(1 : Fin 2)] = b := rfl

/-- A focused round-robin singleton is the replacement of its only slot; on large threads this is
far cheaper than `rw [vget1]` (measured: >100k heartbeats in `cas_interleaving_rr`). -/
private theorem rr_focus1 (t : Thread sE Bn) (m : Nat) (s : SSig) :
    interp_schedule_rr sh 1 #v[t] (some 0) m s =
      interp_schedule_rr sh 1 ((#v[t] : Pool sE Bn 1).set (0 : Fin 1) t) (some 0) m s := rfl

/-- Focus the scheduled slot of a literal pool, computing its thread. -/
local macro "rr_focus" : tactic => `(tactic|
  (try rr_norm
   first
   | rw [rr_focus1]
   | (first | rw [rr_focus] | rw [nd_focus]
      first | rw [vget1] | rw [vget2_0] | rw [vget2_1])))

/-- Rewrite by one `~` source rule, then normalize the continuation and the state. -/
local macro "rr_by " t:term : tactic => `(tactic|
  (refine sbisim_trans $t ?_
   try dsimp only [csl_context, csl_set_context, csl_memory, csl_counter]))

/-- Rewrite by one source equation (matched up to unfolding), then normalize. -/
local macro "rr_eq " t:term : tactic => `(tactic|
  (refine Eq.mpr (congrArg (· ~ _) $t) ?_
   try dsimp only))

/-- Split a shared leading observation. -/
local macro "rr_log" : tactic => `(tactic| (rw [log_vis]; refine sb_vis _ fun _ => ?_))

/-- Round-robin selection logs the computed slot. -/
local macro "rr_select" : tactic => `(tactic|
  (rr_by interp_schedule_rr_select sh _ _ _ _
   simp only [rr_pick_0, rr_pick_even, rr_pick_odd, Nat.reduceMod, Nat.reduceAdd]
   refine sb_vis _ fun _ => ?_))

/-- A focused finished slot is removed and the remaining pool is normalized. -/
local macro "rr_finish" : tactic => `(tactic|
  (rr_by interp_schedule_rr_ret sh _ _ _ _ _ (by simp)
   try rr_norm))

theorem scoped_fork_no_parent_replay :
    run_rr (.bind (.fork (.emit 1 7)) fun _ => .emit 0 9) state0 ~
      (emit_list [.inl (CSLObs.emit (stamp (0, 9) 0)), .inr 0,
          .inl (CSLObs.emit (stamp (1, 7) 1))]
        (pure (⟨⟩, (managed_empty, (ctx0, 2))))
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  refine sbisim_trans (run_rr_fork_bind _ _ _) ?_
  simp only [state0, emit_list_cons, emit_list_nil]
  rr_focus
  rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _
  rr_log
  rr_finish
  rr_select
  rr_focus
  rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _
  rr_log
  rr_finish
  exact interp_schedule_rr_empty sh _ _ _

/-! ## Late context reads

`x := 1; fork (z := 9); y := x`. The parent's read of `x` yields once, so the child updates the
shared context first; the parent's assignment then reads the context again, so the child's
update is preserved. Only context observations are emitted; the indexed counter stays `0`. -/

def context_program : CProg Unit :=
  .bind (.assign "x" (.lit 1)) fun _ =>
  .bind (.fork (.assign "z" (.lit 9))) fun _ =>
  .assign "y" (.var "x")

theorem context_resume_preserves_updates :
    let ctx1 := Ctx.add "x" 1 ctx0
    let ctx2 := Ctx.add "z" 9 ctx1
    let ctx3 := Ctx.add "y" 1 ctx2
    run_rr context_program state0 ~
      (emit_list [.inl (CSLObs.ctx ctx1), .inr 0, .inl (CSLObs.ctx ctx2), .inr 0,
          .inl (CSLObs.ctx ctx3)]
        (pure (⟨⟩, (managed_empty, (ctx3, 0))))
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  intro ctx1 ctx2 ctx3
  rw [run_rr_focus]
  simp only [state0, context_program, emit_list_cons, emit_list_nil]
  -- parent: x := 1
  rw [interp_rr_bind, interp_rr_assign, interp_rr_lit]
  rr_by interp_rr_get_ctx _ _ _ _ _ _
  rr_by interp_rr_put_ctx _ _ _ _ _ _ _
  rr_log
  -- parent: fork the child, keep the focus
  rw [interp_rr_bind]
  rr_by interp_rr_fork _ _ _ _ _ _ _
  rr_norm
  -- parent: y := x reads x and yields
  rr_focus
  rw [interp_rr_assign]
  rr_by interp_rr_var _ _ _ "x" 1 _ _ _ (by decide)
  -- the child runs next: z := 9, then halts
  rr_select
  rr_norm
  rr_focus
  rw [interp_rr_assign, interp_rr_lit]
  rr_by interp_rr_get_ctx _ _ _ _ _ _
  rr_by interp_rr_put_ctx _ _ _ _ _ _ _
  rr_log
  rr_finish
  -- the parent resumes with the captured value and a fresh context read
  rr_select
  rr_focus
  rr_by interp_rr_get_ctx _ _ _ _ _ _
  rr_by interp_rr_put_ctx _ _ _ _ _ _ _
  rr_log
  rr_finish
  exact interp_schedule_rr_empty sh _ _ _

/-- A successful variable read captures its value before yielding. The child overwrites the
same shared variable, but the parent's resumed continuation emits the captured value rather than
reading it again. -/
def captured_before_yield : CProg Unit :=
  .bind (.fork (.assign "x" (.lit 1))) fun _ =>
  .bind (.eval (.var "x")) fun v => .emit 9 v

theorem captured_before_yield_rr (memory : ManagedHeap) (c : Nat) :
    let ctx0 := Ctx.add "x" 0 []
    let ctx1 := Ctx.add "x" 1 ctx0
    run_rr captured_before_yield (memory, (ctx0, c)) ~
      (emit_list [.inr 0, .inl (CSLObs.ctx ctx1), .inr 0,
          .inl (CSLObs.emit (stamp (9, 0) c))]
        (pure (⟨⟩, (memory, (ctx1, c + 1))))
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  intro ctx0 ctx1
  rr_by run_rr_fork_bind _ _ _
  simp only [emit_list_cons, emit_list_nil]
  -- Parent: capture x = 0, then clear the focus at the read's yield.
  rr_focus
  rr_eq interp_rr_bind _ _ _ _ _ _ _ _
  rw [source_raw_eval]
  rr_by interp_rr_var _ _ _ "x" 0 _ _ _ rfl
  -- Cursor 0 selects the child, which stores x = 1 and terminates.
  rr_select
  rr_focus
  rr_eq interp_rr_assign _ _ _ _ _ _ _ _
  rw [interp_rr_lit]
  rr_by interp_rr_get_ctx _ _ _ _ _ _
  rr_by interp_rr_put_ctx _ _ _ _ _ _ _
  rr_log
  rr_finish
  -- The remaining parent emits the saved 0 in the updated context.
  rr_select
  rr_focus
  rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _
  rr_log
  rr_finish
  exact interp_schedule_rr_empty sh _ _ _

/-! ## Missing variables fault

There is no default value: reading an unbound variable is stuck, so the whole run is `stuck`
rather than an empty observation sequence. -/

theorem missing_variable_stuck :
    run_rr (.bind (.eval (.var "missing")) fun _ => .ret ()) state0 ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, interp_rr_bind, source_raw_eval]
  exact interp_rr_var_missing _ _ _ _ _ _ _ (by decide)

/-! ## Expression-valued CAS

Pure arithmetic introduces no scheduling boundary. -/

def cas_arithmetic : CProg Unit :=
  .bind (.cas (.plus (.lit 1) (.lit 2)) (.minus (.lit 9) (.lit 2)) (.mult (.lit 2) (.lit 4)))
    fun ok => .emit 90 (if ok then 1 else 0)

theorem cas_arithmetic_rr :
    run_rr cas_arithmetic ((upd hemp 3 7, hemp), ([], 0)) ~
      (emit_list [.inl (CSLObs.heap (upd (upd hemp 3 7) 3 8, hemp)),
          .inl (CSLObs.emit (stamp (90, 1) 0))]
        (pure (⟨⟩, ((upd (upd hemp 3 7) 3 8, hemp), (([] : Ctx), 1))))
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, cas_arithmetic, interp_rr_bind, interp_rr_cas_exp]
  simp only [source_raw_exp_plus, source_raw_exp_minus, source_raw_exp_mult, source_raw_lit,
    emit_list_cons, emit_list_nil]
  rr_by interp_rr_cas_value _ _ _ _ _ _ 7 _ _ _ _ _ _ (by decide)
  rw [ite_eq_left rfl]
  rr_log
  rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _
  rr_log
  rr_finish
  exact interp_schedule_rr_empty sh _ _ _

/-- The child changes the context between the parent's four reads, then makes the heap
comparison succeed only after the desired value is saved. -/
def cas_interleaving_child : CProg Unit :=
  .bind (.assign "x" (.lit 1)) fun _ =>
  .bind .yield fun _ =>
  .bind (.assign "x" (.lit 7)) fun _ =>
  .bind .yield fun _ =>
  .bind (.assign "x" (.lit 8)) fun _ =>
  .bind .yield fun _ =>
  .bind (.assign "x" (.lit 9)) fun _ =>
  .write 3 7

def cas_interleaving : CProg Unit :=
  .bind (.fork cas_interleaving_child) fun _ =>
  .bind (.cas (.minus (.var "x") (.var "x")) (.var "x") (.var "x"))
    fun ok => .emit 90 (if ok then 1 else 0)

/-- The focused thread assigns a literal and logs the new context. -/
local macro "rr_assign_lit" : tactic => `(tactic|
  (rw [interp_rr_assign, interp_rr_lit]
   rr_by interp_rr_get_ctx _ _ _ _ _ _
   rr_by interp_rr_put_ctx _ _ _ _ _ _ _
   rr_log))

/-- The focused thread assigns a literal, logs the new context and yields. -/
private theorem rr_assign_lit_yield (n : Nat) (ts : Pool sE Bn (n + 1)) (i : Fin (n + 1))
    (x : String) (v : Nat) (k : Unit → CProg Unit) (K : Option Unit → Thread sE Bn)
    (m : Nat) (h : ManagedHeap) (ctx : Ctx) (c : Nat) :
    interp_schedule_rr sh (n + 1)
        (ts.set i (denote_flow (.bind (.assign x (.lit v)) fun _ => .bind .yield k) >>= K))
        (some i) m (h, (ctx, c)) ~
      CTree.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inl (CSLObs.ctx (Ctx.add x v ctx)))
        fun _ => interp_schedule_rr sh (n + 1) (ts.set i (denote_flow (k ()) >>= K)) none m
          (h, (Ctx.add x v ctx, c)) := by
  rw [interp_rr_bind]
  rr_assign_lit
  rw [interp_rr_bind]
  rr_by interp_rr_yield _ _ _ _ _ _
  exact sbisim_refl _

theorem cas_interleaving_rr :
    let h0 := upd hemp 3 99
    let ctx0 := Ctx.add "x" 4 []
    let ctx1 := Ctx.add "x" 1 ctx0
    let ctx2 := Ctx.add "x" 7 ctx1
    let ctx3 := Ctx.add "x" 8 ctx2
    let ctx4 := Ctx.add "x" 9 ctx3
    run_rr cas_interleaving ((h0, hemp), (ctx0, 0)) ~
      (emit_list [.inr 0, .inl (CSLObs.ctx ctx1), .inr 1, .inr 0,
          .inl (CSLObs.ctx ctx2), .inr 1, .inr 0,
          .inl (CSLObs.ctx ctx3), .inr 1, .inr 0,
          .inl (CSLObs.ctx ctx4), .inl (CSLObs.heap (upd h0 3 7, hemp)), .inr 0,
          .inl (CSLObs.heap (upd (upd h0 3 7) 3 8, hemp)),
          .inl (CSLObs.emit (stamp (90, 1) 0))]
        (pure (⟨⟩, ((upd (upd h0 3 7) 3 8, hemp), (ctx4, 1))))
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  dsimp only
  rr_by run_rr_fork_bind _ _ _
  simp only [emit_list_cons, emit_list_nil]
  -- Parent: the first address read captures 4, then yields.
  rr_focus
  rr_eq interp_rr_bind _ _ _ _ _ _ _ _
  rw [interp_rr_cas_exp, source_raw_exp_minus]
  rr_by interp_rr_var _ _ _ "x" 4 _ _ _ (by decide)
  -- Slot 0: x := 1, then yield.
  rr_select
  rr_focus
  rr_by rr_assign_lit_yield _ _ _ _ _ _ _ _ _ _ _
  refine sb_vis _ fun _ => ?_
  -- Slot 1: the second address read captures 1, giving address 3.
  rr_select
  rr_focus
  rr_by interp_rr_var _ _ _ "x" 1 _ _ _ (by decide)
  -- Slot 0: x := 7, then yield.
  rr_select
  rr_focus
  rr_by rr_assign_lit_yield _ _ _ _ _ _ _ _ _ _ _
  refine sb_vis _ fun _ => ?_
  -- Slot 1: the expected operand captures 7.
  rr_select
  rr_focus
  rr_by interp_rr_var _ _ _ "x" 7 _ _ _ (by decide)
  -- Slot 0: x := 8, then yield.
  rr_select
  rr_focus
  rr_by rr_assign_lit_yield _ _ _ _ _ _ _ _ _ _ _
  refine sb_vis _ fun _ => ?_
  -- Slot 1: the desired operand captures 8 while the heap still holds 99.
  rr_select
  rr_focus
  rr_by interp_rr_var _ _ _ "x" 8 _ _ _ (by decide)
  -- Slot 0: x := 9, write 7 to the heap, then terminate.
  rr_select
  rr_focus
  rw [interp_rr_bind]
  rr_assign_lit
  rr_by interp_rr_write_present _ _ _ _ _ _ _ _ _ _ _ (by decide)
  rr_log
  rr_finish
  -- The singleton parent's saved operands perform CAS 3 7 8 and report true.
  rr_select
  rr_focus
  rr_by interp_rr_cas_value _ _ _ _ _ _ 7 _ _ _ _ _ _ (by decide)
  rw [ite_eq_left rfl]
  rr_log
  rr_by interp_rr_emit_log _ _ _ _ _ _ _ _ _ _
  rr_log
  rr_finish
  exact interp_schedule_rr_empty sh _ _ _

/-! ## Operand faults precede the heap event

No failed operand reaches the report. In particular, the desired operand is evaluated even when
the current heap value does not match. -/

theorem cas_missing_address_rr :
    run_rr (.bind (.cas (.var "missing") (.var "e") (.var "d"))
        fun ok => .emit 90 (if ok then 1 else 0))
      ((upd hemp 3 99, hemp), (Ctx.add "d" 8 (Ctx.add "e" 7 (Ctx.add "a" 3 [])), 0)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, interp_rr_bind, interp_rr_cas_exp]
  exact interp_rr_var_missing _ _ _ _ _ _ _ (by decide)

theorem cas_missing_expected_rr :
    run_rr (.bind (.cas (.var "a") (.var "missing") (.var "d"))
        fun ok => .emit 90 (if ok then 1 else 0))
      ((upd hemp 3 99, hemp), (Ctx.add "d" 8 (Ctx.add "e" 7 (Ctx.add "a" 3 [])), 0)) ~
      (log (.inr 0 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, interp_rr_bind, interp_rr_cas_exp, log_vis]
  rr_by interp_rr_var _ _ _ "a" 3 _ _ _ (by decide)
  rr_select
  rr_focus
  exact interp_rr_var_missing _ _ _ _ _ _ _ (by decide)

theorem cas_missing_desired_rr :
    run_rr (.bind (.cas (.var "a") (.var "e") (.var "missing"))
        fun ok => .emit 90 (if ok then 1 else 0))
      ((upd hemp 3 99, hemp), (Ctx.add "d" 8 (Ctx.add "e" 7 (Ctx.add "a" 3 [])), 0)) ~
      (log (.inr 0 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => log (.inr 0) >>= fun _ => .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, interp_rr_bind, interp_rr_cas_exp]
  simp only [log_vis]
  rr_by interp_rr_var _ _ _ "a" 3 _ _ _ (by decide)
  rr_select
  rr_focus
  rr_by interp_rr_var _ _ _ "e" 7 _ _ _ (by decide)
  rr_select
  rr_focus
  exact interp_rr_var_missing _ _ _ _ _ _ _ (by decide)

theorem cas_missing_cell_rr :
    run_rr (.bind (.cas (.var "a") (.var "e") (.var "d"))
        fun ok => .emit 90 (if ok then 1 else 0))
      (managed_empty, (Ctx.add "d" 8 (Ctx.add "e" 7 (Ctx.add "a" 3 [])), 0)) ~
      (log (.inr 0 : CSLObs (Nat × Nat) ⊕ Nat) >>= fun _ => log (.inr 0) >>= fun _ =>
        log (.inr 0) >>= fun _ => .stuck
        : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) := by
  rw [run_rr_focus, interp_rr_bind, interp_rr_cas_exp]
  simp only [log_vis]
  rr_by interp_rr_var _ _ _ "a" 3 _ _ _ (by decide)
  rr_select
  rr_focus
  rr_by interp_rr_var _ _ _ "e" 7 _ _ _ (by decide)
  rr_select
  rr_focus
  rr_by interp_rr_var _ _ _ "d" 8 _ _ _ (by decide)
  rr_select
  rr_focus
  exact interp_rr_cas_missing _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

/-! ## The sequential-fragment boundary includes every operand -/

theorem cas_yield_fork_free_literals : yield_fork_free (.cas (.lit 3) (.lit 7) (.lit 8)) :=
  ⟨trivial, trivial, trivial, fun _ _ _ => trivial⟩

theorem cas_var_operands_not_yield_fork_free :
    ¬ yield_fork_free (.cas (.var "x") (.lit 7) (.lit 8)) ∧
    ¬ yield_fork_free (.cas (.lit 3) (.var "x") (.lit 8)) ∧
    ¬ yield_fork_free (.cas (.lit 3) (.lit 7) (.var "x")) := by
  simp [yield_fork_free, prog_ok, exp_ok, user_only]

/-! ## Loops and nondeterministic faults under TICL

A source loop may yield and grow its pool before exiting; native return is established only
after both the parent and the spawned child finish. -/

section Ticl
open Tisl.Notation

def yield_fork_body : CProg (Option Unit) :=
  .bind .yield fun _ => .bind (.fork (.emit 8 1)) fun _ => .ret (none : Option Unit)

def yield_fork_loop : CProg Unit := .untilNone yield_fork_body

theorem yield_fork_loop_af_return_nd :
    entails (AF (.ret fun (r : PUnit × SSig) _ => r.2 = (managed_empty, ([], 1)) ∧ r.1 = ⟨⟩))
      (run_nd yield_fork_loop state0) .pure := by
  rw [run_nd_focus]
  refine af_csl_nd_until_none_wf yield_fork_body (fun _ => pure ⟨⟩)
    (fun (_ : Unit) n (_ : Pool sE Bn (n + 1)) (_ : Fin (n + 1)) σ w =>
      n = 0 ∧ σ = state0 ∧ w = .pure)
    (fun _ _ => False) _ ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩ ?_ () 0 _ 0 _ _ ⟨rfl, rfl, rfl⟩
  rintro _ n ts i σ w ⟨rfl, rfl, rfl⟩
  obtain rfl : i = 0 := fin1_eq i
  rw [set1]
  refine auc_mono_r (fun _ _ h => Or.inl h) _ _ ((ticl_au _ _).1 ?_)
  simp only [state0, ctx0, yield_fork_body]
  rw [au_csl_nd_bind, au_csl_nd_yield]
  refine Or.inr ⟨⟨trivial, .pure⟩, fun j => ?_⟩
  obtain rfl : j = 0 := fin1_eq j
  dsimp only
  rw [au_csl_nd_bind, au_csl_nd_fork]
  dsimp only [until_tail]
  rr_focus
  rw [au_csl_nd_ret]
  dsimp only [until_tail]
  rw [proper_entails_meq _ (interp_schedule_nd_ret sh 1 _ 1 _ (by simp))]
  rr_norm
  rw [au_csl_nd_select]
  refine Or.inr ⟨⟨trivial, .pure⟩, fun j => ?_⟩
  obtain rfl : j = 0 := fin1_eq j
  rr_focus
  rw [au_csl_nd_emit]
  refine Or.inr ⟨⟨trivial, .pure⟩, ?_⟩
  rw [proper_entails_meq _ (interp_schedule_nd_ret sh 0 _ 0 _ (by simp)),
    proper_entails_meq _ (interp_schedule_nd_empty sh _ _)]
  exact (ticl_au _ _).2 (.matchA (ret_ret (.obs _ _) ⟨rfl, trivial⟩))

theorem yield_fork_loop_af_return_rr :
    entails (AF (.ret fun (r : PUnit × SSig) _ => r.2 = (managed_empty, ([], 1)) ∧ r.1 = ⟨⟩))
      (run_rr yield_fork_loop state0) .pure := by
  rw [run_rr_focus]
  refine af_csl_rr_until_none_wf yield_fork_body (fun _ => pure ⟨⟩)
    (fun (_ : Unit) n (_ : Pool sE Bn (n + 1)) (_ : Fin (n + 1)) cursor σ w =>
      n = 0 ∧ cursor = 0 ∧ σ = state0 ∧ w = .pure)
    (fun _ _ => False) _ ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩ ?_ () 0 _ 0 0 _ _
    ⟨rfl, rfl, rfl, rfl⟩
  rintro _ n ts i cursor σ w ⟨rfl, rfl, rfl, rfl⟩
  obtain rfl : i = 0 := fin1_eq i
  rw [set1]
  refine auc_mono_r (fun _ _ h => Or.inl h) _ _ ((ticl_au _ _).1 ?_)
  simp only [state0, ctx0, yield_fork_body]
  rw [au_csl_rr_bind, au_csl_rr_yield]
  refine Or.inr ⟨⟨trivial, .pure⟩, ?_⟩
  rw [rr_pick_0]
  dsimp only
  rw [au_csl_rr_bind, au_csl_rr_fork]
  dsimp only [until_tail]
  rr_focus
  rw [au_csl_rr_ret]
  dsimp only [until_tail]
  rw [proper_entails_meq _ (interp_schedule_rr_ret sh 1 _ 1 _ _ (by simp))]
  rr_norm
  rw [au_csl_rr_select]
  refine Or.inr ⟨⟨trivial, .obs _ _⟩, ?_⟩
  rw [rr_pick_0]
  rr_focus
  rw [au_csl_rr_emit]
  refine Or.inr ⟨⟨trivial, .obs _ _⟩, ?_⟩
  rw [proper_entails_meq _ (interp_schedule_rr_ret sh 0 _ 0 _ _ (by simp)),
    proper_entails_meq _ (interp_schedule_rr_empty sh _ _ _)]
  exact (ticl_au _ _).2 (.matchA (ret_ret (.obs _ _) ⟨rfl, trivial⟩))

/-! Nondeterminism may choose a visible successful branch or a fault. Round robin instead logs
its cursor-dependent selection, without changing which branch succeeds or faults. -/

def fault_choice_pool : Vector (CProg Unit) 2 :=
  #v[.emit 7 9, .bind (.read 1) fun _ => .ret ()]

theorem fault_choice_ef_nd :
    entails (EF (visWₜ fun o => o = CSLObs.emit (stamp (7, 9) 0)))
      (run_nd_pool fault_choice_pool none state0) .pure := by
  rw [run_nd_pool, fault_choice_pool, csl_pool_pair, state0, ctx0]
  rw [eu_csl_nd_select]
  refine Or.inr ⟨⟨trivial, .pure⟩, 0, ?_⟩
  rr_focus
  refine (eu_csl_nd_emit _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inr ⟨⟨trivial, .pure⟩, ?_⟩)
  exact (ticl_eu _ _).2 (.matchE ⟨.obs _ _ rfl, .obs _ _⟩)

theorem fault_choice_not_af_nd :
    ¬ entails (AF (visWₜ fun o => o = CSLObs.emit (stamp (7, 9) 0)))
      (run_nd_pool fault_choice_pool none state0) .pure := by
  rw [run_nd_pool, fault_choice_pool, csl_pool_pair, state0, ctx0]
  rw [au_csl_nd_select]
  rintro (Hnow | ⟨_, Hnext⟩)
  · nomatch Hnow.1
  · have H := Hnext 1
    revert H
    rr_focus
    intro H
    have H := (au_csl_nd_bind _ _ _ _ _ _ _ _ _ _ _ _).1 H
    have H := (au_csl_nd_read_missing _ _ _ _ _ _ _ _ _ _ _ _ rfl).1 H
    nomatch H.1

theorem fault_choice_af_rr_zero :
    entails (AF (visWₜ fun o => o = .inl (CSLObs.emit (stamp (7, 9) 0))))
      (run_rr_pool fault_choice_pool none 0 state0) .pure := by
  rw [run_rr_pool, fault_choice_pool, csl_pool_pair, state0, ctx0]
  rw [au_csl_rr_select]
  refine Or.inr ⟨⟨trivial, .pure⟩, ?_⟩
  rw [rr_pick_even rfl]
  rr_focus
  refine (au_csl_rr_emit _ _ _ _ _ _ _ _ _ _ _ _ _).2 (Or.inr ⟨⟨trivial, .obs _ _⟩, ?_⟩)
  exact (ticl_au _ _).2 (.matchA ⟨.obs _ _ rfl, .obs _ _⟩)

theorem fault_choice_not_ef_rr_one :
    ¬ entails (EF (visWₜ fun o => o = .inl (CSLObs.emit (stamp (7, 9) 0))))
      (run_rr_pool fault_choice_pool none 1 state0) .pure := by
  rw [run_rr_pool, fault_choice_pool, csl_pool_pair, state0, ctx0]
  rw [eu_csl_rr_select, rr_pick_odd rfl]
  rintro (Hnow | ⟨_, H⟩)
  · nomatch Hnow.1
  · revert H
    rr_focus
    intro H
    have H := (eu_csl_rr_bind _ _ _ _ _ _ _ _ _ _ _ _ _).1 H
    have H := (eu_csl_rr_read_missing _ _ _ _ _ _ _ _ _ _ _ _ _ rfl).1 H
    nomatch H.1

end Ticl

end Examples.CSL.Control
