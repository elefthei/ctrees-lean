/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Surface
public import Logic.CTree.Yield

/-!
# CoCSL source pools

The generic pool rules of `Logic/CTree/Yield.lean` specialised to source pools `csl_pool ps`: a
turn certificate is an exact first-yield segment of a slot's own denotation that returns to that
same denotation. Also the two-child startup `fork p; fork q; skip` and the native return of
all-`ret` pools (← `Lang/CoCSL/Mod.v`, lines 12442-12636).
-/

@[expose] public section
namespace CoCSL
open CTree Tisl Tisl.CSL Tisl.Yield Tisl.Notation
open ITree (Effect)

/-! ## Closed turns, selection, and structural rules -/

theorem run_nd_pool_turn {n : Nat} (ps : Vector (CProg Unit) (n + 1)) (i : Fin (n + 1))
    (s s' : SSig) (logs : List (CSLObs (Nat × Nat))) :
    segment_to sh csl_equ (csl_pool ps)[i] s logs (csl_pool ps)[i] s' →
    run_nd_pool ps (some i) s ~ emit_list logs (run_nd_pool ps none s') :=
  segment_pool_nd_loop sh n (csl_pool ps) i s logs s'

theorem run_rr_pool_turn {n : Nat} (ps : Vector (CProg Unit) (n + 1)) (i : Fin (n + 1))
    (cursor : Nat) (s s' : SSig) (logs : List (CSLObs (Nat × Nat))) :
    segment_to sh csl_equ (csl_pool ps)[i] s logs (csl_pool ps)[i] s' →
    run_rr_pool ps (some i) cursor s ~
      emit_list (logs.map .inl) (run_rr_pool ps none cursor s') :=
  segment_pool_rr_loop sh n (csl_pool ps) i cursor s logs s'

theorem run_nd_pool_select {n : Nat} (ps : Vector (CProg Unit) (n + 1)) (s : SSig) :
    run_nd_pool ps none s ~ CTree.brSn (n + 1) fun i => run_nd_pool ps (some i) s :=
  interp_schedule_nd_select sh n (csl_pool ps) s

theorem run_rr_pool_select {n : Nat} (ps : Vector (CProg Unit) (n + 1)) (cursor : Nat)
    (s : SSig) :
    run_rr_pool ps none cursor s ~
      .vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inr (slot_index (rr_pick n cursor)))
        fun _ => run_rr_pool ps (some (rr_pick n cursor)) (cursor + 1) s :=
  interp_schedule_rr_select sh n (csl_pool ps) cursor s

theorem ag_csl_nd_invariance {G : Type} {n : Nat} (ps : Vector (CProg Unit) (n + 1))
    (Inv : G → SSig → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    ClosedTurns sh (csl_pool ps) Inv →
    (∀ (o : CSLObs (Nat × Nat)) (t : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) w,
      NotDone w → entails φ t (.obs (E := writerE (CSLObs (Nat × Nat))) o ⟨⟩) →
      entails φ (CTree.vis (E := writerE (CSLObs (Nat × Nat))) o fun _ => t) w) →
    (∀ g s focus w, Inv g s → NotDone w → entails φ (run_nd_pool ps focus s) w) →
    ∀ g s focus w, Inv g s → NotDone w → entails (AG φ) (run_nd_pool ps focus s) w :=
  ag_pool_nd_invariance sh (csl_pool ps) Inv φ

theorem ag_csl_rr_invariance {G : Type} {n : Nat} (ps : Vector (CProg Unit) (n + 1))
    (Inv : G → SSig → Prop) (φ : TiclL (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    ClosedTurns sh (csl_pool ps) Inv →
    (∀ (o : CSLObs (Nat × Nat)) (t : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) w,
      NotDone w → entails φ t (.obs (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inl o) ⟨⟩) →
      entails φ (CTree.vis (E := writerE (CSLObs (Nat × Nat) ⊕ Nat)) (.inl o) fun _ => t) w) →
    (∀ g s focus cursor w, Inv g s → NotDone w →
      entails φ (run_rr_pool ps focus cursor s) w) →
    ∀ g s focus cursor w, Inv g s → NotDone w →
      entails (AG φ) (run_rr_pool ps focus cursor s) w :=
  ag_pool_rr_invariance sh (csl_pool ps) Inv φ

theorem aul_csl_nd_eventually {G V : Type} {n : Nat} (ps : Vector (CProg Unit) (n + 1))
    (Inv : G → SSig → Prop) (rank : G → V) (ltV : V → V → Prop)
    (P : CSLObs (Nat × Nat) → Prop) :
    WellFounded ltV → RankedTurns sh (csl_pool ps) Inv rank ltV P →
    ∀ g s focus w, Inv g s → NotDone w →
      entails (AF (visWₜ P)) (run_nd_pool ps focus s) w :=
  aul_pool_nd_eventually sh (csl_pool ps) Inv rank ltV P

theorem aul_csl_rr_eventually {G V : Type} {n : Nat} (ps : Vector (CProg Unit) (n + 1))
    (Inv : G → SSig → Prop) (rank : G → V) (ltV : V → V → Prop)
    (P : CSLObs (Nat × Nat) → Prop) :
    WellFounded ltV → RankedTurns sh (csl_pool ps) Inv rank ltV P →
    ∀ g s focus cursor w, Inv g s → NotDone w →
      entails (AF (visWₜ (fair_obs P))) (run_rr_pool ps focus cursor s) w :=
  aul_pool_rr_eventually sh (csl_pool ps) Inv rank ltV P

/-! ## Two-child startup

`fork p; fork q; skip`: each fork prepends its child and keeps the parent focused, and the parent
then terminates. What remains is the unfocused pool `[q, p]` at the unchanged state and cursor. -/

/-- The parent after both forks returns at once. -/
private theorem denote_ret_unit_unfold :
    (denote (.ret ())).unfold = .ret ⟨⟩ := by
  simp [denote, denote_flow]

private theorem sb_of_unfold_guard {t u : Completed sE Bn} (h : t.unfold = .guard u) : t ~ u := by
  rw [show t = .guard u from unfold_inj (by rw [h, unfold_guard])]
  exact sb_guard _

theorem run_nd_two_forks (p q : CProg Unit) (s : SSig) :
    run_nd (.bind (.fork p) fun _ => .bind (.fork q) fun _ => .ret ()) s ~
      run_nd_pool #v[q, p] none s := by
  rw [run_nd_unfold]
  refine sbisim_trans (interp_schedule_nd_fork sh 0 _ 0
    (fun child : Bool => if child then denote p else denote (.bind (.fork q) fun _ => .ret ()))
    s (by show (denote (.bind (.fork p) _)).unfold = _; rw [denote_fork_bind]; simp)) ?_
  refine sbisim_trans (interp_schedule_nd_fork sh 1 _ 1
    (fun child : Bool => if child then denote q else denote (.ret ())) s
    (by show (denote (.bind (.fork q) _)).unfold = _; rw [denote_fork_bind]; simp)) ?_
  refine sbisim_trans (interp_schedule_nd_ret sh 2 _ 2 s denote_ret_unit_unfold) ?_
  refine equ_sbisim _ _ (congrArg (fun ts => interp_schedule_nd sh 2 ts none s) ?_)
  simp [csl_pool, Vector.cons]

theorem run_fair_two_forks (sch : Scheduler) (p q : CProg Unit) (st : sch.sched_state)
    (s : SSig) :
    run_fair sch (.bind (.fork p) fun _ => .bind (.fork q) fun _ => .ret ()) st s ~
      run_fair_pool sch #v[q, p] none st s := by
  refine sbisim_trans (run_fair_fork_bind sch p _ st s) ?_
  refine sbisim_trans (interp_schedule_fair_fork sch sh 1 _ 1
    (fun child : Bool => if child then denote q else denote (.ret ())) st s
    (by show (denote (.bind (.fork q) _)).unfold = _; rw [denote_fork_bind]; simp)) ?_
  refine sbisim_trans (interp_schedule_fair_ret sch sh 2 _ 2 st s denote_ret_unit_unfold) ?_
  refine equ_sbisim _ _ (congrArg (fun ts => interp_schedule_fair sch sh 2 ts none st s) ?_)
  simp [csl_pool, Vector.cons]

theorem run_rr_two_forks (p q : CProg Unit) (s : SSig) :
    run_rr (.bind (.fork p) fun _ => .bind (.fork q) fun _ => .ret ()) s ~
      run_rr_pool #v[q, p] none 0 s :=
  run_fair_two_forks rr_scheduler p q (0 : Nat) s

/-- Both forks retain parent focus, so no selection precedes the unfocused two-worker pool. -/
theorem scheduled_visible_two_forks (p q : CProg Unit) :
    scheduled_visible (.bind (.fork p) fun _ => .bind (.fork q) fun _ => .ret ()) ~
      schedule 2 #v[denote q, denote p] none := by
  refine sbisim_trans (sb_of_unfold_guard (schedule_focused_fork 0 _ 0
    (fun child : Bool => if child then denote p else denote (.bind (.fork q) fun _ => .ret ()))
    (by show (denote (.bind (.fork p) _)).unfold = _; rw [denote_fork_bind]; simp))) ?_
  refine sbisim_trans (sb_of_unfold_guard (schedule_focused_fork 1 _ 1
    (fun child : Bool => if child then denote q else denote (.ret ()))
    (by show (denote (.bind (.fork q) _)).unfold = _; rw [denote_fork_bind]; simp))) ?_
  refine sbisim_trans (sb_of_unfold_guard (schedule_focused_ret 2 _ 2 denote_ret_unit_unfold)) ?_
  refine equ_sbisim _ _ (congrArg (fun ts => schedule 2 ts none) ?_)
  simp [Vector.cons]

/-! ## Native whole-pool return -/

/-- Native whole-pool return, with exactly one scheduler step per newly selected source slot. An
already focused slot does not need selection. -/
theorem run_nd_pool_returns (n : Nat) (focus : Option (Fin n)) (s : SSig) :
    run_nd_pool (Vector.replicate n (.ret ())) focus s ~
      Nat.repeat CTree.step (match focus with | none => n | some _ => n.pred)
        (pure (⟨⟩, s) : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) :=
  interp_schedule_nd_returns sh n _ focus s fun _ =>
    ⟨0, by simp [csl_pool, denote, denote_flow]⟩

/-- Native whole-pool return logs each selected slot at its actual shrinking pool size, starting
from the initial RR cursor. -/
theorem run_rr_pool_returns (n : Nat) (focus : Option (Fin n)) (cursor : Nat) (s : SSig) :
    run_rr_pool (Vector.replicate n (.ret ())) focus cursor s ~
      emit_list ((rr_return_picks (match focus with | none => n | some _ => n.pred) cursor).map
          (Sum.inr : Nat → CSLObs (Nat × Nat) ⊕ Nat))
        (pure (⟨⟩, s) : ctreeW (CSLObs (Nat × Nat) ⊕ Nat) Bn (PUnit × SSig)) :=
  interp_schedule_rr_returns sh n _ focus cursor s fun _ =>
    ⟨0, by simp [csl_pool, denote, denote_flow]⟩

end CoCSL
