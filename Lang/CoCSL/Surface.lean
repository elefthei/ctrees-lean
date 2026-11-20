/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.RunnersFair
public import Logic.Yield.Observed
public import Logic.Yield.SBisimSchedule
public import Logic.CTree.SchedulerFairness
public import Logic.CTree.Bind
public import Logic.CTree.TraceRules

/-!
# CoCSL loop examples and structural surface

Actual-observation loops sustain `AG`, guard-only divergence does not; the scheduler-visible,
erased-thread and observed-scheduler views of a source program; constructor equations of the
denotation; expression, singleton-scheduler, flow-preserving statement and raw `while` rules
(← `Lang/CoCSL/Mod.v`, lines 11740-12441).
-/

@[expose] public section
namespace CoCSL
open CTree Coinduction Tisl Tisl.CSL Tisl.Yield Tisl.Heap Tisl.Ctx Tisl.Notation
open ITree (Effect)

/-! ## Source loops: actual observations sustain AG; guard-only divergence does not -/

/-- The emitting loop body, one emission per iteration. -/
private theorem denote_emit_loop (tag value : Nat) :
    denote (.untilNone (.bind (.emit tag value) fun _ => .ret (some ()))) =
      (denote_flow (.emit tag value) >>= fun _ =>
        .guard (denote (.untilNone (.bind (.emit tag value) fun _ => .ret (some ()))))) := by
  show denote_flow _ >>= _ = _
  rw [source_raw_until, source_raw_bind, source_raw_emit_head, source_raw_emit_head]
  simp only [source_raw_ret]
  rfl

theorem run_nd_emit_loop_ag (tag value : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World (writerE (CSLObs (Nat × Nat)))) :
    NotDone w →
    entails (AG ⊤)
      (run_nd (.untilNone (.bind (.emit tag value) fun _ => .ret (some ()))) (memory, (ctx, c)))
      w := by
  refine ag_log_family (fun c => run_nd _ (memory, (ctx, c))) (· + 1)
    (fun c => CSLObs.emit (stamp (tag, value) c)) (fun c => ?_) c w
  simp only [run_nd_unfold]
  rw (occs := .pos [1]) [denote_emit_loop]
  refine sbisim_trans (interp_nd_source_emit_log 0 #v[pure ⟨⟩] 0 tag value _ memory ctx c) ?_
  simp only [log, vis_bind, pure_bind']
  refine sbisim_vis_id _ _ _ fun _ => ⟨sbisim_trans (interp_schedule_nd_guard sh 0
    (#v[pure ⟨⟩].set 0 (.guard (denote (.untilNone (.bind (.emit tag value) fun _ =>
      .ret (some ())))))) 0 (denote (.untilNone (.bind (.emit tag value) fun _ =>
      .ret (some ())))) _ rfl) ?_, rfl⟩
  exact sbisim_refl _

theorem run_rr_emit_loop_ag (tag value : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat)
    (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    NotDone w →
    entails (AG ⊤)
      (run_rr (.untilNone (.bind (.emit tag value) fun _ => .ret (some ()))) (memory, (ctx, c)))
      w := by
  refine ag_log_family (fun c => run_rr _ (memory, (ctx, c))) (· + 1)
    (fun c => .inl (CSLObs.emit (stamp (tag, value) c))) (fun c => ?_) c w
  simp only [run_rr_unfold]
  rw (occs := .pos [1]) [denote_emit_loop]
  refine sbisim_trans (interp_rr_emit_log 0 #v[pure ⟨⟩] 0 tag value _ 0 memory ctx c) ?_
  simp only [log, vis_bind, pure_bind']
  refine sbisim_vis_id _ _ _ fun _ => ⟨sbisim_trans (interp_schedule_fair_guard rr_scheduler sh 0
    (#v[pure ⟨⟩].set 0 (.guard (denote (.untilNone (.bind (.emit tag value) fun _ =>
      .ret (some ())))))) 0 (denote (.untilNone (.bind (.emit tag value) fun _ =>
      .ret (some ())))) _ _ rfl) ?_, rfl⟩
  exact sbisim_refl _

/-- The silent loop is its own guard. -/
private theorem denote_silent_loop :
    denote (.untilNone (.ret (some ()))) = .guard (denote (.untilNone (.ret (some ())))) := by
  show denote_flow _ >>= _ = _
  rw [source_raw_until, source_raw_ret]
  rfl

/-- The silent loop starts focused, so the whole run is raw-equivalent to its own guard and hence
to `spin`; no scheduler tau is erased. -/
theorem run_nd_silent_loop_no_ag (s : SSig) (w : World (writerE (CSLObs (Nat × Nat)))) :
    ¬ entails (AG ⊤) (run_nd (.untilNone (.ret (some ()))) s) w := by
  refine guard_fixed_no_ag _ w _ ?_
  have hs : schedule 1 #v[denote (.untilNone (.ret (some ())))] (some 0) =
      .guard (schedule 1 #v[denote (.untilNone (.ret (some ())))] (some 0)) :=
    unfold_inj (by
      rw [schedule_focused_guard 0 _ 0 _ (congrArg CTree.unfold denote_silent_loop),
        unfold_guard]
      rfl)
  rw [run_nd_unfold, interp_schedule_nd]
  conv => lhs; rw [hs, project_scheduled_guard, interp_state_guard]

theorem run_rr_silent_loop_no_ag (s : SSig) (w : World (writerE (CSLObs (Nat × Nat) ⊕ Nat))) :
    ¬ entails (AG ⊤) (run_rr (.untilNone (.ret (some ()))) s) w := by
  refine guard_fixed_no_ag _ w _ ?_
  rw [run_rr_unfold]
  exact interp_schedule_fair_guard_exact rr_scheduler sh 0 _ 0 _ _ s
    (congrArg CTree.unfold denote_silent_loop)

/-! ## Yield-language structural surface

The Yield-style expression and control fragment of `CProg` is reasoned about through three
views, all built from the generic eraser and state interpreter:
- `scheduled_visible`: the scheduled program with scheduler `Scheduled` observations and user
  effects visible;
- `instr_exp_erased`/`instr_flow_erased`: a standalone erased thread run through `sh`, exposing
  the outer option flow;
- `run_nd`: the erased nondeterministic singleton schedule. -/

def scheduled_visible (p : CProg Unit) : Completed sE Bn :=
  schedule 1 #v[denote p] (some 0)

def instr_exp_erased (e : CExp) (s : SSig) : ctreeW (CSLObs (Nat × Nat)) Bn (Nat × SSig) :=
  interp_state sh (interp_thread (denote_exp e)) s

def instr_flow_erased {A : Type} (p : CProg A) (s : SSig) :
    ctreeW (CSLObs (Nat × Nat)) Bn (Option A × SSig) :=
  interp_state sh (interp_thread (denote_flow p)) s

/-! ### Constructor unfold equations -/

theorem denote_exp_cvar (name : String) :
    denote_exp (.var name) =
      (source_get >>= fun ctx =>
        match Ctx.lookup name ctx with
        | some value => source_yield >>= fun _ => pure value
        | none => .stuck) := by
  rw [denote_exp]; rfl

theorem denote_exp_clit (n : Nat) : denote_exp (.lit n) = pure n := by
  rw [denote_exp]

theorem denote_exp_cplus (a b : CExp) :
    denote_exp (.plus a b) =
      (denote_exp a >>= fun x => denote_exp b >>= fun y => pure (x + y)) := by
  rw [denote_exp]

theorem denote_exp_cminus (a b : CExp) :
    denote_exp (.minus a b) =
      (denote_exp a >>= fun x => denote_exp b >>= fun y => pure (x - y)) := by
  rw [denote_exp]

theorem denote_exp_cmult (a b : CExp) :
    denote_exp (.mult a b) =
      (denote_exp a >>= fun x => denote_exp b >>= fun y => pure (x * y)) := by
  rw [denote_exp]

theorem denote_unfold (p : CProg Unit) : denote p = (denote_flow p >>= fun _ => pure ⟨⟩) := rfl

theorem denote_flow_cassign (name : String) (e : CExp) :
    denote_flow (.assign name e) =
      (denote_exp e >>= fun value =>
        source_get >>= fun ctx =>
        source_put (Ctx.add name value ctx) >>= fun _ =>
        pure (some ())) := by
  rw [denote_flow]

theorem denote_flow_cbind_unit (a b : CProg Unit) :
    denote_flow (.bind a fun _ => b) =
      (denote_flow a >>= fun flow =>
        match flow with
        | none => pure none
        | some _ => denote_flow b) := by
  rw [denote_flow]
  congr 1; funext flow
  cases flow <;> rfl

theorem denote_flow_cif {A : Type} (test : CExp) (yes no : CProg A) :
    denote_flow (.ite test yes no) =
      (denote_exp test >>= fun value =>
        if is_true value then denote_flow yes else denote_flow no) := by
  rw [denote_flow]

theorem denote_flow_cret_unit : denote_flow (.ret ()) = pure (some ()) := by
  rw [denote_flow]

theorem denote_flow_cyield : denote_flow .yield = (source_yield >>= fun _ => pure (some ())) := by
  rw [denote_flow]

/-- Rocq `≅` congruence, kept by name for clients. -/
theorem denote_flow_bind_equ {A B : Type} (p q : CProg A) (next next' : A → CProg B) :
    denote_flow p = denote_flow q → (∀ a, denote_flow (next a) = denote_flow (next' a)) →
    denote_flow (.bind p next) = denote_flow (.bind q next') := by
  intro hp hn
  rw [denote_flow, denote_flow, hp]
  congr 1; funext flow
  cases flow
  · rfl
  · exact hn _

theorem denote_flow_fork_equ (p q : CProg Unit) :
    denote_flow p = denote_flow q → denote_flow (.fork p) = denote_flow (.fork q) := by
  intro h
  rw [denote_flow, denote_flow, h]

theorem denote_equ (p q : CProg Unit) : denote_flow p = denote_flow q → denote p = denote q := by
  intro h; unfold denote; rw [h]

/-! ### Startup normalizations used by the singleton rules -/

theorem source_yield_bind {X : Type} (k : PUnit → CTree CEff Bn X) :
    (source_yield >>= k) = .vis (.inl ⟨⟩) k := by
  simp [source_yield]

theorem denote_ret_unit : denote (.ret ()) = pure ⟨⟩ := by
  simp [denote, denote_flow]

theorem denote_yield_vis : denote .yield = .vis (E := CEff) (.inl ⟨⟩) fun _ => pure ⟨⟩ := by
  simp [denote, denote_flow, source_yield]

theorem denote_assign_lit (name : String) (n : Nat) :
    denote (.assign name (.lit n)) =
      (source_get >>= fun ctx => source_put (Ctx.add name n ctx) >>= fun _ => pure ⟨⟩) := by
  simp [denote, denote_flow, denote_exp]

/-! ### Expression rules -/

theorem axr_csl_exp_lit (n n' : Nat) (s s' : SSig) (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    n = n' → s = s' → w = w' → NotDone w →
    entails (ret= (n', s') w') (instr_exp_erased (.lit n) s) w := by
  rintro rfl rfl rfl hnd
  rw [instr_exp_erased, denote_exp_clit, interp_state_thread_ret]
  exact ret_ret hnd ⟨rfl, rfl⟩

theorem axr_csl_exp_var_some (name : String) (value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    Ctx.lookup name (csl_context s) = some value → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.var name) s) w := by
  rintro hlookup rfl rfl hnd
  rw [instr_exp_erased, denote_exp_cvar, proper_entails_meq _ (interp_thread_get_ctx _ s)]
  simp only [hlookup, source_yield_bind]
  rw [proper_entails_meq _ (interp_state_thread_yield sh _ s), interp_state_thread_ret]
  exact ret_ret hnd ⟨rfl, rfl⟩

/-- Shared shape of the binary expression rules. -/
private theorem axr_csl_exp_binop (a b : CExp) (op : Nat → Nat → Nat) (x y : Nat) (s : SSig)
    (w : World (writerE (CSLObs (Nat × Nat))))
    (ha : entails (ret= (x, s) w) (instr_exp_erased a s) w)
    (hb : entails (ret= (y, s) w) (instr_exp_erased b s) w) :
    entails (ret= (op x y, s) w)
      (interp_state sh (interp_thread
        (denote_exp a >>= fun x => denote_exp b >>= fun y => pure (op x y))) s) w := by
  rw [interp_state_thread_bind]
  refine ticl_bind_ret_eq ha ?_
  dsimp only
  rw [interp_state_thread_bind]
  refine ticl_bind_ret_eq hb ?_
  dsimp only
  rw [interp_state_thread_ret]
  exact ret_ret (ticl_not_done _ ha) ⟨rfl, rfl⟩

theorem axr_csl_exp_plus (a b : CExp) (x y value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    entails (ret= (x, s) w) (instr_exp_erased a s) w →
    entails (ret= (y, s) w) (instr_exp_erased b s) w →
    value = x + y → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.plus a b) s) w := by
  rintro ha hb rfl rfl rfl -
  exact axr_csl_exp_binop a b (· + ·) x y s w ha hb

theorem axr_csl_exp_minus (a b : CExp) (x y value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    entails (ret= (x, s) w) (instr_exp_erased a s) w →
    entails (ret= (y, s) w) (instr_exp_erased b s) w →
    value = x - y → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.minus a b) s) w := by
  rintro ha hb rfl rfl rfl -
  exact axr_csl_exp_binop a b (· - ·) x y s w ha hb

theorem axr_csl_exp_mult (a b : CExp) (x y value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    entails (ret= (x, s) w) (instr_exp_erased a s) w →
    entails (ret= (y, s) w) (instr_exp_erased b s) w →
    value = x * y → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.mult a b) s) w := by
  rintro ha hb rfl rfl rfl -
  exact axr_csl_exp_binop a b (· * ·) x y s w ha hb

theorem axr_csl_exp_plus_lit_lit (x y value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    value = x + y → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.plus (.lit x) (.lit y)) s) w := by
  rintro rfl rfl rfl hnd
  exact axr_csl_exp_plus _ _ x y _ s s w w (axr_csl_exp_lit x x s s w w rfl rfl rfl hnd)
    (axr_csl_exp_lit y y s s w w rfl rfl rfl hnd) rfl rfl rfl hnd

theorem axr_csl_exp_minus_lit_lit (x y value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    value = x - y → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.minus (.lit x) (.lit y)) s) w := by
  rintro rfl rfl rfl hnd
  exact axr_csl_exp_minus _ _ x y _ s s w w (axr_csl_exp_lit x x s s w w rfl rfl rfl hnd)
    (axr_csl_exp_lit y y s s w w rfl rfl rfl hnd) rfl rfl rfl hnd

theorem axr_csl_exp_mult_lit_lit (x y value : Nat) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    value = x * y → s = s' → w = w' → NotDone w →
    entails (ret= (value, s') w') (instr_exp_erased (.mult (.lit x) (.lit y)) s) w := by
  rintro rfl rfl rfl hnd
  exact axr_csl_exp_mult _ _ x y _ s s w w (axr_csl_exp_lit x x s s w w rfl rfl rfl hnd)
    (axr_csl_exp_lit y y s s w w rfl rfl rfl hnd) rfl rfl rfl hnd

/-- The matching case of `AU`. -/
private theorem auc_here {E B : Effect.{0}} {X : Type} {i : Option Type} {φ : TiclL E}
    {ψ : Ticl E i} {t : CTree E B X} {w : World E} (h : entails ψ t w) :
    entails (.cu .A φ ψ) t w :=
  Auc.matchA h

/-- One log step, then the `AU` endpoint. -/
private theorem auc_log_here {W X : Type} {i : Option Type} {φ : TiclL (writerE W)}
    {ψ : Ticl (writerE W) i} {e : W} {k : PUnit → ctreeW W Bn X} {w : World (writerE W)}
    (hφ : entails φ (CTree.vis (E := writerE W) e k) w)
    (hψ : entails ψ (k ⟨⟩) (.obs (E := writerE W) e ⟨⟩)) :
    entails (.cu .A φ ψ) (CTree.vis (E := writerE W) e k) w :=
  Auc.stepA hφ ((can_step_vis PUnit.unit).2 (ticl_not_done φ hφ)) fun t' w' tr => by
    obtain ⟨⟨⟩, rfl, rfl, -⟩ := ktrans_vis.1 tr
    exact Auc.matchA hψ

/-! ### Scheduled singleton rules (nondeterministic scheduler) -/

/-- A finished singleton pool returns with its state. -/
private theorem run_nd_singleton_ret (s : SSig) :
    interp_schedule_nd sh 1 #v[(pure ⟨⟩ : Thread sE Bn)] (some 0) s ~
      (pure (⟨⟩, s) : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) :=
  sbisim_trans (interp_schedule_nd_ret sh 0 _ 0 s rfl) (interp_schedule_nd_empty sh _ s)

theorem axr_csl_nd_skip (s s' : SSig) (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    s = s' → w = w' → NotDone w →
    entails (ret= ((⟨⟩ : PUnit), s') w') (run_nd (.ret ()) s) w := by
  rintro rfl rfl hnd
  rw [run_nd_unfold, denote_ret_unit, proper_entails_meq _ (run_nd_singleton_ret s)]
  exact ret_ret hnd ⟨rfl, rfl⟩

/-- The `AX ret` count is specific to the nondeterministic scheduler: its scheduling point is a
real branch, whereas round robin selects deterministically. -/
theorem axr_csl_nd_yield (s s' : SSig) (w w' : World (writerE (CSLObs (Nat × Nat)))) :
    s = s' → w = w' → NotDone w →
    entails (AX (ret= ((⟨⟩ : PUnit), s') w')) (run_nd .yield s) w := by
  rintro rfl rfl hnd
  obtain ⟨memory, ctx, c⟩ := s
  rw [run_nd_unfold, denote_yield_vis,
    proper_entails_meq _ (interp_schedule_nd_yield sh 0 _ 0 (fun _ => pure ⟨⟩) _ rfl),
    an_csl_nd_select]
  refine ⟨⟨trivial, hnd⟩, fun j => ?_⟩
  rw [fin1_eq j]
  refine (proper_entails_meq _ (run_nd_singleton_ret _)).2 ?_
  exact ret_ret hnd ⟨rfl, rfl⟩

theorem aur_csl_nd_yield_ret (s s' : SSig) (w w' : World (writerE (CSLObs (Nat × Nat))))
    (ψ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    s = s' → w = w' → NotDone w →
    entails (ψ AU AX (ret= ((⟨⟩ : PUnit), s') w')) (run_nd .yield s) w :=
  fun hs hw hnd => auc_here (axr_csl_nd_yield s s' w w' hs hw hnd)

/-! ### Flow-preserving statement rules

The context-update observation is stated on the exact successor tree (one log whose
continuation is the finished program). The endpoint formula is indexed at the instrumented
flow/state result; native-return clients supply `CProg.ret` and prove the final `pure`
premise. -/

theorem au_csl_flow_assign {i : Option Type} (name : String) (expr : CExp) (value : Nat)
    (s : SSig) (w : World (writerE (CSLObs (Nat × Nat))))
    (φ : TiclL (writerE (CSLObs (Nat × Nat)))) (ψ : Ticl (writerE (CSLObs (Nat × Nat))) i) :
    entails (ret= (value, s) w) (instr_exp_erased expr s) w →
    entails φ (CTree.vis (E := writerE (CSLObs (Nat × Nat)))
        (CSLObs.ctx (Ctx.add name value (csl_context s))) fun _ =>
          (pure (some (), csl_set_context s (Ctx.add name value (csl_context s))) :
            ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))) w →
    entails ψ (pure (some (), csl_set_context s (Ctx.add name value (csl_context s))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig))
      (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.ctx (Ctx.add name value (csl_context s)))
        ⟨⟩) →
    entails (.cu .A φ ψ) (instr_flow_erased (.assign name expr) s) w := by
  intro hexp hlog hret
  rw [instr_exp_erased] at hexp
  rw [instr_flow_erased, denote_flow_cassign, interp_state_thread_bind]
  refine u_bind_r_eq (auc_here hexp) ?_
  dsimp only
  rw [proper_entails_meq _ (interp_thread_ctx_update (Ctx.add name value) (some ()) s)]
  simp only [log, vis_bind, pure_bind']
  exact auc_log_here hlog hret

theorem anr_csl_flow_bind_fallthrough (a b : CProg Unit) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) (some (Option Unit × SSig))) :
    entails (ret= (some (), s') w') (instr_flow_erased a s) w →
    entails (φ AN ψ) (instr_flow_erased b s') w' →
    entails (φ AN ψ) (instr_flow_erased (.bind a fun _ => b) s) w := by
  intro ha hb
  rw [instr_flow_erased, denote_flow_cbind_unit, interp_state_thread_bind]
  exact ticl_bind_ret_eq ha hb

theorem au_csl_flow_bind {i : Option Type} (a b : CProg Unit) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) i) :
    entails (φ AU ret= (some (), s') w') (instr_flow_erased a s) w →
    entails (.cu .A φ ψ) (instr_flow_erased b s') w' →
    entails (.cu .A φ ψ) (instr_flow_erased (.bind a fun _ => b) s) w := by
  intro ha hb
  rw [instr_flow_erased, denote_flow_cbind_unit, interp_state_thread_bind]
  exact u_bind_r_eq ha hb

/-- A halted first statement skips the second: the halt flow propagates. -/
theorem aur_csl_flow_bind_halt (a b : CProg Unit) (s s' : SSig)
    (w w' : World (writerE (CSLObs (Nat × Nat)))) (φ : TiclL (writerE (CSLObs (Nat × Nat)))) :
    entails (φ AU ret= ((none : Option Unit), s') w') (instr_flow_erased a s) w → NotDone w' →
    entails (φ AU ret= ((none : Option Unit), s') w')
      (instr_flow_erased (.bind a fun _ => b) s) w := by
  intro ha hnd
  rw [instr_flow_erased, denote_flow_cbind_unit, interp_state_thread_bind]
  refine u_bind_r_eq ha ?_
  dsimp only
  rw [interp_state_thread_ret]
  exact auc_here (ret_ret hnd ⟨rfl, rfl⟩)

theorem au_csl_flow_if {A : Type} {i : Option Type} (test : CExp) (yes no : CProg A)
    (condition : Nat) (s : SSig) (w : World (writerE (CSLObs (Nat × Nat))))
    (φ : TiclL (writerE (CSLObs (Nat × Nat)))) (ψ : Ticl (writerE (CSLObs (Nat × Nat))) i) :
    entails (ret= (condition, s) w) (instr_exp_erased test s) w →
    (if is_true condition then entails (.cu .A φ ψ) (instr_flow_erased yes s) w
     else entails (.cu .A φ ψ) (instr_flow_erased no s) w) →
    entails (.cu .A φ ψ) (instr_flow_erased (.ite test yes no) s) w := by
  intro htest hbranch
  rw [instr_exp_erased] at htest
  rw [instr_flow_erased, denote_flow_cif, interp_state_thread_bind]
  refine u_bind_r_eq (auc_here htest) ?_
  dsimp only
  cases h : is_true condition <;> simp only [h] at hbranch ⊢ <;> exact hbranch

/-! ### Raw source-flow while rules

These are stated over raw `World CEff` events and expose the option flow directly; they make no
claim about scheduled liveness. The shared step rules accept an indexed endpoint; clients
requiring a next step pass their entire `AX` formula as that endpoint. -/

theorem au_csl_raw_while {i : Option Type} (test : CExp) (body : CProg Unit) (condition : Nat)
    (w w' : World CEff) (φ : TiclL CEff) (ψ : Ticl CEff i) :
    entails (φ AU ret= condition w) (denote_exp test) w →
    is_true condition = true →
    entails (φ AU ret= (some ()) w') (denote_flow body) w →
    NotDone w' →
    entails (.cu .A φ ψ) (denote_flow (.while test body)) w' →
    entails (.cu .A φ ψ) (denote_flow (.while test body)) w := by
  intro htest htrue hbody hnd hloop
  rw [denote_flow_cwhile] at hloop ⊢
  refine u_iter_next (fun _ w0 => w0 = w') ?_ fun _ _ h => h ▸ hloop
  rw [cwhile_iteration]
  refine u_bind_r_eq htest ?_
  simp only [htrue, ↓reduceIte]
  refine u_bind_r_eq hbody ?_
  exact auc_here (ret_ret hnd ⟨(), rfl, rfl⟩)

theorem au_csl_raw_while_false {i : Option Type} (test : CExp) (body : CProg Unit)
    (condition : Nat) (w : World CEff) (φ : TiclL CEff) (ψ : Ticl CEff i) :
    entails (φ AU ret= condition w) (denote_exp test) w →
    is_true condition = false →
    entails ψ (pure (some ()) : CTree CEff Bn (Option Unit)) w →
    entails (.cu .A φ ψ) (denote_flow (.while test body)) w := by
  intro htest hfalse hret
  have hnd := ticl_not_done _ htest
  rw [denote_flow_cwhile, unfold_iter]
  refine u_bind_r_eq (r := .inr (some ())) (wr := w) ?_ (auc_here hret)
  rw [cwhile_iteration]
  refine u_bind_r_eq htest ?_
  simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
  exact auc_here (ret_ret hnd ⟨rfl, rfl⟩)

theorem aul_csl_raw_while_halt (test : CExp) (body : CProg Unit) (condition : Nat)
    (w w' : World CEff) (φ ψ : TiclL CEff) :
    entails (φ AU ret= condition w) (denote_exp test) w →
    is_true condition = true →
    entails (φ AU ret= (none : Option Unit) w') (denote_flow body) w →
    NotDone w' →
    entails ψ (pure none : CTree CEff Bn (Option Unit)) w' →
    entails (φ AU ψ) (denote_flow (.while test body)) w := by
  intro htest htrue hbody hnd hret
  rw [denote_flow_cwhile, unfold_iter]
  refine u_bind_r_eq (r := .inr none) (wr := w') ?_ (auc_here hret)
  rw [cwhile_iteration]
  refine u_bind_r_eq htest ?_
  simp only [htrue, ↓reduceIte]
  refine u_bind_r_eq hbody ?_
  exact auc_here (ret_ret hnd ⟨rfl, rfl⟩)

theorem ag_csl_raw_while (test : CExp) (body : CProg Unit) (R : World CEff → Prop)
    (w : World CEff) (φ : TiclL CEff) :
    R w →
    (∀ w, R w →
      entails φ (denote_flow (.while test body)) w ∧
      entails (AX (φ AU .ret fun (lr : Unit ⊕ Option Unit) w' =>
        ∃ i' : Unit, lr = .inl i' ∧ R w')) (cwhile_iteration test body ()) w) →
    entails (AG φ) (denote_flow (.while test body)) w := by
  intro hR hstep
  rw [denote_flow_cwhile]
  refine ag_iter (fun _ w => R w) hR fun i w0 h => ?_
  obtain ⟨hφ, hnext⟩ := hstep w0 h
  rw [denote_flow_cwhile] at hφ
  exact ⟨hφ, hnext⟩

/-- A ranked raw while rule: every iteration either establishes the goal or returns to the loop
head at a smaller natural rank. -/
theorem aul_csl_raw_while_nat (test : CExp) (body : CProg Unit) (Ri : World CEff → Prop)
    (f : World CEff → Nat) (w : World CEff) (φ ψ : TiclL CEff) :
    NotDone w → Ri w →
    (∀ w, NotDone w → Ri w →
      entails (φ AU ψ) (cwhile_iteration test body ()) w ∨
      entails (φ AU .ret fun (lr : Unit ⊕ Option Unit) w' =>
        ∃ i' : Unit, lr = .inl i' ∧ NotDone w' ∧ Ri w' ∧ f w' < f w)
        (cwhile_iteration test body ()) w) →
    entails (φ AU ψ) (denote_flow (.while test body)) w := by
  intro hnd hRi hstep
  rw [denote_flow_cwhile]
  exact u_iter_prefix_nat (fun _ w => Ri w) (fun _ w => f w) hnd hRi fun _ w0 h1 h2 =>
    hstep w0 h1 h2

/-! ### Scheduled assignment rules -/

theorem au_csl_nd_assign_lit {i : Option Type} (name : String) (n : Nat) (s : SSig)
    (w : World (writerE (CSLObs (Nat × Nat)))) (φ : TiclL (writerE (CSLObs (Nat × Nat))))
    (ψ : Ticl (writerE (CSLObs (Nat × Nat))) i) :
    entails φ (CTree.vis (E := writerE (CSLObs (Nat × Nat)))
        (CSLObs.ctx (Ctx.add name n (csl_context s))) fun _ =>
          interp_schedule_nd sh 1 #v[(pure ⟨⟩ : Thread sE Bn)] (some 0)
            (csl_set_context s (Ctx.add name n (csl_context s)))) w →
    entails ψ (pure (⟨⟩, csl_set_context s (Ctx.add name n (csl_context s))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))
      (.obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.ctx (Ctx.add name n (csl_context s)))
        ⟨⟩) →
    entails (.cu .A φ ψ) (run_nd (.assign name (.lit n)) s) w := by
  intro hlog hret
  rw [run_nd_unfold, denote_assign_lit]
  have hsb := sbisim_trans
    (interp_nd_get_ctx 0 #v[(pure ⟨⟩ : Thread sE Bn)] 0
      (fun ctx => source_put (Ctx.add name n ctx) >>= fun _ => pure ⟨⟩) s)
    (interp_nd_put_ctx 0 _ 0 (Ctx.add name n (csl_context s)) (fun _ => pure ⟨⟩) s)
  refine (proper_entails_meq _ hsb).2 ?_
  simp only [log, vis_bind, pure_bind']
  exact auc_log_here hlog ((proper_entails_meq _ (run_nd_singleton_ret _)).2 hret)

/-! ### Scheduler-visible and observed-scheduler bridges -/

theorem sbisim_scheduled_visible (p q : CProg Unit) :
    denote p ~ denote q → scheduled_visible p ~ scheduled_visible q := by
  intro hpq
  refine sbisim_schedule 1 _ _ _ (fun i => ?_) (fun i => ?_) (fun i => ?_) <;> rw [fin1_eq i]
  · exact denote_branchfree p
  · exact denote_branchfree q
  · exact hpq

def scheduled_observed (p : CProg Unit) : observed_completed sE Bn :=
  schedule_with_offers 1 #v[denote p] (some 0)

theorem forget_scheduled_observed_is_scheduled_visible (p : CProg Unit) :
    forget_scheduler_offers (scheduled_observed p) ~ scheduled_visible p :=
  forget_scheduler_offers_preserves_schedule 1 _ _

/-- Conditional on scheduler progress; this is about scheduling-point offers, not fair thread
selection. -/
theorem scheduled_observed_every_live_slot_eventually_offered (p : CProg Unit) :
    SchedulerProgress (scheduled_observed p) .pure →
    agc scheduling_point_offer_obligation (scheduled_observed p) .pure :=
  every_live_slot_is_eventually_offered_at_scheduling_points 1 _ _

-- Not ported: nothing; every declaration of Rocq lines 11740-12441 is ported. Rocq `Local`
-- lemmas `source_yield_bind`, `denote_ret_unit`, `denote_yield_vis` are public here.

end CoCSL
