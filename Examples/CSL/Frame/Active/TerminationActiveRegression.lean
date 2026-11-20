/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Shared
public import Lang.CoCSL.Owned
public import Logic.Sep.Asep
public import Logic.Congruence

/-!
# Regression: native termination of two active processes

`proc 1` (child) and `proc 2` (parent) each read, increment, write and emit their own cell, yield
once and return. Each lineage's local `AU ret` fact composes through the active separating
conjunction into a global native return with both cells and counter `2` (`both_af_final_cells`).
A concrete owned execution in which the parent finishes first shows the parent's obligation
becoming a native return while the child is still live (`early_until_ret`)
(← `examples/CSL/Frame/Active.v`, module `TerminationActiveRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.TerminationActiveRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared

def cfg : OwnedCfg := init_owned (proc 1) (proc 2) (region 1 3) (region 2 5) [] 0

def initial : AsepState := { cfg := cfg, global := .pure, loc := fun _ => .pure }

/-- Lineage `i` returns with its incremented cell, an empty context, one emission and the emission
as its last world. -/
def local_post (i value : Nat) : Unit × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop :=
  fun r w => csl_memory r.2 ≈ region i value ∧ csl_context r.2 = [] ∧ csl_counter r.2 = 1 ∧
    w = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (i, value) 0)) ⟨⟩

def RC := local_post 1 4

def RP := local_post 2 6

def live : ctreeW (CSLObs (Nat × Nat)) Bn (Unit × SSig) →
    World (writerE (CSLObs (Nat × Nat))) → Prop :=
  entails (.now fun _ => True : TiclL (writerE (CSLObs (Nat × Nat))))

theorem admitted : admissible (proc 1) (proc 2) (region 1 3) (region 2 5) [] 0 :=
  admissible_regions _ _ _ _ _ _ _ _ (by decide)
    (by simp [component_ok, prog_ok, proc, work, okE_thread, okE_lift, component_event_ok])
    (by simp [component_ok, prog_ok, proc, work, okE_thread, okE_lift, component_event_ok])
    (by simp [addr_ok, proc, work, region, hsingle])
    (by simp [addr_ok, proc, work, region, hsingle])

theorem initial_ok : asep_state_ok initial :=
  ⟨admissible_active_erasable _ _ _ _ _ _ admitted, .pure, fun _ => .pure⟩

theorem focused_proc_af (i a : Nat) (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    entails (.cu .A (.now fun _ => True) (.ret (local_post i (a + 1))))
      (interp_schedule_nd sh 1 #v[denote (proc i)] (some 0) (own i a [] 0)) w := by
  intro Hw
  show entails _ (interp_schedule_nd sh (0 + 1) ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
    (denote_flow (.bind (work i) fun _ => .bind .yield fun _ => .ret ()) >>= fun _ => pure ⟨⟩))
    (some 0) (own i a [] 0)) w
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (run_nd_prefix 0 _ 0 _ _ _ (work_yield_fork_free i))).2 ?_
  refine u_bind_r (q := .A) (work_af_ret i a [] 0 w Hw) ?_
  rintro ⟨r, s⟩ w' ⟨rfl, Hm, Haux, rfl⟩
  dsimp only
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 0 _ s)).2 ?_
  refine (au_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).1 (.inr ⟨⟨trivial, .obs _ _⟩, fun j => ?_⟩)
  refine (fun i => ?_ : ∀ i : Fin 1, entails _ (interp_schedule_nd sh _ _ (some i) s) _) _
  obtain rfl := fin1_eq i
  refine (proper_entails_meq _ (interp_schedule_nd_ret sh 0 _ 0 s (by simp [denote_flow]))).2 ?_
  refine (proper_entails_meq _ (interp_schedule_nd_empty sh _ s)).2 ?_
  exact .matchA (ret_ret (.obs _ _) ⟨Hm, congrArg Prod.fst Haux, congrArg Prod.snd Haux, rfl⟩)

theorem singleton_state (i : Side) (p : CProg Unit) (h : ManagedHeap) (focused : Bool) :
    joined_state (init_local i p h [] 0 focused) = (h, ([], 0)) := by
  cases i
  · exact Prod.ext (managed_heap_ext _ _ (pop_emp_r h (pdef_emp_r h))) rfl
  · exact Prod.ext (managed_heap_ext _ _ (pop_emp h)) rfl

theorem local_proc_af (i a : Nat) (tag : Side) (focused : Bool) :
    entails (.cu .A (.now fun _ => True) (.ret (local_post i (a + 1))))
      (owned_interp (init_local tag (proc i) (region i a) [] 0 focused)) .pure := by
  rw [owned_interp, singleton_state]
  show entails _ (interp_schedule_nd sh 1 #v[denote (proc i)]
    (if focused then some 0 else none) (own i a [] 0)) .pure
  cases focused
  · refine (proper_entails_meq _ (interp_schedule_nd_select sh 0 _ _)).2 ?_
    refine (au_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).1 (.inr ⟨⟨trivial, .pure⟩, fun j => ?_⟩)
    refine (fun i => ?_ : ∀ i : Fin 1, entails _ (interp_schedule_nd sh _ _ (some i) _) _) _
    obtain rfl := fin1_eq i
    exact focused_proc_af _ _ _ .pure
  · exact focused_proc_af _ _ _ .pure

theorem local_returns :
    entails (.cu .A (.now fun _ => True) (.ret RC)) (owned_interp (project .child cfg)) .pure ∧
    entails (.cu .A (.now fun _ => True) (.ret RP)) (owned_interp (project .parent cfg)) .pure :=
  ⟨(proper_entails_meq _ (owned_interp_equ _ _ (project_init_child _ _ _ _ _ _))).2
      (local_proc_af 1 3 _ _),
    (proper_entails_meq _ (owned_interp_equ _ _ (project_init_parent _ _ _ _ _ _))).2
      (local_proc_af 2 5 _ _)⟩

def base_inv (s : AsepState) : Prop := s.cfg.base = 0

def termination_inv (s : AsepState) : Prop :=
  asep_at base_inv
    (entails (.cu .A (.now fun _ => True) (.ret RC)))
    (entails (.cu .A (.now fun _ => True) (.ret RP))) s

theorem base_inv_closed : asep_closed base_inv :=
  fun _ _ _ _ Hbase Hstep => (owned_step_frozen _ _ _ Hstep.1).2.2.trans Hbase

theorem termination_inv_init : termination_inv initial :=
  asep_at_intro _ _ _ _ initial_ok rfl local_returns.1 local_returns.2

theorem termination_inv_closed : asep_closed termination_inv :=
  fun s a s' _ Hinv Hstep => asep_at_auc_ret_step base_inv live live RC RP s a s'
    base_inv_closed (asep_pred_ok_entails _) (asep_pred_ok_entails _) Hinv Hstep

theorem both_af_ret :
    entails (.cu .A (.now fun _ => True) (.ret (asep_ret base_inv RC RP)))
      (owned_interp cfg) .pure :=
  asep_af_ret_compose _ _ _ _ _ base_inv_closed
    (asep_sat_intro _ _ _ initial termination_inv_init)

theorem both_ef_ret :
    entails (.cu .E (.now fun _ => True) (.ret (asep_ret base_inv RC RP)))
      (owned_interp cfg) .pure := by
  obtain ⟨Hok, -, Hbase, HC, HP⟩ := asep_at_inv _ _ _ _ termination_inv_init
  exact asep_ef_ret_compose _ _ _ _ _ base_inv_closed (asep_sat_intro _ _ _ initial
    (asep_at_intro _ _ _ _ Hok Hbase (ticl_au_eu (p := .now fun _ => True) (r := .ret RC) HC)
      (ticl_au_eu (p := .now fun _ => True) (r := .ret RP) HP)))

theorem final_state (r : Unit × SSig) (w : World (writerE (CSLObs (Nat × Nat)))) :
    asep_ret base_inv RC RP r w →
    (csl_memory r.2).1 1 = some 4 ∧ (csl_memory r.2).1 2 = some 6 ∧
      csl_context r.2 = [] ∧ csl_counter r.2 = 2 := by
  obtain ⟨⟨⟩, st⟩ := r
  intro Hret
  obtain ⟨s, -, Hbase, -, -, rfl, -, ⟨HC, Hctx, HcountC, -⟩, ⟨HP, -, HcountP, -⟩⟩ :=
    asep_ret_elim base_inv RC RP st w Hret
  have Hm : both 4 6 (joined_heap s.cfg) := pop_resp _ _ _ _ HC HP
  obtain ⟨H1, H2⟩ := both_lookup 4 6 _ Hm
  refine ⟨H1, H2, Hctx, ?_⟩
  simp only [base_inv] at Hbase
  simp only [csl_counter, local_state] at HcountC HcountP
  simp only [csl_counter, joined_state, global_count]
  omega

def final_cells : Unit × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop :=
  fun r _ => (csl_memory r.2).1 1 = some 4 ∧ (csl_memory r.2).1 2 = some 6 ∧
    csl_context r.2 = [] ∧ csl_counter r.2 = 2

theorem both_af_final_cells :
    entails (.cu .A (.now fun _ => True) (.ret final_cells)) (owned_interp cfg) .pure :=
  aur_ret_mono _ _ _ _ _ (fun r w H => final_state r w H) both_af_ret

theorem both_ef_final_cells :
    entails (.cu .E (.now fun _ => True) (.ret final_cells)) (owned_interp cfg) .pure :=
  impl_ticl_until .E (fun _ _ H => H) (ret_impl_ticl _ _ fun r w H => final_state r w H) _ _
    both_ef_ret

/-! ## A parent-first owned execution

The script `[1]` selects the parent after its yield. The following configurations record those
machine actions, then remove its native return. -/

def tY : Thread sE Bn := .vis (E := CEff) (.inl ⟨⟩) fun _ => pure ⟨⟩

def tE : Thread sE Bn := .vis (E := CEff) (.inr (.inr (.inr (.inr (2, 6))))) fun _ => tY

def tW (v : Nat) : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inl (.write 2 v)))) fun _ =>
    .vis (E := CEff) (.inr (.inr (.inr (.inr (2, v))))) fun _ => tY

def c1 : OwnedCfg :=
  set_pool cfg (mk_pool 2 #v[denote (proc 1), tW 6] #v[.child, .parent] (some 1))

def c2 : OwnedCfg :=
  set_pool (set_heap c1 .parent (upd (region 2 5).1 2 6, (region 2 5).2))
    (mk_pool 2 #v[denote (proc 1), tE] #v[.child, .parent] (some 1))

def c3 : OwnedCfg :=
  set_pool (emit_cfg c2 .parent (2, 6))
    (mk_pool 2 #v[denote (proc 1), tY] #v[.child, .parent] (some 1))

def c4 : OwnedCfg :=
  set_pool c3 (mk_pool 2 #v[denote (proc 1), pure ⟨⟩] #v[.child, .parent] none)

def c5 : OwnedCfg :=
  set_pool c4 (mk_pool 2 #v[denote (proc 1), pure ⟨⟩] #v[.child, .parent] (some 1))

def c6 : OwnedCfg := set_pool c5 (mk_pool 1 #v[denote (proc 1)] #v[.child] none)

theorem proc_parent_head :
    denote (proc 2) =
      .vis (E := CEff) (.inr (.inr (.inl (.read 2)))) fun (v : Nat) => tW (v + 1) := by
  simp only [denote, proc, work, source_raw_bind, source_raw_read_head, source_raw_write_head,
    source_raw_emit_head, source_raw_yield_head, source_raw_ret, tW, tY]

theorem step01 : owned_step cfg (act .parent .read) c1 :=
  .inr (.inr (.inr (.inr ⟨.inl (.read 2), fun (v : Nat) => tW (v + 1), .read, (5 : Nat), cfg,
    ⟨0, proc_parent_head⟩, rfl, rfl, rfl⟩)))

theorem step12 : owned_step c1 (act .parent .write) c2 :=
  .inr (.inr (.inr (.inr ⟨.inl (.write 2 6), fun _ => tE, .write, ⟨⟩,
    set_heap c1 .parent (upd (region 2 5).1 2 6, (region 2 5).2), ⟨0, rfl⟩, rfl, rfl, rfl⟩)))

theorem step23 : owned_step c2 (act .parent (.emit (2, 6) 0)) c3 :=
  .inr (.inr (.inr (.inr ⟨.inr (.inr (2, 6)), fun _ => tY, .emit (2, 6) 0, ⟨⟩,
    emit_cfg c2 .parent (2, 6), ⟨0, rfl⟩, rfl, rfl, rfl⟩)))

theorem step34 : owned_step c3 (act .parent .yield) c4 :=
  .inr (.inl ⟨fun _ => pure ⟨⟩, ⟨0, rfl⟩, rfl, rfl⟩)

theorem step45 : owned_step c4 (act .parent .select) c5 := ⟨1, rfl, rfl⟩

theorem step56 : owned_step c5 (act .parent .ret) c6 :=
  .inr (.inr (.inr (.inl ⟨⟨0, rfl⟩, rfl, by
    unfold c6; congr 2 <;> exact Vector.ext fun i hi => by
      match i, hi with | 0, _ => simp⟩)))

def early1 : AsepState := asep_advance initial (act .parent .read) c1
def early2 : AsepState := asep_advance early1 (act .parent .write) c2
def early3 : AsepState := asep_advance early2 (act .parent (.emit (2, 6) 0)) c3
def early4 : AsepState := asep_advance early3 (act .parent .yield) c4
def early5 : AsepState := asep_advance early4 (act .parent .select) c5
def early6 : AsepState := asep_advance early5 (act .parent .ret) c6

theorem early_steps :
    asep_step initial (act .parent .read) early1 ∧
    asep_step early1 (act .parent .write) early2 ∧
    asep_step early2 (act .parent (.emit (2, 6) 0)) early3 ∧
    asep_step early3 (act .parent .yield) early4 ∧
    asep_step early4 (act .parent .select) early5 ∧
    asep_step early5 (act .parent .ret) early6 :=
  ⟨⟨step01, rfl⟩, ⟨step12, rfl⟩, ⟨step23, rfl⟩, ⟨step34, rfl⟩, ⟨step45, rfl⟩, ⟨step56, rfl⟩⟩

theorem early_termination_inv : termination_inv early6 := by
  obtain ⟨H01, H12, H23, H34, H45, H56⟩ := early_steps
  have Hok1 := asep_state_ok_step _ _ _ initial_ok H01
  have HI1 := termination_inv_closed _ _ _ initial_ok termination_inv_init H01
  have Hok2 := asep_state_ok_step _ _ _ Hok1 H12
  have HI2 := termination_inv_closed _ _ _ Hok1 HI1 H12
  have Hok3 := asep_state_ok_step _ _ _ Hok2 H23
  have HI3 := termination_inv_closed _ _ _ Hok2 HI2 H23
  have Hok4 := asep_state_ok_step _ _ _ Hok3 H34
  have HI4 := termination_inv_closed _ _ _ Hok3 HI3 H34
  have Hok5 := asep_state_ok_step _ _ _ Hok4 H45
  have HI5 := termination_inv_closed _ _ _ Hok4 HI4 H45
  exact termination_inv_closed _ _ _ Hok5 HI5 H56

theorem early_worlds :
    early6.global = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (2, 6) 0)) ⟨⟩ ∧
    early6.loc .parent =
      .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (2, 6) 0)) ⟨⟩ ∧
    early6.loc .child = .pure ∧ early6.cfg.pool.size = 1 ∧ early6.cfg.pool.focus = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem early_child_af :
    Auc live (entails (.ret RC)) (owned_interp (project .child early6.cfg)) (early6.loc .child) :=
  (asep_at_inv _ _ _ _ early_termination_inv).2.2.2.1

theorem early_parent_ret :
    entails (.ret RP) (owned_interp (project .parent early6.cfg)) (early6.loc .parent) := by
  obtain ⟨Hok, -, -, -, HP⟩ := asep_at_inv _ _ _ _ early_termination_inv
  exact asep_auc_ret_empty _ live _ _ Hok.1.2.2 rfl (asep_pred_ok_entails _) HP

/-- The completed side needs no live guard: this one is deliberately false. -/
def finished_guard : ctreeW (CSLObs (Nat × Nat)) Bn (Unit × SSig) →
    World (writerE (CSLObs (Nat × Nat))) → Prop := fun _ _ => False

theorem finished_guard_ok : asep_pred_ok finished_guard :=
  ⟨fun _ _ H => H.elim, fun _ _ => Iff.rfl⟩

def early_inv (s : AsepState) : Prop :=
  asep_at base_inv (entails (.cu .A (.now fun _ => True) (.ret RC))) (entails (.ret RP)) s

theorem early_inv_init : early_inv early6 := by
  obtain ⟨Hok, -, Hbase, -, -⟩ := asep_at_inv _ _ _ _ early_termination_inv
  exact asep_at_intro _ _ _ _ Hok Hbase early_child_af early_parent_ret

theorem early_inv_closed : asep_closed early_inv := by
  intro s a s' Hok Hinv Hstep
  obtain ⟨-, -, Hbase, HC, HP⟩ := asep_at_inv _ _ _ _ Hinv
  have Hlocal : asep_at base_inv (Auc live (entails (.ret RC)))
      (Auc finished_guard (entails (.ret RP))) s :=
    asep_at_intro _ _ _ _ Hok Hbase HC (.matchA HP)
  obtain ⟨Hok', -, Hbase', HC', HP'⟩ := asep_at_inv _ _ _ _
    (asep_at_auc_ret_step base_inv live finished_guard RC RP s a s' base_inv_closed
      (asep_pred_ok_entails _) finished_guard_ok Hlocal Hstep)
  refine asep_at_intro _ _ _ _ Hok' Hbase' HC' ?_
  cases HP' with
  | matchA HR => exact HR
  | stepA HF _ _ => exact HF.elim

theorem early_parent_return_phase : asep_until_guard base_inv live finished_guard RC RP
    (owned_interp early6.cfg) early6.global := by
  obtain ⟨Hok, -, Hbase, HC, HP⟩ := asep_at_inv _ _ _ _ early_inv_init
  exact .inr (.inr (asep_sat_intro _ _ _ early6
    (asep_at_intro _ _ _ _ Hok Hbase ⟨trivial, ticl_not_done _ HC⟩ HP)))

theorem early_not_live_live :
    ¬ asep_sat base_inv live finished_guard (owned_interp early6.cfg) early6.global := by
  intro Hsat
  obtain ⟨_, _, _, _, _, _, _, HP⟩ := asep_sat_inv _ _ _ _ _ Hsat
  exact HP

theorem early_until_ret :
    Auc (asep_until_guard base_inv live finished_guard RC RP)
      (entails (.ret (asep_ret base_inv RC RP))) (owned_interp early6.cfg) early6.global := by
  obtain ⟨Hok, -, Hbase, HC, HP⟩ := asep_at_inv _ _ _ _ early_inv_init
  exact asep_auc_ret_compose _ _ _ _ _ _ _ base_inv_closed (asep_pred_ok_entails _)
    finished_guard_ok
    (asep_sat_intro _ _ _ early6 (asep_at_intro _ _ _ _ Hok Hbase HC (.matchA HP)))

end Examples.CSL.Frame.Active.TerminationActiveRegression
