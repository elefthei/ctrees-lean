/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.Asep
public import Lang.CoCSL.Owned
public import Examples.CSL.Frame.Shared

/-!
# Active separation: native return regression

A focused parent singleton that has already returned. Its owned runner is the native return of
the joined state, and both lineages reach the empty pool through erased-silent actions only
(← `examples/CSL/Frame/Active.v`, module `NativeReturnRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.NativeReturnRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm CoCSL
open Examples.CSL.Frame.Shared

def cfg : OwnedCfg :=
  init_local_thread .parent (pure ⟨⟩) (region 2 6) [] 1 true

def initial : AsepState := { cfg := cfg, global := .pure, loc := fun _ => .pure }

def empty_cfg : OwnedCfg := set_pool cfg (mk_pool 0 #v[] #v[] none)

theorem cfg_wf : owned_wf cfg :=
  owned_wf_equ _ _
    (project_init_threads_parent (pure ⟨⟩) (pure ⟨⟩) managed_empty (region 2 6) [] 1)
    (owned_wf_project _ _ (init_owned_threads_wf _ _ _ _ _ _ managed_wf_empty
      (managed_wf_preallocated _) ⟨fun _ => .inl rfl, fun _ => .inl rfl⟩))

theorem cfg_erasable : erasable cfg := by
  refine erasable_single_side .parent cfg cfg_wf (fun j => ?_) (fun j => ?_) (fun j => ?_) ?_
  · obtain rfl := fin1_eq j; rfl
  · obtain rfl := fin1_eq j; exact fr_ret _ _
  · obtain rfl := fin1_eq j; exact bf_ret _
  · have E : init_local .parent (.ret ()) (region 2 6) [] 1 true = cfg := by
      simp [init_local, cfg, denote, denote_flow]
    exact E ▸ addr_ok_confined _ _ _ _ _ _ _ trivial

theorem cfg_parent_equ : owned_equ (project .parent cfg) cfg := by
  refine ⟨⟨?_, rfl⟩, fun i => ?_, fun i => ?_, rfl, rfl, fun i => ?_, fun i => ?_⟩
  · rw [Forall2_slot_iff]; show tp_slots (project_pool _ _) = _; rw [tp_slots_project]; rfl
  all_goals cases i <;> first | exact peq_refl _ | rfl

theorem cfg_child_erasable : erasable (project .child cfg) := by
  refine ⟨owned_wf_project _ _ cfg_wf, fun j => j.elim0, fun j => j.elim0, fun d Hd => ?_⟩
  have Hd : d = project .child cfg := by
    induction Hd with
    | refl => rfl
    | tail _ hab ih => obtain ⟨a, Ha⟩ := hab; subst ih; exact (owned_step_empty _ a _ rfl Ha).elim
  subst Hd
  intro t i e k Hf
  nomatch Hf

theorem initial_ok : asep_state_ok initial :=
  ⟨⟨cfg_erasable, cfg_child_erasable,
    erasable_equ _ _ (owned_equ_Equivalence.symm cfg_parent_equ) cfg_erasable⟩,
    .pure, fun _ => .pure⟩

theorem focused_ret_run : owned_interp cfg ~ (pure (⟨⟩, joined_state cfg) : AsepTree) :=
  sbisim_trans (interp_schedule_nd_ret sh 0 #v[pure ⟨⟩] 0 (joined_state cfg) rfl)
    (interp_schedule_nd_empty sh _ _)

theorem focused_ret_not_empty :
    cfg.pool.size = 1 ∧
    entails (Ticl.ret fun (r : PUnit × SSig) w => r = (⟨⟩, joined_state cfg) ∧ w = .pure)
      (owned_interp cfg) .pure :=
  ⟨rfl, (proper_entails_meq _ focused_ret_run).2 (ret_ret .pure (And.intro rfl rfl))⟩

theorem empty_ret_run :
    empty_cfg.pool.size = 0 ∧
    owned_interp empty_cfg ~ (pure (⟨⟩, joined_state empty_cfg) : AsepTree) :=
  ⟨rfl, interp_schedule_nd_empty sh _ _⟩

theorem native_ret_silent_frontier :
    ∃ s', Star asep_silent initial s' ∧ s'.cfg.pool.size = 0 ∧
      owned_interp cfg ~ (pure (⟨⟩, joined_state s'.cfg) : AsepTree) ∧
      s'.global = .pure ∧ ∀ i, s'.loc i = .pure := by
  have HP :
      entails (Ticl.ret fun (_ : PUnit × SSig) _ => True) (owned_interp (project .child cfg))
        .pure ∧
      entails (Ticl.ret fun (_ : PUnit × SSig) _ => True) (owned_interp (project .parent cfg))
        .pure := by
    refine ⟨(proper_entails_meq _ (interp_schedule_nd_empty sh _ _)).2 (ret_ret .pure trivial),
      ?_⟩
    rw [proper_entails_meq _ (owned_interp_equ _ _ cfg_parent_equ),
      proper_entails_meq _ focused_ret_run]
    exact ret_ret .pure trivial
  obtain ⟨s', Hsil, Ew, El, Hz, HE, -⟩ := asep_ret_frontier initial _ _ initial_ok HP
  exact ⟨s', Hsil, Hz, HE, Ew, El⟩

end Examples.CSL.Frame.Active.NativeReturnRegression
