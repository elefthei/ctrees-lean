/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.OwnedProject

/-!
# Owned machine: erasability and the canonical runner

Erasable configurations, exact guarded heads of the canonical nondeterministic runner
`owned_interp`, primitive reflection on the joined heap, and the correspondence between owned
actions and raw interpreted transitions (← `CTree/Interp/CSL/Owned.v`, lines 2004-3224).
-/

@[expose] public section
namespace Tisl.CSL
open CTree Coinduction Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield
open ITree (Effect)

/-! ## Erasability -/

/-- Admitted, well-formed configurations whose every reachable pending primitive stays in its
owner's reservation. -/
def erasable (c : OwnedCfg) : Prop :=
  owned_wf c ∧ pool_framable component_event_ok c.pool.threads ∧
    pool_branchfree c.pool.threads ∧ ∀ d, Star owned_next c d → head_confined d

/-- A single lineage's fixed confinement certificate covers every reachable pending primitive,
including accesses that would fail. -/
theorem erasable_single_side (i : Side) (c : OwnedCfg) (W : owned_wf c)
    (Hi : ∀ j : Fin c.pool.size, c.pool.tags[j] = i)
    (F : pool_framable component_event_ok c.pool.threads) (Bf : pool_branchfree c.pool.threads)
    (Cf : confined (c.anchor i) c) : erasable c := by
  refine ⟨W, F, Bf, fun d Hd => ?_⟩
  have Hinv : (∀ j : Fin d.pool.size, d.pool.tags[j] = i) ∧ d.anchor = c.anchor := by
    induction Hd with
    | refl => exact ⟨Hi, rfl⟩
    | tail _ hab ih =>
      obtain ⟨a, Ha⟩ := hab
      exact ⟨owned_step_single_side i _ a _ ih.1 Ha, (owned_step_frozen _ a _ Ha).1.trans ih.2⟩
  intro t j e k Hf Hh
  have Hji : j = i := by
    unfold focused_thread at Hf
    rcases hq : d.pool.focus with _ | q <;> rw [hq] at Hf
    · cases Hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at Hf
      rw [← Hf.2]; exact Hinv.1 q
  subst Hji
  rw [Hinv.2]
  exact Cf d Hd t j e k Hf Hh

/-! ## Exact canonical runner heads, guards kept -/

/-- The canonical nondeterministic runner on the joined state. -/
def owned_interp (c : OwnedCfg) : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig) :=
  interp_schedule_nd sh c.pool.size c.pool.threads c.pool.focus (joined_state c)

/-- The logs an action contributes to the raw runner. -/
def action_logs (a : OwnedAction) (post : ManagedHeap) : List (CSLObs (Nat × Nat)) :=
  match erase_action_label a post with
  | none => []
  | some l => label_logs [l]

set_option hygiene false in
local notation "RHS" => interp_schedule_nd (E := sE) (sh (A := Nat × Nat))

theorem owned_interp_pool (c : OwnedCfg) {n : Nat} {v : Pool sE Bn n} {g : Vector Side n}
    {f : Option (Fin n)} (hp : c.pool = mk_pool n v g f) :
    owned_interp c = RHS n v f (joined_state c) := by
  unfold owned_interp; rw [hp]; rfl

theorem rhs_empty (v : Pool sE Bn 0) (s : SSig) : RHS 0 v none s = pure (⟨⟩, s) := by
  have : schedule 0 v none = pure ⟨⟩ := unfold_inj (by rw [schedule_empty_none, unfold_pure])
  rw [interp_schedule_nd, this, project_scheduled_ret, interp_state_ret]

theorem rhs_ret (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1)) (s : SSig)
    (h : v[j].unfold = .ret ⟨⟩) :
    RHS (n + 1) v (some j) s = .guard (RHS n (v.eraseIdx j) none s) := by
  have : schedule (n + 1) v (some j) = .guard (schedule n (v.eraseIdx j) none) :=
    unfold_inj (by rw [schedule_focused_ret n v j h, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]

theorem rhs_stuck (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1)) (s : SSig)
    (h : v[j].unfold = .stuck) : RHS (n + 1) v (some j) s = .stuck := by
  have : schedule (n + 1) v (some j) = .stuck :=
    unfold_inj (by rw [schedule_focused_stuck n v j h, unfold_stuck])
  simp only [interp_schedule_nd, this, project_scheduled_stuck, interp_state_stuck]

theorem rhs_step (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1)) (t : Thread sE Bn)
    (s : SSig) (h : v[j].unfold = .step t) :
    RHS (n + 1) v (some j) s = .step (guards 2 (RHS (n + 1) (v.set j t) (some j) s)) := by
  have : schedule (n + 1) v (some j) = .step (schedule (n + 1) (v.set j t) (some j)) :=
    unfold_inj (by rw [schedule_focused_step n v j t h, unfold_step])
  simp only [interp_schedule_nd, this, project_scheduled_step, interp_state_step,
    interp_state_guard, guards_succ, guards_zero]

theorem rhs_guard (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1)) (t : Thread sE Bn)
    (s : SSig) (h : v[j].unfold = .guard t) :
    RHS (n + 1) v (some j) s = .guard (RHS (n + 1) (v.set j t) (some j) s) := by
  have : schedule (n + 1) v (some j) = .guard (schedule (n + 1) (v.set j t) (some j)) :=
    unfold_inj (by rw [schedule_focused_guard n v j t h, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]

theorem rhs_yield (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1))
    (k : PUnit → Thread sE Bn) (s : SSig) (h : v[j].unfold = .vis (.inl ⟨⟩) k) :
    RHS (n + 1) v (some j) s = .guard (RHS (n + 1) (v.set j (k ⟨⟩)) none s) := by
  have : schedule (n + 1) v (some j) = .guard (schedule (n + 1) (v.set j (k ⟨⟩)) none) :=
    unfold_inj (by rw [schedule_focused_yield n v j k h, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]

theorem rhs_fork (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1))
    (k : Bool → Thread sE Bn) (s : SSig) (h : v[j].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    RHS (n + 1) v (some j) s =
      .guard (RHS (n + 2) (Vector.cons (k true) (v.set j (k false))) (some j.succ) s) := by
  have : schedule (n + 1) v (some j) =
      .guard (schedule (n + 2) (Vector.cons (k true) (v.set j (k false))) (some j.succ)) :=
    unfold_inj (by rw [schedule_focused_fork n v j k h, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]

theorem rhs_user (n : Nat) (v : Pool sE Bn (n + 1)) (j : Fin (n + 1)) (e : sE.I)
    (k : sE.O e → Thread sE Bn) (s : SSig) (h : v[j].unfold = .vis (.inr (.inr e)) k) :
    RHS (n + 1) v (some j) s =
      (sh e s >>= fun p => guards 2 (RHS (n + 1) (v.set j (k p.1)) (some j) p.2)) := by
  have : schedule (n + 1) v (some j) =
      .vis (.inl e) fun x => schedule (n + 1) (v.set j (k x)) (some j) :=
    unfold_inj (by rw [schedule_focused_user_event n v j e k h, unfold_vis])
  simp only [interp_schedule_nd, this, project_scheduled_user, interp_state_vis,
    interp_state_guard, guards_succ, guards_zero]

theorem rhs_none (n : Nat) (v : Pool sE Bn (n + 1)) (s : SSig) :
    RHS (n + 1) v none s = match n, v with
      | 0, v => .step (guards 2 (RHS 1 v (some 0) s))
      | m + 1, v => CTree.brn (m + 2) fun i =>
          guards 2 (.step (guards 2 (RHS (m + 2) v (some i) s))) := by
  rw [interp_schedule_nd, schedule_no_focus_nonempty]
  cases n with
  | zero =>
    simp only [project_scheduled_scheduled, interp_state_step, interp_state_guard, guards_succ,
      guards_zero, interp_schedule_nd]
  | succ m =>
    simp only [CTree.brn, CTree.br', project_scheduled_br, project_scheduled_scheduled,
      interp_state_br, CTree.branch', br_bind, pure_bind, interp_state_guard, interp_state_step,
      guards_succ, guards_zero, interp_schedule_nd]
    rfl

/-- Leading guards of the focused slot are leading guards of the runner. -/
theorem rhs_focus_guards (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (m : Nat) (u : Thread sE Bn)
    (H : v[j] = guards m u) :
    owned_interp (set_pool c (mk_pool (n + 1) v g (some j))) =
      guards m (owned_interp (set_pool c (mk_pool (n + 1) (v.set j u) g (some j)))) := by
  induction m generalizing v with
  | zero => subst H; simp
  | succ m ih =>
    have E := rhs_guard n v j (guards m u) (joined_state c) (by rw [H, guards_succ, unfold_guard])
    have := ih (v.set j (guards m u)) (by simp)
    simp only [Vector.set_set] at this
    change RHS (n + 1) v (some j) (joined_state c) = _
    rw [E, guards_succ]
    exact congrArg CTree.guard this

/-! ## Primitive reflection on the joined heap -/

/-- A cell inside its owner's reservation is looked up in the joined heap as in the owner's. -/
theorem joined_lookup (c : OwnedCfg) (i : Side) (a : Nat) (W : owned_wf c)
    (Ha : (c.anchor i).1 a ≠ none) : (joined_heap c).1 a = (c.heap i).1 a := by
  obtain ⟨-, -, -, -, ⟨Dr, -⟩, ⟨SC, -⟩, ⟨SP, -⟩, -⟩ := W
  show hunion _ _ a = _
  unfold hunion
  cases i with
  | child =>
    split
    · simp_all
    · rename_i hc
      rcases hp : (c.heap .parent).1 a with _ | v
      · simp_all
      · exact absurd ((Dr a).resolve_left Ha) (SP a (by simp [hp]))
  | parent =>
    split
    · rename_i v hc
      exact absurd ((Dr a).resolve_right Ha) (SC a (by simp [hc]))
    · rfl

theorem joined_token (c : OwnedCfg) (i : Side) (b : Nat) (W : owned_wf c)
    (Ha : (c.anchor i).2 b ≠ none) : (joined_heap c).2 b = (c.heap i).2 b := by
  obtain ⟨-, -, -, -, ⟨-, Dr⟩, ⟨-, SC⟩, ⟨-, SP⟩, -⟩ := W
  show hunion _ _ b = _
  unfold hunion
  cases i with
  | child =>
    split
    · simp_all
    · rename_i hc
      rcases hp : (c.heap .parent).2 b with _ | v
      · simp_all
      · exact absurd ((Dr b).resolve_left Ha) (SP b (by simp [hp]))
  | parent =>
    split
    · rename_i v hc
      exact absurd ((Dr b).resolve_right Ha) (SC b (by simp [hc]))
    · rfl

/-- Writing an owned cell commutes with joining. -/
theorem joined_write (c : OwnedCfg) (i : Side) (a v : Nat) (W : owned_wf c)
    (Ha : (c.heap i).1 a ≠ none) :
    joined_heap (set_heap c i (upd (c.heap i).1 a v, (c.heap i).2)) ≈
      (upd (joined_heap c).1 a v, (joined_heap c).2) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨Dh, -⟩⟩ := W
  cases i <;> refine ⟨fun x => ?_, fun x => rfl⟩ <;>
    simp only [joined_heap, set_heap, side_upd, side_eqb, ↓reduceIte, Bool.false_eq_true,
      PCM.pop, hunion, upd] <;>
    by_cases hx : x = a <;> simp [hx]
  rcases hc : (c.heap .child).1 a with _ | w
  · simp
  · exact absurd ((Dh a).resolve_left (by simp [hc])) Ha

theorem global_count_emit (c : OwnedCfg) (i : Side) (p : Nat × Nat) :
    global_count (emit_cfg c i p) = global_count c + 1 := by
  cases i <;> simp [global_count, emit_cfg, side_upd, side_eqb] <;> omega

/-- Freeing an owned block commutes with joining. -/
theorem joined_free (c : OwnedCfg) (i : Side) (b : Nat) (m' : ManagedHeap) (W : owned_wf c)
    (Hf : managed_free (c.heap i) b = some m') :
    ∃ J, managed_free (joined_heap c) b = some J ∧ J ≈ joined_heap (set_heap c i m') := by
  obtain ⟨WC, WP, -, -, -, -, -, Dh⟩ := W
  cases i with
  | child =>
    obtain ⟨⟨J, HJ, EJ⟩, -⟩ := managed_free_pop _ _ _ _ Dh WC Hf
    exact ⟨J, HJ, EJ⟩
  | parent =>
    have Dh' := pdef_comm _ _ Dh
    obtain ⟨⟨J, HJ, EJ⟩, D'⟩ := managed_free_pop _ _ _ _ Dh' WP Hf
    obtain ⟨J', HJ', EJ'⟩ := managed_free_peq _ _ _ _ (pop_comm _ _ Dh') HJ
    exact ⟨J', HJ', peq_trans _ _ _ (peq_sym _ _ EJ') (peq_trans _ _ _ EJ (pop_comm _ _ D'))⟩

/-- A free that faults in its owner's reservation faults in the joined heap. -/
theorem joined_free_none (c : OwnedCfg) (i : Side) (b : Nat) (W : owned_wf c)
    (Hb : (c.anchor i).2 b ≠ none) (Hf : managed_free (c.heap i) b = none) :
    managed_free (joined_heap c) b = none := by
  by_cases h0 : b = 0
  · simp [managed_free, h0] at Hf
  · simp only [managed_free, h0, ite_false] at Hf ⊢
    rw [joined_token c i b W Hb]
    revert Hf; split <;> simp

/-- One primitive of lineage `i`: the runner's handler agrees with `prim_step` on success and on
fault. -/
theorem prim_reflect_joined (i : Side) (c : OwnedCfg) (e : sE.I) (W : owned_wf c)
    (Hok : component_event_ok e) (Ha : prim_addr_ok (c.anchor i) e) :
    match prim_step i c e with
    | some (kind, y, d) =>
        sh e (joined_state c) =
          emit_list (action_logs (act i kind) (joined_heap d)) (pure (y, joined_state d))
    | none => sh e (joined_state c) = .stuck := by
  rcases e with ((a | ⟨a, v⟩ | n | b | ⟨a, ex, de⟩) | (_ | _) | p)
  · have El := joined_lookup c i a W Ha
    simp only [prim_step, heap_prim]
    rcases hx : (c.heap i).1 a with _ | v
    · exact heap_handlerW_rd_none (B := Bn) CSLObs.heap a _ _ _ (El.trans hx)
    · exact heap_handlerW_rd_some (B := Bn) CSLObs.heap a _ _ _ v (El.trans hx)
  · have El := joined_lookup c i a W Ha
    simp only [prim_step, heap_prim]
    rcases hx : (c.heap i).1 a with _ | old
    · exact heap_handlerW_wr_none (B := Bn) CSLObs.heap a _ _ _ v (El.trans hx)
    · have Ep := managed_heap_ext _ _ (joined_write c i a v W (by simp [hx]))
      show _ = emit_list [CSLObs.heap (joined_heap (set_heap c i (upd (c.heap i).1 a v,
        (c.heap i).2)))] (pure (PUnit.unit, (joined_heap (set_heap c i (upd (c.heap i).1 a v,
        (c.heap i).2)), (c.ctx, global_count c))))
      rw [Ep]
      exact heap_handlerW_wr_some (B := Bn) CSLObs.heap a _ _ _ v old (El.trans hx)
  · exact (Hok : False).elim
  · simp only [prim_step, heap_prim]
    cases b with
    | zero =>
      have hm : managed_free (c.heap i) 0 = some (c.heap i) := by simp [managed_free]
      have hj : joined_state (set_heap c i (c.heap i)) = joined_state c := by cases i <;> rfl
      simp only [hm]
      show _ = pure (PUnit.unit, joined_state (set_heap c i (c.heap i)))
      rw [hj]
      exact heap_handlerW_free (B := Bn) CSLObs.heap 0 _ _ _ (by simp [managed_free])
    | succ b =>
      have Hb : (c.anchor i).2 (b + 1) ≠ none := Ha.resolve_left (by omega)
      rcases hf : managed_free (c.heap i) (b + 1) with _ | m'
      · exact heap_handlerW_free_invalid (B := Bn) CSLObs.heap _ _ _
          (joined_free_none c i (b + 1) W Hb hf)
      · obtain ⟨J, HJ, EJ⟩ := joined_free c i (b + 1) m' W hf
        show _ = emit_list [CSLObs.heap (joined_heap (set_heap c i m'))]
          (pure (PUnit.unit, (joined_heap (set_heap c i m'), (c.ctx, global_count c))))
        refine (heap_handlerW_free (B := Bn) CSLObs.heap _ _ _ _ HJ).trans ?_
        rw [managed_heap_ext _ _ EJ]
        rfl
  · have El := joined_lookup c i a W Ha
    simp only [prim_step, heap_prim]
    rcases hx : (c.heap i).1 a with _ | cur
    · exact heap_handlerW_cas_missing (B := Bn) CSLObs.heap a ex de _ _ _ (El.trans hx)
    · by_cases hc : cur = ex
      · subst hc
        have Ep := managed_heap_ext _ _ (joined_write c i a de W (by simp [hx]))
        simp only [ite_true]
        show _ = emit_list [CSLObs.heap (joined_heap (set_heap c i (upd (c.heap i).1 a de,
          (c.heap i).2)))] (pure (true, (joined_heap (set_heap c i (upd (c.heap i).1 a de,
          (c.heap i).2)), (c.ctx, global_count c))))
        rw [Ep]
        exact heap_handlerW_cas_success (B := Bn) CSLObs.heap a cur de _ _ _ (El.trans hx)
      · simp only [hc, ite_false]
        exact heap_handlerW_cas_failure (B := Bn) CSLObs.heap a ex de cur _ _ _ (El.trans hx) hc
  · rfl
  · exact (Hok : False).elim
  · show _ = emit_list [CSLObs.emit (stamp p (global_count c))]
      (pure (PUnit.unit, (joined_heap c, (c.ctx, global_count (emit_cfg c i p)))))
    rw [global_count_emit]
    rfl

/-! ## Admissibility along owned actions -/

/-- An admitted, branch-free thread. -/
def thread_ok (t : Thread sE Bn) : Prop :=
  Framable (okE_thread component_event_ok) t ∧ BranchFree t

theorem thread_ok_guards (n : Nat) (t u : Thread sE Bn) (E : t = guards n u)
    (h : thread_ok t) : thread_ok u := by
  subst E
  induction n with
  | zero => exact h
  | succ n ih =>
    obtain ⟨F, Bf⟩ := h
    rw [guards_succ, framable_unfold, unfold_guard] at F
    rw [guards_succ, branchfree_unfold, unfold_guard] at Bf
    cases F with | guard _ F => cases Bf with | guard _ Bf => exact ih ⟨F, Bf⟩

theorem thread_ok_headed (t u : Thread sE Bn) (h : headed t u) : thread_ok t → thread_ok u :=
  let ⟨n, E⟩ := h; thread_ok_guards n t u E

theorem thread_ok_step (t : Thread sE Bn) (h : thread_ok (.step t)) : thread_ok t := by
  obtain ⟨F, Bf⟩ := h
  rw [framable_unfold, unfold_step] at F
  rw [branchfree_unfold, unfold_step] at Bf
  cases F with | step _ F => cases Bf with | step _ Bf => exact ⟨F, Bf⟩

theorem thread_ok_vis (e : CEff.I) (k : CEff.O e → Thread sE Bn) (x : CEff.O e)
    (h : thread_ok (.vis e k)) : thread_ok (k x) := by
  obtain ⟨F, Bf⟩ := h
  rw [framable_unfold, unfold_vis] at F
  rw [branchfree_unfold, unfold_vis] at Bf
  cases F with | vis _ _ _ F => cases Bf with | vis _ _ Bf => exact ⟨F x, Bf x⟩

theorem thread_ok_vis_ok (e : sE.I) (k : sE.O e → Thread sE Bn)
    (h : thread_ok (.vis (E := CEff) (.inr (.inr e)) k)) : component_event_ok e := by
  obtain ⟨F, -⟩ := h
  rw [framable_unfold, unfold_vis] at F
  cases F with | vis _ _ ok _ => exact ok

/-- An admitted, branch-free pool. -/
def pool_ok {n : Nat} (v : Pool sE Bn n) : Prop :=
  pool_framable component_event_ok v ∧ pool_branchfree v

theorem pool_ok_nth {n : Nat} (v : Pool sE Bn n) (j : Fin n) (h : pool_ok v) :
    thread_ok v[j] :=
  ⟨h.1 j, h.2 j⟩

theorem pool_ok_replace {n : Nat} (v : Pool sE Bn n) (j : Fin n) (t : Thread sE Bn)
    (h : pool_ok v) (ht : thread_ok t) : pool_ok (v.set j t) :=
  ⟨pool_framable_replace _ v j t h.1 ht.1, pool_branchfree_replace v j t h.2 ht.2⟩

theorem pool_ok_remove {n : Nat} (v : Pool sE Bn (n + 1)) (j : Fin (n + 1)) (h : pool_ok v) :
    pool_ok (vector_remove v j) :=
  ⟨pool_framable_remove _ v j h.1, pool_branchfree_remove v j h.2⟩

theorem pool_ok_cons {n : Nat} (t : Thread sE Bn) (v : Pool sE Bn n) (ht : thread_ok t)
    (h : pool_ok v) : pool_ok (Vector.cons t v) :=
  ⟨pool_framable_cons _ t v ht.1 h.1, pool_branchfree_cons t v ht.2 h.2⟩

theorem set_pool_eta (c : OwnedCfg) : set_pool c c.pool = c := rfl

/-! ## `owned_step` by pool shape -/

theorem owned_step_sel (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (a : OwnedAction) (c' : OwnedCfg)
    (hp : c.pool = mk_pool (n + 1) v g none) : owned_step c a c' ↔ sel_step c n v g a c' := by
  unfold owned_step; rw [hp]; rfl

theorem owned_step_focus (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (a : OwnedAction) (c' : OwnedCfg)
    (hp : c.pool = mk_pool (n + 1) v g (some j)) :
    owned_step c a c' ↔ focus_step c n v g j a c' := by
  unfold owned_step; rw [hp]; rfl

theorem pool_ok_step (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg)
    (Hp : pool_ok c.pool.threads) (Hs : owned_step c a c') : pool_ok c'.pool.threads := by
  rcases hp : c.pool with ⟨_ | n, v, g, _ | j⟩
  · exact (owned_step_empty c a c' (by rw [hp]) Hs).elim
  · exact (owned_step_empty c a c' (by rw [hp]) Hs).elim
  · obtain ⟨j, rfl, rfl⟩ := (owned_step_sel c n v g a c' hp).1 Hs
    rw [hp] at Hp; exact Hp
  · rw [hp] at Hp
    have Ht := fun u (h : headed v[j] u) => thread_ok_headed _ u h (pool_ok_nth v j Hp)
    rcases (owned_step_focus c n v g j a c' hp).1 Hs with
      ⟨t, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨Hh, rfl, rfl⟩ |
      ⟨e, k, kind, y, c1, Hh, -, rfl, rfl⟩
    · exact pool_ok_replace v j t Hp (thread_ok_step _ (Ht _ Hh))
    · exact pool_ok_replace v j _ Hp (thread_ok_vis _ _ _ (Ht _ Hh))
    · exact pool_ok_cons _ _ (thread_ok_vis _ _ _ (Ht _ Hh))
        (pool_ok_replace v j _ Hp (thread_ok_vis _ _ _ (Ht _ Hh)))
    · exact pool_ok_remove v j Hp
    · exact pool_ok_replace v j _ Hp (thread_ok_vis _ _ _ (Ht _ Hh))

theorem erasable_step (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg) (He : erasable c)
    (Hs : owned_step c a c') : erasable c' := by
  obtain ⟨W, F, Bf, Cf⟩ := He
  obtain ⟨F', Bf'⟩ := pool_ok_step c a c' ⟨F, Bf⟩ Hs
  exact ⟨owned_step_wf c a c' W Hs, F', Bf', fun d Hd => Cf d (Star.head ⟨a, Hs⟩ Hd)⟩

/-! ### Forgetting a guard of the focused slot -/

theorem headed_guard (t t' u : Thread sE Bn) (E : t = .guard t') (h : headed t' u) :
    headed t u :=
  let ⟨n, Hn⟩ := h; ⟨n + 1, by rw [E, Hn]; rfl⟩

theorem prim_step_set_pool (i : Side) (c : OwnedCfg) (p : TaggedPool) (e : sE.I) :
    prim_step i (set_pool c p) e =
      (prim_step i c e).map fun r => (r.1, r.2.1, set_pool r.2.2 p) := by
  rcases e with ((a | ⟨a, v⟩ | n | b | ⟨a, ex, de⟩) | (_ | _) | q) <;>
    simp only [prim_step, heap_prim, ctx_prim, emit_prim, set_pool] <;>
    (repeat' split) <;> simp_all [global_count, emit_cfg, set_heap]

theorem prim_step_repool (i : Side) (c : OwnedCfg) (p q : TaggedPool) (e : sE.I)
    (kind : OwnedKind) (y : sE.O e) (c1 : OwnedCfg)
    (H : prim_step i (set_pool c p) e = some (kind, y, c1)) :
    prim_step i (set_pool c q) e = some (kind, y, set_pool c1 q) := by
  rw [prim_step_set_pool] at H ⊢
  rcases h : prim_step i c e with _ | ⟨kind', y', c'⟩ <;> rw [h] at H
  · cases H
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at H ⊢
    obtain ⟨rfl, rfl, rfl⟩ := H
    exact ⟨rfl, rfl, rfl⟩

/-- Forgetting a leading guard of the focused slot keeps every action. -/
theorem strip_step (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (t : Thread sE Bn) (a : OwnedAction) (d : OwnedCfg)
    (H : v[j].unfold = .guard t)
    (Hs : owned_step (set_pool c (mk_pool (n + 1) (v.set j t) g (some j))) a d) :
    owned_step (set_pool c (mk_pool (n + 1) v g (some j))) a d := by
  have E : v[j] = .guard t := unfold_inj (by rw [H, unfold_guard])
  change focus_step _ n (v.set j t) g j a d at Hs
  change focus_step _ n v g j a d
  have hs : (v.set j t)[j] = t := by simp
  simp only [focus_step] at Hs
  rw [hs] at Hs
  rcases Hs with ⟨t1, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨k, Hh, rfl, rfl⟩ | ⟨Hh, rfl, rfl⟩ |
    ⟨e, k, kind, y, c1, Hh, Hpr, rfl, rfl⟩ <;>
    have Hh' := headed_guard _ _ _ E Hh
  · exact .inl ⟨t1, Hh', rfl, by simp [Vector.set_set, set_pool]⟩
  · exact .inr (.inl ⟨k, Hh', rfl, by simp [Vector.set_set, set_pool]⟩)
  · exact .inr (.inr (.inl ⟨k, Hh', rfl, by simp [Vector.set_set, set_pool]⟩))
  · exact .inr (.inr (.inr (.inl ⟨Hh', rfl, by rw [vector_remove_replace]; rfl⟩)))
  · exact .inr (.inr (.inr (.inr ⟨e, k, kind, y, set_pool c1 (mk_pool (n + 1) v g (some j)),
      Hh', prim_step_repool _ _ _ _ _ _ _ _ Hpr, rfl, by simp [Vector.set_set, set_pool]⟩)))

theorem strip_head_confined (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (t : Thread sE Bn)
    (H : v[j].unfold = .guard t)
    (Hc : head_confined (set_pool c (mk_pool (n + 1) v g (some j)))) :
    head_confined (set_pool c (mk_pool (n + 1) (v.set j t) g (some j))) := by
  intro t0 i e k Hf Hh
  have hs : (v.set j t)[j] = t := by simp
  simp only [focused_thread, set_pool, mk_pool, Option.some.injEq, Prod.mk.injEq] at Hf
  obtain ⟨rfl, rfl⟩ := Hf
  have Hh' : headed (v.set j t)[j] (.vis (E := CEff) (.inr (.inr e)) k) := Hh
  rw [hs] at Hh'
  exact Hc v[j] g[j] e k rfl (headed_guard _ _ _ (unfold_inj (by rw [H, unfold_guard])) Hh')

theorem erasable_guard (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (t : Thread sE Bn)
    (H : v[j].unfold = .guard t) (He : erasable (set_pool c (mk_pool (n + 1) v g (some j)))) :
    erasable (set_pool c (mk_pool (n + 1) (v.set j t) g (some j))) := by
  obtain ⟨W, F, Bf, Cf⟩ := He
  have Ht := thread_ok_guards 1 v[j] t (unfold_inj (by rw [H, guards_succ, guards_zero,
    unfold_guard]))
    (pool_ok_nth v j ⟨F, Bf⟩)
  obtain ⟨F', Bf'⟩ := pool_ok_replace v j t ⟨F, Bf⟩ Ht
  refine ⟨W, F', Bf', fun d Hd => ?_⟩
  rcases Hd.cases_head with rfl | ⟨d1, ⟨a, Ha⟩, Hrest⟩
  · exact strip_head_confined c n v g j t H (Cf _ .refl)
  · exact Cf d (Star.head ⟨a, strip_step c n v g j t a d1 H Ha⟩ Hrest)

/-! ## Erasure -/

theorem headed_obs (t : Thread sE Bn) (ot : CTreeF CEff Bn PUnit (Thread sE Bn))
    (H : t.unfold = ot) : headed t (CTree.fold ot) :=
  ⟨0, by rw [← H, fold_unfold]; rfl⟩

theorem erasable_reach (c d : OwnedCfg) (He : erasable c) (H : Star owned_next c d) :
    erasable d := by
  induction H with
  | refl => exact He
  | tail _ hab ih => obtain ⟨a, Ha⟩ := hab; exact erasable_step _ a _ ih Ha

theorem Forall2_nth_error_r {A B : Type _} (P : A → B → Prop) (l1 : List A) (l2 : List B)
    (k : Nat) (y : B) (H : Forall2 P l1 l2) (Hk : l2[k]? = some y) :
    ∃ x, l1[k]? = some x ∧ P x y := by
  induction H generalizing k with
  | nil => simp at Hk
  | cons hxy _ ih =>
    cases k with
    | zero => simp at Hk; subst Hk; exact ⟨_, rfl, hxy⟩
    | succ k => exact ih k (by simpa using Hk)

/-- Every slot of `q` has an equal slot at the same position in `p`. -/
theorem tp_equ_slot (p q : TaggedPool) (j : Fin q.size) (H : tp_equ p q) :
    ∃ j0 : Fin p.size, fin_nat j0 = fin_nat j ∧ p.threads[j0] = q.threads[j] ∧
      p.tags[j0] = q.tags[j] := by
  obtain ⟨⟨t, s⟩, Hn, Ht, Hs⟩ := Forall2_nth_error_r _ _ _ _ _ H.1 (tp_slots_nth_error q j)
  have Hlt : fin_nat j < p.size := by
    have := (List.getElem?_eq_some_iff.1 Hn).1
    simpa [tp_slots] using this
  have Hp := tp_slots_nth_error p ⟨_, Hlt⟩
  rw [Hn] at Hp
  simp only [Option.some.injEq, Prod.mk.injEq] at Hp
  obtain ⟨rfl, rfl⟩ := Hp
  exact ⟨⟨_, Hlt⟩, rfl, Ht, Hs⟩

theorem head_confined_equ (c d : OwnedCfg) (E : owned_equ c d) (Hc : head_confined c) :
    head_confined d := by
  obtain rfl := owned_equ_eq E; exact Hc

theorem erasable_equ (c d : OwnedCfg) (E : owned_equ c d) (H : erasable c) : erasable d := by
  obtain rfl := owned_equ_eq E; exact H

/-! ## Canonical runner and lineage operational support -/

theorem owned_interp_set_pool (c : OwnedCfg) (n : Nat) (v : Pool sE Bn n) (g : Vector Side n)
    (f : Option (Fin n)) :
    owned_interp (set_pool c (mk_pool n v g f)) = RHS n v f (joined_state c) := rfl

theorem guards_trans_inv {E B : Effect.{0}} {X : Type} {l : Label E} (n : Nat)
    {t u : CTree E B X} (h : trans l (guards n t) u) : trans l t u := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (trans_guard_inv h)

/-- Labels other than those of selection and source steps are single observations. -/
theorem erase_label_shape (a : OwnedAction) (h : ManagedHeap)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (hl : erase_action_label a h = some l) :
    (l = .tau ∧ (a.action_kind = .select ∨ a.action_kind = .step)) ∨
      ∃ o, l = .obs (E := writerE (CSLObs (Nat × Nat))) o ⟨⟩ := by
  unfold erase_action_label at hl
  split at hl <;> cases hl <;> simp_all

theorem action_logs_some (a : OwnedAction) (h : ManagedHeap)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (hl : erase_action_label a h = some l) :
    action_logs a h = label_logs [l] := by
  simp [action_logs, hl]

theorem action_logs_none (a : OwnedAction) (h : ManagedHeap)
    (hl : erase_action_label a h = none) : action_logs a h = [] := by
  simp [action_logs, hl]

/-- Primitives are never selections or source steps. -/
theorem prim_step_kind (i : Side) (c : OwnedCfg) (e : sE.I) (kind : OwnedKind) (y : sE.O e)
    (c1 : OwnedCfg) (H : prim_step i c e = some (kind, y, c1)) :
    kind ≠ .select ∧ kind ≠ .step := by
  rcases e with ((a | ⟨a, v⟩ | sz | b | ⟨a, ex, de⟩) | (_ | s) | p) <;>
    simp only [prim_step, heap_prim, ctx_prim, emit_prim] at H <;>
    (repeat' split at H) <;> cases H <;> simp

/-- A single owned action, with its exact operational response. -/
theorem owned_interp_action (c : OwnedCfg) (a : OwnedAction) (d : OwnedCfg) (He : erasable c)
    (Hs : owned_step c a d) :
    (erase_action_label a (joined_heap d) = none → owned_interp c ~ owned_interp d) ∧
    (∀ l, erase_action_label a (joined_heap d) = some l →
      ∃ T, trans l (owned_interp c) T ∧ T ~ owned_interp d) := by
  suffices ∀ n v g f, erasable (set_pool c (mk_pool n v g f)) →
      owned_step (set_pool c (mk_pool n v g f)) a d →
      (erase_action_label a (joined_heap d) = none →
        owned_interp (set_pool c (mk_pool n v g f)) ~ owned_interp d) ∧
      (∀ l, erase_action_label a (joined_heap d) = some l →
        ∃ T, trans l (owned_interp (set_pool c (mk_pool n v g f))) T ∧ T ~ owned_interp d) from
    this c.pool.size c.pool.threads c.pool.tags c.pool.focus He Hs
  intro n v g f He Hs
  rcases n with _ | n
  · exact Hs.elim
  rcases f with _ | j
  · obtain ⟨j, rfl, rfl⟩ := (Hs : sel_step _ n v g a d)
    refine ⟨fun h => by simp [erase_action_label, act] at h, fun l hl => ?_⟩
    simp only [erase_action_label, act, Option.some.injEq] at hl
    subst hl
    rw [owned_interp_set_pool c _ v g none, rhs_none]
    cases n with
    | zero =>
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      exact ⟨_, trans_step _, guards_sbisim 2 _⟩
    | succ n =>
      refine ⟨_, ?_, guards_sbisim 2 _⟩
      exact trans_br' (B₁ := Bn) ⟨j⟩ (guards_trans 2 (trans_step _))
  have Hs : focus_step _ n v g j a d := Hs
  rcases Hs with ⟨t, ⟨m, Hh⟩, rfl, rfl⟩ | ⟨k, ⟨m, Hh⟩, rfl, rfl⟩ | ⟨k, ⟨m, Hh⟩, rfl, rfl⟩ |
    ⟨⟨m, Hh⟩, rfl, rfl⟩ | ⟨e, k, kind, y, c1, ⟨m, Hh⟩, P, rfl, rfl⟩ <;>
    have E := rhs_focus_guards c n v g j m _ Hh
  · rw [owned_interp_set_pool c _ (v.set j (.step t)) g (some j),
      rhs_step n (v.set j (.step t)) j t _ (by simp [unfold_step]), Vector.set_set] at E
    refine ⟨fun h => by simp [erase_action_label, act] at h, fun l hl => ?_⟩
    simp only [erase_action_label, act, Option.some.injEq] at hl
    subst hl
    exact ⟨_, by rw [E]; exact guards_trans m (trans_step _), guards_sbisim 2 _⟩
  · rw [owned_interp_set_pool c _ (v.set j (.vis (.inl ⟨⟩) k)) g (some j),
      rhs_yield n (v.set j (.vis (.inl ⟨⟩) k)) j k _ (by simp [unfold_vis]),
      Vector.set_set] at E
    refine ⟨fun _ => ?_, fun l hl => by simp [erase_action_label, act] at hl⟩
    rw [E]
    exact sbisim_trans (guards_sbisim m _) (sb_guard _)
  · rw [owned_interp_set_pool c _ (v.set j (.vis (.inr (.inl ⟨⟩)) k)) g (some j),
      rhs_fork n (v.set j (.vis (.inr (.inl ⟨⟩)) k)) j k _ (by simp [unfold_vis]),
      Vector.set_set] at E
    refine ⟨fun _ => ?_, fun l hl => by simp [erase_action_label, act] at hl⟩
    rw [E]
    exact sbisim_trans (guards_sbisim m _) (sb_guard _)
  · rw [owned_interp_set_pool c _ (v.set j (pure ⟨⟩)) g (some j),
      rhs_ret n (v.set j (pure ⟨⟩)) j _ (by simp [unfold_pure])] at E
    refine ⟨fun _ => ?_, fun l hl => by simp [erase_action_label, act] at hl⟩
    rw [E, show (v.set j (pure ⟨⟩)).eraseIdx j = vector_remove v j from
      vector_remove_replace v j _]
    exact sbisim_trans (guards_sbisim m _) (sb_guard _)
  · obtain ⟨W, F, Bf, C⟩ := He
    have Hok : component_event_ok e :=
      thread_ok_vis_ok e k (thread_ok_headed v[j] _ ⟨m, Hh⟩ (pool_ok_nth v j ⟨F, Bf⟩))
    have Ha : prim_addr_ok ((set_pool c (mk_pool (n + 1) v g (some j))).anchor g[j]) e :=
      C _ .refl v[j] g[j] e k rfl ⟨m, Hh⟩
    have Hr : sh e (joined_state c) = emit_list (action_logs (act g[j] kind) (joined_heap c1))
        (pure (y, joined_state c1)) := by
      have H0 := prim_reflect_joined g[j] _ e W Hok Ha
      rw [P] at H0; exact H0
    rw [owned_interp_set_pool c _ (v.set j (.vis (.inr (.inr e)) k)) g (some j),
      rhs_user n (v.set j (.vis (.inr (.inr e)) k)) j e k _ (by simp [unfold_vis])] at E
    change _ = guards m (sh e (joined_state c) >>= _) at E
    rw [Hr, emit_list_ret_bind] at E
    simp only [Vector.set_set] at E
    change owned_interp _ = guards m (emit_list _
      (guards 2 (owned_interp (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j)))))) at E
    rw [show joined_heap c1 = joined_heap (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g
      (some j))) from rfl] at E
    have Hk := prim_step_kind _ _ _ _ _ _ P
    rcases hl : erase_action_label (act g[j] kind)
      (joined_heap (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j)))) with _ | l
    · rw [action_logs_none _ _ hl] at E
      refine ⟨fun _ => ?_, fun l h => by cases h⟩
      rw [E]
      exact sbisim_trans (guards_sbisim m _) (guards_sbisim 2 _)
    · rcases erase_label_shape _ _ l hl with ⟨-, hk | hk⟩ | ⟨o, rfl⟩
      · exact absurd hk Hk.1
      · exact absurd hk Hk.2
      rw [action_logs_some _ _ _ hl, show label_logs [Label.obs o PUnit.unit] = [o] from rfl,
        emit_list_cons] at E
      refine ⟨fun h => (by cases h), fun l' hl' => ?_⟩
      cases hl'
      refine ⟨_, ?_, guards_sbisim 2 _⟩
      rw [E]
      exact guards_trans m (trans_vis (E := writerE (CSLObs (Nat × Nat))) ⟨⟩ _)

/-- Selection contributes one raw step. -/
theorem owned_interp_select (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) :
    owned_interp (set_pool c (mk_pool (n + 1) v g none)) ~
      CTree.brSn (n + 1) fun j => owned_interp (set_pool c (mk_pool (n + 1) v g (some j))) :=
  interp_schedule_nd_select _ n v (joined_state c)

/-- Both projections, and the global configuration, are erasable. -/
def active_erasable (c : OwnedCfg) : Prop :=
  erasable c ∧ erasable (project .child c) ∧ erasable (project .parent c)

theorem owned_interp_equ (c d : OwnedCfg) (E : owned_equ c d) : owned_interp c ~ owned_interp d :=
  by obtain rfl := owned_equ_eq E; exact sbisim_refl _

theorem active_erasable_equ (c d : OwnedCfg) (E : owned_equ c d) (H : active_erasable c) :
    active_erasable d := by
  obtain rfl := owned_equ_eq E; exact H

theorem active_erasable_step (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg)
    (H : active_erasable c) (Hs : owned_step c a c') : active_erasable c' := by
  obtain ⟨H, HC, HP⟩ := H
  have HL : ∀ i, erasable (project i c) → erasable (project i c') := by
    intro i Hi
    by_cases Ho : a.owner = i
    · obtain ⟨d, Hd, E⟩ := owned_step_own i c a c' Hs Ho
      obtain rfl := owned_equ_eq E
      exact erasable_step _ _ _ Hi Hd
    · rw [owned_equ_eq (owned_step_foreign i c a c' Hs Ho)]; exact Hi
  exact ⟨erasable_step c a c' H Hs, HL _ HC, HL _ HP⟩

/-- Lineage `i` may act next: nothing is focused, or the focused slot is its own. -/
def owned_side_ready (i : Side) (c : OwnedCfg) : Prop :=
  c.pool.focus = none ∨ ∃ j, c.pool.focus = some j ∧ c.pool.tags[j] = i

theorem owned_label_none_heap (a : OwnedAction) (h h' : ManagedHeap)
    (H : erase_action_label a h = none) : erase_action_label a h' = none := by
  unfold erase_action_label at H ⊢; split <;> simp_all

theorem owned_project_label_none (i : Side) (c : OwnedCfg) (a : OwnedAction)
    (h h' : ManagedHeap) :
    erase_action_label (project_action i c a) h' = none ↔ erase_action_label a h = none := by
  unfold project_action erase_action_label
  split <;> split <;> simp_all [act]

theorem owned_label_not_value (a : OwnedAction) (h : ManagedHeap) {X : Type} (x : X) :
    erase_action_label a h ≠ some (.val x) := by
  intro hl
  rcases erase_label_shape a h _ hl with ⟨h, -⟩ | ⟨o, h⟩ <;> cases h

theorem owned_silent_erasable (c d : OwnedCfg) (H : erasable c) (Hp : Star silent_next c d) :
    erasable d := by
  induction Hp with
  | refl => exact H
  | tail _ hab ih => obtain ⟨a, Hs, -⟩ := hab; exact erasable_step _ a _ ih Hs

theorem owned_silent_active (c d : OwnedCfg) (H : active_erasable c)
    (Hp : Star silent_next c d) : active_erasable d := by
  induction Hp with
  | refl => exact H
  | tail _ hab ih => obtain ⟨a, Hs, -⟩ := hab; exact active_erasable_step _ a _ ih Hs

theorem owned_active_local (c : OwnedCfg) (i : Side) (H : active_erasable c) :
    erasable (project i c) := by
  cases i
  · exact H.2.1
  · exact H.2.2

theorem owned_interp_silent (c d : OwnedCfg) (He : erasable c) (Hp : Star silent_next c d) :
    owned_interp c ~ owned_interp d := by
  induction Hp with
  | refl => exact sbisim_refl _
  | tail Hp hab ih =>
    obtain ⟨a, Hs, Hl⟩ := hab
    exact sbisim_trans ih ((owned_interp_action _ a _ (owned_silent_erasable _ _ He Hp) Hs).1 Hl)

theorem owned_interp_visible (c d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (He : erasable c) (Hp : Star silent_next c d)
    (Hs : owned_step d a d') (Hl : erase_action_label a (joined_heap d') = some l) :
    ∃ T, trans l (owned_interp c) T ∧ T ~ owned_interp d' := by
  obtain ⟨U, HU, EU⟩ := (owned_interp_action d a d' (owned_silent_erasable c d He Hp) Hs).2 l Hl
  obtain ⟨T, HT, ET⟩ :=
    Tisl.Yield.sbisim_trans_l _ _ _ _ (sbisim_symm (owned_interp_silent c d He Hp)) HU
  exact ⟨T, HT, sbisim_trans (sbisim_symm ET) EU⟩

/-! ## Canonical raw transitions -/

/-- A finite answer of the canonical runner: a silent owned prefix, then one visible action or
the terminal empty pool. -/
def owned_forward_result (c : OwnedCfg) (l : Label (writerE (CSLObs (Nat × Nat))))
    (T : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) : Prop :=
  ∃ d, Star silent_next c d ∧
    ((∃ a d', owned_step d a d' ∧ erase_action_label a (joined_heap d') = some l ∧
        T ~ owned_interp d') ∨
     (d.pool.size = 0 ∧ l = .val (PUnit.unit, joined_state d) ∧
        T ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))))

theorem owned_result_visible (c : OwnedCfg) (a : OwnedAction) (d : OwnedCfg)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (T : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))
    (Hs : owned_step c a d) (Hl : erase_action_label a (joined_heap d) = some l)
    (HT : T ~ owned_interp d) : owned_forward_result c l T :=
  ⟨c, .refl, .inl ⟨a, d, Hs, Hl, HT⟩⟩

theorem owned_result_silent (c : OwnedCfg) (a : OwnedAction) (d : OwnedCfg)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (T : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))
    (Hs : owned_step c a d) (Hl : erase_action_label a (joined_heap d) = none)
    (H : owned_forward_result d l T) : owned_forward_result c l T :=
  let ⟨out, Hp, Hout⟩ := H; ⟨out, Star.head ⟨a, Hs, Hl⟩ Hp, Hout⟩

/-- Removing a source guard is not an owned action: lift the first action of the finite answer
back to the original focused slot instead. -/
theorem owned_result_guard (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (t : Thread sE Bn)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (T : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))
    (Hg : v[j].unfold = .guard t)
    (H : owned_forward_result (set_pool c (mk_pool (n + 1) (v.set j t) g (some j))) l T) :
    owned_forward_result (set_pool c (mk_pool (n + 1) v g (some j))) l T := by
  obtain ⟨d, Hp, Hout⟩ := H
  rcases Hp.cases_head with rfl | ⟨mid, ⟨a, Hs, Hl⟩, Hrest⟩
  · rcases Hout with ⟨a, d', Hs, Hl, HT⟩ | ⟨Hz, -⟩
    · exact owned_result_visible _ a d' l T (strip_step c n v g j t a d' Hg Hs) Hl HT
    · exact absurd Hz (Nat.succ_ne_zero n)
  · exact ⟨d, Star.head ⟨a, strip_step c n v g j t a mid Hg Hs, Hl⟩ Hrest, Hout⟩

/-- Delayed canonical heads expose a positive finite guard prefix; silent owned actions and
source guards lift the eventual finite result. -/
theorem owned_interp_head (c : OwnedCfg) (He : erasable c) :
    (∀ l T, trans l (owned_interp c) T → owned_forward_result c l T) ∨
    ∃ d k, owned_interp c = guards (k + 1) (owned_interp d) ∧ erasable d ∧
      ∀ l T, owned_forward_result d l T → owned_forward_result c l T := by
  suffices ∀ n v g f, erasable (set_pool c (mk_pool n v g f)) →
      (∀ l T, trans l (owned_interp (set_pool c (mk_pool n v g f))) T →
        owned_forward_result (set_pool c (mk_pool n v g f)) l T) ∨
      ∃ d k, owned_interp (set_pool c (mk_pool n v g f)) = guards (k + 1) (owned_interp d) ∧
        erasable d ∧ ∀ l T, owned_forward_result d l T →
          owned_forward_result (set_pool c (mk_pool n v g f)) l T from
    this c.pool.size c.pool.threads c.pool.tags c.pool.focus He
  intro n v g f He
  obtain ⟨W, F, Bf, Cf⟩ := He
  rcases n with _ | n
  · rcases f with _ | j
    · refine .inl fun l T HT => ?_
      rw [owned_interp_set_pool, rhs_empty] at HT
      obtain ⟨rfl, rfl⟩ := trans_ret_inv HT
      exact ⟨_, .refl, .inr ⟨rfl, rfl, sbisim_refl _⟩⟩
    · exact j.elim0
  rcases f with _ | j
  · refine .inl fun l T HT => ?_
    rw [owned_interp_set_pool, rhs_none] at HT
    cases n with
    | zero =>
      obtain ⟨rfl, rfl⟩ := trans_step_inv HT
      exact owned_result_visible _ (act g[0] .select) _ _ _ ⟨0, rfl, rfl⟩ rfl
        (guards_sbisim 2 _)
    | succ n =>
      obtain ⟨⟨j⟩, HT⟩ := trans_br'_inv HT
      obtain ⟨rfl, rfl⟩ := trans_step_inv (guards_trans_inv 2 HT)
      exact owned_result_visible _ (act g[j] .select) _ _ _ ⟨j, rfl, rfl⟩ rfl
        (guards_sbisim 2 _)
  have He : erasable (set_pool c (mk_pool (n + 1) v g (some j))) := ⟨W, F, Bf, Cf⟩
  have Ht := pool_ok_nth v j ⟨F, Bf⟩
  rcases H : v[j].unfold with ⟨⟩ | _ | t | t | ⟨(⟨⟩ | ⟨⟩ | pe), k⟩ | ⟨b, k⟩
  · -- return
    have Hs : owned_step (set_pool c (mk_pool (n + 1) v g (some j))) (act g[j] .ret)
        (set_pool c (mk_pool n (vector_remove v j) (vector_remove g j) none)) :=
      .inr (.inr (.inr (.inl ⟨headed_obs _ _ H, rfl, rfl⟩)))
    exact .inr ⟨_, 0, by rw [owned_interp_set_pool, rhs_ret n v j _ H]; rfl,
      erasable_step _ _ _ He Hs, fun l T => owned_result_silent _ _ _ l T Hs rfl⟩
  · refine .inl fun l T HT => ?_
    rw [owned_interp_set_pool, rhs_stuck n v j _ H] at HT
    exact (trans_stuck_inv HT).elim
  · refine .inl fun l T HT => ?_
    rw [owned_interp_set_pool, rhs_step n v j t _ H] at HT
    obtain ⟨rfl, rfl⟩ := trans_step_inv HT
    exact owned_result_visible _ (act g[j] .step) _ _ _ (.inl ⟨t, headed_obs _ _ H, rfl, rfl⟩)
      rfl (guards_sbisim 2 _)
  · exact .inr ⟨_, 0, by rw [owned_interp_set_pool, rhs_guard n v j t _ H]; rfl,
      erasable_guard c n v g j t H He, fun l T => owned_result_guard c n v g j t l T H⟩
  · -- yield
    have Hs : owned_step (set_pool c (mk_pool (n + 1) v g (some j))) (act g[j] .yield)
        (set_pool c (mk_pool (n + 1) (v.set j (k ⟨⟩)) g none)) :=
      .inr (.inl ⟨k, headed_obs _ _ H, rfl, rfl⟩)
    exact .inr ⟨_, 0, by rw [owned_interp_set_pool, rhs_yield n v j k _ H]; rfl,
      erasable_step _ _ _ He Hs, fun l T => owned_result_silent _ _ _ l T Hs rfl⟩
  · -- fork
    have Hs : owned_step (set_pool c (mk_pool (n + 1) v g (some j))) (act g[j] .fork)
        (set_pool c (mk_pool (n + 2) (Vector.cons (k true) (v.set j (k false)))
          (Vector.cons g[j] g) (some j.succ))) :=
      .inr (.inr (.inl ⟨k, headed_obs _ _ H, rfl, rfl⟩))
    exact .inr ⟨_, 0, by rw [owned_interp_set_pool, rhs_fork n v j k _ H]; rfl,
      erasable_step _ _ _ He Hs, fun l T => owned_result_silent _ _ _ l T Hs rfl⟩
  · -- primitive
    have Hok : component_event_ok pe :=
      thread_ok_vis_ok pe k (thread_ok_headed _ _ (headed_obs _ _ H) Ht)
    have Ha : prim_addr_ok ((set_pool c (mk_pool (n + 1) v g (some j))).anchor g[j]) pe :=
      Cf _ .refl v[j] g[j] pe k rfl (headed_obs _ _ H)
    have Hr0 := prim_reflect_joined g[j] _ pe W Hok Ha
    have E := rhs_user n v j pe k (joined_state c) H
    rcases P : prim_step g[j] (set_pool c (mk_pool (n + 1) v g (some j))) pe with
      _ | ⟨kind, y, c1⟩ <;> rw [P] at Hr0
    · have Hr : sh pe (joined_state c) = .stuck := Hr0
      refine .inl fun l T HT => ?_
      rw [owned_interp_set_pool, E] at HT
      change trans l (sh pe (joined_state c) >>= _) T at HT
      rw [Hr, stuck_bind] at HT
      exact (trans_stuck_inv HT).elim
    have Hr : sh pe (joined_state c) = emit_list (action_logs (act g[j] kind) (joined_heap c1))
        (pure (y, joined_state c1)) := Hr0
    change _ = sh pe (joined_state c) >>= _ at E
    rw [Hr, emit_list_ret_bind] at E
    change RHS (n + 1) v (some j) (joined_state c) = emit_list _
      (guards 2 (owned_interp (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j))))) at E
    rw [show joined_heap c1 = joined_heap (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g
      (some j))) from rfl] at E
    have Hs : owned_step (set_pool c (mk_pool (n + 1) v g (some j))) (act g[j] kind)
        (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j))) :=
      .inr (.inr (.inr (.inr ⟨pe, k, kind, y, c1, headed_obs _ _ H, P, rfl, rfl⟩)))
    have Hk := prim_step_kind _ _ _ _ _ _ P
    rcases hl : erase_action_label (act g[j] kind)
      (joined_heap (set_pool c1 (mk_pool (n + 1) (v.set j (k y)) g (some j)))) with _ | l
    · rw [action_logs_none _ _ hl] at E
      exact .inr ⟨_, 1, E, erasable_step _ _ _ He Hs,
        fun l T => owned_result_silent _ _ _ l T Hs hl⟩
    · rcases erase_label_shape _ _ l hl with ⟨-, hk | hk⟩ | ⟨o, rfl⟩
      · exact absurd hk Hk.1
      · exact absurd hk Hk.2
      rw [action_logs_some _ _ _ hl, show label_logs [Label.obs o PUnit.unit] = [o] from rfl,
        emit_list_cons] at E
      refine .inl fun l' T HT => ?_
      rw [owned_interp_set_pool, E] at HT
      obtain ⟨⟨⟩, rfl, rfl⟩ := trans_vis_inv HT
      exact owned_result_visible _ _ _ _ _ Hs hl (guards_sbisim 2 _)
  · exfalso
    have Hb := Ht.2
    rw [branchfree_unfold, H] at Hb
    cases Hb

private theorem owned_interp_trans_aux {l : Label (writerE (CSLObs (Nat × Nat)))}
    {ot : CTreeF (writerE (CSLObs (Nat × Nat))) Bn (PUnit × SSig)
      (ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))}
    {T : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)} (HT : Trans_ l ot T) :
    Trans_ l ot T → ∀ n c, erasable c → ot = (guards n (owned_interp c)).unfold →
      owned_forward_result c l T := by
  induction HT
  case guard t t' l h ih =>
    intro H0 n c He Et
    cases n with
    | succ n =>
      rw [guards_succ, unfold_guard] at Et
      injection Et with Et
      exact ih h n c He (congrArg CTree.unfold Et)
    | zero =>
      rcases owned_interp_head c He with Hnow | ⟨d, k, Eh, Hd, Hlift⟩
      · exact Hnow _ _ (by
          unfold CTree.trans; rw [← guards_zero (owned_interp c), ← Et]; exact H0)
      · rw [guards_zero, Eh, guards_succ, unfold_guard] at Et
        injection Et with Et
        exact Hlift _ _ (ih h k d Hd (congrArg CTree.unfold Et))
  all_goals
    intro H0 n c He Et
    cases n with
    | succ n => rw [guards_succ, unfold_guard] at Et; cases Et
    | zero =>
      rcases owned_interp_head c He with Hnow | ⟨d, k, Eh, -, -⟩
      · exact Hnow _ _ (by
          unfold CTree.trans; rw [← guards_zero (owned_interp c), ← Et]; exact H0)
      · rw [guards_zero, Eh, guards_succ, unfold_guard] at Et; cases Et

theorem owned_interp_trans_forward (c : OwnedCfg) (l : Label (writerE (CSLObs (Nat × Nat))))
    (T : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) (He : erasable c)
    (HT : trans l (owned_interp c) T) :
    ∃ d, Star silent_next c d ∧
      ((∃ a d', owned_step d a d' ∧ erase_action_label a (joined_heap d') = some l ∧
          T ~ owned_interp d') ∨
       (d.pool.size = 0 ∧ l = .val (PUnit.unit, joined_state d) ∧
          T ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)))) :=
  owned_interp_trans_aux HT HT 0 c He rfl

theorem owned_silent_local (c d : OwnedCfg) (i : Side) (He : active_erasable c)
    (Hp : Star silent_next c d) : owned_interp (project i c) ~ owned_interp (project i d) := by
  induction Hp with
  | refl => exact sbisim_refl _
  | @tail b d' Hp hab ih =>
    refine sbisim_trans ih ?_
    obtain ⟨a, Hs, Hl⟩ := hab
    by_cases Ho : a.owner = i
    · obtain ⟨q, Hq, Eq⟩ := owned_step_own i b a d' Hs Ho
      obtain rfl := owned_equ_eq Eq
      exact owned_interp_silent _ _ (owned_active_local _ i (owned_silent_active _ _ He Hp))
        (Star.single ⟨_, Hq, (owned_project_label_none i b a _ _).2 Hl⟩)
    · rw [owned_equ_eq (owned_step_foreign i b a d' Hs Ho)]; exact sbisim_refl _

theorem owned_label_ktrans (a : OwnedAction) (h : ManagedHeap)
    (l : Label (writerE (CSLObs (Nat × Nat)))) (t u : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig))
    (w : World (writerE (CSLObs (Nat × Nat)))) (Hl : erase_action_label a h = some l)
    (HT : trans l t u) (Hw : NotDone w) : ktrans t w u (after_logs (action_logs a h) w) := by
  rw [action_logs_some a h l Hl]
  rcases erase_label_shape a h l Hl with ⟨rfl, -⟩ | ⟨o, rfl⟩
  · exact .tau Hw HT
  · exact .obs o ⟨⟩ Hw HT

theorem owned_ktrans_forward (c : OwnedCfg) (w : World (writerE (CSLObs (Nat × Nat))))
    (u : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) (v : World (writerE (CSLObs (Nat × Nat))))
    (He : erasable c) (Hw : NotDone w) (HT : ktrans (owned_interp c) w u v) (Hv : NotDone v) :
    ∃ d a d' l, Star silent_next c d ∧ owned_step d a d' ∧
      erase_action_label a (joined_heap d') = some l ∧ u ~ owned_interp d' ∧
      v = after_logs (action_logs a (joined_heap d')) w := by
  cases HT with
  | tau _ Ht =>
    obtain ⟨d, Hp, ⟨a, d', Hs, Hl, Eu⟩ | ⟨-, Hl, -⟩⟩ := owned_interp_trans_forward c _ u He Ht
    · exact ⟨d, a, d', _, Hp, Hs, Hl, Eu, by rw [action_logs_some _ _ _ Hl]; rfl⟩
    · cases Hl
  | obs e x _ Ht =>
    obtain ⟨d, Hp, ⟨a, d', Hs, Hl, Eu⟩ | ⟨-, Hl, -⟩⟩ := owned_interp_trans_forward c _ u He Ht
    · exact ⟨d, a, d', _, Hp, Hs, Hl, Eu, by rw [action_logs_some _ _ _ Hl]; rfl⟩
    · cases Hl
  | done => cases Hv
  | finish => cases Hv

theorem owned_owner_ktrans (c : OwnedCfg) (a : OwnedAction) (d : OwnedCfg) (i : Side)
    (w : World (writerE (CSLObs (Nat × Nat)))) (He : active_erasable c) (Hs : owned_step c a d)
    (Ho : a.owner = i) (Hv : erase_action_label a (joined_heap d) ≠ none) (Hw : NotDone w) :
    ∃ u, ktrans (owned_interp (project i c)) w u
        (after_logs (action_logs (project_action i c a) (joined_heap (project i d))) w) ∧
      u ~ owned_interp (project i d) := by
  obtain ⟨q, Hq, Eq⟩ := owned_step_own i c a d Hs Ho
  obtain rfl := owned_equ_eq Eq
  rcases Hl : erase_action_label (project_action i c a) (joined_heap (project i d)) with _ | l
  · exact absurd ((owned_project_label_none i c a _ _).1 Hl) Hv
  obtain ⟨u, Hu, Eu⟩ :=
    owned_interp_visible _ _ _ _ l (owned_active_local c i He) .refl Hq Hl
  exact ⟨u, owned_label_ktrans _ _ l _ u w Hl Hu Hw, Eu⟩

theorem owned_interp_val_forward (c : OwnedCfg) (r : PUnit × SSig)
    (u : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) (He : erasable c)
    (HT : trans (.val r) (owned_interp c) u) :
    ∃ d, Star silent_next c d ∧ d.pool.size = 0 ∧ r = (PUnit.unit, joined_state d) ∧
      u ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  obtain ⟨d, Hp, ⟨a, d', -, Hl, -⟩ | ⟨Hz, Hl, Eu⟩⟩ := owned_interp_trans_forward c _ u He HT
  · exact absurd Hl (owned_label_not_value a _ r)
  · exact ⟨d, Hp, Hz, val_eq_inv Hl, Eu⟩

theorem owned_ktrans_terminal (c : OwnedCfg) (w : World (writerE (CSLObs (Nat × Nat))))
    (u : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) (v : World (writerE (CSLObs (Nat × Nat))))
    (He : erasable c) (HT : ktrans (owned_interp c) w u v) (Hnd : ¬ NotDone v) :
    ∃ d, Star silent_next c d ∧ d.pool.size = 0 ∧
      u ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) ∧
      DoneWith (fun r predecessor => r = (PUnit.unit, joined_state d) ∧ predecessor = w) v := by
  cases HT with
  | tau Hw => exact absurd Hw Hnd
  | obs e x => exact absurd (.obs e x) Hnd
  | done x Ht =>
    obtain ⟨d, Hp, Hz, Ex, Eu⟩ := owned_interp_val_forward c x u He Ht
    exact ⟨d, Hp, Hz, Eu, .done x ⟨Ex, rfl⟩⟩
  | finish e y x Ht =>
    obtain ⟨d, Hp, Hz, Ex, Eu⟩ := owned_interp_val_forward c x u He Ht
    exact ⟨d, Hp, Hz, Eu, .finish e y x ⟨Ex, rfl⟩⟩

theorem owned_side_ready_step (i : Side) (c : OwnedCfg) (a : OwnedAction) (c' : OwnedCfg)
    (Hs : owned_step c a c') (Ho : a.owner = i) : owned_side_ready i c' := by
  rcases c with ⟨⟨_ | n, v, g, _ | j⟩, an, he, cx, b, co, la⟩
  · exact Hs.elim
  · exact Hs.elim
  · obtain ⟨j, rfl, rfl⟩ := (Hs : sel_step _ n v g a c')
    exact .inr ⟨j, rfl, Ho⟩
  · rcases (Hs : focus_step _ n v g j a c') with ⟨t, -, rfl, rfl⟩ | ⟨k, -, rfl, rfl⟩ |
      ⟨k, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨e, k, kind, y, c1, -, -, rfl, rfl⟩
    · exact .inr ⟨j, rfl, Ho⟩
    · exact .inl rfl
    · exact .inr ⟨j.succ, rfl, (Vector.getElem_cons_succ _ _ _ (by omega)).trans Ho⟩
    · exact .inl rfl
    · exact .inr ⟨j, rfl, Ho⟩

theorem owned_local_silent_lift_cfg (i : Side) (d d' : OwnedCfg) (Hp : Star silent_next d d') :
    ∀ c, owned_equ (project i c) d → owned_side_ready i c →
      ∃ c', Star silent_next c c' ∧ owned_side_ready i c' ∧ owned_equ (project i c') d' ∧
        owned_equ (project (other i) c') (project (other i) c) := by
  induction Hp with
  | refl =>
    intro c E Hr
    exact ⟨c, .refl, Hr, E, owned_equ_Equivalence.refl _⟩
  | tail _ hab ih =>
    intro c E Hr
    obtain ⟨c1, H1, Hr1, E1, Ef1⟩ := ih c E Hr
    obtain ⟨a, Hs, Hl⟩ := hab
    obtain rfl := owned_equ_eq E1
    obtain ⟨b, c', Hb, Ho, Ha, Ep⟩ := owned_step_lift i c1 a _ Hr1 Hs
    refine ⟨c', H1.tail ⟨b, Hb, ?_⟩, owned_side_ready_step i c1 b c' Hb Ho, Ep, ?_⟩
    · subst Ha
      exact (owned_project_label_none i c1 b _ _).1 Hl
    · rw [owned_equ_eq (owned_step_foreign (other i) c1 b c' Hb (by rw [Ho]; cases i <;> nofun))]
      exact Ef1

theorem owned_side_ready_empty (i : Side) (c : OwnedCfg) (Hr : owned_side_ready i c)
    (Hz : (project i c).pool.size = 0) : c.pool.focus = none := by
  rcases Hr with Hf | ⟨j, Hf, Htag⟩
  · exact Hf
  · obtain ⟨r, -⟩ := project_focused_index i c.pool j Hf Htag
    exact absurd (Hz ▸ r.isLt : r.val < 0) (Nat.not_lt_zero _)

theorem owned_interp_terminal (c : OwnedCfg) (_ : erasable c) (Hz : c.pool.size = 0) :
    owned_interp c ~ (pure (PUnit.unit, joined_state c) :
      ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  rcases c with ⟨⟨n, v, g, f⟩, an, he, cx, b, co, la⟩
  cases Hz
  rcases f with _ | j
  · exact (rhs_empty v _).symm ▸ sbisim_refl _
  · exact j.elim0

theorem owned_interp_terminal_trans (c d : OwnedCfg) (He : erasable c)
    (Hp : Star silent_next c d) (Hz : d.pool.size = 0) :
    ∃ T, trans (.val (PUnit.unit, joined_state d)) (owned_interp c) T ∧
      T ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  have Eback : (pure (PUnit.unit, joined_state d) : ctreeW (CSLObs (Nat × Nat)) Bn _) ~
      owned_interp c :=
    sbisim_trans (sbisim_symm (owned_interp_terminal d (owned_silent_erasable c d He Hp) Hz))
      (sbisim_symm (owned_interp_silent c d He Hp))
  obtain ⟨T, HC, ET⟩ := Tisl.Yield.sbisim_trans_l _ _ _ _ Eback (trans_ret _)
  exact ⟨T, HC, sbisim_symm ET⟩

theorem owned_silent_unfocused (c d : OwnedCfg) (Hp : Star silent_next c d)
    (Hf : c.pool.focus = none) : c = d := by
  rcases Hp.cases_head with rfl | ⟨b, ⟨a, Hs, Hl⟩, -⟩
  · rfl
  · have Hk := owned_step_unfocused c a b Hf Hs
    unfold erase_action_label at Hl
    rw [Hk] at Hl
    cases Hl

/-- Projected canonical results expose exactly one lineage's state. -/
theorem owned_joined_state_project (i : Side) (c : OwnedCfg) :
    joined_state (project i c) = local_state i c := by
  cases i <;> simp [joined_state, local_state, joined_heap, global_count, project, side_only,
    side_eqb]
  · exact managed_heap_ext _ _ (pop_emp_r _ (pdef_emp_r _))
  · exact managed_heap_ext _ _ (pop_emp _)

-- Not ported: `thread_ok_equ` (Rocq `≅` is `=`), `reach_equ` and `prim_addr_ok_peq` (only used
-- by `head_confined_equ`/`erasable_equ`, which follow from `owned_equ_eq`).

end Tisl.CSL
