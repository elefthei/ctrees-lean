/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Shared
public import Logic.CTree.TraceRules
public import Logic.Congruence

/-!
# Regression: two cooperating processes, `AF` under both schedulers

`fork2 (proc 1) (proc 2)`: each process reads, increments and emits its own cell, then yields.
Each process's native `AF ret` fact is proved on its own region and framed by the other's
(`work_af_framed_ret`); the cooperative prefix equation (`run_rr_prefix`/`run_nd_prefix`) runs the
focused process alone, then the yield rejoins the pool. Both processes finish and the heap is the
join of the two incremented regions (← `examples/CSL/Frame/AF.v`).
-/

@[expose] public section
namespace Examples.CSL.Frame.AF
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared

/-- Round-robin execution finishes both processes with their incremented regions. -/
private theorem af_two_procs_rr_ret (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AF (.ret fun (r : PUnit × SSig) _ => both (a + 1) (b + 1) (csl_memory r.2)))
      (run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_rr_fork_bind _ _ _)).2 ?_
  rw [show (#v[denote (proc 1), denote (proc 2)] : Pool sE Bn 2) =
    (#v[denote (proc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (proc 2) >>= fun _ => pure ⟨⟩) from rfl]
  rw [show proc 2 = .bind (work 2) _ from rfl, interp_rr_bind]
  refine (proper_entails_meq _ (run_rr_prefix 1 _ 1 _ _ 0 _ (work_yield_fork_free 2))).2 ?_
  refine u_bind_r (q := .A) (work_af_framed_ret_W 2 1 b a ctx c _ _ .pure
    (frame_rel_shared_2 a b ctx c)) ?_
  rintro ⟨r, s1⟩ w1 HP
  obtain ⟨rfl, HM1, HS1, rfl⟩ := frame_post_work_W _ _ _ _ _ _ _ _ _ HP
  dsimp only
  rw [interp_rr_bind]
  refine (proper_entails_meq _ (interp_rr_yield _ _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_rr_select sh 1 _ 0 s1)).2 ?_
  refine (au_vis PUnit.unit).1 (.inr ⟨ticll_top (.obs _ _), fun _ => ?_⟩)
  show entails _ (interp_schedule_rr sh (1 + 1)
      ((#v[denote (.ret ()), denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
        (denote_flow (.bind (work 1) fun _ => .bind .yield fun _ => .ret ()) >>= fun _ => pure ⟨⟩))
      (some 0) (0 + 1) s1) _
  rw [interp_rr_bind]
  refine (proper_entails_meq _ (run_rr_prefix 1 _ 0 _ _ _ _ (work_yield_fork_free 1))).2 ?_
  refine u_bind_r (q := .A) (work_af_framed_ret_W 1 2 a (b + 1) ctx (c + 1) _ _ (.obs _ _)
    (frame_rel_both_1 _ _ _ _ _ ?_ HS1)) ?_
  · exact peq_trans _ _ _ HM1 (pop_comm _ _ (region_disj _ _ _ _ (by decide)))
  rintro ⟨r, s2⟩ w2 HP
  obtain ⟨rfl, HM2, -, rfl⟩ := frame_post_work_W _ _ _ _ _ _ _ _ _ HP
  dsimp only
  rw [interp_rr_bind]
  refine (proper_entails_meq _ (interp_rr_yield _ _ _ _ _ _)).2 ?_
  show entails _ (interp_schedule_rr sh 2 #v[denote (.ret ()), denote (.ret ())] none 1 s2) _
  rw [show (#v[denote (.ret ()), denote (.ret ())] : Pool sE Bn 2) =
    csl_pool (Vector.replicate 2 (.ret ())) from
      Vector.ext fun i hi => by match i, hi with | 0, _ | 1, _ => simp [csl_pool]]
  change entails _ (run_rr_pool _ none 1 s2) _
  refine (proper_entails_meq _ (run_rr_pool_returns 2 none 1 s2)).2 ?_
  exact f_emit_list .A _ _ _ _ (.obs _ _)
    (.matchA (ret_ret (after_logs_not_done _ (.obs _ _)) HM2))

/-- Preserve the original eventual terminal claim. -/
theorem af_two_procs_rr (a b : Nat) (ctx : Ctx) (c : Nat) :
    Auc (entails (⊤ : TiclL (writerE rr_obs)))
      (fun _ wd => DoneWith (X := PUnit × SSig)
        (fun r _ => both (a + 1) (b + 1) (csl_memory r.2)) wd)
      (run_rr (fork2 (proc 1) (proc 2)) (shared a b ctx c)) .pure :=
  af_ret_done _ (af_two_procs_rr_ret a b ctx c)

/-- Process 1 alone in the pool, framed by process 2's finished region. -/
private theorem nd_tail_work1_ret (a b : Nat) (ctx : Ctx) (c : Nat) (s : SSig)
    (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    csl_memory s ≈ region 1 a ⊎ region 2 (b + 1) → s.2 = (ctx, c + 1) →
    entails (AF (.ret fun (r : PUnit × SSig) _ => both (a + 1) (b + 1) (csl_memory r.2)))
      (interp_schedule_nd sh 1 #v[denote_flow (proc 1) >>= fun _ => pure ⟨⟩] none s) w := by
  intro Hw HM HS
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 0 _ s)).2 ?_
  refine (au_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).1 (.inr ⟨ticll_top Hw, fun j => ?_⟩)
  refine (fun i => ?_ : ∀ i : Fin 1, entails _ (interp_schedule_nd sh _ _ (some i) s) w) _
  obtain rfl := fin1_eq i
  show entails _ (interp_schedule_nd sh (0 + 1) ((#v[denote (.ret ())] : Pool sE Bn 1).set
    (0 : Fin 1) (denote_flow (.bind (work 1) fun _ => .bind .yield fun _ => .ret ()) >>=
      fun _ => pure ⟨⟩)) (some 0) s) w
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (run_nd_prefix 0 _ 0 _ _ _ (work_yield_fork_free 1))).2 ?_
  refine u_bind_r (q := .A) (work_af_framed_ret 1 2 a (b + 1) ctx (c + 1) _ _ Hw
    (frame_rel_both_1 _ _ _ _ _ HM HS)) ?_
  rintro ⟨r, s2⟩ w2 HP
  obtain ⟨rfl, HM2, -, rfl⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  dsimp only
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
  show entails _ (interp_schedule_nd sh 1 #v[denote (.ret ())] none s2) _
  rw [show (#v[denote (.ret ())] : Pool sE Bn 1) = csl_pool (Vector.replicate 1 (.ret ())) from
      Vector.ext fun i hi => by match i, hi with | 0, _ => simp [csl_pool]]
  change entails _ (run_nd_pool _ none s2) _
  refine (proper_entails_meq _ (run_nd_pool_returns 1 none s2)).2 ?_
  exact au_step.1 (.inr ⟨ticll_top (.obs _ _), .matchA (ret_ret (.obs _ _) HM2)⟩)

/-- Every nondeterministic schedule finishes both processes with their incremented regions. -/
private theorem af_two_procs_nd_ret (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AF (.ret fun (r : PUnit × SSig) _ => both (a + 1) (b + 1) (csl_memory r.2)))
      (run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_nd_fork_bind _ _ _)).2 ?_
  rw [show (#v[denote (proc 1), denote (proc 2)] : Pool sE Bn 2) =
    (#v[denote (proc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (proc 2) >>= fun _ => pure ⟨⟩) from rfl]
  rw [show proc 2 = .bind (work 2) _ from rfl, interp_nd_source_bind]
  refine (proper_entails_meq _ (run_nd_prefix 1 _ 1 _ _ _ (work_yield_fork_free 2))).2 ?_
  refine u_bind_r (q := .A) (work_af_framed_ret 2 1 b a ctx c _ _ .pure
    (frame_rel_shared_2 a b ctx c)) ?_
  rintro ⟨r, s1⟩ w1 HP
  obtain ⟨rfl, HM1, HS1, rfl⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  have HM1' : csl_memory s1 ≈ region 1 a ⊎ region 2 (b + 1) :=
    peq_trans _ _ _ HM1 (pop_comm _ _ (region_disj _ _ _ _ (by decide)))
  dsimp only
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 1 _ s1)).2 ?_
  refine (au_brS (B := Bn) (c := ⟨1 + 1⟩) ⟨0⟩).1 (.inr ⟨ticll_top (.obs _ _), fun j => ?_⟩)
  refine (fun i => ?_ : ∀ i : Fin 2, entails _ (interp_schedule_nd sh _ _ (some i) s1) _) _
  match i with
  | 0 =>
    -- Child first.
    show entails _ (interp_schedule_nd sh (1 + 1)
        ((#v[denote (.ret ()), denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
          (denote_flow (.bind (work 1) fun _ => .bind .yield fun _ => .ret ()) >>=
            fun _ => pure ⟨⟩))
        (some 0) s1) _
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (run_nd_prefix 1 _ 0 _ _ _ (work_yield_fork_free 1))).2 ?_
    refine u_bind_r (q := .A) (work_af_framed_ret 1 2 a (b + 1) ctx (c + 1) _ _ (.obs _ _)
      (frame_rel_both_1 _ _ _ _ _ HM1' HS1)) ?_
    rintro ⟨r, s2⟩ w2 HP
    obtain ⟨rfl, HM2, -, rfl⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
    dsimp only
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
    show entails _ (interp_schedule_nd sh 2 #v[denote (.ret ()), denote (.ret ())] none s2) _
    rw [show (#v[denote (.ret ()), denote (.ret ())] : Pool sE Bn 2) =
      csl_pool (Vector.replicate 2 (.ret ())) from
        Vector.ext fun i hi => by match i, hi with | 0, _ | 1, _ => simp [csl_pool]]
    change entails _ (run_nd_pool _ none s2) _
    refine (proper_entails_meq _ (run_nd_pool_returns 2 none s2)).2 ?_
    refine au_step.1 (.inr ⟨ticll_top (.obs _ _), au_step.1 (.inr ⟨ticll_top (.obs _ _), ?_⟩)⟩)
    exact .matchA (ret_ret (.obs _ _) HM2)
  | 1 =>
    -- Parent first: it returns and leaves the child alone in the pool.
    rw [interp_nd_source_ret]
    refine (proper_entails_meq _ (interp_schedule_nd_ret sh 1 _ 1 s1 (by simp))).2 ?_
    rw [show ((#v[denote (proc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
        (pure ⟨⟩)).eraseIdx (1 : Fin 2) = #v[denote_flow (proc 1) >>= fun _ => pure ⟨⟩] from
      Vector.ext fun i hi => by match i, hi with | 0, _ => simp [denote]]
    exact nd_tail_work1_ret a b ctx c s1 _ (.obs _ _) HM1' HS1

/-- Preserve the original eventual terminal claim for every schedule. -/
theorem af_two_procs_nd (a b : Nat) (ctx : Ctx) (c : Nat) :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (X := PUnit × SSig)
        (fun r _ => both (a + 1) (b + 1) (csl_memory r.2)) wd)
      (run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)) .pure :=
  af_ret_done _ (af_two_procs_nd_ret a b ctx c)

/-- Concrete round-robin result for initial cell values `3` and `5`. -/
theorem af_rr_3_5 (ctx : Ctx) :
    Auc (entails (⊤ : TiclL (writerE rr_obs)))
      (fun _ wd => DoneWith (X := PUnit × SSig)
        (fun r _ => (csl_memory r.2).1 1 = some 4 ∧ (csl_memory r.2).1 2 = some 6) wd)
      (run_rr (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) .pure :=
  aur_done_mono _ _ _ _ _ (fun _ _ HB => both_lookup _ _ _ HB) (af_two_procs_rr 3 5 ctx 0)

/-- Concrete nondeterministic result for initial cell values `3` and `5`. -/
theorem af_nd_3_5 (ctx : Ctx) :
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (X := PUnit × SSig)
        (fun r _ => (csl_memory r.2).1 1 = some 4 ∧ (csl_memory r.2).1 2 = some 6) wd)
      (run_nd (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) .pure :=
  aur_done_mono _ _ _ _ _ (fun _ _ HB => both_lookup _ _ _ HB) (af_two_procs_nd 3 5 ctx 0)

#print axioms af_two_procs_rr

end Examples.CSL.Frame.AF
