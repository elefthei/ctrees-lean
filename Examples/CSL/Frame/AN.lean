/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Shared

/-!
# Regression: two heap-writing processes joined through `yield`

`fork2 (wproc 1) (wproc 2)`: each process writes `1` into its own cell and yields. Two heap
observations and three logged scheduler selections precede the native return. Each write is proved
on its own region and framed by the other one. `write_ax_ret_framed` packages each write's
observation and native return for `an_bind_l`; `frame_post_write` recovers the joined memory,
unchanged context/counter and exact post-write world. The final value transition gives the six-next
terminal contracts below (← `examples/CSL/Frame/AN.v`).
-/

@[expose] public section
namespace Examples.CSL.Frame.AN
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared

/-- The frame of process `1` after process `2` wrote: the shared memory seen with region `2`
first. -/
theorem frame_rel_after_2 (a : Nat) (s : SSig) (ctx : Ctx) (c : Nat) :
    csl_memory s ≈ region 2 1 ⊎ region 1 a → s.2 = (ctx, c) →
    frame_rel (region 2 1) (own 1 a ctx c) s := fun Hm Hs =>
  frame_rel_both_1 a 1 ctx c s
    (peq_trans _ _ _ Hm (pop_comm _ _ (region_disj 2 1 1 a (by decide)))) Hs

/-- Native return follows two heap observations and three logged round-robin picks. -/
theorem an_two_procs_rr_ret (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AX (AX (AX (AX (AX (.ret fun (r : PUnit × SSig) _ =>
        both 1 1 (csl_memory r.2)))))))
      (run_rr (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_rr_fork_bind _ _ _)).2 ?_
  -- parent: write 2, yield
  rw [show (#v[denote (wproc 1), denote (wproc 2)] : Pool sE Bn 2) =
    (#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (wproc 2) >>= fun _ => pure ⟨⟩) from rfl]
  rw [show wproc 2 = .bind (.write 2 1) _ from rfl, interp_rr_bind]
  refine (proper_entails_meq _ (run_rr_prefix 1 _ 1 _ _ 0 _ (write_yield_fork_free 2))).2 ?_
  refine an_bind_l (write_ax_ret_framed_W 2 1 b a ctx c _ _ .pure
    (frame_rel_shared_2 a b ctx c)) ?_
  rintro ⟨r, s1⟩ w1 HP
  obtain ⟨rfl, Hm1, Hs1, rfl⟩ := frame_post_write_W _ _ _ _ _ _ _ _ HP
  dsimp only
  rw [interp_rr_bind]
  refine (proper_entails_meq _ (interp_rr_yield _ _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_rr_select sh 1 _ 0 s1)).2 ?_
  refine (an_vis PUnit.unit).2 ⟨ticll_top (.obs _ _), fun _ => ?_⟩
  -- child: write 1, yield
  show entails _ (interp_schedule_rr sh (1 + 1)
      ((#v[pure ⟨⟩, denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
        (denote_flow (.bind (.write 1 1) fun _ => .bind .yield fun _ => .ret ()) >>=
          fun _ => pure ⟨⟩)) (some 0) (0 + 1) s1) _
  rw [interp_rr_bind]
  refine (proper_entails_meq _ (run_rr_prefix 1 _ 0 _ _ _ _ (write_yield_fork_free 1))).2 ?_
  refine an_bind_l (write_ax_ret_framed_W 1 2 a 1 ctx c _ _ (.obs _ _)
    (frame_rel_after_2 a s1 ctx c Hm1 Hs1)) ?_
  rintro ⟨r, s2⟩ w2 HP
  obtain ⟨rfl, Hm2, -, rfl⟩ := frame_post_write_W _ _ _ _ _ _ _ _ HP
  dsimp only
  rw [interp_rr_bind]
  refine (proper_entails_meq _ (interp_rr_yield _ _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_rr_select sh 1 _ _ s2)).2 ?_
  refine (an_vis PUnit.unit).2 ⟨ticll_top (.obs _ _), fun _ => ?_⟩
  -- parent returns
  show entails _ (interp_schedule_rr sh (1 + 1)
      ((#v[denote (.ret ()), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
        (denote_flow (.ret ()) >>= fun _ => pure ⟨⟩)) (some 1) (0 + 1 + 1) s2) _
  rw [interp_rr_ret]
  refine (proper_entails_meq _ (interp_schedule_rr_ret sh 1 _ 1 _ s2 (by simp))).2 ?_
  rw [show ((#v[denote (.ret ()), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (pure ⟨⟩)).eraseIdx (1 : Fin 2) = #v[denote (.ret ())] from
    Vector.ext fun i hi => by match i, hi with | 0, _ => simp [denote]]
  refine (proper_entails_meq _ (interp_schedule_rr_select sh 0 _ _ s2)).2 ?_
  refine (an_vis PUnit.unit).2 ⟨ticll_top (.obs _ _), fun _ => ?_⟩
  -- child returns
  show entails _ (interp_schedule_rr sh (0 + 1)
      ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
        (denote_flow (.ret ()) >>= fun _ => pure ⟨⟩)) (some 0) (0 + 1 + 1 + 1) s2) _
  rw [interp_rr_ret]
  refine (proper_entails_meq _ (interp_schedule_rr_ret sh 0 _ 0 _ s2 (by simp))).2 ?_
  refine (proper_entails_meq _ (interp_schedule_rr_empty sh _ _ s2)).2 ?_
  exact ret_ret (.obs _ _) Hm2

/-- Consequence under six semantic next layers. -/
theorem ax6_done_mono {W X : Type} (t : ctreeW W Bn X) (w : World (writerE W))
    (P Q : X → World (writerE W) → Prop) :
    (∀ x w, P x w → Q x w) →
    anc (entails (⊤ : TiclL (writerE W))) (anc (entails (⊤ : TiclL (writerE W)))
      (anc (entails (⊤ : TiclL (writerE W))) (anc (entails (⊤ : TiclL (writerE W)))
        (anc (entails (⊤ : TiclL (writerE W))) (anc (entails (⊤ : TiclL (writerE W)))
          (fun _ wd => DoneWith P wd)))))) t w →
    anc (entails (⊤ : TiclL (writerE W))) (anc (entails (⊤ : TiclL (writerE W)))
      (anc (entails (⊤ : TiclL (writerE W))) (anc (entails (⊤ : TiclL (writerE W)))
        (anc (entails (⊤ : TiclL (writerE W))) (anc (entails (⊤ : TiclL (writerE W)))
          (fun _ wd => DoneWith Q wd)))))) t w := fun HPQ =>
  anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r
    (fun _ _ => done_with_mono HPQ)))))) _ _

/-- A nondeterministic singleton pool whose thread returns: one selection, then the native
return carrying any postcondition that holds now. -/
private theorem nd_singleton_ret (ts : Pool sE Bn 1) (s : SSig)
    (w : World (writerE (CSLObs (Nat × Nat))))
    (P : PUnit × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop)
    (hts : ts[0] = denote (.ret ())) :
    NotDone w → P (⟨⟩, s) w → entails (AX (.ret P)) (interp_schedule_nd sh 1 ts none s) w := by
  obtain rfl : ts = #v[denote (.ret ())] :=
    Vector.ext fun i hi => by match i, hi with | 0, _ => exact hts
  intro Hw Hm
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 0 _ s)).2 ?_
  refine (an_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).2 ⟨ticll_top Hw, fun j => ?_⟩
  refine (fun i => ?_ : ∀ i : Fin 1, entails _ (interp_schedule_nd sh _ _ (some i) s) w) _
  obtain rfl := fin1_eq i
  show entails _ (interp_schedule_nd sh (0 + 1) ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
    (denote_flow (.ret ()) >>= fun _ => pure ⟨⟩)) (some 0) s) w
  rw [interp_nd_source_ret]
  refine (proper_entails_meq _ (interp_schedule_nd_ret sh 0 _ 0 s (by simp))).2 ?_
  refine (proper_entails_meq _ (interp_schedule_nd_empty sh _ s)).2 ?_
  exact ret_ret Hw Hm

/-- Native return follows two heap observations and three nondeterministic picks. -/
theorem an_two_procs_nd_ret (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AX (AX (AX (AX (AX (.ret fun (r : PUnit × SSig) _ =>
        both 1 1 (csl_memory r.2)))))))
      (run_nd (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_nd_fork_bind _ _ _)).2 ?_
  -- parent: write 2, yield
  rw [show (#v[denote (wproc 1), denote (wproc 2)] : Pool sE Bn 2) =
    (#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (wproc 2) >>= fun _ => pure ⟨⟩) from rfl]
  rw [show wproc 2 = .bind (.write 2 1) _ from rfl, interp_nd_source_bind]
  refine (proper_entails_meq _ (run_nd_prefix 1 _ 1 _ _ _ (write_yield_fork_free 2))).2 ?_
  refine an_bind_l (write_ax_ret_framed 2 1 b a ctx c _ _ .pure
    (frame_rel_shared_2 a b ctx c)) ?_
  rintro ⟨r, s1⟩ w1 HP
  obtain ⟨rfl, Hm1, Hs1, rfl⟩ := frame_post_write _ _ _ _ _ _ _ _ HP
  dsimp only
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 1 _ s1)).2 ?_
  refine (an_brS (B := Bn) (c := ⟨1 + 1⟩) ⟨0⟩).2 ⟨ticll_top (.obs _ _), fun j => ?_⟩
  refine (fun i => ?_ : ∀ i : Fin 2, entails _ (interp_schedule_nd sh _ _ (some i) s1) _) _
  match i with
  | 0 =>
    -- child first: write 1, yield
    show entails _ (interp_schedule_nd sh (1 + 1)
        ((#v[pure ⟨⟩, denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
          (denote_flow (.bind (.write 1 1) fun _ => .bind .yield fun _ => .ret ()) >>=
            fun _ => pure ⟨⟩)) (some 0) s1) _
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (run_nd_prefix 1 _ 0 _ _ _ (write_yield_fork_free 1))).2 ?_
    refine an_bind_l (write_ax_ret_framed 1 2 a 1 ctx c _ _ (.obs _ _)
      (frame_rel_after_2 a s1 ctx c Hm1 Hs1)) ?_
    rintro ⟨r, s2⟩ w2 HP
    obtain ⟨rfl, Hm2, -, rfl⟩ := frame_post_write _ _ _ _ _ _ _ _ HP
    dsimp only
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
    refine (proper_entails_meq _ (interp_schedule_nd_select sh 1 _ s2)).2 ?_
    refine (an_brS (B := Bn) (c := ⟨1 + 1⟩) ⟨0⟩).2 ⟨ticll_top (.obs _ _), fun j => ?_⟩
    refine (fun i => ?_ : ∀ i : Fin 2, entails _ (interp_schedule_nd sh _ _ (some i) s2) _) _
    match i with
    | 0 =>
      -- child returns, then parent
      show entails _ (interp_schedule_nd sh (1 + 1)
          ((#v[pure ⟨⟩, denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
            (denote_flow (.ret ()) >>= fun _ => pure ⟨⟩)) (some 0) s2) _
      rw [interp_nd_source_ret]
      refine (proper_entails_meq _ (interp_schedule_nd_ret sh 1 _ 0 s2 (by simp))).2 ?_
      exact nd_singleton_ret _ s2 _ _ (by simp [denote]) (.obs _ _) Hm2
    | 1 =>
      -- parent returns, then child
      show entails _ (interp_schedule_nd sh (1 + 1)
          ((#v[denote (.ret ()), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
            (denote_flow (.ret ()) >>= fun _ => pure ⟨⟩)) (some 1) s2) _
      rw [interp_nd_source_ret]
      refine (proper_entails_meq _ (interp_schedule_nd_ret sh 1 _ 1 s2 (by simp))).2 ?_
      exact nd_singleton_ret _ s2 _ _ (by simp [denote]) (.obs _ _) Hm2
  | 1 =>
    -- parent first: returns; then the child writes, yields, returns
    show entails _ (interp_schedule_nd sh (1 + 1)
        ((#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
          (denote_flow (.ret ()) >>= fun _ => pure ⟨⟩)) (some 1) s1) _
    rw [interp_nd_source_ret]
    refine (proper_entails_meq _ (interp_schedule_nd_ret sh 1 _ 1 s1 (by simp))).2 ?_
    rw [show ((#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
        (pure ⟨⟩)).eraseIdx (1 : Fin 2) = #v[denote (wproc 1)] from
      Vector.ext fun i hi => by match i, hi with | 0, _ => simp [denote]]
    refine (proper_entails_meq _ (interp_schedule_nd_select sh 0 _ s1)).2 ?_
    refine (an_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).2 ⟨ticll_top (.obs _ _), fun j => ?_⟩
    refine (fun i => ?_ : ∀ i : Fin 1, entails _ (interp_schedule_nd sh _ _ (some i) s1) _) _
    obtain rfl := fin1_eq i
    show entails _ (interp_schedule_nd sh (0 + 1)
        ((#v[pure ⟨⟩] : Pool sE Bn 1).set (0 : Fin 1)
          (denote_flow (.bind (.write 1 1) fun _ => .bind .yield fun _ => .ret ()) >>=
            fun _ => pure ⟨⟩)) (some 0) s1) _
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (run_nd_prefix 0 _ 0 _ _ _ (write_yield_fork_free 1))).2 ?_
    refine an_bind_l (write_ax_ret_framed 1 2 a 1 ctx c _ _ (.obs _ _)
      (frame_rel_after_2 a s1 ctx c Hm1 Hs1)) ?_
    rintro ⟨r, s2⟩ w2 HP
    obtain ⟨rfl, Hm2, -, rfl⟩ := frame_post_write _ _ _ _ _ _ _ _ HP
    dsimp only
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
    exact nd_singleton_ret _ s2 _ _ (by simp [denote]) (.obs _ _) Hm2

/-- Preserve the terminal properties at their six-transition boundary. -/
theorem an_two_procs_rr (a b : Nat) (ctx : Ctx) (c : Nat) :
    anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
      (anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
        (anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
          (fun _ wd => DoneWith (X := PUnit × SSig)
            (fun r _ => both 1 1 (csl_memory r.2)) wd))))))
      (run_rr (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)) .pure :=
  anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r
    (fun _ _ h => ret_done_next _ h))))) _ _ (an_two_procs_rr_ret a b ctx c)

theorem an_two_procs_nd (a b : Nat) (ctx : Ctx) (c : Nat) :
    anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
        (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
          (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
            (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
              (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
                (fun _ wd => DoneWith (X := PUnit × SSig)
                  (fun r _ => both 1 1 (csl_memory r.2)) wd))))))
      (run_nd (fork2 (wproc 1) (wproc 2)) (shared a b ctx c)) .pure :=
  anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r (anc_mono_r
    (fun _ _ h => ret_done_next _ h))))) _ _ (an_two_procs_nd_ret a b ctx c)

/-! ## Closed terms -/

/-- Instantiate the round-robin result and expose both final cell values. -/
theorem an_rr_3_5 (ctx : Ctx) :
    anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
      (anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
        (anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
          (fun _ wd => DoneWith (X := PUnit × SSig)
            (fun r _ => (csl_memory r.2).1 1 = some 1 ∧ (csl_memory r.2).1 2 = some 1) wd))))))
      (run_rr (fork2 (wproc 1) (wproc 2)) (shared 3 5 ctx 0)) .pure :=
  ax6_done_mono _ _ _ _ (fun _ _ H => both_lookup _ _ _ H) (an_two_procs_rr 3 5 ctx 0)

/-- Instantiate the nondeterministic result and expose both final cell values. -/
theorem an_nd_3_5 (ctx : Ctx) :
    anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
        (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
          (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
            (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
              (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
                (fun _ wd => DoneWith (X := PUnit × SSig)
                  (fun r _ => (csl_memory r.2).1 1 = some 1 ∧ (csl_memory r.2).1 2 = some 1)
                  wd))))))
      (run_nd (fork2 (wproc 1) (wproc 2)) (shared 3 5 ctx 0)) .pure :=
  ax6_done_mono _ _ _ _ (fun _ _ H => both_lookup _ _ _ H) (an_two_procs_nd 3 5 ctx 0)

/-! ## Negative control: without region `1` the child's write faults -/

/-- Follow a transition of a strongly bisimilar tree through `anc`. -/
private theorem anc_sbisim_next {W X : Type} {p q : ctreeW W Bn X → World (writerE W) → Prop}
    {t u u' : ctreeW W Bn X} {w w' : World (writerE W)} (h : t ~ u) (tr : ktrans u w u' w')
    (H : anc p q t w) : ∃ t', t' ~ u' ∧ q t' w' :=
  let ⟨t', tr', h'⟩ := ktrans_semiproper (sbisim_symm h) tr
  ⟨t', sbisim_symm h', H.2.2 _ _ tr'⟩

/-- The relabelled parent write on `own 2 b`: its snapshot is exactly `region 2 1`. -/
private theorem write_2_run_W (b : Nat) (ctx : Ctx) (c : Nat) {Y : Type}
    (k : Option Unit × SSig → ctreeW rr_obs Bn Y) :
    (translate relabel_log (instr_flow_erased (.write 2 1) (own 2 b ctx c)) >>= k) ~
      .vis (E := writerE rr_obs) (.inl (CSLObs.heap (region 2 1))) fun _ =>
        k (some (), own 2 1 ctx c) := by
  have H := translate_sbisim relabel_log
    (instr_flow_write_single 2 1 (own 2 b ctx c) (by simp [own, region, csl_memory, hsingle]))
  rw [translate_log_bind, translate_ret] at H
  refine sbisim_trans (sbisim_clo_bind_eq H fun _ => sbisim_refl _) ?_
  have Hr := managed_heap_ext _ _ (upd_region 2 b 1)
  simp only [csl_memory, own] at Hr ⊢
  rw [Hr, bind_assoc, log_vis]
  simp only [pure_bind']
  exact sbisim_refl _

/-- The unrelabelled parent write on `own 2 b`. -/
private theorem write_2_run (b : Nat) (ctx : Ctx) (c : Nat) {Y : Type}
    (k : Option Unit × SSig → ctreeW (CSLObs (Nat × Nat)) Bn Y) :
    (instr_flow_erased (.write 2 1) (own 2 b ctx c) >>= k) ~
      .vis (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 2 1)) fun _ =>
        k (some (), own 2 1 ctx c) := by
  refine sbisim_trans (sbisim_clo_bind_eq (instr_flow_write_single 2 1 (own 2 b ctx c)
    (by simp [own, region, csl_memory, hsingle])) fun _ => sbisim_refl _) ?_
  have Hr := managed_heap_ext _ _ (upd_region 2 b 1)
  simp only [csl_memory, own] at Hr ⊢
  rw [Hr, bind_assoc, log_vis]
  simp only [pure_bind']
  exact sbisim_refl _

/-- The parent's post-write snapshot remains visible before the first pick hands the child a heap
without cell `1`, where its write faults. -/
theorem wproc_own_2_stuck (b : Nat) (ctx : Ctx) (c : Nat) :
    run_rr (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c) ~
      (log (.inl (CSLObs.heap (region 2 1)) : rr_obs) >>= fun _ =>
        log (.inr 0 : rr_obs) >>= fun _ =>
          (.stuck : ctreeW rr_obs Bn (PUnit × SSig))) := by
  refine sbisim_trans (run_rr_fork_bind _ _ _) ?_
  rw [show (#v[denote (wproc 1), denote (wproc 2)] : Pool sE Bn 2) =
    (#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (wproc 2) >>= fun _ => pure ⟨⟩) from rfl]
  rw [show wproc 2 = .bind (.write 2 1) _ from rfl, interp_rr_bind]
  refine sbisim_trans (run_rr_prefix 1 _ 1 _ _ 0 _ (write_yield_fork_free 2)) ?_
  refine sbisim_trans (write_2_run_W b ctx c _) ?_
  rw [log_vis, log_vis]
  refine sb_vis _ fun _ => ?_
  dsimp only
  rw [interp_rr_bind]
  refine sbisim_trans (interp_rr_yield _ _ _ _ _ _) ?_
  refine sbisim_trans (interp_schedule_rr_select sh 1 _ 0 _) ?_
  refine sb_vis _ fun _ => ?_
  show interp_schedule_rr sh (1 + 1)
      ((#v[pure ⟨⟩, denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
        (denote_flow (.bind (.write 1 1) fun _ => .bind .yield fun _ => .ret ()) >>=
          fun _ => pure ⟨⟩)) (some 0) (0 + 1) ((hsingle 2 1, hemp), (ctx, c)) ~ _
  rw [interp_rr_bind]
  exact interp_rr_write_missing 1 _ 0 1 1 _ _ _ _ ctx c (hsingle_neq 2 1 1 (by decide))

/-- Six universal next steps fail under round robin without region `1`. -/
example (b : Nat) (ctx : Ctx) (c : Nat) :
    ¬ anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
      (anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
        (anc (entails (⊤ : TiclL (writerE rr_obs))) (anc (entails (⊤ : TiclL (writerE rr_obs)))
          (fun _ wd => DoneWith (fun (_ : PUnit × SSig) _ => True) wd))))))
      (run_rr (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c)) .pure := by
  intro H
  have h := wproc_own_2_stuck b ctx c
  rw [log_vis, log_vis] at h
  obtain ⟨t1, h1, H1⟩ := anc_sbisim_next h (ktrans_vis.2 ⟨⟨⟩, rfl, rfl, .pure⟩) H
  obtain ⟨t2, h2, H2⟩ := anc_sbisim_next h1 (ktrans_vis.2 ⟨⟨⟩, rfl, rfl, .obs _ _⟩) H1
  exact can_step_stuck ((proper_can_step h2).1 H2.2.1)

/-- A permitted child selection faults without region `1`, refuting universal next. -/
theorem wproc_own_2_no_ax6_nd (b : Nat) (ctx : Ctx) (c : Nat) :
    ¬ anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
        (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
          (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
            (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
              (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
                (fun _ wd => DoneWith (fun (_ : PUnit × SSig) _ => True) wd))))))
      (run_nd (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c)) .pure := by
  intro H
  have h0 : run_nd (fork2 (wproc 1) (wproc 2)) (own 2 b ctx c) ~
      .vis (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (region 2 1)) fun _ =>
        interp_schedule_nd sh 2 #v[denote (wproc 1), denote (.bind .yield fun _ => .ret ())]
          (some 1) (own 2 1 ctx c) := by
    refine sbisim_trans (run_nd_fork_bind _ _ _) ?_
    rw [show (#v[denote (wproc 1), denote (wproc 2)] : Pool sE Bn 2) =
      (#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
        (denote_flow (wproc 2) >>= fun _ => pure ⟨⟩) from rfl]
    rw [show wproc 2 = .bind (.write 2 1) _ from rfl, interp_nd_source_bind]
    refine sbisim_trans (run_nd_prefix 1 _ 1 _ _ _ (write_yield_fork_free 2)) ?_
    exact write_2_run b ctx c _
  have h1 : interp_schedule_nd sh 2 #v[denote (wproc 1), denote (.bind .yield fun _ => .ret ())]
      (some 1) (own 2 1 ctx c) ~
      CTree.brSn 2 fun i => interp_schedule_nd sh 2 #v[denote (wproc 1), denote (.ret ())]
        (some i) (own 2 1 ctx c) := by
    show interp_schedule_nd sh (1 + 1)
        ((#v[denote (wproc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
          (denote_flow (.bind .yield fun _ => .ret ()) >>= fun _ => pure ⟨⟩)) (some 1)
        (own 2 1 ctx c) ~ _
    rw [interp_nd_source_bind]
    exact sbisim_trans (interp_nd_source_yield _ _ _ _ _)
      (interp_schedule_nd_select sh 1 _ _)
  have h2 : interp_schedule_nd sh 2 #v[denote (wproc 1), denote (.ret ())] (some 0)
      (own 2 1 ctx c) ~ (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
    show interp_schedule_nd sh (1 + 1)
        ((#v[pure ⟨⟩, denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
          (denote_flow (.bind (.write 1 1) fun _ => .bind .yield fun _ => .ret ()) >>=
            fun _ => pure ⟨⟩)) (some 0) ((hsingle 2 1, hemp), (ctx, c)) ~ _
    rw [interp_nd_source_bind]
    exact interp_nd_source_write_missing 1 _ 0 1 1 _ _ _ ctx c (hsingle_neq 2 1 1 (by decide))
  obtain ⟨t1, ht1, H1⟩ := anc_sbisim_next h0 (ktrans_vis.2 ⟨⟨⟩, rfl, rfl, .pure⟩) H
  obtain ⟨t2, ht2, H2⟩ := anc_sbisim_next (sbisim_trans ht1 h1)
    ((ktrans_brS (B := Bn) (c := ⟨2⟩)).2 ⟨⟨0⟩, rfl, rfl, .obs _ _⟩) H1
  exact can_step_stuck ((proper_can_step (sbisim_trans ht2 h2)).1 H2.2.1)

#print axioms an_two_procs_rr

-- Not ported: the Ltacs `focus_parent`, `focus_child`, `focus_single`, `unfocus`,
-- `finish_nd_singleton`, `nd_select`, `fin_case`, `fin_none`, `fin2_cases`, `fin1_case` (proof
-- automation; replaced by `show` refocusing and the private helper `nd_singleton_ret`).

end Examples.CSL.Frame.AN
