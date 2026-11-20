/- SPDX-License-Identifier: MIT -/
module

public import Lang.CoCSL.Mod
public import Lang.CoCSL.Sequential
public import Lang.CoCSL.Owned

/-!
# Shared material for the two-process frame regressions

Two processes own cells `1` and `2`. Each process's facts are proved standalone on its own region
(`own`) and transported to the shared heap by framing with the other region (`work_af_framed`,
`write_ax_done_framed`). The AF/AN/AG files join these through the cooperative prefix equation
(← `examples/CSL/Frame/Shared.v`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Shared
open CTree Tisl Tisl.Heap Tisl.Pcm Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Notation CoCSL
open ITree (Effect)

/-! ## Programs -/

/-- Read, increment, write, and emit one owned cell. -/
def work (i : Nat) : CProg Unit :=
  .bind (.read i) fun v => .bind (.write i (v + 1)) fun _ => .emit i (v + 1)

/-- Perform work, yield once, and return. -/
def proc (i : Nat) : CProg Unit := .bind (work i) fun _ => .bind .yield fun _ => .ret ()

/-- Write one, yield once, and return. -/
def wproc (i : Nat) : CProg Unit := .bind (.write i 1) fun _ => .bind .yield fun _ => .ret ()

/-- One iteration of the looping worker: work, yield, and continue. -/
def lproc_body (i : Nat) : CProg (Option Unit) :=
  .bind (work i) fun _ => .bind .yield fun _ => .ret (some ())

/-- Repeat the yielding worker indefinitely. -/
def lproc (i : Nat) : CProg Unit := .untilNone (lproc_body i)

/-- Fork one program and continue with the other. -/
def fork2 (p1 p2 : CProg Unit) : CProg Unit := .bind (.fork p1) fun _ => p2

/-! ## Regions and states -/

/-- A single owned cell with no managed allocation extent. -/
def region (i a : Nat) : ManagedHeap := (hsingle i a, hemp)

/-- A process state containing only its own cell. -/
def own (i a : Nat) (ctx : Ctx) (c : Nat) : SSig := (region i a, (ctx, c))

/-- Two disjoint cells with shared context and emission counter. -/
def shared (a b : Nat) (ctx : Ctx) (c : Nat) : SSig := (region 1 a ⊎ region 2 b, (ctx, c))

/-- The managed heap consists of exactly the two owned regions. -/
def both (a b : Nat) (m : ManagedHeap) : Prop := m ≈ region 1 a ⊎ region 2 b

/-- Distinct singleton regions are disjoint. -/
theorem region_disj (i j a b : Nat) : i ≠ j → region i a # region j b := fun Hij =>
  ⟨hsingle_disj i j a b Hij, fun _ => .inl rfl⟩

/-- Two programs confined to distinct singleton regions are admissible. -/
theorem admissible_regions (child parent : CProg Unit) (i j a b : Nat) (ctx : Ctx)
    (base : Nat) : i ≠ j → component_ok child → component_ok parent →
    addr_ok (region i a) child → addr_ok (region j b) parent →
    admissible child parent (region i a) (region j b) ctx base := fun Hij =>
  admissible_intro _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    (region_disj i j a b Hij)

/-- A process region is well formed and disjoint from another cell. -/
theorem region_frame_inv (i j a b : Nat) (ctx : Ctx) (c : Nat) :
    i ≠ j → frame_inv (region j b) (own i a ctx c) := fun h =>
  ⟨region_disj i j a b h, managed_wf_preallocated _⟩

/-- `upd` on a single-cell region is the region at the new value. -/
theorem upd_region (i a v : Nat) : ((upd (region i a).1 i v, (region i a).2) : ManagedHeap) ≈
    region i v := by
  refine ⟨fun x => ?_, fun _ => rfl⟩
  by_cases h : x = i
  · subst h; simp [region, upd, hsingle]
  · simp [region, upd, hsingle, h, Ne.symm h]

/-! ## Standalone process facts -/

/-- Standalone work returns its incremented region and one stamped emission. -/
def Qwork (i a : Nat) (ctx : Ctx) (c : Nat) :
    Option Unit × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop :=
  fun x w' => x.1 = some () ∧ csl_memory x.2 ≈ region i (a + 1) ∧ x.2.2 = (ctx, c + 1) ∧
    w' = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (i, a + 1) c)) ⟨⟩

/-- The standalone worker reads, writes, and emits in order. -/
theorem work_run (i a : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    memory.1 i = some a →
    instr_flow_erased (work i) (memory, (ctx, c)) ~
      (emit_list [CSLObs.heap (upd memory.1 i (a + 1), memory.2), .emit (stamp (i, a + 1) c)]
        (pure (some (), ((upd memory.1 i (a + 1), memory.2), (ctx, c + 1))))
        : ctreeW (CSLObs (Nat × Nat)) Bn (Option Unit × SSig)) := by
  intro HV
  refine sbisim_trans (instr_flow_read i a _ _ HV) ?_
  refine sbisim_trans (instr_flow_write i (a + 1) _ _ (by simp [csl_memory, HV])) ?_
  simp only [csl_memory, emit_list_cons, emit_list_nil, log_vis]
  refine sb_vis _ fun _ => ?_
  refine sbisim_trans (instr_flow_head (.emit i (a + 1)) (.inr (.inr (i, a + 1)))
    (fun _ => pure (some ())) _ (by simp [denote_flow, CTree.trigger])) ?_
  simp only [sh, h_sum, csl_emit_handler_log, interp_state_thread_ret, log_vis, vis_bind,
    pure_bind']
  exact sbisim_refl _

/-- Standalone work eventually returns its postcondition. -/
theorem work_af_ret (i a : Nat) (ctx : Ctx) (c : Nat) (w : World (writerE (CSLObs (Nat × Nat)))) :
    NotDone w →
    entails (AF (.ret (Qwork i a ctx c))) (instr_flow_erased (work i) (own i a ctx c)) w := by
  intro Hw
  refine (proper_entails_meq _ (work_run i a _ ctx c (hsingle_eq i a))).2 ?_
  exact af_log Hw (af_log (.obs _ _) (.matchA (ret_ret (.obs _ _)
    ⟨rfl, upd_region i a (a + 1), rfl, rfl⟩)))

/-- The original eventual terminal claim follows through the final value transition. -/
theorem work_af (i a : Nat) (ctx : Ctx) (c : Nat) (w : World (writerE (CSLObs (Nat × Nat)))) :
    NotDone w →
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (Qwork i a ctx c) wd)
      (instr_flow_erased (work i) (own i a ctx c)) w := fun Hw =>
  af_ret_done _ (work_af_ret i a ctx c w Hw)

/-- A standalone write preserves context and counter and records its post-memory. -/
def Qwrite (i : Nat) (ctx : Ctx) (c : Nat) :
    Option Unit × SSig → World (writerE (CSLObs (Nat × Nat))) → Prop :=
  fun x w' => x.1 = some () ∧ csl_memory x.2 ≈ region i 1 ∧ x.2.2 = (ctx, c) ∧
    w' = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (csl_memory x.2)) ⟨⟩

/-- An owned cell of `own` is present. -/
private theorem own_present (i a : Nat) (ctx : Ctx) (c : Nat) :
    (csl_memory (own i a ctx c)).1 i ≠ none := by
  simp [own, region, csl_memory, hsingle]

/-- The write's heap observation precedes its native return. -/
theorem write_ax_ret (i a : Nat) (ctx : Ctx) (c : Nat)
    (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    entails (AX (.ret (Qwrite i ctx c))) (instr_flow_erased (.write i 1) (own i a ctx c)) w := by
  intro Hw
  refine (proper_entails_meq _ (instr_flow_write_single i 1 _ (own_present i a ctx c))).2 ?_
  exact ax_log Hw (ret_ret (.obs _ _) ⟨rfl, upd_region i a 1, rfl, rfl⟩)

/-! ## Framed process facts -/

/-- The worker head neither yields nor forks. -/
theorem work_yield_fork_free (i : Nat) : yield_fork_free (work i) :=
  ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩

/-- A write neither yields nor forks. -/
theorem write_yield_fork_free (i : Nat) : yield_fork_free (.write i 1) := trivial

/-- Work on a framed state eventually returns the framed postcondition. -/
theorem work_af_framed_ret (i j a b : Nat) (ctx : Ctx) (c : Nat) (s' : SSig)
    (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    frame_rel (region j b) (own i a ctx c) s' →
    entails (AF (.ret (frame_post (region j b) (Qwork i a ctx c))))
      (instr_flow_erased (work i) s') w := by
  intro Hw HR
  obtain ⟨memory, aux⟩ := s'
  obtain rfl : aux = (ctx, c) := HR.2.1
  have HV : memory.1 i = some a :=
    frame_rel_read (region j b) (own i a ctx c) (memory, (ctx, c)) i a HR (hsingle_eq i a)
  refine (proper_entails_meq _ (work_run i a memory ctx c HV)).2 ?_
  have Hwrite := frame_rel_write (region j b) (own i a ctx c) (memory, (ctx, c)) i (a + 1) HR
    (own_present i a ctx c)
  refine af_log Hw (af_log (.obs _ _) (.matchA (ret_ret (.obs _ _)
    ⟨(some (), ((upd (region i a).1 i (a + 1), (region i a).2), (ctx, c + 1))),
      .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (i, a + 1) c)) ⟨⟩,
      ⟨rfl, frame_rel_aux (region j b) _ _ (ctx, c + 1) Hwrite⟩,
      .obs _ _ _ _ (frameER_emit _ _) HEq.rfl, rfl, upd_region i a (a + 1), rfl, rfl⟩)))

/-- Preserve the original eventual terminal claim on a framed state. -/
theorem work_af_framed (i j a b : Nat) (ctx : Ctx) (c : Nat) (s' : SSig)
    (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    frame_rel (region j b) (own i a ctx c) s' →
    Auc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (fun _ wd => DoneWith (frame_post (region j b) (Qwork i a ctx c)) wd)
      (instr_flow_erased (work i) s') w := fun Hw HR =>
  af_ret_done _ (work_af_framed_ret i j a b ctx c s' w Hw HR)

/-- A framed write records its post-memory before returning, from any live world. -/
theorem write_ax_ret_framed (i j a b : Nat) (ctx : Ctx) (c : Nat) (s' : SSig)
    (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    frame_rel (region j b) (own i a ctx c) s' →
    entails (AX (.ret (frame_post (region j b) (Qwrite i ctx c))))
      (instr_flow_erased (.write i 1) s') w := by
  intro Hw HR
  have Present' : (csl_memory s').1 i ≠ none := by
    rw [frame_rel_read (region j b) (own i a ctx c) s' i a HR (hsingle_eq i a)]
    exact Option.some_ne_none _
  have Hwrite := frame_rel_write (region j b) (own i a ctx c) s' i 1 HR (own_present i a ctx c)
  refine (proper_entails_meq _ (instr_flow_write_single i 1 s' Present')).2 ?_
  exact ax_log Hw (ret_ret (.obs _ _)
    ⟨(some (), ((upd (region i a).1 i 1, (region i a).2), (ctx, c))),
      .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (upd (region i a).1 i 1,
        (region i a).2)) ⟨⟩,
      ⟨rfl, Hwrite⟩, .obs _ _ _ _ (frameER_heap _ _ _ Hwrite) HEq.rfl,
      rfl, upd_region i a 1, rfl, rfl⟩)

/-- The heap observation and final value transition give two semantic next steps. -/
theorem write_ax_done_framed (i j a b : Nat) (ctx : Ctx) (c : Nat) (s' : SSig)
    (w : World (writerE (CSLObs (Nat × Nat)))) : NotDone w →
    frame_rel (region j b) (own i a ctx c) s' →
    anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
      (anc (entails (⊤ : TiclL (writerE (CSLObs (Nat × Nat)))))
        (fun _ wd => DoneWith (frame_post (region j b) (Qwrite i ctx c)) wd))
      (instr_flow_erased (.write i 1) s') w := fun Hw HR =>
  anc_mono_r (fun _ _ h => ret_done_next _ h) _ _
    (write_ax_ret_framed i j a b ctx c s' w Hw HR)

/-- A passive heap frame preserves an indexed user emission exactly. -/
theorem frame_emit_world {A X : Type} (fr : ManagedHeap) (emission : Indexed A)
    (w' : World (writerE (CSLObs A))) :
    simW (frameER fr) (frameRV (X := X) fr)
      (.obs (E := writerE (CSLObs A)) (CSLObs.emit emission) ⟨⟩) w' →
    w' = .obs (E := writerE (CSLObs A)) (CSLObs.emit emission) ⟨⟩ := fun HW =>
  simW_not_done_right_unique (frameER fr) (frameRV fr) (frameER_right_unique fr) _ _ _
    (.obs _ _) HW (.obs _ _ _ _ (frameER_emit fr emission) HEq.rfl)

/-- Unpacking a framed postcondition. -/
theorem frame_post_work (i j a b : Nat) (ctx : Ctx) (c : Nat) (s'' : SSig) (r : Option Unit)
    (w' : World (writerE (CSLObs (Nat × Nat)))) :
    frame_post (region j b) (Qwork i a ctx c) (r, s'') w' →
    r = some () ∧ csl_memory s'' ≈ region i (a + 1) ⊎ region j b ∧ s''.2 = (ctx, c + 1) ∧
      w' = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (i, a + 1) c)) ⟨⟩ := by
  rintro ⟨⟨x, m, aux⟩, source, ⟨rfl, -, HA, HE⟩, HW, Hr, Hm, Haux, rfl⟩
  exact ⟨Hr, peq_trans _ _ _ HE (pop_resp _ _ _ _ Hm (peq_refl _)), HA.trans Haux,
    frame_emit_world _ _ _ HW⟩

/-- Unpack a framed write into memory, auxiliary state, and world facts. -/
theorem frame_post_write (i j b : Nat) (ctx : Ctx) (c : Nat) (s'' : SSig) (r : Option Unit)
    (w' : World (writerE (CSLObs (Nat × Nat)))) :
    frame_post (region j b) (Qwrite i ctx c) (r, s'') w' →
    r = some () ∧ csl_memory s'' ≈ region i 1 ⊎ region j b ∧ s''.2 = (ctx, c) ∧
      w' = .obs (E := writerE (CSLObs (Nat × Nat))) (CSLObs.heap (csl_memory s'')) ⟨⟩ := by
  rintro ⟨⟨x, m, aux⟩, source, ⟨rfl, ⟨HD, Hwf⟩, HA, HE⟩, HW, Hr, Hm, Haux, rfl⟩
  refine ⟨Hr, peq_trans _ _ _ HE (pop_resp _ _ _ _ Hm (peq_refl _)), HA.trans Haux, ?_⟩
  rw [managed_heap_ext _ _ HE]
  exact simW_not_done_right_unique (frameER (region j b)) (frameRV (X := Option Unit) (region j b))
    (frameER_right_unique _) _ _ _ (.obs _ _) HW (.obs _ _ _ _ ⟨HD, Hwf, peq_refl _⟩ HEq.rfl)

/-! ## Logged round-robin views of the standalone facts

Program observations are relabelled under `.inl`, including every heap snapshot. Scheduling
selections occupy `.inr` and remain separate. -/

abbrev rr_obs : Type := CSLObs (Nat × Nat) ⊕ Nat

def QworkW (i a : Nat) (ctx : Ctx) (c : Nat) :
    Option Unit × SSig → World (writerE rr_obs) → Prop :=
  fun x w' => x.1 = some () ∧ csl_memory x.2 ≈ region i (a + 1) ∧ x.2.2 = (ctx, c + 1) ∧
    w' = .obs (E := writerE rr_obs) (.inl (CSLObs.emit (stamp (i, a + 1) c))) ⟨⟩

def QwriteW (i : Nat) (ctx : Ctx) (c : Nat) :
    Option Unit × SSig → World (writerE rr_obs) → Prop :=
  fun x w' => x.1 = some () ∧ csl_memory x.2 ≈ region i 1 ∧ x.2.2 = (ctx, c) ∧
    w' = .obs (E := writerE rr_obs) (.inl (CSLObs.heap (csl_memory x.2))) ⟨⟩

/-- Relabelling preserves the worker's two-observation prefix exactly. -/
theorem work_run_W (i a : Nat) (memory : ManagedHeap) (ctx : Ctx) (c : Nat) :
    memory.1 i = some a →
    translate relabel_log (instr_flow_erased (work i) (memory, (ctx, c))) ~
      (emit_list [.inl (CSLObs.heap (upd memory.1 i (a + 1), memory.2)),
          .inl (.emit (stamp (i, a + 1) c))]
        (pure (some (), ((upd memory.1 i (a + 1), memory.2), (ctx, c + 1))))
        : ctreeW rr_obs Bn (Option Unit × SSig)) := by
  intro HV
  have H := translate_sbisim relabel_log (work_run i a memory ctx c HV)
  rw [translate_emit_list, translate_ret] at H
  exact H

theorem work_af_ret_W (i a : Nat) (ctx : Ctx) (c : Nat) (w : World (writerE rr_obs)) :
    NotDone w →
    entails (AF (.ret (QworkW i a ctx c)))
      (translate relabel_log (instr_flow_erased (work i) (own i a ctx c))) w := by
  intro Hw
  refine (proper_entails_meq _ (work_run_W i a _ ctx c (hsingle_eq i a))).2 ?_
  exact af_log Hw (af_log (.obs _ _) (.matchA (ret_ret (.obs _ _)
    ⟨rfl, upd_region i a (a + 1), rfl, rfl⟩)))

/-- The relabelled standalone write. -/
private theorem write_run_W (a v : Nat) (s : SSig) : (csl_memory s).1 a ≠ none →
    translate relabel_log (instr_flow_erased (.write a v) s) ~
      (log (.inl (CSLObs.heap (upd (csl_memory s).1 a v, (csl_memory s).2)) : rr_obs)
        >>= fun _ => (pure (some (), ((upd (csl_memory s).1 a v, (csl_memory s).2), s.2)) :
          ctreeW rr_obs Bn (Option Unit × SSig))) := by
  intro Hv
  have H := translate_sbisim relabel_log (instr_flow_write_single a v s Hv)
  rw [translate_log_bind, translate_ret] at H
  exact H

theorem write_ax_ret_W (i a : Nat) (ctx : Ctx) (c : Nat) (w : World (writerE rr_obs)) :
    NotDone w →
    entails (AX (.ret (QwriteW i ctx c)))
      (translate relabel_log (instr_flow_erased (.write i 1) (own i a ctx c))) w := by
  intro Hw
  refine (proper_entails_meq _ (write_run_W i 1 _ (own_present i a ctx c))).2 ?_
  exact ax_log Hw (ret_ret (.obs _ _) ⟨rfl, upd_region i a 1, rfl, rfl⟩)

/-- Framing still relates the local and whole-heap snapshots; it does not identify them merely
because both observations are under `.inl`. -/
theorem work_af_framed_ret_W (i j a b : Nat) (ctx : Ctx) (c : Nat) (s' : SSig)
    (w : World (writerE rr_obs)) : NotDone w →
    frame_rel (region j b) (own i a ctx c) s' →
    entails (AF (.ret (frame_postW (region j b) (QworkW i a ctx c))))
      (translate relabel_log (instr_flow_erased (work i) s')) w := by
  intro Hw HR
  obtain ⟨memory, aux⟩ := s'
  obtain rfl : aux = (ctx, c) := HR.2.1
  have HV : memory.1 i = some a :=
    frame_rel_read (region j b) (own i a ctx c) (memory, (ctx, c)) i a HR (hsingle_eq i a)
  refine (proper_entails_meq _ (work_run_W i a memory ctx c HV)).2 ?_
  have Hwrite := frame_rel_write (region j b) (own i a ctx c) (memory, (ctx, c)) i (a + 1) HR
    (own_present i a ctx c)
  refine af_log Hw (af_log (.obs _ _) (.matchA (ret_ret (.obs _ _)
    ⟨(some (), ((upd (region i a).1 i (a + 1), (region i a).2), (ctx, c + 1))),
      .obs (E := writerE rr_obs) (.inl (CSLObs.emit (stamp (i, a + 1) c))) ⟨⟩,
      ⟨rfl, frame_rel_aux (region j b) _ _ (ctx, c + 1) Hwrite⟩,
      .obs _ _ _ _ (frameERW_emit _ _) HEq.rfl, rfl, upd_region i a (a + 1), rfl, rfl⟩)))

theorem write_ax_ret_framed_W (i j a b : Nat) (ctx : Ctx) (c : Nat) (s' : SSig)
    (w : World (writerE rr_obs)) : NotDone w →
    frame_rel (region j b) (own i a ctx c) s' →
    entails (AX (.ret (frame_postW (region j b) (QwriteW i ctx c))))
      (translate relabel_log (instr_flow_erased (.write i 1) s')) w := by
  intro Hw HR
  have Present' : (csl_memory s').1 i ≠ none := by
    rw [frame_rel_read (region j b) (own i a ctx c) s' i a HR (hsingle_eq i a)]
    exact Option.some_ne_none _
  have Hwrite := frame_rel_write (region j b) (own i a ctx c) s' i 1 HR (own_present i a ctx c)
  refine (proper_entails_meq _ (write_run_W i 1 s' Present')).2 ?_
  exact ax_log Hw (ret_ret (.obs _ _)
    ⟨(some (), ((upd (region i a).1 i 1, (region i a).2), (ctx, c))),
      .obs (E := writerE rr_obs) (.inl (CSLObs.heap (upd (region i a).1 i 1,
        (region i a).2))) ⟨⟩,
      ⟨rfl, Hwrite⟩, .obs _ _ _ _ (frameERW_heap (A := Nat × Nat) _ _ _ Hwrite) HEq.rfl,
      rfl, upd_region i a 1, rfl, rfl⟩)

theorem frame_emit_world_W {A X : Type} (fr : ManagedHeap) (emission : Indexed A)
    (w' : World (writerE (CSLObs A ⊕ Nat))) :
    simW (frameERW fr) (frameRV (X := X) fr)
      (.obs (E := writerE (CSLObs A ⊕ Nat)) (.inl (CSLObs.emit emission)) ⟨⟩) w' →
    w' = .obs (E := writerE (CSLObs A ⊕ Nat)) (.inl (CSLObs.emit emission)) ⟨⟩ := fun HW =>
  simW_not_done_right_unique (frameERW fr) (frameRV fr) (frameERW_right_unique fr) _ _ _
    (.obs _ _) HW (.obs _ _ _ _ (frameERW_emit fr emission) HEq.rfl)

theorem frame_post_work_W (i j a b : Nat) (ctx : Ctx) (c : Nat) (s'' : SSig) (r : Option Unit)
    (w' : World (writerE rr_obs)) :
    frame_postW (region j b) (QworkW i a ctx c) (r, s'') w' →
    r = some () ∧ csl_memory s'' ≈ region i (a + 1) ⊎ region j b ∧ s''.2 = (ctx, c + 1) ∧
      w' = .obs (E := writerE rr_obs) (.inl (CSLObs.emit (stamp (i, a + 1) c))) ⟨⟩ := by
  rintro ⟨⟨x, m, aux⟩, source, ⟨rfl, -, HA, HE⟩, HW, Hr, Hm, Haux, rfl⟩
  exact ⟨Hr, peq_trans _ _ _ HE (pop_resp _ _ _ _ Hm (peq_refl _)), HA.trans Haux,
    frame_emit_world_W _ _ _ HW⟩

theorem frame_post_write_W (i j b : Nat) (ctx : Ctx) (c : Nat) (s'' : SSig) (r : Option Unit)
    (w' : World (writerE rr_obs)) :
    frame_postW (region j b) (QwriteW i ctx c) (r, s'') w' →
    r = some () ∧ csl_memory s'' ≈ region i 1 ⊎ region j b ∧ s''.2 = (ctx, c) ∧
      w' = .obs (E := writerE rr_obs) (.inl (CSLObs.heap (csl_memory s''))) ⟨⟩ := by
  rintro ⟨⟨x, m, aux⟩, source, ⟨rfl, ⟨HD, Hwf⟩, HA, HE⟩, HW, Hr, Hm, Haux, rfl⟩
  refine ⟨Hr, peq_trans _ _ _ HE (pop_resp _ _ _ _ Hm (peq_refl _)), HA.trans Haux, ?_⟩
  rw [managed_heap_ext _ _ HE]
  exact simW_not_done_right_unique (frameERW (region j b))
    (frameRV (X := Option Unit) (region j b)) (frameERW_right_unique _) _ _ _ (.obs _ _) HW
    (.obs _ _ _ _ (frameERW_heap (A := Nat × Nat) (region j b) (m, aux)
      (frame_state (region j b) (m, aux)) (frame_rel_state _ _ ⟨HD, Hwf⟩)) HEq.rfl)

/-- The shared state frames each own state. -/
theorem frame_rel_shared_2 (a b : Nat) (ctx : Ctx) (c : Nat) :
    frame_rel (region 1 a) (own 2 b ctx c) (shared a b ctx c) :=
  ⟨region_frame_inv 2 1 b a ctx c (by decide), rfl,
    pop_comm _ _ (region_disj 1 2 a b (by decide))⟩

/-- A heap with both regions frames the first process state. -/
theorem frame_rel_both_1 (a b : Nat) (ctx : Ctx) (c : Nat) (s : SSig) :
    csl_memory s ≈ region 1 a ⊎ region 2 b → s.2 = (ctx, c) →
    frame_rel (region 2 b) (own 1 a ctx c) s := fun HE HA =>
  ⟨region_frame_inv 1 2 a b ctx c (by decide), HA, HE⟩

/-- A heap with both regions frames the second process state. -/
theorem frame_rel_both_2 (a b : Nat) (ctx : Ctx) (c : Nat) (s : SSig) :
    csl_memory s ≈ region 1 a ⊎ region 2 b → s.2 = (ctx, c) →
    frame_rel (region 1 a) (own 2 b ctx c) s := fun HE HA =>
  ⟨region_frame_inv 2 1 b a ctx c (by decide), HA,
    peq_trans _ _ _ HE (pop_comm _ _ (region_disj 1 2 a b (by decide)))⟩

/-! ## Pool bookkeeping -/

/-- The child is the first slot. -/
def child : Fin 2 := 0

/-- The parent is the second slot. -/
def parent : Fin 2 := 1

/-- Round-robin cursor zero picks the child in a two-slot pool. -/
theorem rr_pick_1_0 : rr_pick 1 0 = child := rfl

/-- Round-robin cursor one picks the parent in a two-slot pool. -/
theorem rr_pick_1_1 : rr_pick 1 1 = parent := rfl

/-- Closed-term extraction of `both`. -/
theorem both_lookup (a b : Nat) (m : ManagedHeap) :
    both a b m → m.1 1 = some a ∧ m.1 2 = some b := fun ⟨HE, _⟩ =>
  ⟨(HE 1).trans rfl, (HE 2).trans rfl⟩

-- Not ported: the Ltacs `close_ret`, `rr_prefix`, `nd_prefix` and `unpack_frame_post` (proof
-- automation, inlined); `rr_pick_0` (identical to `Tisl.Yield.rr_pick_0`); `hsingle_eq`,
-- `hsingle_neq` (moved to `Tisl.Heap`).

end Examples.CSL.Frame.Shared
