/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Shared
public import Logic.CTree.Yield
public import Logic.CTree.EX
public import Logic.Congruence

/-!
# Cursor-free concrete separation experiments

Ordinary managed-heap `asep` supplies spatial invariants. Native-return postconditions retain
obtained local proofs across foreign observations; neither observations nor program/scheduler
state carry provenance (← `examples/CSL/Frame/Asep.v`, module `InvariantSeparation`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Asep
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared

namespace InvariantSeparation

def exact_cell (i value : Nat) : assn ManagedHeap :=
  fun m => m ≈ region i value

def split_cells (a b : Nat) : assn ManagedHeap :=
  asep (exact_cell 1 a) (exact_cell 2 b)

theorem exact_cell_proper (i value : Nat) : AProper (exact_cell i value) :=
  fun _ _ hmn hm => peq_trans _ _ _ (peq_sym _ _ hmn) hm

theorem split_cells_iff_both (a b : Nat) (m : ManagedHeap) : split_cells a b m ↔ both a b m :=
  ⟨fun ⟨_, _, _, hm, h1, h2⟩ => peq_trans _ _ _ hm (pop_resp _ _ _ _ h1 h2),
    fun hm => ⟨region 1 a, region 2 b, region_disj _ _ _ _ (by decide), hm, peq_refl _,
      peq_refl _⟩⟩

theorem split_cells_lookup (a b : Nat) (m : ManagedHeap) :
    split_cells a b m → m.1 1 = some a ∧ m.1 2 = some b :=
  fun h => both_lookup _ _ _ ((split_cells_iff_both _ _ _).1 h)

/-- Observation worlds of the nondeterministic runner (Rocq `Local Definition`). -/
abbrev ObsWorld := World (writerE (CSLObs (Nat × Nat)))

def emit_world (i v k : Nat) : ObsWorld :=
  .obs (E := writerE _) (CSLObs.emit (stamp (i, v) k)) ⟨⟩

def parent_post (a b : Nat) (ctx : Ctx) (c : Nat) : Option Unit × SSig → ObsWorld → Prop :=
  frame_post (region 1 a) (Qwork 2 b ctx c)

def workers_post (a b : Nat) (ctx : Ctx) (c : Nat) : PUnit.{1} × SSig → ObsWorld → Prop :=
  fun r w =>
    split_cells (a + 1) (b + 1) (csl_memory r.2) ∧
    r.2.2 = (ctx, c + 2) ∧
    w = emit_world 1 (a + 1) (c + 1) ∧
    ∃ sp wp, parent_post a b ctx c (some (), sp) wp ∧ wp ≠ w

def sequence_post (a b : Nat) (ctx : Ctx) (c : Nat) : Option Unit × SSig → ObsWorld → Prop :=
  fun r w => r.1 = some () ∧ workers_post a b ctx c (⟨⟩, r.2) w

/-- Consume Child's post while retaining the actual obtained Parent proof. -/
private theorem child_keeps_parent (a b : Nat) (ctx : Ctx) (c : Nat) (sp : SSig) (wp : ObsWorld)
    (s : SSig) (r : Option Unit) (w : ObsWorld) :
    parent_post a b ctx c (some (), sp) wp →
    frame_post (region 2 (b + 1)) (Qwork 1 a ctx (c + 1)) (r, s) w →
    sequence_post a b ctx c (r, s) w := by
  intro HP HC
  obtain ⟨-, -, -, Hwp⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  obtain ⟨rfl, HM, HS, Hw⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HC
  refine ⟨rfl, (split_cells_iff_both _ _ _).2 HM, HS, Hw, sp, wp, HP, ?_⟩
  rw [Hwp, Hw]; simp only [ne_eq, World.obs.injEq, stamp]
  intro h; injection h.1 with h; injection h with h; injection h with h; cases h

theorem bind_keeps_parent_post (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AF (.ret (sequence_post a b ctx c)))
      (instr_flow_erased (work 2) (shared a b ctx c) >>= fun r =>
        instr_flow_erased (work 1) r.2) .pure := by
  refine u_bind_r (q := .A) (R := parent_post a b ctx c)
    (work_af_framed_ret 2 1 b a ctx c _ _ .pure (frame_rel_shared_2 a b ctx c)) ?_
  rintro ⟨rp, sp⟩ wp HP
  obtain ⟨rfl, HM, HS, Hwp⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  refine aur_ret_mono _ _ _ _ _ (fun r w HC => child_keeps_parent a b ctx c sp wp r.2 r.1 w HP HC)
    (work_af_framed_ret 1 2 a (b + 1) ctx (c + 1) _ _ (Hwp ▸ .obs _ _)
      (frame_rel_both_1 _ _ _ _ _ ?_ HS))
  exact peq_trans _ _ _ HM (pop_comm _ _ (region_disj _ _ _ _ (by decide)))

/-- Parent has already returned: its obtained proof remains a hypothesis while the unfocused
singleton Child is selected and performs its work. -/
private theorem nd_tail_work1_ret (a b : Nat) (ctx : Ctx) (c : Nat) (sp : SSig) (wp : ObsWorld) :
    parent_post a b ctx c (some (), sp) wp →
    entails (AF (.ret (workers_post a b ctx c)))
      (interp_schedule_nd sh 1 #v[denote_flow (proc 1) >>= fun _ => pure ⟨⟩] none sp) wp := by
  intro HP
  obtain ⟨-, HM, HS, Hwp⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  have HM' : csl_memory sp ≈ region 1 a ⊎ region 2 (b + 1) :=
    peq_trans _ _ _ HM (pop_comm _ _ (region_disj _ _ _ _ (by decide)))
  subst Hwp
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 0 _ sp)).2 ?_
  refine (au_brS (B := Bn) (c := ⟨0 + 1⟩) ⟨0⟩).1 (.inr ⟨ticll_top (.obs _ _), fun j => ?_⟩)
  refine (fun i => ?_ : ∀ i : Fin 1, entails _ (interp_schedule_nd sh _ _ (some i) sp) _) _
  obtain rfl := fin1_eq i
  show entails _ (interp_schedule_nd sh (0 + 1) ((#v[denote (.ret ())] : Pool sE Bn 1).set
    (0 : Fin 1) (denote_flow (.bind (work 1) fun _ => .bind .yield fun _ => .ret ()) >>=
      fun _ => pure ⟨⟩)) (some 0) sp) _
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (run_nd_prefix 0 _ 0 _ _ _ (work_yield_fork_free 1))).2 ?_
  refine u_bind_r (q := .A) (work_af_framed_ret 1 2 a (b + 1) ctx (c + 1) _ _ (.obs _ _)
    (frame_rel_both_1 _ _ _ _ _ HM' HS)) ?_
  rintro ⟨r, s⟩ w HC
  obtain ⟨rfl, HB⟩ := child_keeps_parent a b ctx c sp _ s r w HP HC
  have Hlive : NotDone w := by rw [HB.2.2.1]; exact .obs _ _
  dsimp only
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
  show entails _ (interp_schedule_nd sh 1 #v[denote (.ret ())] none s) _
  rw [show (#v[denote (.ret ())] : Pool sE Bn 1) = csl_pool (Vector.replicate 1 (.ret ())) from
      Vector.ext fun i hi => by match i, hi with | 0, _ => simp [csl_pool]]
  change entails _ (run_nd_pool _ none s) _
  refine (proper_entails_meq _ (run_nd_pool_returns 1 none s)).2 ?_
  exact au_step.1 (.inr ⟨ticll_top Hlive, .matchA (ret_ret Hlive HB)⟩)

theorem asep_two_procs_nd_ret (a b : Nat) (ctx : Ctx) (c : Nat) :
    entails (AF (.ret (workers_post a b ctx c)))
      (run_nd (fork2 (proc 1) (proc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_nd_fork_bind _ _ _)).2 ?_
  rw [show (#v[denote (proc 1), denote (proc 2)] : Pool sE Bn 2) =
    (#v[denote (proc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (proc 2) >>= fun _ => pure ⟨⟩) from rfl]
  rw [show proc 2 = .bind (work 2) _ from rfl, interp_nd_source_bind]
  refine (proper_entails_meq _ (run_nd_prefix 1 _ 1 _ _ _ (work_yield_fork_free 2))).2 ?_
  refine u_bind_r (q := .A) (R := parent_post a b ctx c)
    (work_af_framed_ret 2 1 b a ctx c _ _ .pure (frame_rel_shared_2 a b ctx c)) ?_
  rintro ⟨r, sp⟩ wp HP
  obtain ⟨rfl, HM, HS, Hwp⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  have HM' : csl_memory sp ≈ region 1 a ⊎ region 2 (b + 1) :=
    peq_trans _ _ _ HM (pop_comm _ _ (region_disj _ _ _ _ (by decide)))
  dsimp only
  rw [interp_nd_source_bind]
  refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
  refine (proper_entails_meq _ (interp_schedule_nd_select sh 1 _ sp)).2 ?_
  refine (au_brS (B := Bn) (c := ⟨1 + 1⟩) ⟨0⟩).1
    (.inr ⟨ticll_top (Hwp ▸ .obs _ _), fun j => ?_⟩)
  refine (fun i => ?_ : ∀ i : Fin 2, entails _ (interp_schedule_nd sh _ _ (some i) sp) _) _
  match i with
  | 0 =>
    -- Child first: retain `HP` across its foreign emission.
    show entails _ (interp_schedule_nd sh (1 + 1)
        ((#v[denote (.ret ()), denote (.ret ())] : Pool sE Bn 2).set (0 : Fin 2)
          (denote_flow (.bind (work 1) fun _ => .bind .yield fun _ => .ret ()) >>=
            fun _ => pure ⟨⟩))
        (some 0) sp) _
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (run_nd_prefix 1 _ 0 _ _ _ (work_yield_fork_free 1))).2 ?_
    refine u_bind_r (q := .A) (work_af_framed_ret 1 2 a (b + 1) ctx (c + 1) _ _
      (Hwp ▸ .obs _ _) (frame_rel_both_1 _ _ _ _ _ HM' HS)) ?_
    rintro ⟨r, s⟩ w HC
    obtain ⟨rfl, HB⟩ := child_keeps_parent a b ctx c sp wp s r w HP HC
    have Hlive : NotDone w := by rw [HB.2.2.1]; exact .obs _ _
    dsimp only
    rw [interp_nd_source_bind]
    refine (proper_entails_meq _ (interp_nd_source_yield _ _ _ _ _)).2 ?_
    show entails _ (interp_schedule_nd sh 2 #v[denote (.ret ()), denote (.ret ())] none s) _
    rw [show (#v[denote (.ret ()), denote (.ret ())] : Pool sE Bn 2) =
      csl_pool (Vector.replicate 2 (.ret ())) from
        Vector.ext fun i hi => by match i, hi with | 0, _ | 1, _ => simp [csl_pool]]
    change entails _ (run_nd_pool _ none s) _
    refine (proper_entails_meq _ (run_nd_pool_returns 2 none s)).2 ?_
    exact au_step.1 (.inr ⟨ticll_top Hlive,
      au_step.1 (.inr ⟨ticll_top Hlive, .matchA (ret_ret Hlive HB)⟩)⟩)
  | 1 =>
    -- Parent first: remove Parent before Child performs any work.
    rw [interp_nd_source_ret]
    refine (proper_entails_meq _ (interp_schedule_nd_ret sh 1 _ 1 sp (by simp))).2 ?_
    rw [show ((#v[denote (proc 1), pure ⟨⟩] : Pool sE Bn 2).set (1 : Fin 2)
        (pure ⟨⟩)).eraseIdx (1 : Fin 2) = #v[denote_flow (proc 1) >>= fun _ => pure ⟨⟩] from
      Vector.ext fun i hi => by match i, hi with | 0, _ => simp [denote]]
    exact nd_tail_work1_ret a b ctx c sp wp HP

theorem asep_two_procs_nd_3_5 (ctx : Ctx) :
    entails (AF (.ret fun (r : PUnit × SSig) w =>
      (csl_memory r.2).1 1 = some 4 ∧ (csl_memory r.2).1 2 = some 6 ∧
      r.2.2 = (ctx, 2) ∧ w = emit_world 1 4 1 ∧
      ∃ sp wp, parent_post 3 5 ctx 0 (some (), sp) wp ∧ wp = emit_world 2 6 0 ∧ wp ≠ w))
      (run_nd (fork2 (proc 1) (proc 2)) (shared 3 5 ctx 0)) .pure := by
  refine aur_ret_mono _ _ _ _ _ (fun r w H => ?_) (asep_two_procs_nd_ret 3 5 ctx 0)
  obtain ⟨HM, HS, Hw, sp, wp, HP, Hne⟩ := H
  obtain ⟨H1, H2⟩ := split_cells_lookup _ _ _ HM
  obtain ⟨-, -, -, Hwp⟩ := frame_post_work _ _ _ _ _ _ _ _ _ HP
  exact ⟨H1, H2, HS, Hw, sp, wp, HP, Hwp, Hne⟩

def heap_10 : CSLObs (Nat × Nat) → Prop
  | .heap m => split_cells 1 0 m
  | _ => False

def heap_01 : CSLObs (Nat × Nat) → Prop
  | .heap m => split_cells 0 1 m
  | _ => False

def one_write_obs (o : CSLObs (Nat × Nat)) : Prop := heap_10 o ∨ heap_01 o

/-- Weaken the observed payload of an `AX visW` fact. -/
private theorem ax_visW_mono {P Q : CSLObs (Nat × Nat) → Prop} {t : ctreeW _ Bn (PUnit × SSig)}
    {w : ObsWorld} (hPQ : ∀ o, P o → Q o) :
    entails (AX (visWₜ P)) t w → entails (AX (visWₜ Q)) t w :=
  fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun t' w' tr =>
    match h3 t' w' tr with
    | ⟨.obs o v hP, hd⟩ => ⟨.obs o v (hPQ o hP), hd⟩⟩

/-- A focused write advances exactly one spatial component. -/
private theorem focused_write_child (ctx : Ctx) (c : Nat) :
    entails (AX (visWₜ heap_10))
      (interp_schedule_nd sh 2 (csl_pool #v[.write 1 1, .write 2 1]) (some child)
        (shared 0 0 ctx c)) .pure := by
  rw [show csl_pool #v[.write 1 1, .write 2 1] =
    (#v[denote (.ret ()), denote (.write 2 1)] : Pool sE Bn 2).set (0 : Fin 2)
      (denote_flow (.write 1 1) >>= fun _ => pure ⟨⟩) from
    Vector.ext fun i hi => by match i, hi with | 0, _ | 1, _ => simp [csl_pool, denote]]
  refine (proper_entails_meq _ (run_nd_prefix 1 _ 0 _ _ _ (write_yield_fork_free 1))).2 ?_
  refine an_bind_l (write_ax_ret_framed 1 2 0 0 ctx c _ _ .pure
    (frame_rel_both_1 _ _ _ _ _ (peq_refl _) rfl)) ?_
  rintro ⟨r, s⟩ w HP
  obtain ⟨-, HM, -, rfl⟩ := frame_post_write _ _ _ _ _ _ _ _ HP
  exact ⟨.obs _ _ ((split_cells_iff_both _ _ _).2 HM), .obs _ _⟩

private theorem focused_write_parent (ctx : Ctx) (c : Nat) :
    entails (AX (visWₜ heap_01))
      (interp_schedule_nd sh 2 (csl_pool #v[.write 1 1, .write 2 1]) (some parent)
        (shared 0 0 ctx c)) .pure := by
  rw [show csl_pool #v[.write 1 1, .write 2 1] =
    (#v[denote (.write 1 1), denote (.ret ())] : Pool sE Bn 2).set (1 : Fin 2)
      (denote_flow (.write 2 1) >>= fun _ => pure ⟨⟩) from
    Vector.ext fun i hi => by match i, hi with | 0, _ | 1, _ => simp [csl_pool, denote]]
  refine (proper_entails_meq _ (run_nd_prefix 1 _ 1 _ _ _ (write_yield_fork_free 2))).2 ?_
  refine an_bind_l (write_ax_ret_framed 2 1 0 0 ctx c _ _ .pure (frame_rel_shared_2 _ _ _ _)) ?_
  rintro ⟨r, s⟩ w HP
  obtain ⟨-, HM, -, rfl⟩ := frame_post_write _ _ _ _ _ _ _ _ HP
  refine ⟨.obs _ _ ((split_cells_iff_both _ _ _).2 ?_), .obs _ _⟩
  exact peq_trans _ _ _ HM (pop_comm _ _ (region_disj _ _ _ _ (by decide)))

theorem asep_writes_ax2 (ctx : Ctx) (c : Nat) :
    entails (AX (AX (visWₜ one_write_obs)))
      (run_nd_pool #v[.write 1 1, .write 2 1] none (shared 0 0 ctx c)) .pure := by
  refine (an_csl_nd_select 1 _ ctx c _ _ _ _).2 ⟨ticll_top .pure, fun j => ?_⟩
  match j with
  | 0 => exact ax_visW_mono (fun _ => Or.inl) (focused_write_child ctx c)
  | 1 => exact ax_visW_mono (fun _ => Or.inr) (focused_write_parent ctx c)

theorem asep_writes_not_ax1 (ctx : Ctx) (c : Nat) :
    ¬ entails (AX (visWₜ one_write_obs))
      (run_nd_pool #v[.write 1 1, .write 2 1] none (shared 0 0 ctx c)) .pure := fun H =>
  not_visWith_pure (((an_csl_nd_select 1 _ ctx c _ _ _ _).1 H).2 0).1

theorem asep_writes_ex_child (ctx : Ctx) (c : Nat) :
    entails (EX (AX (visWₜ heap_10)))
      (run_nd_pool #v[.write 1 1, .write 2 1] none (shared 0 0 ctx c)) .pure :=
  (en_csl_nd_select 1 _ ctx c _ _ _ _).2 ⟨ticll_top .pure, child, focused_write_child ctx c⟩

theorem asep_writes_ex_parent (ctx : Ctx) (c : Nat) :
    entails (EX (AX (visWₜ heap_01)))
      (run_nd_pool #v[.write 1 1, .write 2 1] none (shared 0 0 ctx c)) .pure :=
  (en_csl_nd_select 1 _ ctx c _ _ _ _).2 ⟨ticll_top .pure, parent, focused_write_parent ctx c⟩

/-- Ghost `(a, b, c)`: the two cell values and the emission counter. -/
def loop_inv (ctx : Ctx) (g : Nat × Nat × Nat) (s : SSig) : Prop :=
  split_cells g.1 g.2.1 (csl_memory s) ∧ s.2 = (ctx, g.2.2)

def fresh_emit (k : Nat) (o : CSLObs (Nat × Nat)) : Prop :=
  csl_indexed (fun e => k ≤ e.index) o

/-- Exact first-yield segment; the guard is normalized without a raw step. -/
private theorem exact_lproc_turn (i v : Nat) (h allocs : Heap) (ctx : Ctx) (c : Nat) :
    h i = some v →
    segment_to sh csl_equ (denote (lproc i)) ((h, allocs), (ctx, c))
      [CSLObs.heap (upd h i (v + 1), allocs), .emit (stamp (i, v + 1) c)]
      (denote (lproc i)) ((upd h i (v + 1), allocs), (ctx, c + 1)) := by
  intro HV
  refine exact_source_until _ _ _ _ _ _ (exact_source_bind _ _ _ _ _ _ _ ?_)
  refine exact_source_bind _ _ _ _ _ _ _ ?_
  refine exact_source_read _ _ _ _ _ _ _ _ _ _ HV ?_
  refine exact_source_bind _ _ _ _ _ _ _ ?_
  refine exact_source_write _ _ _ _ _ _ _ _ _ _ (by rw [HV]; nofun) ?_
  refine exact_source_emit _ _ _ _ _ _ _ _ _ ?_
  refine exact_source_bind _ _ _ _ _ _ _ ?_
  refine exact_source_yield _ _ _ ?_
  rw [source_raw_ret]
  exact guard_equ_left _ _ (guard_equ_equ _ _ rfl)

theorem loop_child_turn (ctx : Ctx) (a b c : Nat) (s : SSig) : loop_inv ctx (a, b, c) s →
    ∃ s', segment_to sh csl_equ (denote (lproc 1)) s
      [CSLObs.heap (csl_memory s'), .emit (stamp (1, a + 1) c)] (denote (lproc 1)) s' ∧
      loop_inv ctx (a + 1, b, c + 1) s' := by
  obtain ⟨⟨h, allocs⟩, ctx0, c0⟩ := s
  rintro ⟨HM, HS⟩
  cases HS
  obtain ⟨H1, -⟩ := split_cells_lookup _ _ _ HM
  refine ⟨((upd h 1 (a + 1), allocs), (ctx, c + 1)), exact_lproc_turn _ _ _ _ _ _ H1,
    (split_cells_iff_both _ _ _).2 ?_, rfl⟩
  have HR := frame_rel_both_1 a b ctx c ((h, allocs), (ctx, c))
    ((split_cells_iff_both _ _ _).1 HM) rfl
  have HW := frame_rel_write _ _ _ 1 (a + 1) HR (by simp [own, region, csl_memory, hsingle_eq])
  exact peq_trans _ _ _ HW.2.2 (pop_resp _ _ _ _ (upd_region _ _ _) (peq_refl _))

theorem loop_parent_turn (ctx : Ctx) (a b c : Nat) (s : SSig) : loop_inv ctx (a, b, c) s →
    ∃ s', segment_to sh csl_equ (denote (lproc 2)) s
      [CSLObs.heap (csl_memory s'), .emit (stamp (2, b + 1) c)] (denote (lproc 2)) s' ∧
      loop_inv ctx (a, b + 1, c + 1) s' := by
  obtain ⟨⟨h, allocs⟩, ctx0, c0⟩ := s
  rintro ⟨HM, HS⟩
  cases HS
  obtain ⟨-, H2⟩ := split_cells_lookup _ _ _ HM
  refine ⟨((upd h 2 (b + 1), allocs), (ctx, c + 1)), exact_lproc_turn _ _ _ _ _ _ H2,
    (split_cells_iff_both _ _ _).2 ?_, rfl⟩
  have HR := frame_rel_both_2 a b ctx c ((h, allocs), (ctx, c))
    ((split_cells_iff_both _ _ _).1 HM) rfl
  have HW := frame_rel_write _ _ _ 2 (b + 1) HR (by simp [own, region, csl_memory, hsingle_eq])
  refine peq_trans _ _ _ HW.2.2 (peq_trans _ _ _
    (pop_resp _ _ _ _ (upd_region _ _ _) (peq_refl _)) ?_)
  exact pop_comm _ _ (region_disj _ _ _ _ (by decide))

theorem loop_ranked (ctx : Ctx) (k : Nat) :
    RankedTurns sh (csl_pool #v[lproc 1, lproc 2]) (loop_inv ctx) (fun g => k - g.2.2)
      (· < ·) (fresh_emit k) := by
  rintro ⟨a, b, c⟩ s i Hinv
  have rank : ∀ m o, (k ≤ c → fresh_emit k o) →
      (∃ x ∈ [CSLObs.heap m, o], fresh_emit k x) ∨ k - (c + 1) < k - c :=
    fun _ o ho => if hle : k ≤ c then .inl ⟨o, .tail _ (.head _), ho hle⟩ else .inr (by omega)
  match i with
  | 0 =>
    obtain ⟨s', Hseg, Hinv'⟩ := loop_child_turn ctx a b c s Hinv
    exact ⟨(a + 1, b, c + 1), s', _, by simpa [csl_pool] using Hseg, Hinv',
      by simpa using rank _ _ id⟩
  | 1 =>
    obtain ⟨s', Hseg, Hinv'⟩ := loop_parent_turn ctx a b c s Hinv
    exact ⟨(a, b + 1, c + 1), s', _, by simpa [csl_pool] using Hseg, Hinv',
      by simpa using rank _ _ id⟩

/-- The two looping processes started by `fork2`, as a source pool. -/
theorem fork2_lprocs_pool :
    (#v[denote (lproc 1), denote (lproc 2)] : Pool sE Bn 2) = csl_pool #v[lproc 1, lproc 2] :=
  Vector.ext fun i hi => by match i, hi with | 0, _ | 1, _ => simp [csl_pool]

theorem asep_lprocs_agaf_nd (a b : Nat) (ctx : Ctx) (c k : Nat) :
    entails (AG (AF (visWₜ (fresh_emit k))))
      (run_nd (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_nd_fork_bind _ _ _)).2 ?_
  rw [fork2_lprocs_pool]
  refine ag_csl_nd_invariance _ (loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (loop_ranked ctx k)) ?_ ?_ (a, b, c) _ (some parent) _
    ⟨(split_cells_iff_both _ _ _).2 (peq_refl _), rfl⟩ .pure
  · intro o t w Hw Hphi
    rw [← log_vis]; exact af_log Hw Hphi
  · intro g s focus w Hinv Hw
    exact aul_csl_nd_eventually _ _ _ _ _ Nat.lt_wfRel.wf (loop_ranked ctx k) g s focus w Hinv Hw

theorem asep_lprocs_agaf_rr (a b : Nat) (ctx : Ctx) (c k : Nat) :
    entails (AG (AF (visWₜ (fair_obs (fresh_emit k)))))
      (run_rr (fork2 (lproc 1) (lproc 2)) (shared a b ctx c)) .pure := by
  refine (proper_entails_meq _ (run_rr_fork_bind _ _ _)).2 ?_
  rw [fork2_lprocs_pool]
  refine ag_csl_rr_invariance _ (loop_inv ctx) _
    (ranked_turns_closed sh _ _ _ _ _ (loop_ranked ctx k)) ?_ ?_ (a, b, c) _ (some parent) 0 _
    ⟨(split_cells_iff_both _ _ _).2 (peq_refl _), rfl⟩ .pure
  · intro o t w Hw Hphi
    rw [← log_vis]; exact af_log Hw Hphi
  · intro g s focus turn w Hinv Hw
    exact aul_csl_rr_eventually _ _ _ _ _ Nat.lt_wfRel.wf (loop_ranked ctx k) g s focus turn w
      Hinv Hw

end InvariantSeparation

end Examples.CSL.Frame.Asep
