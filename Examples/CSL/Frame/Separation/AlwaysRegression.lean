/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Separation.Shared
public import Lang.CoCSL.Owned
public import Logic.Utils.Execution

/-!
# Obligation 6: AG splitting with release certificates, and its boundaries

Two forked lineages loop forever (write their own cell, emit, yield). A step-closed phase
invariant with release ranks splits the global `AG` into one `AG` per lineage; one fair execution
splits `EG`. A parent that never yields has no release certificate for the child, and a
guard-only divergent thread has no action
(← `examples/CSL/Frame/Separation.v`, module `AlwaysRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.AlwaysRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.CSL Tisl.Yield CoCSL

/-! ## Threads -/

/-- Each lineage loops: write its cell with the value it already holds, emit, yield. -/
def body (a v tag : Nat) : CProg (Option Unit) :=
  .bind (.write a v) fun _ => .bind (.emit tag v) fun _ =>
    .bind .yield fun _ => .ret (some ())

def cloop (a v tag : Nat) : CProg Unit := .untilNone (body a v tag)

/-! Its three phases, after any guards and pure binds. -/

def tY (a v tag : Nat) : Thread sE Bn :=
  .vis (E := CEff) (.inl ⟨⟩) fun _ => .guard (denote (cloop a v tag))

def tE (a v tag : Nat) : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inr (.inr (tag, v))))) fun _ => tY a v tag

def tW (a v tag : Nat) : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inl (.write a v)))) fun _ => tE a v tag

theorem cloop_unfold (a v tag : Nat) : denote (cloop a v tag) = tW a v tag := by
  simp only [denote, cloop, source_raw_until, body, source_raw_bind, source_raw_write_head,
    source_raw_emit_head, source_raw_yield_head, source_raw_ret]
  rfl

inductive phase
  | PW
  | PE
  | PY

def in_phase (a v tag : Nat) : phase → Thread sE Bn → Prop
  | .PW, t => ∃ n, t = guards n (tW a v tag)
  | .PE, t => t = tE a v tag
  | .PY, t => t = tY a v tag

def phase_succ : phase → phase
  | .PW => .PE
  | .PE => .PY
  | .PY => .PW

def phase_thread (a v tag : Nat) : phase → Thread sE Bn
  | .PW => tE a v tag
  | .PE => tY a v tag
  | .PY => .guard (denote (cloop a v tag))

def phase_kind (_a v tag : Nat) (ph : phase) (c : OwnedCfg) : OwnedKind :=
  match ph with
  | .PW => .write
  | .PE => .emit (tag, v) (global_count c)
  | .PY => .yield

def phase_cfg (i : Side) (a v tag : Nat) (ph : phase) (c : OwnedCfg) : OwnedCfg :=
  match ph with
  | .PW => set_heap c i (upd (c.heap i).1 a v, (c.heap i).2)
  | .PE => emit_cfg c i (tag, v)
  | .PY => c

def phase_focus {n : Nat} (j : Fin n) : phase → Option (Fin n)
  | .PY => none
  | _ => some j

theorem phase_thread_in (a v tag : Nat) (ph : phase) (t : Thread sE Bn) :
    t = phase_thread a v tag ph → in_phase a v tag (phase_succ ph) t := by
  cases ph <;> intro H
  · exact H
  · exact H
  · exact ⟨1, H.trans (congrArg CTree.guard (cloop_unfold a v tag))⟩

theorem tE_in (a v tag : Nat) : in_phase a v tag .PE (tE a v tag) := rfl
theorem tY_in (a v tag : Nat) : in_phase a v tag .PY (tY a v tag) := rfl

/-- The focused slot in a phase has exactly one action. -/
theorem phase_step (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1)) (g : Vector Side (n + 1))
    (j : Fin (n + 1)) (a0 v0 tag0 : Nat) (ph : phase) (a : OwnedAction) (c' : OwnedCfg) :
    in_phase a0 v0 tag0 ph v[j] → (c.heap g[j]).1 a0 = some v0 →
    focus_step c n v g j a c' →
    ∃ t, t = phase_thread a0 v0 tag0 ph ∧ a = act g[j] (phase_kind a0 v0 tag0 ph c) ∧
      c' = set_pool (phase_cfg g[j] a0 v0 tag0 ph c)
        (mk_pool (n + 1) (v.set j t) g (phase_focus j ph)) := by
  intro Hph Hcell H
  cases ph with
  | PW =>
    obtain ⟨m, Hm⟩ := Hph
    obtain ⟨k, kind, y, c1, Hk, Hprim, rfl, rfl⟩ :=
      (focus_step_head_prim c n v g j _ _ m _ _ Hm).1 H
    simp only [prim_step, heap_prim, Hcell, Option.some.injEq, Prod.mk.injEq] at Hprim
    obtain ⟨rfl, -, rfl⟩ := Hprim
    exact ⟨k y, Hk _, rfl, rfl⟩
  | PE =>
    obtain ⟨k, kind, y, c1, Hk, Hprim, rfl, rfl⟩ :=
      (focus_step_head_prim c n v g j _ _ 0 _ _ Hph).1 H
    simp only [prim_step, emit_prim, Option.some.injEq, Prod.mk.injEq] at Hprim
    obtain ⟨rfl, -, rfl⟩ := Hprim
    exact ⟨k y, Hk _, rfl, rfl⟩
  | PY =>
    obtain ⟨k, Hk, rfl, rfl⟩ := (focus_step_head_yield c n v g j _ 0 _ _ Hph).1 H
    exact ⟨k ⟨⟩, Hk _, rfl, rfl⟩

theorem phase_step_intro (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (a0 v0 tag0 : Nat) (ph : phase) :
    in_phase a0 v0 tag0 ph v[j] → (c.heap g[j]).1 a0 = some v0 →
    focus_step c n v g j (act g[j] (phase_kind a0 v0 tag0 ph c))
      (set_pool (phase_cfg g[j] a0 v0 tag0 ph c)
        (mk_pool (n + 1) (v.set j (phase_thread a0 v0 tag0 ph)) g (phase_focus j ph))) := by
  intro Hph Hcell
  cases ph with
  | PW =>
    obtain ⟨m, Hm⟩ := Hph
    refine (focus_step_head_prim c n v g j _ _ m _ _ Hm).2
      ⟨fun _ => tE a0 v0 tag0, .write, ⟨⟩, _, fun _ => rfl, ?_, rfl, rfl⟩
    simp only [prim_step, heap_prim, Hcell]; rfl
  | PE =>
    exact (focus_step_head_prim c n v g j _ _ 0 _ _ Hph).2
      ⟨fun _ => tY a0 v0 tag0, .emit (tag0, v0) (global_count c), ⟨⟩, _, fun _ => rfl, rfl, rfl,
        rfl⟩
  | PY =>
    exact (focus_step_head_yield c n v g j _ 0 _ _ Hph).2 ⟨_, fun _ => rfl, rfl, rfl⟩

theorem phase_cfg_own (i : Side) (a0 v0 tag0 : Nat) (ph : phase) (c : OwnedCfg) :
    (c.heap i).1 a0 = some v0 → ((phase_cfg i a0 v0 tag0 ph c).heap i).1 a0 = some v0 := by
  intro H
  cases ph with
  | PW => simp [phase_cfg, set_heap, side_upd, upd]
  | PE => exact H
  | PY => exact H

theorem phase_cfg_other (i k : Side) (a0 v0 tag0 : Nat) (ph : phase) (c : OwnedCfg) :
    i ≠ k → (phase_cfg i a0 v0 tag0 ph c).heap k = c.heap k := by
  intro H
  cases ph with
  | PW => simp [phase_cfg, set_heap, side_upd, Ne.symm H]
  | PE => rfl
  | PY => rfl

/-! ## Release ranks -/

/-- 3/2/1 before a write/emit/yield head; guards count as a write head. -/
def head_rank (t : Thread sE Bn) : Nat :=
  match t.unfold with
  | .vis e _ =>
    match e with
    | .inl _ => 1
    | .inr (.inr (.inr (.inr _))) => 2
    | _ => 3
  | _ => 3

theorem head_rank_equ (t u : Thread sE Bn) : t = u → head_rank t = head_rank u := by
  rintro rfl; rfl

def phase_rank : phase → Nat
  | .PW => 3
  | .PE => 2
  | .PY => 1

theorem head_rank_phase (a v tag : Nat) (ph : phase) (t : Thread sE Bn) :
    in_phase a v tag ph t → head_rank t = phase_rank ph := by
  cases ph with
  | PW =>
    rintro ⟨_ | m, rfl⟩
    · simp [head_rank, tW, phase_rank]
    · simp [head_rank, phase_rank]
  | PE => rintro rfl; simp [head_rank, tE, phase_rank]
  | PY => rintro rfl; simp [head_rank, tY, phase_rank]

/-- The focused thread's rank; `0` when the scheduler must select. -/
def rank (d : OwnedCfg) : Nat :=
  match focused_thread d.pool with
  | some (t, _) => head_rank t
  | none => 0

/-- Lineage `i`'s release rank: `0` when `i` is directly ready (focused or selectable), else the
foreign focused head's rank. -/
def release_rank (i : Side) (d : OwnedCfg) : Nat :=
  match focused_thread d.pool with
  | some (t, j) => if side_eqb j i then 0 else head_rank t
  | none => 0

theorem release_rank_le (i : Side) (d : OwnedCfg) : release_rank i d ≤ rank d := by
  unfold release_rank rank
  rcases focused_thread d.pool with _ | ⟨t, j⟩
  · exact Nat.le_refl _
  · dsimp only; split <;> omega

/-- Every action from a focused configuration belongs to the focused lineage. -/
theorem owned_step_owner (d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg) (t : Thread sE Bn)
    (j : Side) : focused_thread d.pool = some (t, j) → owned_step d a d' → a.owner = j := by
  unfold focused_thread
  intro Hf Hs
  split at Hf
  · rename_i k Hk
    cases Hf
    exact owned_step_focused_owner d a d' Hs k Hk
  · cases Hf

/-! ## The two-loop fork -/

def pc : CProg Unit := cloop 1 1 1
def pp : CProg Unit := cloop 2 8 0
def hC : ManagedHeap := (hsingle 1 1, hemp)
def hP : ManagedHeap := (hsingle 2 8, hemp)
def ctx0 : Ctx := []
def c0 : OwnedCfg := init_owned pc pp hC hP ctx0 0

def cellC : hprop := fun c => (c.heap .child).1 1 = some 1
def cellP : hprop := fun c => (c.heap .parent).1 2 = some 8

theorem cellC_proper : hproper cellC := cell_proper _ _ _
theorem cellP_proper : hproper cellP := cell_proper _ _ _

def thC : phase → Thread sE Bn → Prop := in_phase 1 1 1
def thP : phase → Thread sE Bn → Prop := in_phase 2 8 0

/-- Unfocused slots are before their write; with no focus, both are. -/
def pool_ok (tc tp : Thread sE Bn) : Option (Fin 2) → Prop
  | none => thC .PW tc ∧ thP .PW tp
  | some j =>
    (j = 0 ∧ (∃ ph, thC ph tc) ∧ thP .PW tp) ∨
    (j = 1 ∧ thC .PW tc ∧ ∃ ph, thP ph tp)

/-- The step-closed invariant of the two loop phases. -/
def Inv (d : OwnedCfg) : Prop :=
  owned_wf d ∧ cellC d ∧ cellP d ∧
  ∃ tc tp f, d.pool = mk_pool 2 #v[tc, tp] #v[.child, .parent] f ∧ pool_ok tc tp f

theorem hC_hP_disj : hC # hP := ⟨hsingle_disj _ _ _ _ (by decide), hdisj_hemp _⟩

theorem Inv_c0 : Inv c0 := by
  refine ⟨init_owned_wf _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    hC_hP_disj, rfl, rfl, denote pc, denote pp, some 1, rfl, .inr ⟨rfl, ⟨0, ?_⟩, .PW, 0, ?_⟩⟩
  · exact cloop_unfold 1 1 1
  · exact cloop_unfold 2 8 0

/-- Every action preserves `Inv`; a focused action lowers the rank. -/
theorem Inv_step (d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg) :
    Inv d → owned_step d a d' →
    Inv d' ∧ (focused_thread d.pool = none ∨ rank d' < rank d) := by
  intro HI Hs
  obtain ⟨Hwf, Hc, Hp, tc, tp, f, Hpool, Hok⟩ := HI
  have Hwf' := owned_step_wf d a d' Hwf Hs
  unfold rank focused_thread
  unfold owned_step at Hs
  rw [Hpool] at Hs ⊢
  rcases f with _ | j
  · refine ⟨?_, .inl rfl⟩
    obtain ⟨j, rfl, rfl⟩ := Hs
    obtain ⟨HtC, HtP⟩ := Hok
    refine ⟨Hwf', Hc, Hp, tc, tp, some j, rfl, ?_⟩
    match j with
    | 0 => exact .inl ⟨rfl, ⟨.PW, HtC⟩, HtP⟩
    | 1 => exact .inr ⟨rfl, HtC, .PW, HtP⟩
  · rcases Hok with ⟨rfl, ⟨ph, Hph⟩, HtP⟩ | ⟨rfl, HtC, ⟨ph, Hph⟩⟩
    · obtain ⟨t, Ht, rfl, rfl⟩ := phase_step d 1 #v[tc, tp] #v[.child, .parent] 0 1 1 1 ph a d'
        Hph Hc Hs
      have Hin := phase_thread_in _ _ _ _ _ Ht
      refine ⟨⟨Hwf', phase_cfg_own _ _ _ _ _ _ Hc, ?_, t, tp, phase_focus 0 ph, rfl, ?_⟩, ?_⟩
      · show ((phase_cfg _ _ _ _ _ _).heap .parent).1 2 = some 8
        rw [phase_cfg_other _ _ _ _ _ _ _ (by decide)]; exact Hp
      · cases ph with
        | PW => exact .inl ⟨rfl, ⟨.PE, Hin⟩, HtP⟩
        | PE => exact .inl ⟨rfl, ⟨.PY, Hin⟩, HtP⟩
        | PY => exact ⟨Hin, HtP⟩
      · refine .inr ?_
        show _ < head_rank tc
        rw [head_rank_phase _ _ _ _ _ Hph]
        cases ph with
        | PY => show 0 < 1; omega
        | PW | PE =>
          show head_rank t < _
          rw [head_rank_phase _ _ _ _ _ Hin]; decide
    · obtain ⟨t, Ht, rfl, rfl⟩ := phase_step d 1 #v[tc, tp] #v[.child, .parent] 1 2 8 0 ph a d'
        Hph Hp Hs
      have Hin := phase_thread_in _ _ _ _ _ Ht
      refine ⟨⟨Hwf', ?_, phase_cfg_own _ _ _ _ _ _ Hp, tc, t, phase_focus 1 ph, rfl, ?_⟩, ?_⟩
      · show ((phase_cfg _ _ _ _ _ _).heap .child).1 1 = some 1
        rw [phase_cfg_other _ _ _ _ _ _ _ (by decide)]; exact Hc
      · cases ph with
        | PW => exact .inr ⟨rfl, HtC, .PE, Hin⟩
        | PE => exact .inr ⟨rfl, HtC, .PY, Hin⟩
        | PY => exact ⟨HtC, Hin⟩
      · refine .inr ?_
        show _ < head_rank tp
        rw [head_rank_phase _ _ _ _ _ Hph]
        cases ph with
        | PY => show 0 < 1; omega
        | PW | PE =>
          show head_rank t < _
          rw [head_rank_phase _ _ _ _ _ Hin]; decide

theorem Inv_closed : step_closed Inv := fun d a d' HI Hs => (Inv_step d a d' HI Hs).1

theorem Inv_select (d : OwnedCfg) (i : Side) :
    Inv d → focused_thread d.pool = none → ∃ d', owned_step d (act i .select) d' := by
  rintro ⟨-, -, -, tc, tp, f, Hpool, -⟩ Hf
  unfold focused_thread at Hf
  rw [Hpool] at Hf
  rcases f with _ | j
  · unfold owned_step
    rw [Hpool]
    cases i
    · exact ⟨_, 0, rfl, rfl⟩
    · exact ⟨_, 1, rfl, rfl⟩
  · cases Hf

theorem Inv_can (d : OwnedCfg) : Inv d → hcan_step owned_next d := by
  intro HI
  have ⟨_, Hc, Hp, tc, tp, f, Hpool, Hok⟩ := HI
  rcases f with _ | j
  · obtain ⟨d', Hs⟩ := Inv_select d .child HI (by unfold focused_thread; rw [Hpool]; rfl)
    exact ⟨d', _, Hs⟩
  · unfold hcan_step owned_next owned_step
    rw [Hpool]
    rcases Hok with ⟨rfl, ⟨ph, Hph⟩, -⟩ | ⟨rfl, -, ⟨ph, Hph⟩⟩
    · exact ⟨_, _, phase_step_intro d 1 #v[tc, tp] #v[.child, .parent] 0 1 1 1 ph Hph Hc⟩
    · exact ⟨_, _, phase_step_intro d 1 #v[tc, tp] #v[.child, .parent] 1 2 8 0 ph Hph Hp⟩

/-- From every progressing state, lineage `i` is enabled after finitely many rank-decreasing
foreign actions. -/
theorem Inv_release (i : Side) : finite_release i Inv (release_rank i) := by
  intro d HI Hcan
  rcases scheduler_shape i d Hcan with Hst | Hown
  · refine .inr ?_
    obtain ⟨d', a, Hs⟩ := Hcan
    obtain ⟨HI', Hf | Hr⟩ := Inv_step d a d' HI Hs
    · obtain ⟨d'', Hsel⟩ := Inv_select d i HI Hf
      exact absurd rfl (Hst _ _ Hsel)
    · refine ⟨d', ⟨a, Hs, Hst _ _ Hs⟩, HI', ?_⟩
      have Hj : release_rank i d = rank d := by
        unfold release_rank rank
        rcases Ef : focused_thread d.pool with _ | ⟨t, j⟩
        · rfl
        · have Hne : side_eqb j i = false := by
            cases h : side_eqb j i
            · rfl
            · exact (Hst _ _ Hs ((owned_step_owner _ _ _ _ _ Ef Hs).trans
                ((side_eqb_spec _ _).1 h))).elim
          dsimp only
          rw [Hne]; rfl
      rw [Hj]
      exact Nat.lt_of_le_of_lt (release_rank_le _ _) Hr
  · exact .inl Hown

/-! ## Global AG and its split -/

theorem Inv_hsep (d : OwnedCfg) :
    Inv d → state_sat (fun c => asep (state_obligation .child cellC c)
      (state_obligation .parent cellP c)) d :=
  fun ⟨Hwf, Hc, Hp, _⟩ => (state_split_iff _ _ _).2 ⟨Hwf, Hc, Hp⟩

theorem loops_global_hag :
    hAG owned_next (state_sat fun c => asep (state_obligation .child cellC c)
      (state_obligation .parent cellP c)) c0 :=
  hAG_coind _ _ Inv (fun d HI => ⟨Inv_hsep d HI, Inv_can d HI,
    fun d' ⟨a, Hs⟩ => Inv_closed d a d' HI Hs⟩) c0 Inv_c0

theorem loops_admissible : admissible pc pp hC hP ctx0 0 :=
  admissible_intro _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    hC_hP_disj
    ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩⟩
    ⟨trivial, fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩⟩
    ⟨by simp [addr_ok, hC, hsingle], fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩⟩
    ⟨by simp [addr_ok, hP, hsingle], fun _ => ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩⟩

/-- Both lineages always keep their cells, from the conventional focused singleton
initializers. -/
theorem loops_fork_hag :
    hAG owned_next cellC (init_local .child pc hC ctx0 0 true) ∧
    hAG owned_next cellP (init_local .parent pp hP ctx0 0 true) :=
  fork_hag_split pc (fun _ => pp) hC hP ctx0 0 Inv (release_rank .child) (release_rank .parent)
    cellC cellP loops_admissible cellC_proper cellP_proper Inv_c0 Inv_closed
    (Inv_release .child) (Inv_release .parent) loops_global_hag

theorem loops_global_hag_split :
    hAG owned_next cellC (project .child c0) ∧ hAG owned_next cellP (project .parent c0) ∧
    hAG owned_next cellC (init_local .child pc hC ctx0 0 false) ∧
    hAG owned_next cellC (init_local .child pc hC ctx0 0 true) ∧
    hAG owned_next cellP (init_local .parent pp hP ctx0 0 true) := by
  obtain ⟨HC, HP⟩ := global_hag_split Inv (release_rank .child) (release_rank .parent) cellC
    cellP c0 (coupled_init _ _ _ _ _ _ loops_admissible) cellC_proper cellP_proper Inv_c0
    Inv_closed (Inv_release .child) (Inv_release .parent) loops_global_hag
  have HC' : hAG owned_next cellC (init_local .child pc hC ctx0 0 false) :=
    (hAG_proper cellC cellC_proper _ _ (project_init_child pc pp hC hP ctx0 0)).1 HC
  exact ⟨HC, HP, HC', hAG_select_strip _ _ _ _ _ _ HC',
    (hAG_proper cellP cellP_proper _ _ (project_init_parent pc pp hC hP ctx0 0)).1 HP⟩

/-! ## EG along one fair execution -/

/-- Schedule positions: the parent's first iteration, then the child's first selection and
write, then the periodic rounds. -/
inductive pos
  | Q0 | Q1 | Q2 | R0 | R1 | C0 | C1 | C2 | C3 | P0 | P1 | P2 | P3

def next_pos : pos → pos
  | .Q0 => .Q1 | .Q1 => .Q2 | .Q2 => .R0 | .R0 => .R1 | .R1 => .C2
  | .C0 => .C1 | .C1 => .C2 | .C2 => .C3 | .C3 => .P0
  | .P0 => .P1 | .P1 => .P2 | .P2 => .P3 | .P3 => .C0

def GLc : Thread sE Bn := .guard (denote pc)
def GLp : Thread sE Bn := .guard (denote pp)

def pool_of : pos → TaggedPool
  | .Q0 => mk_pool 2 #v[denote pc, denote pp] #v[.child, .parent] (some 1)
  | .Q1 => mk_pool 2 #v[denote pc, tE 2 8 0] #v[.child, .parent] (some 1)
  | .Q2 => mk_pool 2 #v[denote pc, tY 2 8 0] #v[.child, .parent] (some 1)
  | .R0 => mk_pool 2 #v[denote pc, GLp] #v[.child, .parent] none
  | .R1 => mk_pool 2 #v[denote pc, GLp] #v[.child, .parent] (some 0)
  | .C0 => mk_pool 2 #v[GLc, GLp] #v[.child, .parent] none
  | .C1 => mk_pool 2 #v[GLc, GLp] #v[.child, .parent] (some 0)
  | .C2 => mk_pool 2 #v[tE 1 1 1, GLp] #v[.child, .parent] (some 0)
  | .C3 => mk_pool 2 #v[tY 1 1 1, GLp] #v[.child, .parent] (some 0)
  | .P0 => mk_pool 2 #v[GLc, GLp] #v[.child, .parent] none
  | .P1 => mk_pool 2 #v[GLc, GLp] #v[.child, .parent] (some 1)
  | .P2 => mk_pool 2 #v[GLc, tE 2 8 0] #v[.child, .parent] (some 1)
  | .P3 => mk_pool 2 #v[GLc, tY 2 8 0] #v[.child, .parent] (some 1)

def pos_owner : pos → Side
  | .Q0 | .Q1 | .Q2 | .P0 | .P1 | .P2 | .P3 => .parent
  | .R0 | .R1 | .C0 | .C1 | .C2 | .C3 => .child

def pos_phase : pos → Option phase
  | .Q0 | .R1 | .C1 | .P1 => some .PW
  | .Q1 | .C2 | .P2 => some .PE
  | .Q2 | .C3 | .P3 => some .PY
  | .R0 | .C0 | .P0 => none

def side_cell : Side → Nat × Nat × Nat
  | .child => (1, 1, 1)
  | .parent => (2, 8, 0)

def pos_kind (p : pos) (c : OwnedCfg) : OwnedKind :=
  match pos_phase p with
  | some ph => match side_cell (pos_owner p) with
    | (a, v, tag) => phase_kind a v tag ph c
  | none => .select

def pos_cfg (p : pos) (c : OwnedCfg) : OwnedCfg :=
  match pos_phase p with
  | some ph => match side_cell (pos_owner p) with
    | (a, v, tag) => phase_cfg (pos_owner p) a v tag ph c
  | none => c

/-- The concrete pool update is iterated without a second recursive runner. -/
def run (n : Nat) : pos × OwnedCfg :=
  Nat.repeat (fun pc => (next_pos pc.1, set_pool (pos_cfg pc.1 pc.2) (pool_of (next_pos pc.1))))
    n (.Q0, c0)

def fair_exec : Execution OwnedCfg OwnedAction Unit where
  states n := (run n).2
  selected n := act (pos_owner (run n).1) (pos_kind (run n).1 (run n).2)
  emitted _ := ()

theorem run_pool (n : Nat) : (run n).2.pool = pool_of (run n).1 := by
  cases n <;> rfl

theorem run_step (n : Nat) :
    cellC (run n).2 → cellP (run n).2 →
    owned_step (fair_exec.states n) (fair_exec.selected n) (fair_exec.states (n + 1)) := by
  intro Hc Hp
  show owned_step (run n).2 (act (pos_owner (run n).1) (pos_kind (run n).1 (run n).2))
    (set_pool (pos_cfg (run n).1 (run n).2) (pool_of (next_pos (run n).1)))
  have Hpool := run_pool n
  generalize run n = r at Hc Hp Hpool ⊢
  obtain ⟨p, c⟩ := r
  dsimp only at Hc Hp Hpool ⊢
  unfold owned_step
  rw [Hpool]
  have HWc : thC .PW (denote pc) := ⟨0, cloop_unfold 1 1 1⟩
  have HWp : thP .PW (denote pp) := ⟨0, cloop_unfold 2 8 0⟩
  have HGc : thC .PW GLc := ⟨1, congrArg CTree.guard (cloop_unfold 1 1 1)⟩
  have HGp : thP .PW GLp := ⟨1, congrArg CTree.guard (cloop_unfold 2 8 0)⟩
  cases p
  · exact phase_step_intro c 1 #v[denote pc, denote pp] #v[.child, .parent] 1 2 8 0 .PW HWp Hp
  · exact phase_step_intro c 1 #v[denote pc, tE 2 8 0] #v[.child, .parent] 1 2 8 0 .PE
      (tE_in _ _ _) Hp
  · exact phase_step_intro c 1 #v[denote pc, tY 2 8 0] #v[.child, .parent] 1 2 8 0 .PY
      (tY_in _ _ _) Hp
  · exact ⟨0, rfl, rfl⟩
  · exact phase_step_intro c 1 #v[denote pc, GLp] #v[.child, .parent] 0 1 1 1 .PW HWc Hc
  · exact ⟨0, rfl, rfl⟩
  · exact phase_step_intro c 1 #v[GLc, GLp] #v[.child, .parent] 0 1 1 1 .PW HGc Hc
  · exact phase_step_intro c 1 #v[tE 1 1 1, GLp] #v[.child, .parent] 0 1 1 1 .PE
      (tE_in _ _ _) Hc
  · exact phase_step_intro c 1 #v[tY 1 1 1, GLp] #v[.child, .parent] 0 1 1 1 .PY
      (tY_in _ _ _) Hc
  · exact ⟨1, rfl, rfl⟩
  · exact phase_step_intro c 1 #v[GLc, GLp] #v[.child, .parent] 1 2 8 0 .PW HGp Hp
  · exact phase_step_intro c 1 #v[GLc, tE 2 8 0] #v[.child, .parent] 1 2 8 0 .PE
      (tE_in _ _ _) Hp
  · exact phase_step_intro c 1 #v[GLc, tY 2 8 0] #v[.child, .parent] 1 2 8 0 .PY
      (tY_in _ _ _) Hp

theorem fair_exec_spec : (∀ n, Inv (fair_exec.states n)) ∧ owned_run fair_exec :=
  execution_invariant_steps (fun a c (_ : Unit) c' => owned_step c a c') Inv fair_exec Inv_c0
    fun n HI =>
      have Hstep := run_step n HI.2.1 HI.2.2.1
      ⟨Hstep, Inv_closed _ _ _ HI Hstep⟩

theorem run_pos_S (n : Nat) : (run (n + 1)).1 = next_pos (run n).1 := rfl

theorem run_pos_add (n k : Nat) : (run (n + k)).1 = Nat.repeat next_pos k (run n).1 := by
  induction k with
  | zero => rfl
  | succ k ih => exact (run_pos_S _).trans (congrArg next_pos ih)

theorem fair_exec_recurrent (i : Side) :
    infinitely (fun n => (fair_exec.selected n).owner = i) := by
  intro n
  have H : ∃ k, pos_owner (Nat.repeat next_pos k (run n).1) = i := by
    cases i <;> cases (run n).1 <;>
      first
        | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩
        | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩
  obtain ⟨k, Hk⟩ := H
  exact ⟨n + k, Nat.le_add_right _ _, (congrArg pos_owner (run_pos_add n k)).trans Hk⟩

theorem loops_global_heg :
    hEG owned_next cellC (project .child c0) ∧ hEG owned_next cellP (project .parent c0) :=
  global_heg_fair_split cellC cellP c0 fair_exec (coupled_init _ _ _ _ _ _ loops_admissible)
    cellC_proper cellP_proper rfl fair_exec_spec.2 (fun n => Inv_hsep _ (fair_exec_spec.1 n))
    (fair_exec_recurrent .child) (fair_exec_recurrent .parent)

theorem loops_fork_heg :
    hEG owned_next cellC (init_local .child pc hC ctx0 0 true) ∧
    hEG owned_next cellP (init_local .parent pp hP ctx0 0 true) :=
  fork_heg_fair_split pc (fun _ => pp) hC hP ctx0 0 cellC cellP fair_exec loops_admissible
    cellC_proper cellP_proper rfl fair_exec_spec.2 (fun n => Inv_hsep _ (fair_exec_spec.1 n))
    (fair_exec_recurrent .child) (fair_exec_recurrent .parent)

/-! ## Boundary: a parent that never yields -/

/-- The parent emits forever without yielding; the child's write of `1` over its `0` is
pending. -/
def bchild : CProg Unit := .write 1 1
def bparent : CProg Unit := .untilNone (.bind (.emit 0 8) fun _ => .ret (some ()))
def bC : ManagedHeap := (hsingle 1 0, hemp)
def b0 : OwnedCfg := init_owned bchild bparent bC hP ctx0 0

def cell0 : hprop := fun c => (c.heap .child).1 1 = some 0

def tM : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inr (.inr (0, 8))))) fun _ => .guard (denote bparent)

def tWc : Thread sE Bn :=
  .vis (E := CEff) (.inr (.inr (.inl (.write 1 1)))) fun _ => pure ⟨⟩

theorem bparent_unfold : denote bparent = tM := by
  simp only [denote, bparent, source_raw_until, source_raw_bind, source_raw_emit_head,
    source_raw_ret]
  rfl

theorem bchild_unfold : denote bchild = tWc := by
  simp only [denote, bchild, source_raw_write_head]
  rfl

def BInv (d : OwnedCfg) : Prop :=
  owned_wf d ∧ cell0 d ∧
  ∃ tp, d.pool = mk_pool 2 #v[denote bchild, tp] #v[.child, .parent] (some 1) ∧
    ∃ m, tp = guards m tM

theorem bC_hP_disj : bC # hP := ⟨hsingle_disj _ _ _ _ (by decide), hdisj_hemp _⟩

theorem BInv_b0 : BInv b0 :=
  ⟨init_owned_wf _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _) bC_hP_disj,
    rfl, denote bparent, rfl, 0, bparent_unfold⟩

/-- Only the parent ever acts: one emission, after its guards. -/
theorem BInv_step (d : OwnedCfg) (a : OwnedAction) (d' : OwnedCfg) :
    BInv d → owned_step d a d' → BInv d' := by
  rintro ⟨Hwf, Hc, tp, Hpool, m, Hm⟩ Hs
  have Hwf' := owned_step_wf d a d' Hwf Hs
  unfold owned_step at Hs
  rw [Hpool] at Hs
  obtain ⟨k, kind, y, c1, Hk, Hprim, rfl, rfl⟩ :=
    (focus_step_head_prim d 1 #v[denote bchild, tp] #v[.child, .parent] 1 _ _ m _ _ Hm).1 Hs
  simp only [prim_step, emit_prim, Option.some.injEq, Prod.mk.injEq] at Hprim
  obtain ⟨rfl, -, rfl⟩ := Hprim
  exact ⟨Hwf', Hc, k y, rfl, 1, (Hk _).trans (congrArg CTree.guard bparent_unfold)⟩

theorem BInv_can (d : OwnedCfg) : BInv d → ∃ d', owned_next d d' ∧ BInv d' := by
  intro HI
  have ⟨_, _, tp, Hpool, m, Hm⟩ := HI
  have Hs : ∃ d', owned_next d d' := by
    unfold owned_next owned_step
    rw [Hpool]
    exact ⟨_, _,
      (focus_step_head_prim d 1 #v[denote bchild, tp] #v[.child, .parent] 1 _ _ m _ _ Hm).2
        ⟨fun _ => .guard (denote bparent), .emit (0, 8) (global_count d), ⟨⟩, _, fun _ => rfl,
          rfl, rfl, rfl⟩⟩
  obtain ⟨d', a, Hs⟩ := Hs
  exact ⟨d', ⟨a, Hs⟩, BInv_step d a d' HI Hs⟩

theorem boundary_global_hag :
    hAG owned_next (state_sat fun c => asep (state_obligation .child cell0 c)
      (state_obligation .parent hTrue c)) b0 :=
  hAG_coind _ _ BInv (fun d HI =>
    ⟨(state_split_iff _ _ _).2 ⟨HI.1, HI.2.1, trivial⟩,
      (BInv_can d HI).imp fun _ H => H.1, fun d' ⟨a, Hs⟩ => BInv_step d a d' HI Hs⟩) b0 BInv_b0

theorem boundary_global_heg :
    hEG owned_next (state_sat fun c => asep (state_obligation .child cell0 c)
      (state_obligation .parent hTrue c)) b0 :=
  hEG_coind _ _ BInv (fun d HI =>
    ⟨(state_split_iff _ _ _).2 ⟨HI.1, HI.2.1, trivial⟩, BInv_can d HI⟩) b0 BInv_b0

/-- The premises a release certificate cannot be traded for. -/
theorem boundary_premises :
    bC # hP ∧ 0 < (project .child b0).pool.size ∧ 0 < (project .parent b0).pool.size := by
  refine ⟨bC_hP_disj, ?_, ?_⟩
  · unfold b0; rw [owned_equ_eq (project_init_child ..)]; exact Nat.one_pos
  · unfold b0; rw [owned_equ_eq (project_init_parent ..)]; exact Nat.one_pos

def s1 : OwnedCfg := init_local .child bchild bC ctx0 0 true

/-- The standalone child's only action writes `1`. -/
theorem s1_step (a : OwnedAction) (d : OwnedCfg) : owned_step s1 a d → ¬ cell0 d := by
  intro Hs
  obtain ⟨k, kind, y, c1, -, Hprim, rfl, rfl⟩ :=
    (focus_step_head_prim s1 0 #v[denote bchild] #v[.child] 0 _ _ 0 _ _ bchild_unfold).1 Hs
  simp only [prim_step, heap_prim] at Hprim
  obtain ⟨rfl, rfl, rfl⟩ := Hprim
  simp [cell0, set_pool, set_heap, side_upd, upd]

theorem s1_can : ∃ d, owned_next s1 d :=
  ⟨_, _, (focus_step_head_prim s1 0 #v[denote bchild] #v[.child] 0 _ _ 0 _ _ bchild_unfold).2
    ⟨fun _ => pure ⟨⟩, .write, ⟨⟩, _, fun _ => rfl, rfl, rfl, rfl⟩⟩

theorem boundary_local_no_hag : ¬ hAG owned_next cell0 s1 := by
  intro H
  obtain ⟨-, -, Hall⟩ := (hAG_unfold _ _ _).1 H
  obtain ⟨d, a, Hs⟩ := s1_can
  exact s1_step a d Hs ((hAG_unfold _ _ _).1 (Hall d ⟨a, Hs⟩)).1

theorem boundary_local_no_heg : ¬ hEG owned_next cell0 s1 := by
  intro H
  obtain ⟨-, d, ⟨a, Hs⟩, Hd⟩ := (hEG_unfold _ _ _).1 H
  exact s1_step a d Hs ((hEG_unfold _ _ _).1 Hd).1

theorem boundary_admissible : admissible bchild bparent bC hP ctx0 0 :=
  admissible_intro _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    bC_hP_disj trivial ⟨trivial, fun _ => trivial⟩ (by simp [addr_ok, bchild, bC, hsingle])
    ⟨trivial, fun _ => trivial⟩

/-- Hence no release certificate for the child exists. -/
theorem boundary_no_release (I : hprop) (rankC rankP : OwnedCfg → Nat) :
    I b0 → step_closed I → finite_release .parent I rankP → ¬ finite_release .child I rankC := by
  intro HI Hcl HrP HrC
  obtain ⟨HC, -⟩ := global_hag_split I rankC rankP cell0 hTrue b0
    (coupled_init _ _ _ _ _ _ boundary_admissible) (cell_proper .child 1 0)
    (fun _ _ _ => Iff.rfl) HI Hcl HrC HrP boundary_global_hag
  have HC' := (hAG_proper cell0 (cell_proper .child 1 0) _ _
    (project_init_child bchild bparent bC hP ctx0 0)).1 HC
  exact boundary_local_no_hag (hAG_select_strip _ _ _ _ _ _ HC')

/-! ## A guard-only divergent thread has no action -/

def spin : CProg Unit := .untilNone (.ret (some ()))

theorem spin_unfold : denote spin = .guard (denote spin) := by
  conv => lhs; simp only [denote, spin, source_raw_until, source_raw_ret]
  rfl

theorem spin_no_action (a : OwnedAction) (d : OwnedCfg) :
    ¬ owned_step (init_local .child spin managed_empty ctx0 0 true) a d := by
  intro Hs
  rcases Hs with ⟨t, Hh, -⟩ | ⟨k, Hh, -⟩ | ⟨k, Hh, -⟩ | ⟨Hh, -⟩ | ⟨e, k, kind, y, c1, Hh, -⟩ <;>
    obtain ⟨v, Hv⟩ := self_guard_headed_guard _ _ spin_unfold Hh <;>
    simp at Hv

theorem spin_no_hag :
    ¬ hAG owned_next hTrue (init_local .child spin managed_empty ctx0 0 true) := by
  intro H
  obtain ⟨-, ⟨d, a, Hs⟩, -⟩ := (hAG_unfold _ _ _).1 H
  exact spin_no_action a d Hs

-- Not ported: `cell_proper` (redundant with `Separation.cell_proper`).

end Examples.CSL.Frame.Separation.AlwaysRegression
