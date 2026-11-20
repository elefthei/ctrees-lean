/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Separation.Shared
public import Lang.CoCSL.Asep
public import Logic.Sep.AsepCore

/-!
# Finite regression for the CoCSL owned machine

Finite AU/EU splits of a concrete forked program, the canonical raw trace through
`owned_fork_runner`, local versus global emission indices, the read-only context, and rejected
allocation/assignment (← `examples/CSL/Frame/Separation.v`, module `FiniteRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.FiniteRegression
open CTree CTree.Coinduction Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation
open CoCSL

def fchild : CProg Unit :=
  .bind (.read 1) fun v => .bind (.write 1 (v + 1)) fun _ => .emit 1 1
def fparent : CProg Unit :=
  .bind (.read 2) fun v => .bind (.write 2 (v + 1)) fun _ => .emit 0 8
def fk : Unit → CProg Unit := fun _ => fparent
def hC : ManagedHeap := (hsingle 1 0, hemp)
def hP : ManagedHeap := (hsingle 2 7, hemp)
def ctx0 : Ctx := []

theorem denote_write_bind (a v : Nat) (next : Unit → CProg Unit) :
    denote (.bind (.write a v) next) =
      .vis (E := CEff) (.inr (.inr (.inl (.write a v)))) fun u => denote (next u) := by
  rw [denote, source_raw_bind, source_raw_write_head]; rfl

theorem denote_emit (q v : Nat) :
    denote (.emit q v) = .vis (E := CEff) (.inr (.inr (.inr (.inr (q, v))))) fun _ => pure ⟨⟩ :=
  source_raw_emit_head q v _

theorem hC_hP_disj : hC # hP := ⟨hsingle_disj _ _ _ _ (by decide), hdisj_hemp _⟩

theorem fadmissible : admissible fchild (fk ()) hC hP ctx0 0 :=
  admissible_intro _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _) hC_hP_disj
    ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩ ⟨trivial, fun _ => ⟨trivial, fun _ => trivial⟩⟩
    ⟨by simp [addr_ok, hC, hsingle], fun _ => ⟨by simp [addr_ok, hC, hsingle], fun _ => trivial⟩⟩
    ⟨by simp [addr_ok, hP, hsingle], fun _ => ⟨by simp [addr_ok, hP, hsingle], fun _ => trivial⟩⟩

/-! ## Concrete configurations of the finite run -/

def hC' : ManagedHeap := (upd (hsingle 1 0) 1 1, hemp)
def hP' : ManagedHeap := (upd (hsingle 2 7) 2 8, hemp)
def hsd (hc hp : ManagedHeap) : Side → ManagedHeap
  | .child => hc
  | .parent => hp

def mkc {n : Nat} (v : Pool sE Bn n) (g : Vector Side n) (f : Option (Fin n))
    (hc hp : ManagedHeap) (cc cp : Nat) (lc lp : Option (Indexed (Nat × Nat))) : OwnedCfg where
  pool := mk_pool n v g f
  anchor := hsd hC hP
  heap := hsd hc hp
  ctx := ctx0
  base := 0
  count := fun | .child => cc | .parent => cp
  last := fun | .child => lc | .parent => lp

def tC1 : Thread sE Bn := denote (.bind (.write 1 1) fun _ => .emit 1 1)
def tC2 : Thread sE Bn := denote (.emit 1 1)
def tP1 : Thread sE Bn := denote (.bind (.write 2 8) fun _ => .emit 0 8)
def tP2 : Thread sE Bn := denote (.emit 0 8)
def lP : Option (Indexed (Nat × Nat)) := some (stamp (0, 8) 0)
def lC : Option (Indexed (Nat × Nat)) := some (stamp (1, 1) 0)

def s0 : OwnedCfg := init_owned fchild (fk ()) hC hP ctx0 0
def s1 : OwnedCfg := mkc #v[denote fchild, tP1] #v[.child, .parent] (some 1) hC hP 0 0 none none
def s2 : OwnedCfg := mkc #v[denote fchild, tP2] #v[.child, .parent] (some 1) hC hP' 0 0 none none
def s3 : OwnedCfg := mkc #v[denote fchild, pure ⟨⟩] #v[.child, .parent] (some 1) hC hP' 0 1 none lP
def s4 : OwnedCfg := mkc #v[denote fchild] #v[.child] none hC hP' 0 1 none lP
def s5 : OwnedCfg := mkc #v[denote fchild] #v[.child] (some 0) hC hP' 0 1 none lP
def s6 : OwnedCfg := mkc #v[tC1] #v[.child] (some 0) hC hP' 0 1 none lP
def s7 : OwnedCfg := mkc #v[tC2] #v[.child] (some 0) hC' hP' 0 1 none lP
def s8 : OwnedCfg := mkc #v[pure ⟨⟩] #v[.child] (some 0) hC' hP' 1 1 lC lP
def s9 : OwnedCfg := mkc #v[] #v[] none hC' hP' 1 1 lC lP

/-- `s` has exactly one action `a`, to `s'` up to `owned_equ`. -/
def det_act (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) : Prop :=
  (∃ c', owned_step s a c' ∧ owned_equ c' s') ∧
  (∀ b c', owned_step s b c' → b = a ∧ owned_equ c' s')

/-! Generic deterministic heads (replace the Rocq `det_prim`/`det_ret`/`det_select`/`det_yield`
tactics). -/

private theorem det_prim_of {c s' : OwnedCfg} {n : Nat} {v : Pool sE Bn (n + 1)}
    {g : Vector Side (n + 1)} {j : Fin (n + 1)} {e : sE.I} {k0 : sE.O e → Thread sE Bn}
    {kind : OwnedKind} {y : sE.O e} {c1 : OwnedCfg} {i : Side}
    (hp : c.pool = mk_pool (n + 1) v g (some j)) (hg : g[j] = i)
    (hv : v[j] = .vis (E := CEff) (.inr (.inr e)) k0)
    (hs : prim_step g[j] c e = some (kind, y, c1))
    (he : owned_equ (set_pool c1 (mk_pool (n + 1) (v.set j (k0 y)) g (some j))) s') :
    det_act c (act i kind) s' := by
  subst hg
  have hv' : v[j] = guards 0 (.vis (E := CEff) (.inr (.inr e)) k0) := hv
  refine ⟨⟨_, (owned_step_focus c n v g j _ _ hp).2 ((focus_step_head_prim c n v g j e k0 0 _ _
    hv').2 ⟨k0, kind, y, c1, fun _ => rfl, hs, rfl, rfl⟩), he⟩, fun b c' H => ?_⟩
  obtain ⟨k, kind', y', c1', hk, hs', rfl, rfl⟩ :=
    (focus_step_head_prim c n v g j e k0 0 _ _ hv').1 ((owned_step_focus c n v g j _ _ hp).1 H)
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl⟩ := hs'
  rw [funext hk]
  exact ⟨rfl, he⟩

private theorem det_ret_of {c s' : OwnedCfg} {n : Nat} {v : Pool sE Bn (n + 1)}
    {g : Vector Side (n + 1)} {j : Fin (n + 1)} {i : Side}
    (hp : c.pool = mk_pool (n + 1) v g (some j)) (hg : g[j] = i) (hv : v[j] = pure ⟨⟩)
    (he : owned_equ (set_pool c (mk_pool n (vector_remove v j) (vector_remove g j) none)) s') :
    det_act c (act i .ret) s' := by
  subst hg
  have hv' : v[j] = guards 0 (pure ⟨⟩) := hv
  refine ⟨⟨_, (owned_step_focus c n v g j _ _ hp).2
    ((focus_step_head_ret c n v g j 0 _ _ hv').2 ⟨rfl, rfl⟩), he⟩, fun b c' H => ?_⟩
  obtain ⟨rfl, rfl⟩ :=
    (focus_step_head_ret c n v g j 0 _ _ hv').1 ((owned_step_focus c n v g j _ _ hp).1 H)
  exact ⟨rfl, he⟩

private theorem det_yield_of {c s' : OwnedCfg} {n : Nat} {v : Pool sE Bn (n + 1)}
    {g : Vector Side (n + 1)} {j : Fin (n + 1)} {k0 : PUnit → Thread sE Bn} {i : Side}
    (hp : c.pool = mk_pool (n + 1) v g (some j)) (hg : g[j] = i)
    (hv : v[j] = .vis (E := CEff) (.inl ⟨⟩) k0)
    (he : owned_equ (set_pool c (mk_pool (n + 1) (v.set j (k0 ⟨⟩)) g none)) s') :
    det_act c (act i .yield) s' := by
  subst hg
  have hv' : v[j] = guards 0 (.vis (E := CEff) (.inl ⟨⟩) k0) := hv
  refine ⟨⟨_, (owned_step_focus c n v g j _ _ hp).2
    ((focus_step_head_yield c n v g j k0 0 _ _ hv').2 ⟨k0, fun _ => rfl, rfl, rfl⟩), he⟩,
    fun b c' H => ?_⟩
  obtain ⟨k, hk, rfl, rfl⟩ :=
    (focus_step_head_yield c n v g j k0 0 _ _ hv').1 ((owned_step_focus c n v g j _ _ hp).1 H)
  rw [funext hk]
  exact ⟨rfl, he⟩

private theorem det_select_of {c s' : OwnedCfg} {v : Pool sE Bn 1} {g : Vector Side 1}
    {i : Side} (hp : c.pool = mk_pool 1 v g none) (hg : g[0] = i)
    (he : owned_equ (set_pool c (mk_pool 1 v g (some 0))) s') :
    det_act c (act i .select) s' := by
  subst hg
  refine ⟨⟨_, (owned_step_sel c 0 v g _ _ hp).2 ⟨0, rfl, rfl⟩, he⟩, fun b c' H => ?_⟩
  obtain ⟨j, rfl, rfl⟩ := (owned_step_sel c 0 v g _ _ hp).1 H
  obtain rfl := fin1_eq j
  exact ⟨rfl, he⟩

/-- Field-wise `owned_equ` of concrete configurations (Rocq `oequ`). -/
local macro "oequ" : tactic => `(tactic|
  (refine ⟨(tp_equ_mk _ _ _ _ _ _ _).2 ⟨fun j => ?_, ?_, rfl⟩, fun i => ?_, fun i => ?_, rfl, rfl,
      fun i => ?_, fun i => ?_⟩
   all_goals first
     | rfl
     | (cases i <;> first | rfl | exact peq_refl _)
     | (match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl)
     | (obtain ⟨_ | _, _⟩ := j
        · simp [vector_remove]
        · omega)
     | (ext k hk; obtain _ | _ := k
        · simp [vector_remove]
        · omega)))

theorem det01 : det_act s0 (act .parent .read) s1 :=
  det_prim_of (j := 1) (e := .inl (.read 2)) (y := (7 : Nat)) (by rfl) rfl
    (by exact denote_read_bind 2 _)
    (by rfl) (by oequ)
theorem det12 : det_act s1 (act .parent .write) s2 :=
  det_prim_of (j := 1) (e := .inl (.write 2 8)) (y := ⟨⟩) (by rfl) rfl
    (by exact denote_write_bind 2 8 _) (by rfl) (by oequ)
theorem det23 : det_act s2 (act .parent (.emit (0, 8) 0)) s3 :=
  det_prim_of (j := 1) (e := .inr (.inr (0, 8))) (y := ⟨⟩) (by rfl) rfl (by exact denote_emit 0 8)
    (by rfl) (by oequ)
theorem det34 : det_act s3 (act .parent .ret) s4 :=
  det_ret_of (j := 1) (by rfl) rfl (by rfl) (by oequ)
theorem det45 : det_act s4 (act .child .select) s5 :=
  det_select_of (by rfl) rfl (by oequ)
theorem det56 : det_act s5 (act .child .read) s6 :=
  det_prim_of (j := 0) (e := .inl (.read 1)) (y := (0 : Nat)) (by rfl) rfl
    (by exact denote_read_bind 1 _)
    (by rfl) (by oequ)
theorem det67 : det_act s6 (act .child .write) s7 :=
  det_prim_of (j := 0) (e := .inl (.write 1 1)) (y := ⟨⟩) (by rfl) rfl
    (by exact denote_write_bind 1 1 _) (by rfl) (by oequ)
theorem det78 : det_act s7 (act .child (.emit (1, 1) 1)) s8 :=
  det_prim_of (j := 0) (e := .inr (.inr (1, 1))) (y := ⟨⟩) (by rfl) rfl (by exact denote_emit 1 1)
    (by rfl) (by oequ)
theorem det89 : det_act s8 (act .child .ret) s9 :=
  det_ret_of (j := 0) (by rfl) rfl (by rfl) (by oequ)

/-! ## Generic consequences of a deterministic action -/

theorem det_wf (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) :
    det_act s a s' → owned_wf s → owned_wf s' :=
  fun ⟨⟨_, Hs, He⟩, _⟩ W => owned_wf_equ _ _ He (owned_step_wf _ _ _ W Hs)

theorem det_hAU (P Q : hprop) (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) :
    hproper P → hproper Q → det_act s a s' → P s →
    hAU owned_next P Q s' → hAU owned_next P Q s := by
  intro HP HQ ⟨⟨c0, Hs0, _⟩, Hall⟩ Ps H
  refine hAU_step _ _ _ _ Ps ⟨c0, a, Hs0⟩ fun c' ⟨b, Hb⟩ => ?_
  exact (hAU_proper P Q HP HQ c' s' (Hall _ _ Hb).2).2 H

theorem det_hEU (P Q : hprop) (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) :
    hproper P → hproper Q → det_act s a s' → P s →
    hEU owned_next P Q s' → hEU owned_next P Q s := by
  intro HP HQ ⟨⟨c0, Hs0, He⟩, _⟩ Ps H
  exact hEU_step _ _ _ s c0 Ps ⟨a, Hs0⟩ ((hEU_proper P Q HP HQ c0 s' He).2 H)

/-! ## Heap-view assertions -/

def inv_C : hprop := hor (cell .child 1 0) (cell .child 1 1)
def inv_P : hprop := hor (cell .parent 2 7) (cell .parent 2 8)
def done_C : hprop := hDone (cell .child 1 1)
def done_P : hprop := hDone (cell .parent 2 8)

theorem view_hor (P Q : hprop) : view_pred P → view_pred Q → view_pred (hor P Q) :=
  fun HP HQ c d E H => H.imp (HP c d E) (HQ c d E)

theorem view_hDone (P : hprop) : view_pred P → view_pred (hDone P) :=
  fun HP c d E ⟨T, H⟩ => ⟨E.2.2.2.2.2.1 T, HP c d E H⟩

theorem view_inv_C : view_pred inv_C := view_hor _ _ (cell_view _ _ _) (cell_view _ _ _)
theorem view_inv_P : view_pred inv_P := view_hor _ _ (cell_view _ _ _) (cell_view _ _ _)
theorem view_done_C : view_pred done_C := view_hDone _ (cell_view _ _ _)
theorem view_done_P : view_pred done_P := view_hDone _ (cell_view _ _ _)
theorem view_cell_C0 : view_pred (cell .child 1 0) := cell_view _ _ _

theorem proper_sep_inv : hproper (state_sat fun c =>
    asep (state_obligation .child inv_C c) (state_obligation .parent inv_P c)) :=
  state_split_proper _ _ (view_pred_proper _ view_inv_C) (view_pred_proper _ view_inv_P)
theorem proper_sep_done : hproper (state_sat fun c =>
    asep (state_obligation .child done_C c) (state_obligation .parent done_P c)) :=
  state_split_proper _ _ (view_pred_proper _ view_done_C) (view_pred_proper _ view_done_P)
theorem proper_sep_zero : hproper (state_sat fun c =>
    asep (state_obligation .child (cell .child 1 0) c) (state_obligation .parent done_P c)) :=
  state_split_proper _ _ (view_pred_proper _ (cell_view _ _ _)) (view_pred_proper _ view_done_P)

/-! ## Ownership along the run -/

theorem wf0 : owned_wf s0 :=
  init_owned_wf _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _) hC_hP_disj
theorem wf1 : owned_wf s1 := det_wf _ _ _ det01 wf0
theorem wf2 : owned_wf s2 := det_wf _ _ _ det12 wf1
theorem wf3 : owned_wf s3 := det_wf _ _ _ det23 wf2
theorem wf4 : owned_wf s4 := det_wf _ _ _ det34 wf3
theorem wf5 : owned_wf s5 := det_wf _ _ _ det45 wf4
theorem wf6 : owned_wf s6 := det_wf _ _ _ det56 wf5
theorem wf7 : owned_wf s7 := det_wf _ _ _ det67 wf6
theorem wf8 : owned_wf s8 := det_wf _ _ _ det78 wf7
theorem wf9 : owned_wf s9 := det_wf _ _ _ det89 wf8

/-- Rocq `sep_tac`: a split state assertion from well-formedness and both concrete views. -/
local macro "sep_tac " W:term : tactic => `(tactic|
  (refine (state_split_iff _ _ _).2 ⟨$W, ?_, ?_⟩ <;>
   first | exact .inl rfl | exact .inr rfl | exact ⟨rfl, rfl⟩ | rfl))

/-! ## Global AU and EU, and their splits -/

theorem fglobal_hau : hAU owned_next
    (state_sat fun c => asep (state_obligation .child inv_C c) (state_obligation .parent inv_P c))
    (state_sat fun c =>
      asep (state_obligation .child done_C c) (state_obligation .parent done_P c)) s0 := by
  have HP := proper_sep_inv; have HQ := proper_sep_done
  refine det_hAU _ _ _ _ _ HP HQ det01 (by sep_tac wf0) ?_
  refine det_hAU _ _ _ _ _ HP HQ det12 (by sep_tac wf1) ?_
  refine det_hAU _ _ _ _ _ HP HQ det23 (by sep_tac wf2) ?_
  refine det_hAU _ _ _ _ _ HP HQ det34 (by sep_tac wf3) ?_
  refine det_hAU _ _ _ _ _ HP HQ det45 (by sep_tac wf4) ?_
  refine det_hAU _ _ _ _ _ HP HQ det56 (by sep_tac wf5) ?_
  refine det_hAU _ _ _ _ _ HP HQ det67 (by sep_tac wf6) ?_
  refine det_hAU _ _ _ _ _ HP HQ det78 (by sep_tac wf7) ?_
  refine det_hAU _ _ _ _ _ HP HQ det89 (by sep_tac wf8) ?_
  exact hAU_now _ _ _ _ (by sep_tac wf9)

/-- Child done with cell 1 = 1, parent done with cell 2 = 8. -/
theorem fork_hau_finite :
    hAU owned_next inv_C done_C (init_local .child fchild hC ctx0 0 false) ∧
    hAU owned_next inv_P done_P (init_local .parent fparent hP ctx0 0 true) :=
  fork_hau_split fchild fk hC hP ctx0 0 _ _ _ _ fadmissible (view_pred_proper _ view_inv_C)
    (view_pred_proper _ view_inv_P) (view_pred_proper _ view_done_C)
    (view_pred_proper _ view_done_P) fglobal_hau

theorem fork_hau_finite_view :
    hAU owned_next inv_C done_C (init_local .child fchild hC ctx0 0 true) ∧
    hAU owned_next inv_P done_P (init_local .parent fparent hP ctx0 0 true) :=
  fork_hau_split_view fchild fk hC hP ctx0 0 _ _ _ _ fadmissible view_inv_C view_inv_P
    view_done_C view_done_P fglobal_hau

theorem fglobal_heu : hEU owned_next
    (state_sat fun c => asep (state_obligation .child inv_C c) (state_obligation .parent inv_P c))
    (state_sat fun c =>
      asep (state_obligation .child done_C c) (state_obligation .parent done_P c)) s0 := by
  have HP := proper_sep_inv; have HQ := proper_sep_done
  refine det_hEU _ _ _ _ _ HP HQ det01 (by sep_tac wf0) ?_
  refine det_hEU _ _ _ _ _ HP HQ det12 (by sep_tac wf1) ?_
  refine det_hEU _ _ _ _ _ HP HQ det23 (by sep_tac wf2) ?_
  refine det_hEU _ _ _ _ _ HP HQ det34 (by sep_tac wf3) ?_
  refine det_hEU _ _ _ _ _ HP HQ det45 (by sep_tac wf4) ?_
  refine det_hEU _ _ _ _ _ HP HQ det56 (by sep_tac wf5) ?_
  refine det_hEU _ _ _ _ _ HP HQ det67 (by sep_tac wf6) ?_
  refine det_hEU _ _ _ _ _ HP HQ det78 (by sep_tac wf7) ?_
  refine det_hEU _ _ _ _ _ HP HQ det89 (by sep_tac wf8) ?_
  exact hEU_now _ _ _ _ (by sep_tac wf9)

theorem fork_heu_finite :
    hEU owned_next inv_C done_C (init_local .child fchild hC ctx0 0 false) ∧
    hEU owned_next inv_P done_P (init_local .parent fparent hP ctx0 0 true) :=
  fork_heu_split fchild fk hC hP ctx0 0 _ _ _ _ fadmissible (view_pred_proper _ view_inv_C)
    (view_pred_proper _ view_inv_P) (view_pred_proper _ view_done_C)
    (view_pred_proper _ view_done_P) fglobal_heu

/-- Zero own steps: the global witness ends at `s4`, before any child action, where the child's
endpoint already holds at its unchanged projection. -/
theorem fglobal_heu_zero : hEU owned_next
    (state_sat fun c => asep (state_obligation .child inv_C c) (state_obligation .parent inv_P c))
    (state_sat fun c => asep (state_obligation .child (cell .child 1 0) c)
      (state_obligation .parent done_P c)) s0 := by
  have HP := proper_sep_inv; have HQ := proper_sep_zero
  refine det_hEU _ _ _ _ _ HP HQ det01 (by sep_tac wf0) ?_
  refine det_hEU _ _ _ _ _ HP HQ det12 (by sep_tac wf1) ?_
  refine det_hEU _ _ _ _ _ HP HQ det23 (by sep_tac wf2) ?_
  refine det_hEU _ _ _ _ _ HP HQ det34 (by sep_tac wf3) ?_
  exact hEU_now _ _ _ _ (by sep_tac wf4)

theorem fork_heu_zero :
    hEU owned_next inv_C (cell .child 1 0) (init_local .child fchild hC ctx0 0 false) ∧
    hEU owned_next inv_P done_P (init_local .parent fparent hP ctx0 0 true) :=
  fork_heu_split fchild fk hC hP ctx0 0 _ _ _ _ fadmissible (view_pred_proper _ view_inv_C)
    (view_pred_proper _ view_inv_P) (view_pred_proper _ (cell_view _ _ _))
    (view_pred_proper _ view_done_P) fglobal_heu_zero

/-- All five projections of `s0..s4` onto `child` coincide: the four global steps of the zero
witness are foreign. -/
theorem zero_child_projection :
    owned_equ (project .child s4) (project .child s0) ∧
    cell .child 1 0 (init_local .child fchild hC ctx0 0 false) :=
  ⟨by oequ, rfl⟩

/-! ## Canonical trace of the original runner -/

def sfinal : SSig := ((hunion (hsingle 1 1) (hsingle 2 8), hemp), (ctx0, 2))

/-- Parent write snapshot and stamp `(0,8)@0`, one scheduler selection, child write snapshot and
stamp `(1,1)@1`, then counter 2. -/
def ftrace : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig) :=
  .vis (E := writerE _) (CSLObs.heap (hC ⊎ hP')) fun _ =>
  .vis (E := writerE _) (CSLObs.emit (stamp (0, 8) 0)) fun _ =>
  CTree.brSn 1 fun _ =>
  .vis (E := writerE _) (CSLObs.heap (hC' ⊎ hP')) fun _ =>
  .vis (E := writerE _) (CSLObs.emit (stamp (1, 1) 1)) fun _ =>
  pure (⟨⟩, sfinal)

/-- The interpreter's administrative guards are not scheduler steps. -/
private theorem finite_det_runner (s : OwnedCfg) (a : OwnedAction) (s' : OwnedCfg) :
    erasable s → det_act s a s' →
    erasable s' ∧ ((∀ h, erase_action_label a h = none) → owned_interp s ~ owned_interp s') := by
  rintro H ⟨⟨d, Hs, E⟩, _⟩
  refine ⟨erasable_equ d s' E (erasable_step s a d H Hs), fun Hl => ?_⟩
  exact sbisim_trans ((owned_interp_action s a d H Hs).1 (Hl _)) (owned_interp_equ _ _ E)

private theorem finite_log_runner (c : OwnedCfg) (n : Nat) (v : Pool sE Bn (n + 1))
    (g : Vector Side (n + 1)) (j : Fin (n + 1)) (e : sE.I) (k : sE.O e → Thread sE Bn)
    (kind : OwnedKind) (y : sE.O e) (d out : OwnedCfg) (o : CSLObs (Nat × Nat))
    (Hpool : c.pool = mk_pool (n + 1) v g (some j))
    (Hnode : v[j] = .vis (E := CEff) (.inr (.inr e)) k)
    (Hwf : owned_wf c) (Hok : component_event_ok e) (Haddr : prim_addr_ok (c.anchor g[j]) e)
    (Hp : prim_step g[j] c e = some (kind, y, d))
    (Hout : owned_equ (set_pool d (mk_pool (n + 1) (v.set j (k y)) g (some j))) out)
    (Hlog : action_logs (act g[j] kind) (joined_heap d) = [o]) :
    owned_interp c ~ .vis (E := writerE (CSLObs (Nat × Nat))) o fun _ => owned_interp out := by
  have Hr := prim_reflect_joined g[j] c e Hwf Hok Haddr
  simp only [Hp] at Hr
  rw [owned_interp_pool c Hpool]
  refine sbisim_trans (interp_schedule_nd_user sh n v j e k _ (by rw [Hnode, unfold_vis])) ?_
  rw [Hr, Hlog, emit_list_cons, emit_list_nil, vis_bind]
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, rfl⟩
  rw [pure_bind']
  exact owned_interp_equ (set_pool d (mk_pool (n + 1) (v.set j (k y)) g (some j))) out Hout

private theorem finite_trace_runner (t u v : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) :
    t ~ u → sbisim (simL event_eq owned_result_rel) u v →
    sbisim (simL event_eq owned_result_rel) t v :=
  fun Htu Huv => sbisim_clos_sb (gfp_chain _) t u v v Htu Huv (sbisim_refl v)

/-- Branch-by-branch heterogeneous bisimulation of two `brSn` nodes. -/
private theorem sbisim_brSn {L : Label (writerE (CSLObs (Nat × Nat))) →
      Label (writerE (CSLObs (Nat × Nat))) → Prop} {m : Nat}
    {k k' : Fin m → ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)} (hL : L .tau .tau)
    (h : ∀ j, sbisim L (k j) (k' j)) : sbisim L (CTree.brSn m k) (CTree.brSn m k') :=
  sbisim_br_id _ _ _ fun _ => sbisim_step hL (h _)

private theorem simL_log (o : CSLObs (Nat × Nat)) (x : PUnit) :
    simL (X := PUnit × SSig) event_eq owned_result_rel
      (.obs (E := writerE (CSLObs (Nat × Nat))) o x) (.obs o x) :=
  .obs _ _ _ _ rfl HEq.rfl

theorem ferase : sbisim (simL event_eq owned_result_rel) (owned_interp s0) ftrace := by
  have H0 := admissible_erasable _ _ _ _ _ _ fadmissible
  obtain ⟨H1, E01⟩ := finite_det_runner _ _ _ H0 det01
  obtain ⟨H2, -⟩ := finite_det_runner _ _ _ H1 det12
  obtain ⟨H3, -⟩ := finite_det_runner _ _ _ H2 det23
  obtain ⟨H4, E34⟩ := finite_det_runner _ _ _ H3 det34
  obtain ⟨H5, -⟩ := finite_det_runner _ _ _ H4 det45
  obtain ⟨H6, E56⟩ := finite_det_runner _ _ _ H5 det56
  obtain ⟨H7, -⟩ := finite_det_runner _ _ _ H6 det67
  obtain ⟨H8, -⟩ := finite_det_runner _ _ _ H7 det78
  obtain ⟨H9, E89⟩ := finite_det_runner _ _ _ H8 det89
  have E12 : owned_interp s1 ~ .vis (E := writerE (CSLObs (Nat × Nat)))
      (CSLObs.heap (hC ⊎ hP')) fun _ => owned_interp s2 :=
    finite_log_runner s1 1 _ _ 1 (.inl (.write 2 8)) (fun _ => tP2) .write ⟨⟩ _ s2 _ rfl
      (denote_write_bind 2 8 _) wf1 trivial nofun rfl (by oequ) rfl
  have E23 : owned_interp s2 ~ .vis (E := writerE (CSLObs (Nat × Nat)))
      (CSLObs.emit (stamp (0, 8) 0)) fun _ => owned_interp s3 :=
    finite_log_runner s2 1 _ _ 1 (.inr (.inr (0, 8))) (fun _ => pure ⟨⟩) (.emit (0, 8) 0) ⟨⟩ _ s3
      _ rfl (denote_emit 0 8) wf2 trivial trivial rfl (by oequ) rfl
  have E67 : owned_interp s6 ~ .vis (E := writerE (CSLObs (Nat × Nat)))
      (CSLObs.heap (hC' ⊎ hP')) fun _ => owned_interp s7 :=
    finite_log_runner s6 0 _ _ 0 (.inl (.write 1 1)) (fun _ => tC2) .write ⟨⟩ _ s7 _ rfl
      (denote_write_bind 1 1 _) wf6 trivial nofun rfl (by oequ) rfl
  have E78 : owned_interp s7 ~ .vis (E := writerE (CSLObs (Nat × Nat)))
      (CSLObs.emit (stamp (1, 1) 1)) fun _ => owned_interp s8 :=
    finite_log_runner s7 0 _ _ 0 (.inr (.inr (1, 1))) (fun _ => pure ⟨⟩) (.emit (1, 1) 1) ⟨⟩ _ s8
      _ rfl (denote_emit 1 1) wf7 trivial trivial rfl (by oequ) rfl
  refine finite_trace_runner _ _ _ (sbisim_trans (E01 fun _ => rfl) E12) ?_
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, simL_log _ _⟩
  refine finite_trace_runner _ _ _ E23 ?_
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, simL_log _ _⟩
  refine finite_trace_runner _ _ _
    (sbisim_trans (E34 fun _ => rfl) (owned_interp_select s4 0 #v[denote fchild] #v[.child])) ?_
  refine sbisim_brSn .tau fun j => ?_
  obtain rfl := fin1_eq j
  refine finite_trace_runner _ _ _ (sbisim_trans (E56 fun _ => rfl) E67) ?_
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, simL_log _ _⟩
  refine finite_trace_runner _ _ _ E78 ?_
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, simL_log _ _⟩
  refine finite_trace_runner _ _ _
    (sbisim_trans (E89 fun _ => rfl) (owned_interp_terminal s9 H9 rfl)) ?_
  refine sbisim_ret (.val _ _ ⟨rfl, rfl, fun a => ?_, fun _ => rfl⟩)
  show hunion (upd (hsingle 1 0) 1 1) (upd (hsingle 2 7) 2 8) a =
    hunion (hsingle 1 1) (hsingle 2 8) a
  rcases a with _ | _ | _ | a <;> simp [hunion, upd, hsingle]

/-- The original runner, through `owned_fork_runner`, has the same trace. -/
theorem fork_run_nd_trace :
    sbisim (simL event_eq owned_result_rel)
      (run_nd (.bind (.fork fchild) fk) (hC ⊎ hP, (ctx0, 0))) ftrace :=
  finite_trace_runner _ _ _ (sbisim_symm (owned_fork_runner fchild fk hC hP ctx0 0)) ferase

/-! ## Observation projection

Both lineages' first emissions carry local index 0 in their projections; globally the child's is
index 1, reconstructed from both counts. -/

/-- A projected pool given by its slot list and focus. -/
private theorem proj_pool_eq (i : Side) (p : TaggedPool) {n : Nat} (v : Pool sE Bn n)
    (g : Vector Side n) (f : Option (Fin n)) (hs : proj_slots i p = v.toList.zip g.toList)
    (hf : focus_nat (project_pool i p) = f.map fin_nat) : (project_pool i p) = mk_pool n v g f :=
  tp_equ_eq ⟨by rw [Forall2_slot_iff, tp_slots_project, hs]; rfl, hf⟩

/-- `owned_equ` against a configuration whose pool is known (the pool part of `oequ`). -/
private theorem owned_equ_pool {c d : OwnedCfg} {n : Nat} {v w : Pool sE Bn n}
    {g : Vector Side n} {f : Option (Fin n)} (hc : c.pool = mk_pool n v g f)
    (hd : d.pool = mk_pool n w g f) (hv : ∀ j : Fin n, v[j] = w[j])
    (he : (∀ i, c.anchor i ≈ d.anchor i) ∧ (∀ i, c.heap i ≈ d.heap i) ∧ c.ctx = d.ctx ∧
      c.base = d.base ∧ (∀ i, c.count i = d.count i) ∧ (∀ i, c.last i = d.last i)) :
    owned_equ c d :=
  ⟨by rw [hc, hd]; exact (tp_equ_mk _ _ _ _ _ _ _).2 ⟨hv, rfl, rfl⟩, he⟩

local macro "rest_equ" : tactic => `(tactic|
  (refine ⟨fun i => ?_, fun i => ?_, rfl, rfl, fun i => ?_, fun i => ?_⟩ <;>
   cases i <;> first | rfl | exact peq_refl _))

theorem emit_local_parent :
    det_act (project .parent s2) (act .parent (.emit (0, 8) 0)) (project .parent s3) ∧
    project_action .parent s2 (act .parent (.emit (0, 8) 0)) = act .parent (.emit (0, 8) 0) := by
  have hp2 : (project .parent s2).pool = mk_pool 1 #v[tP2] #v[.parent] (some 0) :=
    proj_pool_eq _ _ _ _ _ (by rfl) (by rfl)
  have hp3 : (project .parent s3).pool = mk_pool 1 #v[pure ⟨⟩] #v[.parent] (some 0) :=
    proj_pool_eq _ _ _ _ _ (by rfl) (by rfl)
  refine ⟨det_prim_of (j := 0) (e := .inr (.inr (0, 8))) (y := ⟨⟩) hp2 rfl (denote_emit 0 8)
    (by rfl) (owned_equ_pool rfl hp3 (fun j => by obtain rfl := fin1_eq j; rfl) ?_), rfl⟩
  rest_equ

theorem emit_local_child :
    det_act (project .child s7) (act .child (.emit (1, 1) 0)) (project .child s8) ∧
    project_action .child s7 (act .child (.emit (1, 1) 1)) = act .child (.emit (1, 1) 0) := by
  have hp7 : (project .child s7).pool = mk_pool 1 #v[tC2] #v[.child] (some 0) :=
    proj_pool_eq _ _ _ _ _ (by rfl) (by rfl)
  have hp8 : (project .child s8).pool = mk_pool 1 #v[pure ⟨⟩] #v[.child] (some 0) :=
    proj_pool_eq _ _ _ _ _ (by rfl) (by rfl)
  refine ⟨det_prim_of (j := 0) (e := .inr (.inr (1, 1))) (y := ⟨⟩) hp7 rfl (denote_emit 1 1)
    (by rfl) (owned_equ_pool rfl hp8 (fun j => by obtain rfl := fin1_eq j; rfl) ?_), rfl⟩
  rest_equ

theorem emit_counters :
    global_count s2 = s2.base + s2.count .child + s2.count .parent ∧ global_count s2 = 0 ∧
    global_count s7 = s7.base + s7.count .child + s7.count .parent ∧ global_count s7 = 1 ∧
    s9.last .child = some (stamp (1, 1) 0) ∧ s9.last .parent = some (stamp (0, 8) 0) ∧
    local_state .child s9 = (hC', (ctx0, 1)) ∧ local_state .parent s9 = (hP', (ctx0, 1)) ∧
    (joined_state s9).2 = (ctx0, 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The parent's emission leaves the child's projection, and in particular its last
observation, unchanged. -/
theorem foreign_emit_child (b : OwnedAction) (c' : OwnedCfg) :
    owned_step s2 b c' →
    b.owner = .parent ∧ owned_equ (project .child c') (project .child s2) ∧
    (project .child c').last .child = none := by
  intro H
  obtain ⟨rfl, E⟩ := det23.2 _ _ H
  obtain rfl := owned_equ_eq E
  exact ⟨rfl, by oequ, rfl⟩

/-! ## Read-only context -/

def ctxx : Ctx := [("x", 3)]
def pe : CProg Unit := .bind (.eval (.var "x")) fun _ => .ret ()

theorem denote_var_bind (name : String) (next : Nat → CProg Unit) :
    denote (.bind (.eval (.var name)) next) =
      .vis (E := CEff) (.inr (.inr (.inr (.inl .get)))) fun ctx =>
        match Ctx.lookup name ctx with
        | some v => .vis (E := CEff) (.inl ⟨⟩) fun _ => denote (next v)
        | none => .stuck := by
  rw [denote, source_raw_bind, source_raw_eval, source_raw_var, raw_source_get_head]; rfl

def mkl (ctx : Ctx) {n : Nat} (v : Pool sE Bn n) (g : Vector Side n) (f : Option (Fin n)) :
    OwnedCfg where
  pool := mk_pool n v g f
  anchor := fun _ => managed_empty
  heap := fun _ => managed_empty
  ctx := ctx
  base := 0
  count := fun _ => 0
  last := fun _ => none

def ex0 : OwnedCfg := init_local .child pe managed_empty ctxx 0 true
def ex1 : OwnedCfg :=
  mkl ctxx #v[.vis (E := CEff) (.inl ⟨⟩) fun _ => denote (.ret ())] #v[.child] (some 0)
def ex2 : OwnedCfg := mkl ctxx #v[denote (.ret ())] #v[.child] none

/-- `CVar` reads the context once, then yields; the context never changes. -/
theorem var_get : det_act ex0 (act .child .get) ex1 :=
  det_prim_of (j := 0) (e := .inr (.inl .get)) (y := (ctxx : Ctx)) (by rfl) rfl
    (by exact denote_var_bind "x" _) (by rfl) (by oequ)
theorem var_yield : det_act ex1 (act .child .yield) ex2 :=
  det_yield_of (j := 0) (by rfl) rfl (by rfl) (by oequ)
theorem var_ctx : ex1.ctx = ctxx ∧ ex2.ctx = ctxx ∧ ex2.pool.focus = none := ⟨rfl, rfl, rfl⟩

private theorem denote_pe :
    denote pe = (denote_exp (.var "x") >>= fun _ => denote (.ret ())) := by
  rw [pe, denote, source_raw_bind, source_raw_eval]; rfl

/-- The original runner performs the same read-then-yield. -/
theorem var_run_nd :
    run_nd pe (managed_empty, (ctxx, 0)) ~
      interp_schedule_nd sh 1 #v[denote (.ret ())] none (managed_empty, (ctxx, 0)) := by
  rw [run_nd_unfold, denote_pe]
  exact interp_nd_var 0 #v[denote (.ret ())] 0 "x" 3 (fun _ => denote (.ret ())) _ rfl

/-! A missing variable is stuck after the read, in both semantics. -/

def exm0 : OwnedCfg := init_local .child pe managed_empty ctx0 0 true
def exm1 : OwnedCfg := mkl ctx0 #v[.stuck] #v[.child] (some 0)

theorem var_missing_get : det_act exm0 (act .child .get) exm1 :=
  det_prim_of (j := 0) (e := .inr (.inl .get)) (y := (ctx0 : Ctx)) (by rfl) rfl
    (by exact denote_var_bind "x" _) (by rfl) (by oequ)

theorem var_missing_stuck (a : OwnedAction) (c' : OwnedCfg) : ¬ owned_step exm1 a c' :=
  fun H => focus_step_head_stuck exm1 0 #v[.stuck] #v[.child] 0 0 a c' rfl
    ((owned_step_focus exm1 0 _ _ 0 a c' rfl).1 H)

theorem var_missing_run_nd :
    run_nd pe (managed_empty, (ctx0, 0)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  rw [run_nd_unfold, denote_pe]
  exact interp_nd_var_missing 0 #v[denote (.ret ())] 0 "x" _ _ rfl

/-! The continuation observes the value returned by `Get`, not just its clock. -/

def pe_value : CProg Unit := .bind (.eval (.var "x")) fun v => .emit 9 v
def exv0 : OwnedCfg := init_local .child pe_value managed_empty ctxx 0 true
def exv1 : OwnedCfg :=
  mkl ctxx #v[.vis (E := CEff) (.inl ⟨⟩) fun _ => denote (.emit 9 3)] #v[.child] (some 0)
def exv2 : OwnedCfg := mkl ctxx #v[denote (.emit 9 3)] #v[.child] none
def exv3 : OwnedCfg := mkl ctxx #v[denote (.emit 9 3)] #v[.child] (some 0)
def exv4 : OwnedCfg :=
  set_pool (emit_cfg exv3 .child (9, 3)) (mk_pool 1 #v[pure ⟨⟩] #v[.child] (some 0))

theorem var_value_get : det_act exv0 (act .child .get) exv1 :=
  det_prim_of (j := 0) (e := .inr (.inl .get)) (y := (ctxx : Ctx)) (by rfl) rfl
    (by exact denote_var_bind "x" _) (by rfl) (by oequ)
theorem var_value_yield : det_act exv1 (act .child .yield) exv2 :=
  det_yield_of (j := 0) (by rfl) rfl (by rfl) (by oequ)
theorem var_value_select : det_act exv2 (act .child .select) exv3 :=
  det_select_of (by rfl) rfl (by oequ)
theorem var_value_emit : det_act exv3 (act .child (.emit (9, 3) 0)) exv4 :=
  det_prim_of (j := 0) (e := .inr (.inr (9, 3))) (y := ⟨⟩) (by rfl) rfl
    (by exact denote_emit 9 3) (by rfl) (by oequ)

theorem var_value_state :
    exv0.ctx = ctxx ∧ exv1.ctx = ctxx ∧ exv2.ctx = ctxx ∧ exv3.ctx = ctxx ∧ exv4.ctx = ctxx ∧
    global_count exv3 = 0 ∧ exv4.count .child = 1 ∧
    exv4.last .child = some (stamp (9, 3) 0) ∧
    local_state .child exv4 = (managed_empty, (ctxx, 1)) ∧
    (joined_state exv4).2 = (ctxx, 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem denote_pe_value :
    denote pe_value = (denote_exp (.var "x") >>= fun v => denote (.emit 9 v)) := by
  rw [pe_value, denote, source_raw_bind, source_raw_eval]; rfl

theorem var_value_run_nd_yield :
    run_nd pe_value (managed_empty, (ctxx, 0)) ~
      interp_schedule_nd sh 1 #v[denote (.emit 9 3)] none (managed_empty, (ctxx, 0)) := by
  rw [run_nd_unfold, denote_pe_value]
  exact interp_nd_var 0 #v[denote (.emit 9 3)] 0 "x" 3 (fun v => denote (.emit 9 v)) _ rfl

/-- Exactly one scheduler selection occurs after the implicit yield, before `(9,3)@0`; the
context is retained and only the counter advances. -/
theorem var_value_run_nd_trace :
    run_nd pe_value (managed_empty, (ctxx, 0)) ~
      (CTree.brSn 1 fun _ =>
        .vis (E := writerE (CSLObs (Nat × Nat))) (CSLObs.emit (stamp (9, 3) 0)) fun _ =>
          pure (⟨⟩, (managed_empty, (ctxx, 1))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  refine sbisim_trans var_value_run_nd_yield
    (sbisim_trans (interp_schedule_nd_select sh 0 _ _) (sbisim_brSn rfl fun j => ?_))
  obtain rfl := fin1_eq j
  refine sbisim_trans (interp_nd_source_emit_log 0 #v[denote (.emit 9 3)] 0 9 3
    (fun _ => pure ⟨⟩) managed_empty ctxx 0) ?_
  simp only [log, vis_bind, pure_bind']
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, rfl⟩
  exact sbisim_trans (interp_schedule_nd_ret sh 0 _ 0 _ (by simp))
    (interp_schedule_nd_empty sh _ _)

def exvm0 : OwnedCfg := init_local .child pe_value managed_empty ctx0 0 true

theorem var_value_missing_get : det_act exvm0 (act .child .get) exm1 :=
  det_prim_of (j := 0) (e := .inr (.inl .get)) (y := (ctx0 : Ctx)) (by rfl) rfl
    (by exact denote_var_bind "x" _) (by rfl) (by oequ)

/-- After the only `Get`, no action (in particular no emission) is possible. -/
theorem var_value_missing_fault (a : OwnedAction) (c' : OwnedCfg) :
    owned_step exvm0 a c' → a.action_kind = .get ∧ ∀ b c'', ¬ owned_step c' b c'' := by
  intro H
  obtain ⟨rfl, E⟩ := var_value_missing_get.2 _ _ H
  obtain rfl := owned_equ_eq E
  exact ⟨rfl, var_missing_stuck⟩

theorem var_value_missing_no_emit (a : OwnedAction) (c' : OwnedCfg) (payload : Nat × Nat)
    (index : Nat) : owned_step exvm0 a c' → a.action_kind ≠ .emit payload index := by
  intro H h
  rw [(var_value_missing_fault _ _ H).1] at h
  cases h

theorem var_value_missing_run_nd :
    run_nd pe_value (managed_empty, (ctx0, 0)) ~
      (.stuck : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  rw [run_nd_unfold, denote_pe_value]
  exact interp_nd_var_missing 0 #v[denote (.emit 9 3)] 0 "x" _ _ rfl

theorem var_value_missing_raw_stuck : isStuck (run_nd pe_value (managed_empty, (ctx0, 0))) :=
  isStuck_sbisim var_value_missing_run_nd stuck_isStuck

/-! ## Allocation and context writes are outside the component fragment -/

theorem assign_rejected : ¬ component_ok (.assign "x" (.lit 1)) := fun H => H.2.2 ctx0

/-- Rejection does not change the original runner's context-write semantics. -/
def assigned_ctx : Ctx := Ctx.add "x" 1 ctx0

theorem assign_run_nd_trace (memory : ManagedHeap) (base : Nat) :
    run_nd (.assign "x" (.lit 1)) (memory, (ctx0, base)) ~
      (.vis (E := writerE (CSLObs (Nat × Nat))) (CSLObs.ctx assigned_ctx)
        (fun _ => pure (⟨⟩, (memory, (assigned_ctx, base)))) :
        ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  rw [run_nd_unfold, denote_assign_lit]
  refine sbisim_trans (interp_nd_get_ctx 0 #v[pure ⟨⟩] 0
    (fun ctx => source_put (Ctx.add "x" 1 ctx) >>= fun _ => pure ⟨⟩) _) ?_
  refine sbisim_trans (interp_nd_put_ctx 0 _ 0 _ (fun _ => pure ⟨⟩) _) ?_
  simp only [log, vis_bind, pure_bind']
  refine sbisim_vis_id _ _ _ fun _ => ⟨?_, rfl⟩
  exact sbisim_trans (interp_schedule_nd_ret sh 0 _ 0 _ (by simp))
    (interp_schedule_nd_empty sh _ _)

theorem assign_result (memory : ManagedHeap) (base : Nat) :
    Ctx.lookup "x" (csl_context (memory, (assigned_ctx, base))) = some 1 ∧
    csl_memory (memory, (assigned_ctx, base)) = memory ∧
    csl_counter (memory, (assigned_ctx, base)) = base :=
  ⟨rfl, rfl, rfl⟩

theorem assign_original_return :
    entails (⊤ AU .ret fun (r : PUnit × SSig) _ =>
        Ctx.lookup "x" (csl_context r.2) = some 1 ∧ csl_memory r.2 = hC ∧ csl_counter r.2 = 0 :
        TiclR (writerE (CSLObs (Nat × Nat))) (PUnit × SSig))
      (run_nd (.assign "x" (.lit 1)) (hC, (ctx0, 0))) .pure :=
  au_csl_nd_assign_lit "x" 1 _ .pure _ _ ⟨trivial, .pure⟩
    (ret_ret (.obs _ _) (assign_result hC 0))

theorem alloc_rejected : ¬ component_ok (.alloc 1) := fun H => H

/-- First fit is absolute: alone, the allocator returns 1; with cell 1 framed in, it returns
2. -/
theorem alloc_isolated :
    heap_handler (F := writerE (CSLObs (Nat × Nat))) (B := Bn) (.alloc 1) (managed_empty, ()) =
      pure ((1 : Nat), (managed_alloc managed_empty 1 1, ())) :=
  heap_handler_alloc_first_guards hemp hemp 1 1 () (by omega) (by omega) (fun _ _ => rfl)
    fun _ h1 h2 => absurd h2 (by omega)

theorem alloc_framed :
    heap_handler (F := writerE (CSLObs (Nat × Nat))) (B := Bn) (.alloc 1) (hC, ()) =
      .guard (pure ((2 : Nat), (managed_alloc hC 2 1, ()))) :=
  heap_handler_alloc_first_guards (hsingle 1 0) hemp 1 2 () (by omega) (by omega)
    (fun o h => by simp [hsingle]; omega)
    fun j J1 J2 F => by
      obtain rfl : j = 1 := by omega
      exact absurd (F 0 (by omega)) (by simp [hsingle])

-- Not ported: Ltacs `slot_tac`, `det_prim`, `det_ret`, `det_select`, `det_yield`, `sep_tac`
-- (replaced by the private lemmas `det_{prim,ret,select,yield}_of` and the local `oequ` macro);
-- the unused `#[local] Instance`s `owned_result_rel_Equivalence`,
-- `simL_result_{Symmetric,Transitive}` (no setoid rewriting is used). `denote_read_bind`
-- (redundant with `CoCSL.denote_read_bind`), `cell_is`, `view_cell` (redundant with
-- `Separation.cell`, `Separation.cell_view`).

end Examples.CSL.Frame.Separation.FiniteRegression
