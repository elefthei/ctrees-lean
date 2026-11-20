/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Frame.Separation.Shared

/-!
# Next: the direct AN split, its clocks, and its boundaries

Concrete forked CoCSL programs over `init_owned`/`project`: the direct AN split, own-clock AX/EX,
its necessary boundaries, and the last-finisher `hRet` disjunction
(← `examples/CSL/Frame/Separation.v`, module `NextRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Separation.NextRegression
open CTree Tisl Tisl.CSL Tisl.Heap Tisl.Ctx Tisl.Pcm Tisl.Yield CoCSL

def ctx0 : Ctx := []
def hC : ManagedHeap := (hsingle 1 0, hemp)
def hP : ManagedHeap := (hsingle 2 7, hemp)
def hC' : ManagedHeap := (upd hC.1 1 1, hC.2)
def hP' : ManagedHeap := (upd hP.1 2 8, hP.2)

def Fnone : hprop := fun c => c.pool.focus = none

theorem Fnone_proper : hproper Fnone := fun _ _ E => by
  obtain rfl := owned_equ_eq E; exact Iff.rfl

/-! Thread heads of the denoted programs. -/

theorem denote_write (a v : Nat) :
    denote (.write a v) =
      guards 0 (.vis (E := CEff) (.inr (.inr (.inl (.write a v)))) fun _ => pure ⟨⟩) :=
  source_raw_write_head a v (fun _ => pure ⟨⟩)

def parentY : CProg Unit := .bind .yield fun _ => .write 2 8

theorem denote_yield_write :
    denote parentY = guards 0 (.vis (E := CEff) (.inl ⟨⟩) fun _ => denote (.write 2 8)) := by
  show denote_flow parentY >>= _ = _
  rw [parentY, source_raw_bind, source_raw_yield_head]; rfl

theorem ret_guards (t : Thread sE Bn) : t = pure ⟨⟩ → t = guards 0 (pure ⟨⟩) := fun H => H

/-! Admission of both forks. -/

theorem hC_hP_disj : hC # hP := ⟨hsingle_disj _ _ _ _ (by decide), hdisj_hemp _⟩

theorem admA : admissible (.write 1 1) ((fun _ : Unit => CProg.write 2 8) ()) hC hP ctx0 0 :=
  admissible_intro _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    hC_hP_disj trivial trivial (by simp [addr_ok, hC, hsingle]) (by simp [addr_ok, hP, hsingle])

theorem admB : admissible (.write 1 1) parentY hC hP ctx0 0 :=
  admissible_intro _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _)
    hC_hP_disj trivial ⟨trivial, fun _ => trivial⟩ (by simp [addr_ok, hC, hsingle])
    (by simp [addr_ok, parentY, hP, hsingle])

/-! ### The run `Parent(write, return); Child(select, write, return)` -/

def dc : Thread sE Bn := denote (.write 1 1)
def dp : Thread sE Bn := denote (.write 2 8)

def A0 : OwnedCfg := init_owned (.write 1 1) (.write 2 8) hC hP ctx0 0
def A1 (t : Thread sE Bn) : OwnedCfg :=
  set_pool (set_heap A0 .parent hP') (mk_pool 2 #v[dc, t] #v[.child, .parent] (some 1))
def A2 : OwnedCfg := set_pool (set_heap A0 .parent hP') (mk_pool 1 #v[dc] #v[.child] none)
def A3 : OwnedCfg := set_pool (set_heap A0 .parent hP') (mk_pool 1 #v[dc] #v[.child] (some 0))
def A4 (t : Thread sE Bn) : OwnedCfg :=
  set_pool (set_heap (set_heap A0 .parent hP') .child hC') (mk_pool 1 #v[t] #v[.child] (some 0))
def A5 : OwnedCfg :=
  set_pool (set_heap (set_heap A0 .parent hP') .child hC') (mk_pool 0 #v[] #v[] none)

theorem stepA0 (a : OwnedAction) (c' : OwnedCfg) :
    owned_step A0 a c' ↔ a = act .parent .write ∧ ∃ t, t = pure ⟨⟩ ∧ c' = A1 t := by
  show focus_step A0 1 #v[dc, dp] #v[.child, .parent] 1 a c' ↔ _
  rw [focus_step_head_prim A0 1 #v[dc, dp] #v[.child, .parent] 1 _ _ 0 a c' (denote_write 2 8)]
  constructor
  · rintro ⟨k, kind, y, c1, Hk, Hp, rfl, rfl⟩
    cases Hp
    exact ⟨rfl, k ⟨⟩, Hk ⟨⟩, rfl⟩
  · rintro ⟨rfl, t, rfl, rfl⟩
    exact ⟨fun _ => pure ⟨⟩, .write, ⟨⟩, set_heap A0 .parent hP', fun _ => rfl, rfl, rfl, rfl⟩

theorem stepA1 (t : Thread sE Bn) (a : OwnedAction) (c' : OwnedCfg) (Ht : t = pure ⟨⟩) :
    owned_step (A1 t) a c' ↔ a = act .parent .ret ∧ c' = A2 := by
  show focus_step (A1 t) 1 #v[dc, t] #v[.child, .parent] 1 a c' ↔ _
  rw [focus_step_head_ret (A1 t) 1 #v[dc, t] #v[.child, .parent] 1 0 a c' (ret_guards t Ht),
    vector_remove_pair, vector_remove_pair]
  exact Iff.rfl

theorem stepA2 (a : OwnedAction) (c' : OwnedCfg) :
    owned_step A2 a c' ↔ a = act .child .select ∧ c' = A3 := by
  show sel_step A2 0 #v[dc] #v[.child] a c' ↔ _
  constructor
  · rintro ⟨j, rfl, rfl⟩; obtain rfl := fin1_eq j; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨0, rfl, rfl⟩

theorem stepA3 (a : OwnedAction) (c' : OwnedCfg) :
    owned_step A3 a c' ↔ a = act .child .write ∧ ∃ t, t = pure ⟨⟩ ∧ c' = A4 t := by
  show focus_step A3 0 #v[dc] #v[.child] 0 a c' ↔ _
  rw [focus_step_head_prim A3 0 #v[dc] #v[.child] 0 _ _ 0 a c' (denote_write 1 1)]
  constructor
  · rintro ⟨k, kind, y, c1, Hk, Hp, rfl, rfl⟩
    cases Hp
    exact ⟨rfl, k ⟨⟩, Hk ⟨⟩, rfl⟩
  · rintro ⟨rfl, t, rfl, rfl⟩
    exact ⟨fun _ => pure ⟨⟩, .write, ⟨⟩, set_heap A3 .child hC', fun _ => rfl, rfl, rfl, rfl⟩

theorem stepA4 (t : Thread sE Bn) (a : OwnedAction) (c' : OwnedCfg) (Ht : t = pure ⟨⟩) :
    owned_step (A4 t) a c' ↔ a = act .child .ret ∧ c' = A5 := by
  show focus_step (A4 t) 0 #v[t] #v[.child] 0 a c' ↔ _
  rw [focus_step_head_ret (A4 t) 0 #v[t] #v[.child] 0 0 a c' (ret_guards t Ht),
    vector_remove_single, vector_remove_single]
  exact Iff.rfl

theorem sA0 : owned_step A0 (act .parent .write) (A1 (pure ⟨⟩)) :=
  (stepA0 _ _).2 ⟨rfl, _, rfl, rfl⟩
theorem sA1 : owned_step (A1 (pure ⟨⟩)) (act .parent .ret) A2 := (stepA1 _ _ _ rfl).2 ⟨rfl, rfl⟩
theorem sA2 : owned_step A2 (act .child .select) A3 := (stepA2 _ _).2 ⟨rfl, rfl⟩
theorem sA3 : owned_step A3 (act .child .write) (A4 (pure ⟨⟩)) :=
  (stepA3 _ _).2 ⟨rfl, _, rfl, rfl⟩
theorem sA4 : owned_step (A4 (pure ⟨⟩)) (act .child .ret) A5 := (stepA4 _ _ _ rfl).2 ⟨rfl, rfl⟩

theorem wfA0 : owned_wf A0 :=
  init_owned_wf _ _ _ _ _ _ (managed_wf_preallocated _) (managed_wf_preallocated _) hC_hP_disj
theorem wfA1 (t : Thread sE Bn) (Ht : t = pure ⟨⟩) : owned_wf (A1 t) :=
  owned_step_wf _ _ _ wfA0 ((stepA0 _ _).2 ⟨rfl, t, Ht, rfl⟩)
theorem wfA2 : owned_wf A2 := owned_step_wf _ _ _ (wfA1 _ rfl) sA1
theorem wfA3 : owned_wf A3 := owned_step_wf _ _ _ wfA2 sA2
theorem wfA4 (t : Thread sE Bn) (Ht : t = pure ⟨⟩) : owned_wf (A4 t) :=
  owned_step_wf _ _ _ wfA3 ((stepA3 _ _).2 ⟨rfl, t, Ht, rfl⟩)
theorem wfA5 : owned_wf A5 := owned_step_wf _ _ _ (wfA4 _ rfl) sA4

/-- The global AN premise: every next state keeps the anchored split, the child's cell untouched
and the parent's cell written. -/
theorem A_global_han :
    hAN owned_next
      (state_sat fun c => asep (state_obligation .child hTrue c) (state_obligation .parent hTrue c))
      (state_sat fun c => asep (state_obligation .child (cell .child 1 0) c)
        (state_obligation .parent (cell .parent 2 8) c)) A0 := by
  refine (hAN_iff _ _ _ _).2
    ⟨(state_split_iff _ _ _).2 ⟨wfA0, trivial, trivial⟩, ⟨_, _, sA0⟩, ?_⟩
  rintro c' ⟨a, Ha⟩
  obtain ⟨-, t, Ht, rfl⟩ := (stepA0 a c').1 Ha
  exact (state_split_iff _ _ _).2 ⟨wfA1 t Ht, rfl, rfl⟩

/-- The two-program AN frame theorem on the source fork: the child still owes its selection, the
parent is focused. -/
theorem A_fork_han :
    hAN owned_next hTrue (cell .child 1 0) (init_local .child (.write 1 1) hC ctx0 0 false) ∧
    hAN owned_next hTrue (cell .parent 2 8) (init_local .parent (.write 2 8) hP ctx0 0 true) :=
  fork_han_split (.write 1 1) (fun _ => .write 2 8) hC hP ctx0 0 hTrue hTrue _ _ admA
    hTrue_proper hTrue_proper (cell_proper _ _ _) (cell_proper _ _ _) (cell_stable _ _ _)
    (cell_stable _ _ _) A_global_han

/-- The child's first own action is its selection; the parent's is its write. -/
theorem A_child_first (a : OwnedAction) (d : OwnedCfg) :
    owned_step (init_local .child (.write 1 1) hC ctx0 0 false) a d →
      a = act .child .select ∧ cell .child 1 0 d := fun H => by
  obtain ⟨rfl, rfl⟩ := (init_local_select _ _ _ _ _ _ _).1 H; exact ⟨rfl, rfl⟩

theorem A_parent_first (a : OwnedAction) (d : OwnedCfg) :
    owned_step (init_local .parent (.write 2 8) hP ctx0 0 true) a d → a = act .parent .write := by
  intro H
  change focus_step (init_local .parent (.write 2 8) hP ctx0 0 true) 0 #v[dp] #v[.parent] 0 a d
    at H
  rw [focus_step_head_prim _ 0 #v[dp] #v[.parent] 0 _ _ 0 a d (denote_write 2 8)] at H
  obtain ⟨k, kind, y, c1, -, Hp, rfl, -⟩ := H
  cases Hp; rfl

/-! ### The child's own-action clock -/

theorem rt_no_foreign (i : Side) (c mid : OwnedCfg) :
    (∀ a c', owned_step c a c' → a.owner = i) → Star (foreign_next i) c mid → mid = c := by
  intro Hown H
  rcases H.cases_head with rfl | ⟨_, ⟨a, Hs, Ho⟩, -⟩
  · rfl
  · exact absurd (Hown _ _ Hs) Ho

theorem foreign_star_A0 (mid : OwnedCfg) :
    Star (foreign_next .child) A0 mid →
      mid = A0 ∨ (∃ t, t = pure ⟨⟩ ∧ mid = A1 t) ∨ mid = A2 := by
  refine clos_refl_trans_preserves (foreign_next .child)
    (fun d => d = A0 ∨ (∃ t, t = pure ⟨⟩ ∧ d = A1 t) ∨ d = A2) ?_ A0 mid (.inl rfl)
  rintro y z Hy ⟨a, Hs, Ho⟩
  rcases Hy with rfl | ⟨t, Ht, rfl⟩ | rfl
  · obtain ⟨-, t, Ht, rfl⟩ := (stepA0 a z).1 Hs; exact .inr (.inl ⟨t, Ht, rfl⟩)
  · obtain ⟨-, rfl⟩ := (stepA1 t a z Ht).1 Hs; exact .inr (.inr rfl)
  · obtain ⟨rfl, -⟩ := (stepA2 a z).1 Hs; exact absurd rfl Ho

theorem weak_A0 (c' : OwnedCfg) : weak_next .child A0 c' ↔ c' = A3 := by
  constructor
  · rintro ⟨mid, Hmid, a, Hs, Ho⟩
    rcases foreign_star_A0 mid Hmid with rfl | ⟨t, Ht, rfl⟩ | rfl
    · obtain ⟨rfl, -⟩ := (stepA0 a c').1 Hs; cases Ho
    · obtain ⟨rfl, -⟩ := (stepA1 t a c' Ht).1 Hs; cases Ho
    · exact ((stepA2 a c').1 Hs).2
  · rintro rfl
    refine ⟨A2, ?_, act .child .select, sA2, rfl⟩
    exact (Star.single ⟨_, sA0, nofun⟩).tail ⟨_, sA1, nofun⟩

theorem weak_A3 (c' : OwnedCfg) : weak_next .child A3 c' ↔ ∃ t, t = pure ⟨⟩ ∧ c' = A4 t := by
  constructor
  · rintro ⟨mid, Hmid, a, Hs, -⟩
    rw [rt_no_foreign .child A3 mid (fun _ _ H => by rw [((stepA3 _ _).1 H).1]; rfl) Hmid]
      at Hs
    exact ((stepA3 a c').1 Hs).2
  · rintro ⟨t, Ht, rfl⟩
    exact ⟨A3, .refl, act .child .write, (stepA3 _ _).2 ⟨rfl, t, Ht, rfl⟩, rfl⟩

/-- The child's first own action keeps cell 1 at 0: the weak clock agrees with the projected local
AX. -/
theorem A_weak_ax_select :
    hAX (weak_next .child) (at_side .child (cell .child 1 0)) A0 ∧
    hAX owned_next (cell .child 1 0) (project .child A0) := by
  have H : hAX (weak_next .child) (at_side .child (cell .child 1 0)) A0 :=
    (hAN_iff _ _ _ _).2 ⟨trivial, ⟨A3, (weak_A0 _).2 rfl⟩,
      fun c' h => by obtain rfl := (weak_A0 c').1 h; rfl⟩
  exact ⟨H, weak_hax_to_local _ _ _ (cell_proper _ _ _) H⟩

/-- Its second own action writes cell 1. -/
theorem A_weak_ax2 :
    hAX (weak_next .child) (hAX (weak_next .child) (at_side .child (cell .child 1 1))) A0 := by
  refine (hAN_iff _ _ _ _).2 ⟨trivial, ⟨A3, (weak_A0 _).2 rfl⟩, fun c' h => ?_⟩
  obtain rfl := (weak_A0 c').1 h
  refine (hAN_iff _ _ _ _).2 ⟨trivial, ⟨A4 (pure ⟨⟩), (weak_A3 _).2 ⟨_, rfl, rfl⟩⟩, fun c' h => ?_⟩
  obtain ⟨t, -, rfl⟩ := (weak_A3 c').1 h
  rfl

theorem A_weak_ex2 :
    hEX (weak_next .child) (hEX (weak_next .child) (at_side .child (cell .child 1 1))) A0 :=
  (hEN_iff _ _ _ _).2 ⟨trivial, A3, (weak_A0 _).2 rfl,
    (hEN_iff _ _ _ _).2 ⟨trivial, A4 (pure ⟨⟩), (weak_A3 _).2 ⟨_, rfl, rfl⟩, rfl⟩⟩

/-! ### Boundary (a): a selection-sensitive target defeats the split -/

theorem Fnone_not_stable : ¬ SelectionStable Fnone := by
  intro H
  have Hn : Fnone (init_local .child (.write 1 1) hC ctx0 0 true) :=
    (H (init_local .child (.write 1 1) hC ctx0 0 false) (act .child .select)
      (init_local .child (.write 1 1) hC ctx0 0 true)
      ((init_local_select _ _ _ _ _ _ _).2 ⟨rfl, rfl⟩) rfl).1 rfl
  cases Hn

theorem Fnone_defeats_split :
    hproper Fnone ∧
    hAN owned_next
      (state_sat fun c => asep (state_obligation .child hTrue c) (state_obligation .parent hTrue c))
      (state_sat fun c => asep (state_obligation .child Fnone c)
        (state_obligation .parent (cell .parent 2 8) c)) A0 ∧
    ¬ hAN owned_next hTrue Fnone (init_local .child (.write 1 1) hC ctx0 0 false) := by
  refine ⟨Fnone_proper, ?_, ?_⟩
  · refine (hAN_iff _ _ _ _).2
      ⟨(state_split_iff _ _ _).2 ⟨wfA0, trivial, trivial⟩, ⟨_, _, sA0⟩, ?_⟩
    rintro c' ⟨a, Ha⟩
    obtain ⟨-, t, Ht, rfl⟩ := (stepA0 a c').1 Ha
    exact (state_split_iff _ _ _).2 ⟨wfA1 t Ht, rfl, rfl⟩
  · intro H
    obtain ⟨-, -, H⟩ := (hAN_iff _ _ _ _).1 H
    have Hn : Fnone (init_local .child (.write 1 1) hC ctx0 0 true) :=
      H _ ⟨act .child .select, (init_local_select _ _ _ _ _ _ _).2 ⟨rfl, rfl⟩⟩
    cases Hn

/-! ### Boundary (b): the child conclusion must keep its pending selection -/

def L1 : OwnedCfg :=
  set_pool (set_heap (init_local .child (.write 1 1) hC ctx0 0 true) .child hC')
    (mk_pool 1 #v[pure ⟨⟩] #v[.child] (some 0))

theorem A_focused_child_fails :
    ¬ hAN owned_next hTrue (cell .child 1 0) (init_local .child (.write 1 1) hC ctx0 0 true) := by
  intro H
  obtain ⟨-, -, H⟩ := (hAN_iff _ _ _ _).1 H
  have Hs : owned_step (init_local .child (.write 1 1) hC ctx0 0 true) (act .child .write) L1 := by
    show focus_step (init_local .child (.write 1 1) hC ctx0 0 true) 0 #v[dc] #v[.child] 0
      (act .child .write) L1
    exact (focus_step_head_prim _ 0 #v[dc] #v[.child] 0 _ _ 0 _ _ (denote_write 1 1)).2
      ⟨fun _ => pure ⟨⟩, .write, ⟨⟩,
        set_heap (init_local .child (.write 1 1) hC ctx0 0 true) .child hC',
        fun _ => rfl, rfl, rfl, rfl⟩
  have Hn : some 1 = some 0 := H _ ⟨_, Hs⟩
  simp at Hn

/-! ### Boundary (c): after the parent finishes, its empty projection has no next step although
the survivor satisfies global AN -/

theorem A_finished_parent :
    coupled A2 ∧ (project .parent A2).pool.size = 0 ∧
    hAN owned_next
      (state_sat fun c => asep (state_obligation .child hTrue c) (state_obligation .parent hTrue c))
      (state_sat fun c => asep (state_obligation .child hTrue c) (state_obligation .parent hTrue c))
      A2 ∧
    ¬ hAN owned_next hTrue hTrue (project .parent A2) := by
  have Hz : (project .parent A2).pool.size = 0 := rfl
  refine ⟨coupled_step _ _ _ (coupled_step _ _ _ (coupled_init _ _ _ _ _ _ admA) sA0) sA1, Hz,
    ?_, ?_⟩
  · refine (hAN_iff _ _ _ _).2
      ⟨(state_split_iff _ _ _).2 ⟨wfA2, trivial, trivial⟩, ⟨A3, _, sA2⟩, ?_⟩
    rintro c' ⟨a, Ha⟩
    obtain ⟨-, rfl⟩ := (stepA2 a c').1 Ha
    exact (state_split_iff _ _ _).2 ⟨wfA3, trivial, trivial⟩
  · intro H
    obtain ⟨-, ⟨c', a, Hs⟩, -⟩ := (hAN_iff _ _ _ _).1 H
    exact owned_step_empty _ a c' Hz Hs

/-! ### The symmetric case: the parent yields first -/

def B0 : OwnedCfg := init_owned (.write 1 1) parentY hC hP ctx0 0
def B1 : OwnedCfg := set_pool B0 (mk_pool 2 #v[dc, dp] #v[.child, .parent] none)
def B2 : OwnedCfg := set_pool B0 (mk_pool 2 #v[dc, dp] #v[.child, .parent] (some 0))

theorem sB0 : owned_step B0 (act .parent .yield) B1 := by
  show focus_step B0 1 #v[dc, denote parentY] #v[.child, .parent] 1 (act .parent .yield) B1
  exact (focus_step_head_yield B0 1 #v[dc, denote parentY] #v[.child, .parent] 1 _ 0 _ _
    denote_yield_write).2 ⟨fun _ => dp, fun _ => rfl, rfl, rfl⟩

theorem sB1 : owned_step B1 (act .child .select) B2 := by
  show sel_step B1 1 #v[dc, dp] #v[.child, .parent] (act .child .select) B2
  exact ⟨0, rfl, rfl⟩

theorem coupledB2 : coupled B2 :=
  coupled_step _ _ _ (coupled_step _ _ _ (coupled_init _ _ _ _ _ _ admB) sB0) sB1

theorem B_global_han :
    hAN owned_next
      (state_sat fun c => asep (state_obligation .child hTrue c) (state_obligation .parent hTrue c))
      (state_sat fun c => asep (state_obligation .child (cell .child 1 1) c)
        (state_obligation .parent (cell .parent 2 7) c)) B2 := by
  have Hwf := coupled_wf _ coupledB2
  have Hs : owned_step B2 (act .child .write)
      (set_pool (set_heap B2 .child hC')
        (mk_pool 2 #v[pure ⟨⟩, dp] #v[.child, .parent] (some 0))) := by
    show focus_step B2 1 #v[dc, dp] #v[.child, .parent] 0 (act .child .write) _
    exact (focus_step_head_prim B2 1 #v[dc, dp] #v[.child, .parent] 0 _ _ 0 _ _
      (denote_write 1 1)).2
      ⟨fun _ => pure ⟨⟩, .write, ⟨⟩, set_heap B2 .child hC', fun _ => rfl, rfl, rfl, rfl⟩
  refine (hAN_iff _ _ _ _).2
    ⟨(state_split_iff _ _ _).2 ⟨Hwf, trivial, trivial⟩, ⟨_, _, Hs⟩, ?_⟩
  rintro c' ⟨a, Ha⟩
  have Hwf' := owned_step_wf _ _ _ Hwf Ha
  change focus_step B2 1 #v[dc, dp] #v[.child, .parent] 0 a c' at Ha
  rw [focus_step_head_prim B2 1 #v[dc, dp] #v[.child, .parent] 0 _ _ 0 a c'
    (denote_write 1 1)] at Ha
  obtain ⟨k, kind, y, c1, -, Hp, rfl, rfl⟩ := Ha
  cases Hp
  exact (state_split_iff _ _ _).2 ⟨Hwf', rfl, rfl⟩

theorem B_han_split :
    hAN owned_next hTrue (cell .child 1 1) (project .child B2) ∧
    hAN owned_next hTrue (cell .parent 2 7) (project .parent B2) :=
  global_han_split _ _ _ _ _ coupledB2 hTrue_proper hTrue_proper (cell_proper _ _ _)
    (cell_proper _ _ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (cell_stable _ _ _)
    (cell_stable _ _ _) B_global_han

/-- The yielded parent's projection owes a selection, so "focus is None" is not its next-state
property. -/
theorem B_parent_Fnone_fails : ¬ hAN owned_next hTrue Fnone (project .parent B2) := by
  intro H
  obtain ⟨-, ⟨c', a, Hs⟩, H⟩ := (hAN_iff _ _ _ _).1 H
  have Hn : c'.pool.focus = none := H c' ⟨a, Hs⟩
  have Hf : (project .parent B2).pool.focus = none := rfl
  revert Hs Hf
  generalize project .parent B2 = c
  rcases c with ⟨⟨_ | n, v, g, _ | j⟩, _⟩ <;> intro Hs Hf
  · exact Hs
  · exact Hs
  · obtain ⟨j, -, rfl⟩ := Hs; cases Hn
  · cases Hf

/-! ### Return suffixes: only the last finisher returns -/

theorem A_global_hret :
    hRet owned_next
      (state_sat fun c => asep (state_obligation .child (cell .child 1 1) c)
        (state_obligation .parent (cell .parent 2 8) c)) (A4 (pure ⟨⟩)) := by
  refine ⟨A5, ⟨_, sA4⟩, ?_⟩
  rintro c' ⟨a, Ha⟩
  obtain ⟨-, rfl⟩ := (stepA4 _ a c' rfl).1 Ha
  exact ⟨rfl, same_view_equivalence.refl _, (state_split_iff _ _ _).2 ⟨wfA5, rfl, rfl⟩⟩

theorem A_hret_split :
    (hRet owned_next (cell .child 1 1) (project .child (A4 (pure ⟨⟩))) ∧
      hDone (cell .parent 2 8) (project .parent (A4 (pure ⟨⟩)))) ∨
    (hDone (cell .child 1 1) (project .child (A4 (pure ⟨⟩))) ∧
      hRet owned_next (cell .parent 2 8) (project .parent (A4 (pure ⟨⟩)))) :=
  global_hret_split _ _ _ (cell_proper _ _ _) (cell_proper _ _ _) A_global_hret

theorem A_not_both_hret :
    ¬ (hRet owned_next (cell .child 1 1) (project .child (A4 (pure ⟨⟩))) ∧
      hRet owned_next (cell .parent 2 8) (project .parent (A4 (pure ⟨⟩)))) :=
  fun ⟨_, _, ⟨_, Hs⟩, _⟩ => owned_step_empty (project .parent (A4 (pure ⟨⟩))) _ _ rfl Hs

/-- Equal joined results cannot hide which lineage emitted. -/
theorem unequal_lineage_counts_not_uniform :
    ∃ c0 c1 : OwnedCfg,
      terminal c0 ∧ terminal c1 ∧
      (∀ i, c0.heap i = managed_empty ∧ c1.heap i = managed_empty) ∧
      c0.ctx = c1.ctx ∧ c0.base = c1.base ∧
      (∀ i, c0.last i = none ∧ c1.last i = none) ∧
      c0.count .child = 0 ∧ c0.count .parent = 1 ∧
      c1.count .child = 1 ∧ c1.count .parent = 0 ∧
      joined_state c0 = joined_state c1 ∧
      ∀ src,
        ¬ hRet (fun _ d => d = c0 ∨ d = c1) hTrue src ∧
        ¬ hRet_at .child (fun _ d => d = c0 ∨ d = c1) hTrue src := by
  refine ⟨⟨mk_pool 0 #v[] #v[] none, fun _ => managed_empty, fun _ => managed_empty, [], 0,
      fun | .child => 0 | .parent => 1, fun _ => none⟩,
    ⟨mk_pool 0 #v[] #v[] none, fun _ => managed_empty, fun _ => managed_empty, [], 0,
      fun | .child => 1 | .parent => 0, fun _ => none⟩,
    rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
    fun src => ⟨?_, ?_⟩⟩
  · rintro ⟨out, -, Hall⟩
    obtain ⟨-, ⟨-, -, -, H0, -⟩, -⟩ := Hall _ (.inl rfl)
    obtain ⟨-, ⟨-, -, -, H1, -⟩, -⟩ := Hall _ (.inr rfl)
    have h0 : 0 = out.count .child := H0 .child
    have h1 : 1 = out.count .child := H1 .child
    omega
  · rintro ⟨out, -, Hall⟩
    obtain ⟨-, ⟨-, -, -, H0, -⟩, -⟩ := Hall _ (.inl rfl)
    obtain ⟨-, ⟨-, -, -, H1, -⟩, -⟩ := Hall _ (.inr rfl)
    have h0 : 0 = (project .child out).count .child := H0 .child
    have h1 : 1 = (project .child out).count .child := H1 .child
    omega

-- Not ported: Ltac `chg` (replaced by `show`/`change`). Rocq's `vector_remove_tail`/
-- `vector_remove_head` rewrites on literal vectors are `vector_remove_pair`/`vector_remove_single`.

end Examples.CSL.Frame.Separation.NextRegression
