/- SPDX-License-Identifier: MIT -/
module

public import Logic.CTree.Iter
public import Logic.CTree.Bind
public import Logic.Yield.RoundRobin

/-!
# Hidden vs visible branching

ctrees' LTS crawls through delayed branches `br c k` and `guard`; only `step`/`brS`, `vis` and
`ret` are transitions. The TICL `ret R` atom distinguishes "all transitions return the same value"
(strongly bisimilar to `pure x`) from the shallow universal-next terminal postcondition ("every
transition returns some value satisfying `R`"). The second example is the regression that must
fail if native `ret` is ever weakened to that terminal-next property (← `examples/HiddenBr.v`).
-/

@[expose] public section
namespace Examples.HiddenBr
open CTree Tisl Tisl.Notation Tisl.Yield
open ITree (Effect)

def two : Fin 2 → CTree void1 Bn Nat :=
  fun i => if i = 0 then pure 1 else pure 2

private theorem brn_eq {X : Type} (n : Nat) (k : Fin n → CTree void1 Bn X) :
    CTree.brn n k = .br (B := Bn) ⟨n⟩ fun i => k i.down := rfl

private theorem brSn_eq {X : Type} (n : Nat) (k : Fin n → CTree void1 Bn X) :
    CTree.brSn n k = .brS (B := Bn) ⟨n⟩ fun i => k i.down := rfl

/-- Hidden value choice is one return, not a step: every transition of `brn two` returns `1` or `2`
directly. -/
example : anc (entails (⊤ : TiclL void1))
    (fun _ wd => DoneWith (fun x _ => x = 1 ∨ x = 2) wd) (CTree.brn 2 two) .pure := by
  rw [brn_eq]
  refine ⟨⟨trivial, .pure⟩, can_step_br.2 ⟨⟨0⟩, can_step_ret .pure⟩, fun t' w' tr => ?_⟩
  obtain ⟨⟨i⟩, tr⟩ := ktrans_br.1 tr
  unfold two at tr
  split at tr <;> obtain ⟨rfl, -⟩ := ktrans_done.1 tr <;> exact .done _ (by simp)

/-- … but it is NOT a single-valued return: `ret` fails. -/
example : ¬ entails (.ret fun (_ : Nat) _ => True) (CTree.brn 2 two) (.pure : World void1) := by
  rintro ⟨x, -, -, -, htr⟩
  rw [brn_eq] at htr
  have h1 := htr _ _ (ktrans_br.2 ⟨⟨0⟩, ktrans_done.2 ⟨rfl, rfl⟩⟩)
  have h2 := htr _ _ (ktrans_br.2 ⟨⟨1⟩, ktrans_done.2 ⟨rfl, rfl⟩⟩)
  obtain ⟨⟩ := (done_of_eq _ _ _).1 h1
  rename_i h1; obtain ⟨rfl, -⟩ := h1
  obtain ⟨⟩ := (done_of_eq _ _ _).1 h2
  rename_i h2; exact absurd h2.1 (by decide)

/-- Visible choice is a step, then a deterministic return. -/
example :
    entails (AX (.ret fun x _ => x = 1 ∨ x = 2)) (CTree.brSn 2 two) (.pure : World void1) := by
  rw [brSn_eq]
  refine (an_brS (B := Bn) (c := ⟨2⟩) ⟨0⟩).2 ⟨⟨trivial, .pure⟩, fun ⟨i⟩ => ?_⟩
  unfold two; split <;> exact ret_ret .pure (by simp)

/-- Bind through a visible choice (regime A, `u_bind_r`). -/
example : Auc (entails (⊤ : TiclL void1))
    (anc (entails (⊤ : TiclL void1)) (fun _ wd => DoneWith (fun x w => 1 = x ∧ .pure = w) wd))
    (CTree.brSn 2 two >>= fun x => if x = 1 then pure 1 else .step (pure 1)) .pure := by
  refine auc_mono_r (q := entails (M := CTree) (ret= 1 World.pure))
    (fun t w h => ret_done_next _ h) _ _ ?_
  refine (ticl_au (M := CTree) ⊤ (ret= 1 World.pure)).1
    (u_bind_r (q := .A) (R := fun x w => (x = 1 ∨ x = 2) ∧ w = .pure) ?_ ?_)
  · rw [brSn_eq]
    apply (au_brS (B := Bn) (c := ⟨2⟩) ⟨0⟩).1
    refine .inr ⟨⟨trivial, .pure⟩, fun ⟨i⟩ => ?_⟩
    apply Auc.matchA
    unfold two; split <;> exact ret_ret .pure (by simp)
  · rintro x w ⟨rfl | rfl, rfl⟩
    · exact Auc.matchA (ret_ret .pure ⟨rfl, rfl⟩)
    · apply au_step.1
      exact .inr ⟨⟨trivial, .pure⟩, Auc.matchA (ret_ret .pure ⟨rfl, rfl⟩)⟩

/-- sbisim invariance: a guard is invisible. -/
example (t : CTree void1 Bn Nat) (w : World void1) (φ : TiclR void1 Nat) :
    entails φ (CTree.guard t) w ↔ entails φ t w :=
  proper_entails_meq φ (sb_guard t)

/-- Hidden value choice may mix immediate and delayed return. -/
example : Auc (entails (⊤ : TiclL void1))
    (fun _ wd => DoneWith (fun x w => 1 = x ∧ .pure = w) wd)
    (CTree.brn 2 two >>= fun x => if x = 1 then pure 1 else .step (pure 1)) .pure := by
  rw [brn_eq, br_bind]
  refine .stepA ⟨trivial, .pure⟩ (can_step_br.2 ⟨⟨0⟩, ?_⟩) fun t' w' tr => ?_
  · simp only [two, ↓reduceIte, pure_bind]; exact can_step_ret .pure
  · obtain ⟨⟨i⟩, tr⟩ := ktrans_br.1 tr
    by_cases hi : i = 0
    · simp only [two, hi, ite_true, pure_bind] at tr
      obtain ⟨rfl, rfl⟩ := ktrans_done.1 tr
      exact .matchA (.done _ ⟨rfl, rfl⟩)
    · simp only [two, hi, ite_false, pure_bind] at tr
      obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
      refine .stepA ⟨trivial, .pure⟩ (can_step_ret .pure) fun t'' w'' tr => ?_
      obtain ⟨rfl, rfl⟩ := ktrans_done.1 tr
      exact .matchA (.done _ ⟨rfl, rfl⟩)

/-- Hidden iteration returns a uniform final value despite differing indices. -/
def body (n : Nat) : CTree void1 Bn (Nat ⊕ Nat) :=
  if n = 0 then pure (.inr 7)
  else CTree.brn 2 fun i => pure (.inl (n.pred - if i = 0 then 0 else 1))

theorem iter_body_ret (n : Nat) :
    entails (ret= 7 .pure) (CTree.iter body n) (.pure : World void1) := by
  refine ret_iter_wf (fun _ w => w = .pure) (InvImage (· < ·) Prod.fst)
    (InvImage.wf _ Nat.lt_wfRel.wf) ?_ n .pure rfl
  rintro m w rfl cont hcont
  unfold body
  split
  · rw [pure_bind]; exact ret_ret .pure ⟨rfl, rfl⟩
  · rename_i hm
    rw [brn_eq, br_bind]
    refine ret_br (B := Bn) (c := ⟨2⟩) ⟨0⟩ .pure ⟨rfl, rfl⟩ fun ⟨i⟩ => ?_
    rw [pure_bind]
    exact ret_guard.2 (hcont _ _ rfl (by show _ < m; rw [Nat.pred_eq_sub_one]; split <;> omega))

example : Auc (entails (⊤ : TiclL void1))
    (fun _ wd => DoneWith (fun x w => 7 = x ∧ .pure = w) wd) (CTree.iter body 3) .pure :=
  af_ret_done _ (.matchA (iter_body_ret 3))

/-! Delayed branching forgets branch order under strong bisimulation, but a cursor-driven
refinement observes that order. Such a replacement does not satisfy the guard-alignment premise
of the runner congruences. -/

def branch01 : CTree void1 Bn Nat :=
  .br ⟨2⟩ fun i => if i.down = 0 then pure 0 else pure 1

def branch10 : CTree void1 Bn Nat :=
  .br ⟨2⟩ fun i => if i.down = 0 then pure 1 else pure 0

theorem delayed_branch_permutation : branch01 ~ branch10 :=
  sb_br _ _ _ _ (fun | ⟨0⟩ => ⟨⟨1⟩, sbisim_refl _⟩ | ⟨1⟩ => ⟨⟨0⟩, sbisim_refl _⟩)
    (fun | ⟨0⟩ => ⟨⟨1⟩, sbisim_refl _⟩ | ⟨1⟩ => ⟨⟨0⟩, sbisim_refl _⟩)

theorem refine_rr_branch01_zero :
    refine_rr branch01 0 ~ (pure (0, 1) : CTree void1 Bn (Nat × Nat)) := by
  rw [unfold_refine_rr]
  simp only [branch01, unfold_br]
  rw [unfold_refine_rr]
  simp only [rr_pick]
  exact sb_guard _

theorem refine_rr_branch10_zero :
    refine_rr branch10 0 ~ (pure (1, 1) : CTree void1 Bn (Nat × Nat)) := by
  rw [unfold_refine_rr]
  simp only [branch10, unfold_br]
  rw [unfold_refine_rr]
  simp only [rr_pick]
  exact sb_guard _

theorem refine_rr_not_sbisim_congruent : ¬ (refine_rr branch01 0 ~ refine_rr branch10 0) :=
  fun h => absurd (sbisim_ret_inv (sbisim_trans (sbisim_symm refine_rr_branch01_zero)
    (sbisim_trans h refine_rr_branch10_zero))) (by decide)

/-- The event-only round-robin scheduler never inspects a thread's hidden branches: both
alternatives of a branching thread survive scheduling, and each one still logs its own value.
Contrast `refine_rr_branch01_zero`, where the standalone refiner collapses the branch to its
first alternative. -/
def rr_branch_thread : Thread (stateE Nat) Bn :=
  .br ⟨2⟩ fun i => .vis (.inr (.inr (StateOp.put (slot_index i.down)))) fun _ => pure ⟨⟩

theorem rr_preserves_thread_branch (σ : Nat) :
    interp_schedule_rr h_stateW 1 #v[rr_branch_thread] (some 0) 0 σ ~
      CTree.br (B := Bn) ⟨2⟩ fun i =>
        log (.inl (slot_index i.down)) >>= fun _ => pure (PUnit.unit, slot_index i.down) := by
  refine sbisim_trans (interp_schedule_rr_br h_stateW 0 #v[rr_branch_thread] 0
    (fun i => .vis (.inr (.inr (StateOp.put (slot_index i.down)))) fun _ => pure ⟨⟩) 0 σ
    (by simp [rr_branch_thread])) (sb_br_id _ _ _ fun ⟨i⟩ => ?_)
  refine sbisim_trans (interp_schedule_rr_user h_stateW 0 _ 0 (StateOp.put (slot_index i))
    (fun _ => pure ⟨⟩) 0 σ (by simp; rfl)) ?_
  simp only [h_stateW, translate_log_bind, translate_ret, bind_assoc, pure_bind]
  refine sbisim_bind_eq _ fun _ => ?_
  refine sbisim_trans (interp_schedule_rr_ret h_stateW 0 _ 0 0 _ (by simp)) ?_
  exact interp_schedule_rr_empty h_stateW _ 0 _

/-- Visible iteration takes a real step in every continuing round. -/
theorem iterS_body_af_ret (n : Nat) :
    entails (AF ret= 7 .pure) (CTree.iterS body n) (.pure : World void1) := by
  refine u_iterS_wf (q := .A) (fun _ w => w = .pure) (InvImage (· < ·) Prod.fst)
    (InvImage.wf _ Nat.lt_wfRel.wf) ?_ n .pure rfl
  rintro m w rfl cont hcont
  unfold body
  split
  · rw [pure_bind]; exact .matchA (ret_ret .pure ⟨rfl, rfl⟩)
  · rename_i hm
    rw [brn_eq, br_bind]
    refine Auc.stepA' ⟨⟨trivial, .pure⟩, can_step_br.2 ⟨⟨0⟩, ?_⟩, fun t' w' tr => ?_⟩
    · rw [pure_bind]; exact can_step_step.2 .pure
    · obtain ⟨⟨i⟩, tr⟩ := ktrans_br.1 tr
      rw [pure_bind] at tr
      obtain ⟨rfl, rfl, -⟩ := ktrans_step.1 tr
      exact hcont _ _ rfl (by show _ < m; rw [Nat.pred_eq_sub_one]; split <;> omega)

theorem iterS_body_af : Auc (entails (⊤ : TiclL void1))
    (fun _ wd => DoneWith (fun x w => 7 = x ∧ .pure = w) wd) (CTree.iterS body 3) .pure :=
  af_ret_done _ (iterS_body_af_ret 3)

theorem iterS_body_acc : Acc (kripke_step (M := CTree)) (CTree.iterS body 3, World.pure) :=
  af_done_accessible _ iterS_body_af

/-- Negative: a visible self-loop cannot eventually reach a terminal world. -/
def self_loop : CTree void1 Bn Nat :=
  CTree.iterS (fun u : PUnit => pure (.inl u)) ⟨⟩

theorem self_loop_not_af (R : Nat → World void1 → Prop) :
    ¬ Auc (entails (⊤ : TiclL void1)) (fun _ wd => DoneWith R wd) self_loop .pure := by
  intro H
  have hunf : self_loop = .step self_loop := (unfold_iterS _ _).trans (pure_bind _ _)
  have tr : ktrans (CTree.step self_loop) World.pure self_loop World.pure :=
    ktrans_step.2 ⟨rfl, rfl, .pure⟩
  rw [← hunf] at tr
  exact acc_self_loop _ _ tr (af_done_accessible _ H)

/-- Negative: an empty hidden choice has no transition, so `AF` cannot pass vacuously. -/
def empty_choice : CTree void1 Bn Nat := CTree.brn 0 fun _ => pure 0

theorem empty_choice_not_af (R : Nat → World void1 → Prop) :
    ¬ Auc (entails (⊤ : TiclL void1)) (fun _ wd => DoneWith R wd) empty_choice .pure := by
  rintro (⟨⟨⟩⟩ | ⟨-, ⟨t', w', tr⟩, -⟩)
  rw [empty_choice, brn_eq] at tr
  obtain ⟨⟨i⟩, -⟩ := ktrans_br.1 tr
  exact i.elim0

end Examples.HiddenBr
