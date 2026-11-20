/- SPDX-License-Identifier: MIT -/
module

public import Logic.Sep.Asep
public import Logic.Utils.Execution
public import Logic.Utils.Relations
public import Examples.CSL.Frame.Shared
public import Examples.CSL.Frame.Separation.AlwaysRegression
public import Examples.CSL.Frame.Separation.SilentReadTiclRegression

/-!
# Common EG along one visible fair execution

The two writer loops of `AlwaysRegression` are tracked by an active-separation view of their fair
execution: every state keeps both cells and each lineage's local world shows only its own writes
and emissions. Each lineage owns infinitely many visible emissions, so `asep_egc_run` yields the
common EG; silent reads alone do not give visible recurrence
(← `examples/CSL/Frame/Active.v`, module `CommonEGActiveRegression`).
-/

@[expose] public section
namespace Examples.CSL.Frame.Active.CommonEGActiveRegression
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield Tisl.Pcm Tisl.Notation CoCSL
open Examples.CSL.Frame.Shared Examples.CSL.Frame.Separation
open Examples.CSL.Frame.Separation.AlwaysRegression

def initial : AsepState := { cfg := c0, global := .pure, loc := fun _ => .pure }

theorem initial_ok : asep_state_ok initial :=
  ⟨admissible_active_erasable _ _ _ _ _ _ loops_admissible, .pure, fun _ => .pure⟩

def fair_state : Nat → AsepState
  | 0 => initial
  | k + 1 => asep_advance (fair_state k) (fair_exec.selected k) (fair_exec.states (k + 1))

def fair_view_exec : Execution AsepState OwnedAction Unit where
  states := fair_state
  selected := fair_exec.selected
  emitted := fair_exec.emitted

theorem fair_state_cfg (n : Nat) : (fair_state n).cfg = fair_exec.states n := by
  cases n <;> rfl

def seen (i : Side) (w : World (writerE (CSLObs (Nat × Nat)))) : Prop :=
  match w with
  | .pure => True
  | .obs (CSLObs.heap m) _ =>
    match i with
    | .child => m ≈ region 1 1
    | .parent => m ≈ region 2 8
  | .obs (CSLObs.emit e) _ =>
    e.value = match i with
      | .child => (1, 1)
      | .parent => (0, 8)
  | _ => False

def local_pred (i : Side) :
    ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig) → World (writerE (CSLObs (Nat × Nat))) →
      Prop :=
  entails (.now (seen i) : TiclL (writerE (CSLObs (Nat × Nat))))

theorem projected_heap (i : Side) (c : OwnedCfg) : joined_heap (project i c) = c.heap i :=
  congrArg Prod.fst (owned_joined_state_project i c)

def fair_resources (s : AsepState) : Prop :=
  AlwaysRegression.Inv s.cfg ∧
  s.cfg.heap .child ≈ region 1 1 ∧
  s.cfg.heap .parent ≈ region 2 8

def fair_inv (s : AsepState) : Prop :=
  asep_at fair_resources (local_pred .child) (local_pred .parent) s

/-- One concrete scheduling turn keeps both cells at their fixed values. -/
private theorem regions_step (p : pos) (c : OwnedCfg) :
    c.heap .child ≈ region 1 1 → c.heap .parent ≈ region 2 8 →
    (set_pool (pos_cfg p c) (pool_of (next_pos p))).heap .child ≈ region 1 1 ∧
      (set_pool (pos_cfg p c) (pool_of (next_pos p))).heap .parent ≈ region 2 8 := by
  intro HC HP
  have EC := managed_heap_ext _ _ HC
  have EP := managed_heap_ext _ _ HP
  cases p <;>
    simp only [pos_cfg, pos_phase, pos_owner, side_cell, phase_cfg, set_pool, set_heap, side_upd,
      emit_cfg, side_eqb, EC, EP, ite_true, ite_false, Bool.false_eq_true] <;>
    exact ⟨by first | exact peq_refl _ | exact upd_region _ _ _,
      by first | exact peq_refl _ | exact upd_region _ _ _⟩

theorem fair_view_exec_spec :
    (∀ n, fair_inv (fair_view_exec.states n)) ∧
    (∀ n, asep_step (fair_view_exec.states n) (fair_view_exec.selected n)
      (fair_view_exec.states (n + 1))) := by
  refine execution_invariant_steps (fun a s (_ : Unit) s' => asep_step s a s') fair_inv
    fair_view_exec (asep_at_intro _ _ _ _ initial_ok ⟨Inv_c0, peq_refl _, peq_refl _⟩
      ⟨trivial, .pure⟩ ⟨trivial, .pure⟩) fun k Hinv => ?_
  obtain ⟨Hok, -, ⟨HI, HC, HP⟩, TC, TP⟩ := asep_at_inv _ _ _ _ Hinv
  change AlwaysRegression.Inv (fair_state k).cfg at HI
  change (fair_state k).cfg.heap .child ≈ _ at HC
  change (fair_state k).cfg.heap .parent ≈ _ at HP
  rw [fair_state_cfg] at HI HC HP
  obtain ⟨-, HcellC, HcellP, -⟩ := id HI
  have Hstep := run_step k HcellC HcellP
  have HS : asep_step (fair_state k) (fair_exec.selected k) (fair_state (k + 1)) :=
    ⟨by rw [fair_state_cfg, fair_state_cfg]; exact Hstep, rfl⟩
  refine ⟨HS, ?_⟩
  have Hok' := asep_state_ok_step _ _ _ Hok HS
  have Hregions : (fair_exec.states (k + 1)).heap .child ≈ region 1 1 ∧
      (fair_exec.states (k + 1)).heap .parent ≈ region 2 8 := by
    exact regions_step (run k).1 (run k).2 HC HP
  have HH : ∀ i, seen i ((fair_state k).loc i) := fun | .child => TC.1 | .parent => TP.1
  have Hseen : ∀ i, seen i ((fair_state (k + 1)).loc i) := by
    intro i
    show seen i (if side_eqb (pos_owner (run k).1) i then
      after_logs (action_logs (project_action i (fair_state k).cfg
          (act (pos_owner (run k).1) (pos_kind (run k).1 (run k).2)))
        (joined_heap (project i (fair_exec.states (k + 1))))) ((fair_state k).loc i)
      else (fair_state k).loc i)
    rw [projected_heap]
    generalize fair_exec.states (k + 1) = d at Hregions ⊢
    generalize (fair_state k).cfg = c
    generalize (run k).2 = c'
    generalize (run k).1 = p
    cases p <;> cases i <;>
      simp only [pos_owner, pos_kind, pos_phase, side_cell, phase_kind, act, project_action,
        action_logs, erase_action_label, label_logs, after_logs, side_eqb, ite_true, ite_false,
        Bool.false_eq_true, List.flatMap_cons, List.flatMap_nil, List.append_nil] <;>
      first | exact HH _ | exact Hregions.1 | exact Hregions.2 | rfl
  exact asep_at_intro _ _ _ _ Hok' ⟨Inv_closed _ _ _ HI Hstep, Hregions⟩
    ⟨Hseen .child, Hok'.2.2 .child⟩ ⟨Hseen .parent, Hok'.2.2 .parent⟩

theorem fair_view_exec_valid :
    execution_valid (fun a s (_ : Unit) s' => asep_step s a s') (Eq initial) fair_view_exec :=
  ⟨rfl, fair_view_exec_spec.2⟩

theorem fair_local_assertions (n : Nat) : fair_inv (fair_state n) := fair_view_exec_spec.1 n

/-- Distance from `p` to the next emit position of lineage `i`. -/
private def emit_dist : Side → pos → Nat
  | .child, p => match p with
    | .Q0 => 5 | .Q1 => 4 | .Q2 => 3 | .R0 => 2 | .R1 => 1 | .C0 => 2 | .C1 => 1 | .C2 => 0
    | .C3 => 7 | .P0 => 6 | .P1 => 5 | .P2 => 4 | .P3 => 3
  | .parent, p => match p with
    | .Q0 => 1 | .Q1 => 0 | .Q2 => 7 | .R0 => 6 | .R1 => 5 | .C0 => 6 | .C1 => 5 | .C2 => 4
    | .C3 => 3 | .P0 => 2 | .P1 => 1 | .P2 => 0 | .P3 => 7

private theorem emit_dist_spec (i : Side) (p : pos) :
    pos_owner (Nat.repeat next_pos (emit_dist i p) p) = i ∧
      pos_phase (Nat.repeat next_pos (emit_dist i p) p) = some .PE := by
  cases i <;> cases p <;> exact ⟨rfl, rfl⟩

/-- Each witness is an emit position of this very phase cycle, rather than merely a position
belonging to the requested owner. -/
theorem fair_owner_visible (i : Side) :
    infinitely fun n =>
      owner_visible i (fair_view_exec.states n).cfg (fair_view_exec.selected n)
        (fair_view_exec.states (n + 1)).cfg := by
  intro n
  obtain ⟨k, Ho, He⟩ : ∃ k, pos_owner (Nat.repeat next_pos k (run n).1) = i ∧
      pos_phase (Nat.repeat next_pos k (run n).1) = some .PE := by
    generalize (run n).1 = p
    exact ⟨emit_dist i p, emit_dist_spec i p⟩
  refine ⟨n + k, Nat.le_add_right _ _, ?_⟩
  show pos_owner (run (n + k)).1 = i ∧
    erase_action_label (act (pos_owner (run (n + k)).1) (pos_kind (run (n + k)).1 (run (n + k)).2))
      _ ≠ none
  rw [run_pos_add]
  generalize (run (n + k)).2 = c
  generalize Nat.repeat next_pos k (run n).1 = q at Ho He
  refine ⟨Ho, ?_⟩
  unfold pos_kind; rw [He]
  cases pos_owner q <;> simp [side_cell, phase_kind, erase_action_label, act]

theorem common_visible_execution_eg :
    egc (asep_sat fair_resources (local_pred .child) (local_pred .parent))
      (owned_interp c0) .pure ∧
    asep_sat fair_resources (egc (local_pred .child)) (egc (local_pred .parent))
      (owned_interp c0) .pure :=
  asep_egc_run fair_resources (local_pred .child) (local_pred .parent) initial fair_view_exec
    (asep_pred_ok_entails _) (asep_pred_ok_entails _) fair_view_exec_valid fair_local_assertions
    fair_owner_visible

theorem silent_reads_are_not_visible_recurrence :
    infinitely (fun n => (SilentReadTiclRegression.read_forever.selected n).owner = .parent) ∧
    ¬ infinitely (fun n =>
      erase_action_label (SilentReadTiclRegression.read_forever.selected n)
        (joined_heap (SilentReadTiclRegression.read_forever.states (n + 1))) ≠ none) :=
  ⟨fun n =>
    let ⟨k, Hle, Hread⟩ := SilentReadTiclRegression.read_forever_infinitely_reads n
    ⟨k, Hle, congrArg OwnedAction.owner Hread⟩,
   SilentReadTiclRegression.read_forever_not_infinitely_visible⟩

end Examples.CSL.Frame.Active.CommonEGActiveRegression
