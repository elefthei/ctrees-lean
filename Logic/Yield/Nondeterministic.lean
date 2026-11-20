/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Mod
public import Logic.Interp.State

/-!
# Nondeterministic scheduling interpretation

The native pool scheduler records each selected slot. This program-only view projects that
observation to one silent step, then interprets user effects with an arbitrary state handler
(← `CTree/Interp/Yield/Nondeterministic.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction
open ITree (Effect)

section NondeterministicInterpretation
variable {E F B : Effect.{0}} [Bn -< B] {Sg : Type}

/-- Schedule nondeterministically, project selections to silent steps, interpret user effects. -/
def interp_schedule_nd (handler : (e : E.I) → StateT Sg (CTree F B) (E.O e)) (n : Nat)
    (ts : Pool E B n) (focus : Option (Fin n)) (σ : Sg) : CTree F B (PUnit × Sg) :=
  interp_state handler (project_scheduled (schedule n ts focus)) σ

variable (handler : (e : E.I) → StateT Sg (CTree F B) (E.O e))

/-- Rocq `pool_equ ts ts'` hypothesis, stated pointwise. -/
theorem interp_schedule_nd_equ (n : Nat) (ts ts' : Pool E B n) (focus : Option (Fin n)) (σ : Sg)
    (hts : ∀ i : Fin n, ts[i] = ts'[i]) :
    interp_schedule_nd handler n ts focus σ = interp_schedule_nd handler n ts' focus σ := by
  rw [Vector.ext fun i hi => hts ⟨i, hi⟩]

/-- Any zero-length pool, not only the literal empty vector: removing the last slot yields an
abstract `ts.eraseIdx i` of length zero. -/
theorem interp_schedule_nd_empty (ts : Pool E B 0) (σ : Sg) :
    interp_schedule_nd handler 0 ts none σ ~ (pure (⟨⟩, σ) : CTree F B (PUnit × Sg)) := by
  have : schedule 0 ts none = pure ⟨⟩ := unfold_inj (by rw [schedule_empty_none, unfold_pure])
  rw [interp_schedule_nd, this, project_scheduled_ret, interp_state_ret]; exact sbisim_refl _

theorem interp_schedule_nd_ret (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (σ : Sg)
    (hobs : ts[i].unfold = .ret ⟨⟩) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      interp_schedule_nd handler n (ts.eraseIdx i) none σ := by
  have : schedule (n + 1) ts (some i) = .guard (schedule n (ts.eraseIdx i) none) :=
    unfold_inj (by rw [schedule_focused_ret n ts i hobs, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]
  exact sb_guard _

theorem interp_schedule_nd_guard (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (σ : Sg) (hobs : ts[i].unfold = .guard t) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      interp_schedule_nd handler (n + 1) (ts.set i t) (some i) σ := by
  have : schedule (n + 1) ts (some i) = .guard (schedule (n + 1) (ts.set i t) (some i)) :=
    unfold_inj (by rw [schedule_focused_guard n ts i t hobs, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]
  exact sb_guard _

/-- A visible step of the focused thread is one visible step of the pool. -/
theorem interp_schedule_nd_step (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (σ : Sg) (hobs : ts[i].unfold = .step t) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      .step (interp_schedule_nd handler (n + 1) (ts.set i t) (some i) σ) := by
  have : schedule (n + 1) ts (some i) = .step (schedule (n + 1) (ts.set i t) (some i)) :=
    unfold_inj (by rw [schedule_focused_step n ts i t hobs, unfold_step])
  simp only [interp_schedule_nd, this, project_scheduled_step, interp_state_step,
    interp_state_guard]
  exact sb_step (sb_guard_l (sb_guard _))

/-- Program choices remain choices and do not select another pool slot. -/
theorem interp_schedule_nd_br (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) {c : B.I}
    (k : B.O c → Thread E B) (σ : Sg) (hobs : ts[i].unfold = .br c k) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      .br c fun x => interp_schedule_nd handler (n + 1) (ts.set i (k x)) (some i) σ := by
  have : schedule (n + 1) ts (some i) =
      .br c fun x => schedule (n + 1) (ts.set i (k x)) (some i) :=
    unfold_inj (by rw [schedule_focused_br n ts i k hobs, unfold_br])
  simp only [interp_schedule_nd, this, project_scheduled_br, interp_state_br, CTree.branch',
    CTree.br', br_bind, pure_bind, interp_state_guard]
  exact sb_br_id _ _ _ fun _ => sb_guard_l (sb_guard _)

theorem interp_schedule_nd_yield (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (σ : Sg) (hobs : ts[i].unfold = .vis (.inl ⟨⟩) k) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      interp_schedule_nd handler (n + 1) (ts.set i (k ⟨⟩)) none σ := by
  have : schedule (n + 1) ts (some i) = .guard (schedule (n + 1) (ts.set i (k ⟨⟩)) none) :=
    unfold_inj (by rw [schedule_focused_yield n ts i k hobs, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]
  exact sb_guard _

/-- The uniform visible-choice law, also at the singleton boundary (needs a lawful `Bn -< B` so
that the one-way branch of `brSn 1` is inhabited). -/
theorem interp_schedule_nd_select [LawfulSubeffect Bn B] (n : Nat) (ts : Pool E B (n + 1))
    (σ : Sg) :
    interp_schedule_nd handler (n + 1) ts none σ ~
      CTree.brSn (n + 1) fun i => interp_schedule_nd handler (n + 1) ts (some i) σ := by
  rw [interp_schedule_nd, schedule_no_focus_nonempty]
  cases n with
  | zero =>
    simp only [project_scheduled_scheduled, interp_state_step, interp_state_guard, CTree.brSn,
      CTree.brS', CTree.br']
    obtain ⟨y, -⟩ := LawfulSubeffect.map_surj (E₁ := Bn) (E₂ := B) (⟨1⟩ : Bn.I) ⟨0⟩
    refine sbisim_symm (sb_br_l _ y _ _ fun x => ?_)
    rw [fin1_eq ((ITree.Subeffect.map (E₁ := Bn) (E₂ := B) (⟨1⟩ : Bn.I)).2 x).down]
    exact sb_step (sbisim_symm (sb_guard_l (sb_guard _)))
  | succ m =>
    simp only [CTree.brn, CTree.brSn, CTree.brS', CTree.br', project_scheduled_br,
      project_scheduled_scheduled, interp_state_br, CTree.branch', br_bind, pure_bind,
      interp_state_guard, interp_state_step]
    refine sb_br_id _ _ _ fun x => ?_
    exact sb_guard_l (sb_guard_l (sb_step (sb_guard_l (sb_guard _))))

theorem interp_schedule_nd_fork (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (σ : Sg) (hobs : ts[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      interp_schedule_nd handler (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) σ := by
  have : schedule (n + 1) ts (some i) =
      .guard (schedule (n + 2) (Vector.cons (k true) (ts.set i (k false))) (some i.succ)) :=
    unfold_inj (by rw [schedule_focused_fork n ts i k hobs, unfold_guard])
  simp only [interp_schedule_nd, this, project_scheduled_guard, interp_state_guard]
  exact sb_guard _

theorem interp_schedule_nd_user (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (e : E.I)
    (k : E.O e → Thread E B) (σ : Sg) (hobs : ts[i].unfold = .vis (.inr (.inr e)) k) :
    interp_schedule_nd handler (n + 1) ts (some i) σ ~
      (handler e σ >>= fun p =>
        interp_schedule_nd handler (n + 1) (ts.set i (k p.1)) (some i) p.2) := by
  have : schedule (n + 1) ts (some i) =
      .vis (.inl e) fun x => schedule (n + 1) (ts.set i (k x)) (some i) :=
    unfold_inj (by rw [schedule_focused_user_event n ts i e k hobs, unfold_vis])
  simp only [interp_schedule_nd, this, project_scheduled_user, interp_state_vis,
    interp_state_guard]
  exact sbisim_bind_eq _ fun _ => sb_guard_l (sb_guard _)

/-- A focused `stuck` slot makes the whole interpreted pool `stuck`; no other slot ever runs. -/
theorem interp_schedule_nd_stuck (n : Nat) (ts : Pool E B (n + 1)) (i : Fin (n + 1)) (σ : Sg)
    (hstuck : ts[i] = .stuck) :
    interp_schedule_nd handler (n + 1) ts (some i) σ = .stuck := by
  have : schedule (n + 1) ts (some i) = .stuck :=
    unfold_inj (by rw [schedule_focused_stuck n ts i (by rw [hstuck, unfold_stuck]), unfold_stuck])
  simp only [interp_schedule_nd, this, project_scheduled_stuck, interp_state_stuck]

/-- Keep one scheduler continuation fixed while interpreting a raw user event. -/
@[grind =>] theorem interp_schedule_nd_user_bind (n : Nat) (ts : Pool E B (n + 1))
    (i : Fin (n + 1)) (t : Thread E B) (e : E.I) (k : E.O e → Thread E B) (σ : Sg)
    (hnode : t = .vis (.inr (.inr e)) k) :
    interp_schedule_nd handler (n + 1) (ts.set i t) (some i) σ ~
      (interp_state handler (CTree.trigger e : CTree E B (E.O e)) σ >>= fun p =>
        interp_schedule_nd handler (n + 1) (ts.set i (k p.1)) (some i) p.2) := by
  subst hnode
  have := interp_schedule_nd_user handler n (ts.set i (.vis (.inr (.inr e)) k)) i e k σ (by simp)
  simp only [Vector.set_set] at this
  refine sbisim_trans this ?_
  rw [interp_state_trigger, bind_assoc]
  exact sbisim_bind_eq _ fun _ => by
    simp only [guard_bind, pure_bind]; exact sbisim_symm (sb_guard _)

/-! The focused-slot laws with the slot written by `set`, as the runner equations meet them. -/

@[grind .] theorem interp_schedule_nd_yield_set (n : Nat) (ts : Pool E B (n + 1))
    (i : Fin (n + 1)) (k : PUnit → Thread E B) (σ : Sg) :
    interp_schedule_nd handler (n + 1) (ts.set i (.vis (.inl ⟨⟩) k)) (some i) σ ~
      interp_schedule_nd handler (n + 1) (ts.set i (k ⟨⟩)) none σ := by
  have h := interp_schedule_nd_yield handler n (ts.set i (.vis (.inl ⟨⟩) k)) i k σ
    (by rw [Fin.getElem_fin, Vector.getElem_set_self, unfold_vis])
  rwa [Vector.set_set] at h

@[grind .] theorem interp_schedule_nd_fork_set (n : Nat) (ts : Pool E B (n + 1))
    (i : Fin (n + 1)) (k : Bool → Thread E B) (σ : Sg) :
    interp_schedule_nd handler (n + 1) (ts.set i (.vis (.inr (.inl ⟨⟩)) k)) (some i) σ ~
      interp_schedule_nd handler (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) σ := by
  have h := interp_schedule_nd_fork handler n (ts.set i (.vis (.inr (.inl ⟨⟩)) k)) i k σ
    (by rw [Fin.getElem_fin, Vector.getElem_set_self, unfold_vis])
  rwa [Vector.set_set] at h

@[grind =] theorem interp_schedule_nd_stuck_set (n : Nat) (ts : Pool E B (n + 1))
    (i : Fin (n + 1)) (σ : Sg) :
    interp_schedule_nd handler (n + 1) (ts.set i .stuck) (some i) σ = .stuck :=
  interp_schedule_nd_stuck handler n _ i σ (by rw [Fin.getElem_fin, Vector.getElem_set_self])

end NondeterministicInterpretation

/-- The singleton state-update step under `h_stateW`: read the state, write `f` of it, and finish.
Exactly one log of the new state is observable, followed by the return of the emptied pool. -/
theorem interp_schedule_nd_singleton_update {B : Effect.{0}} [Bn -< B] {Sg : Type}
    (f : Sg → Sg) (ts : Pool (stateE Sg) B 1) (σ : Sg)
    (hobs : ts[0].unfold = .vis (.inr (.inr StateOp.get)) fun s =>
      .vis (.inr (.inr (StateOp.put (f s)))) fun _ => pure ⟨⟩) :
    interp_schedule_nd (B := B) h_stateW 1 ts (some 0) σ ~
      (log (f σ) >>= fun _ => pure (⟨⟩, f σ) : ctreeW Sg B (PUnit × Sg)) := by
  refine sbisim_trans (interp_schedule_nd_user h_stateW 0 ts 0 _ _ σ hobs) ?_
  simp only [h_stateW, pure_bind]
  refine sbisim_trans (interp_schedule_nd_user h_stateW 0 _ 0 (StateOp.put (f σ))
    (fun _ => pure ⟨⟩) σ (by simp; rfl)) ?_
  simp only [h_stateW, bind_assoc]
  refine sbisim_bind_eq _ fun _ => ?_
  simp only [pure_bind]
  refine sbisim_trans (interp_schedule_nd_ret h_stateW 0 _ 0 (f σ) (by simp)) ?_
  exact interp_schedule_nd_empty h_stateW _ _

-- Not ported: `interp_schedule_nd_guard_equ` (moved to `Logic/Yield/SBisimAlign.lean`: needs
-- the galigned scheduler theorems of `Logic/Yield/SBisim*`).

end Tisl.Yield
