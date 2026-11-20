/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Policy
public import Logic.Yield.SBisimAlign
public import Logic.Interp.Refine

/-!
# The round-robin instance of the policy runner

`interp_schedule_rr` is `interp_schedule_fair rr_scheduler`, so every node equation is the generic
`interp_schedule_fair_*` one; only selection is RR-specific: a single alternative, logged as
`.inr (slot_index (rr_pick n m))`. Also: round-robin branch refinement preserves guard alignment
(← `CTree/Interp/Yield/RoundRobin.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction
open ITree (Effect)

/-- The round-robin runner: the `rr_scheduler` instance of the event-only policy runner. -/
abbrev interp_schedule_rr {E : Effect.{0}} {W Sg : Type}
    (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (n : Nat) (ts : Pool E Bn n)
    (focus : Option (Fin n)) (m : Nat) (σ : Sg) : ctreeW (W ⊕ Nat) Bn (PUnit × Sg) :=
  interp_schedule_fair rr_scheduler h n ts focus m σ

section RoundRobinInterpretation
variable {E : Effect.{0}} {W Sg : Type} (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

theorem interp_schedule_rr_equ (n : Nat) (ts ts' : Pool E Bn n) (focus : Option (Fin n))
    (m : Nat) (σ : Sg) (hts : pool_equ ts ts') :
    interp_schedule_rr h n ts focus m σ = interp_schedule_rr h n ts' focus m σ :=
  interp_schedule_fair_equ rr_scheduler h n ts ts' focus m σ hts

theorem interp_schedule_rr_empty (ts : Pool E Bn 0) (m : Nat) (σ : Sg) :
    interp_schedule_rr h 0 ts none m σ ~ (pure (⟨⟩, σ) : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) :=
  interp_schedule_fair_empty rr_scheduler h ts m σ

theorem interp_schedule_rr_ret (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (m : Nat)
    (σ : Sg) (hobs : ts[i].unfold = .ret ⟨⟩) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      interp_schedule_rr h n (ts.eraseIdx i) none m σ :=
  interp_schedule_fair_ret rr_scheduler h n ts i m σ hobs

theorem interp_schedule_rr_guard (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .guard t) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      interp_schedule_rr h (n + 1) (ts.set i t) (some i) m σ :=
  interp_schedule_fair_guard rr_scheduler h n ts i t m σ hobs

theorem interp_schedule_rr_step (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .step t) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      .step (interp_schedule_rr h (n + 1) (ts.set i t) (some i) m σ) :=
  interp_schedule_fair_step rr_scheduler h n ts i t m σ hobs

theorem interp_schedule_rr_br (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    {c : Bn.I} (k : Bn.O c → Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .br c k) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      .br c fun x => interp_schedule_rr h (n + 1) (ts.set i (k x)) (some i) m σ := by
  rw [interp_schedule_rr, interp_schedule_fair_br rr_scheduler h n ts i k m σ hobs]
  exact sb_br_id c _ _ fun _ => sb_guard _

theorem interp_schedule_rr_yield (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .vis (.inl ⟨⟩) k) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      interp_schedule_rr h (n + 1) (ts.set i (k ⟨⟩)) none m σ :=
  interp_schedule_fair_yield rr_scheduler h n ts i k m σ hobs

theorem interp_schedule_rr_fork (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E Bn) (m : Nat) (σ : Sg) (hobs : ts[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      interp_schedule_rr h (n + 2) (Vector.cons (k true) (ts.set i (k false))) (some i.succ) m σ :=
  interp_schedule_fair_fork rr_scheduler h n ts i k m σ hobs

theorem interp_schedule_rr_user (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E Bn) (m : Nat) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inr (.inr e)) k) :
    interp_schedule_rr h (n + 1) ts (some i) m σ ~
      (translate relabel_log (h e σ) >>= fun p =>
        interp_schedule_rr h (n + 1) (ts.set i (k p.1)) (some i) m p.2) :=
  interp_schedule_fair_user rr_scheduler h n ts i e k m σ hobs

theorem interp_schedule_rr_stuck (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1)) (m : Nat)
    (σ : Sg) (hstuck : ts[i] = .stuck) :
    interp_schedule_rr h (n + 1) ts (some i) m σ = .stuck :=
  interp_schedule_fair_stuck rr_scheduler h n ts i m σ hstuck

theorem interp_schedule_rr_user_bind (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (e : E.I) (k : E.O e → Thread E Bn) (m : Nat) (σ : Sg)
    (hnode : t = .vis (.inr (.inr e)) k) :
    interp_schedule_rr h (n + 1) (ts.set i t) (some i) m σ ~
      (translate relabel_log (h e σ) >>= fun p =>
        interp_schedule_rr h (n + 1) (ts.set i (k p.1)) (some i) m p.2) :=
  interp_schedule_fair_user_bind rr_scheduler h n ts i t e k m σ hnode

/-- The scheduling point: one logged pick, then the focused pool. -/
theorem interp_schedule_rr_select_exact (n : Nat) (ts : Pool E Bn (n + 1)) (m : Nat) (σ : Sg) :
    interp_schedule_rr h (n + 1) ts none m σ =
      .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (rr_pick n m))) fun _ =>
        .guard (interp_schedule_rr h (n + 1) ts (some (rr_pick n m)) (m + 1) σ) := by
  have e : schedule_policy rr_scheduler (n + 1) ts none m =
      CTree.vis (E := E ⊕ₑ schedE) (.inr (slot_index (rr_pick n m))) fun _ =>
        schedule_policy rr_scheduler (n + 1) ts (some (rr_pick n m)) (m + 1) :=
    (schedule_policy_no_focus_nonempty rr_scheduler n ts m).trans rfl
  refine (congrArg (fun t => interp_state (policy_handler h) t σ) e).trans ?_
  simp only [interp_state_vis, policy_handler, sched_handler, vis_bind, pure_bind]
  rfl

/-- The scheduling point: the round-robin pick is one logged event. -/
theorem interp_schedule_rr_select (n : Nat) (ts : Pool E Bn (n + 1)) (m : Nat) (σ : Sg) :
    interp_schedule_rr h (n + 1) ts none m σ ~
      .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (rr_pick n m))) fun _ =>
        interp_schedule_rr h (n + 1) ts (some (rr_pick n m)) (m + 1) σ := by
  rw [interp_schedule_rr_select_exact]
  exact sb_vis _ fun _ => sb_guard _

theorem interp_schedule_rr_guard_equ (n : Nat) (ts us : Pool E Bn n) (focus : Option (Fin n))
    (m : Nat) (σ : Sg) (hp : pool_guard_equ ts us) :
    interp_schedule_rr h n ts focus m σ ~ interp_schedule_rr h n us focus m σ :=
  interp_schedule_fair_guard_equ rr_scheduler h n ts us focus m σ hp

end RoundRobinInterpretation

/-! ## Round-robin refinement preserves guard alignment -/

section RoundRobinAlign
variable {E : Effect.{u}} {X : Type u}

theorem run_round_robin_guards (n : Nat) (t : CTree E Bn X) (c : Nat) :
    run_round_robin (guards n t) c = guards n (run_round_robin t c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [guards_succ, guards_succ, unfold_run_round_robin, unfold_guard]
    exact congrArg CTree.guard ih

/-- Guarded `run_round_robin` results of aligned inputs. -/
def rr_rel (T U : CTree E Bn X) : Prop :=
  ∃ (n m : Nat) (t u : CTree E Bn X) (c : Nat), galigned t u ∧
    T = guards n (run_round_robin t c) ∧ U = guards m (run_round_robin u c)

theorem rr_rel_step (T U : CTree E Bn X) (h : rr_rel T U) : GalignF rr_rel T U := by
  obtain ⟨n, m, t, u, c, A, rfl, rfl⟩ := h
  have shift : ∀ (k a : Nat) (s : CTree E Bn X),
      guards k (run_round_robin (guards a s) c) = guards (k + a) (run_round_robin s c) :=
    fun k a s => by rw [run_round_robin_guards, guards_add]
  have rel : ∀ t u : CTree E Bn X, ∀ c, galigned t u →
      rr_rel (run_round_robin t c) (run_round_robin u c) :=
    fun t u c A => ⟨0, 0, t, u, c, A, rfl, rfl⟩
  rcases galigned_unfold.1 A with ⟨a, b, t', u', rfl, rfl, A'⟩ | ⟨a, b, r, rfl, rfl⟩ |
    ⟨a, b, ⟨_ | p⟩, kk, kk', rfl, rfl, Hk⟩ | ⟨a, b, e, kk, kk', rfl, rfl, Hk⟩ | ⟨a, b, rfl, rfl⟩ |
    ⟨a, b, t', u', rfl, rfl, A'⟩
  · refine .guard (n + a) (m + b) _ _ ?_ ?_ (rel t' u' c A') <;>
      rw [run_round_robin_guards, guards_shift]
  · refine .ret (n + a) (m + b) r ?_ ?_ <;>
      rw [shift, unfold_run_round_robin, unfold_ret] <;> rfl
  · refine .stuck (n + a) (m + b) ?_ ?_ <;>
      rw [shift, unfold_run_round_robin, unfold_br] <;> rfl
  · refine .guard (n + a) (m + b) (run_round_robin (kk ⟨rr_pick p c⟩) (c + 1))
      (run_round_robin (kk' ⟨rr_pick p c⟩) (c + 1)) ?_ ?_ (rel _ _ _ (Hk _)) <;>
      rw [shift, unfold_run_round_robin, unfold_br] <;> exact guards_guard _ _
  · refine .vis (n + a) (m + b) e (fun x => run_round_robin (kk x) c)
      (fun x => run_round_robin (kk' x) c) ?_ ?_ (fun x => rel _ _ _ (Hk x)) <;>
      rw [shift, unfold_run_round_robin, unfold_vis] <;> rfl
  · refine .stuck (n + a) (m + b) ?_ ?_ <;>
      rw [shift, unfold_run_round_robin, unfold_stuck] <;> rfl
  · refine .step (n + a) (m + b) (run_round_robin t' c) (run_round_robin u' c) ?_ ?_
      (rel t' u' c A') <;> rw [shift, unfold_run_round_robin, unfold_step] <;> rfl

theorem run_round_robin_galigned (t u : CTree E Bn X) (c : Nat) (h : galigned t u) :
    galigned (run_round_robin t c) (run_round_robin u c) :=
  galigned_coind rr_rel rr_rel_step _ _ ⟨0, 0, t, u, c, h, rfl, rfl⟩

end RoundRobinAlign

-- Not ported: nothing. `rr_rel` is a `def` (Rocq one-constructor inductive `rr_rel_at`).

end Tisl.Yield
