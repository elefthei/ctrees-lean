/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Mod
public import Logic.Interp.Refine
public import Logic.Interp.State
public import Logic.CTree.Trace
public import Logic.Events.Writer

/-!
# The policy-scheduled, instrumented runner

`schedule_policy sch` leaves a `Scheduled i` event at every scheduling decision; here the decision
is logged as `.inr i` next to the program's own observations (`.inl _`), so the interpreted runner
has observation type `W ⊕ Nat`. Also: `translate` helpers and the exact node equations of the
runner (← `CTree/Interp/Yield/Policy.v`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Coinduction
open ITree (Effect)

/-! ## Handlers and the instrumented runner -/

/-- Relabel a program log as a left observation (Rocq `relabel_log : writerE W ~> writerE (W+nat)`,
as a `translate` event morphism). -/
def relabel_log {W : Type} :
    (e : (writerE W).I) →
      (f : (writerE (W ⊕ Nat)).I) × ((writerE (W ⊕ Nat)).O f → (writerE W).O e) :=
  fun w => ⟨.inl w, fun _ => ⟨⟩⟩

/-- Log a scheduling decision as a right observation. -/
def sched_handler {W Sg : Type} :
    (e : schedE.I) → StateT Sg (ctreeW (W ⊕ Nat) Bn) (schedE.O e) :=
  fun i σ => .vis (E := writerE (W ⊕ Nat)) (.inr i) fun _ => pure (⟨⟩, σ)

/-- User events through `h` (relabelled), scheduling decisions through `sched_handler`. -/
def policy_handler {E : Effect.{0}} {W Sg : Type}
    (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) :
    (e : (E ⊕ₑ schedE).I) → StateT Sg (ctreeW (W ⊕ Nat) Bn) ((E ⊕ₑ schedE).O e)
  | .inl e => fun σ => translate relabel_log (h e σ)
  | .inr e => sched_handler e

/-- The policy-scheduled runner, instrumented by `policy_handler h`. -/
def interp_schedule_fair {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
    (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (n : Nat) (ts : Pool E Bn n)
    (focus : Option (Fin n)) (st : sch.sched_state) (σ : Sg) : ctreeW (W ⊕ Nat) Bn (PUnit × Sg) :=
  interp_state (policy_handler h) (schedule_policy sch n ts focus st) σ

/-- Program observations only: scheduling logs never satisfy `fair_obs P`. -/
def fair_obs {W : Type} (P : W → Prop) : W ⊕ Nat → Prop
  | .inl w => P w
  | .inr _ => False

/-! ## `translate` helpers -/

section TranslateHelpers
variable {E F B : Effect.{u}} {X Y : Type u} (f : (e : E.I) → (e' : F.I) × (F.O e' → E.O e))

theorem translate_stuck_node : translate f (.stuck : CTree E B X) = .stuck := translate_stuck f

theorem translate_bind (t : CTree E B X) (k : X → CTree E B Y) :
    translate f (t >>= k) = (translate f t >>= fun x => translate f (k x)) := by
  refine eq_coind_upto (fun a b => ∃ t, a = translate f (t >>= k) ∧
    b = (translate f t >>= fun x => translate f (k x))) ?_ _ _ ⟨t, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  cases t with
  | ret x => simp only [pure_bind, translate_ret]; exact EqF.refl (fun _ => .inr rfl) _
  | stuck => simp only [stuck_bind, translate_stuck, unfold_stuck]; exact .stuck
  | step t => simp only [step_bind, translate_step, unfold_step]; exact .step (.inl ⟨t, rfl, rfl⟩)
  | guard t =>
    simp only [guard_bind, translate_guard, unfold_guard]; exact .guard (.inl ⟨t, rfl, rfl⟩)
  | vis e k' =>
    simp only [vis_bind, translate_vis, unfold_vis]; exact .vis _ fun x => .inl ⟨_, rfl, rfl⟩
  | br c k' => simp only [br_bind, translate_br, unfold_br]; exact .br c fun x => .inl ⟨_, rfl, rfl⟩

@[grind =] theorem translate_mapConst (x : X) (t : CTree E B Y) :
    translate f (Functor.mapConst x t) = Functor.mapConst x (translate f t) := by
  show translate f (t >>= fun _ => pure x) = (translate f t >>= fun _ => pure x)
  rw [translate_bind]; simp only [translate_ret]

end TranslateHelpers

theorem translate_emit_list {W X : Type} (os : List W) (t : ctreeW W Bn X) :
    translate relabel_log (emit_list os t) = emit_list (os.map .inl) (translate relabel_log t) := by
  induction os with
  | nil => rfl
  | cons o os ih => simp only [emit_list_cons, translate_vis, List.map_cons]; rw [← ih]; rfl

theorem translate_log_bind {W X : Type} (o : W) (t : ctreeW W Bn X) :
    translate relabel_log (log o >>= fun _ => t) =
      (log (.inl o) >>= fun _ => translate relabel_log t) := by
  simp only [log, vis_bind, pure_bind, translate_vis]; rfl

@[grind =] theorem translate_log {W : Type} (o : W) :
    translate relabel_log (log o : ctreeW W Bn PUnit) = log (.inl o) := by
  simp only [log, translate_vis, translate_ret]; rfl

/-- A relabelled trigger interpretation is the relabelled handler response up to the trigger's
administrative guard. -/
theorem translate_interp_state_trigger_bind {E : Effect.{0}} {W Sg X : Type}
    (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (e : E.I)
    (k : E.O e × Sg → ctreeW (W ⊕ Nat) Bn X) (σ : Sg) :
    (translate relabel_log (interp_state h (CTree.trigger e : CTree E Bn (E.O e)) σ) >>= k) ~
      (translate relabel_log (h e σ) >>= k) := by
  rw [interp_state_trigger, translate_bind, bind_assoc]
  refine sbisim_bind_eq _ fun x => ?_
  simp only [translate_guard, translate_ret, guard_bind, pure_bind]
  exact sb_guard _

/-! ## `translate` preserves strong bisimulation -/

section TranslateSBisim
variable {E F B : Effect.{u}} {X : Type u} (f : (e : E.I) → (e' : F.I) × (F.O e' → E.O e))

/-- How `translate f` relabels a transition (Rocq `translate_label`; a relation because a Lean
event morphism maps answers backwards, `F.O (f e).1 → E.O e`). -/
inductive TranslateLabel : Label E → Label F → Prop
  | tau : TranslateLabel .tau .tau
  | obs (e : E.I) (y : F.O (f e).1) : TranslateLabel (.obs e ((f e).2 y)) (.obs (f e).1 y)
  | val {Y : Type u} (x : Y) : TranslateLabel (.val x) (.val x)

theorem trans_translate {l : Label E} {l' : Label F} {t t' : CTree E B X}
    (hl : TranslateLabel f l l') (h : CTree.trans l t t') :
    CTree.trans l' (translate f t) (translate f t') := by
  unfold CTree.trans at h
  generalize ht : t.unfold = ot at h
  induction h generalizing t l' with
  | br x _ ih =>
    obtain rfl := unfold_inj (ht.trans (unfold_br _ _).symm)
    rw [translate_br]; exact trans_br x (ih hl rfl)
  | guard _ ih =>
    obtain rfl := unfold_inj (ht.trans (unfold_guard _).symm)
    rw [translate_guard]; exact trans_guard (ih hl rfl)
  | step =>
    obtain rfl := unfold_inj (ht.trans (unfold_step _).symm)
    cases hl; rw [translate_step]; exact trans_step _
  | obs x =>
    obtain rfl := unfold_inj (ht.trans (unfold_vis _ _).symm)
    cases hl with
    | obs e y => rw [translate_vis]; exact trans_vis y _
  | val =>
    obtain rfl := unfold_inj (ht.trans (unfold_ret _).symm)
    cases hl
    show trans _ (translate f (pure _)) _
    rw [translate_ret, translate_stuck]; exact trans_ret _

theorem trans_translate_inv {l' : Label F} {t : CTree E B X} {u' : CTree F B X}
    (h : CTree.trans l' (translate f t) u') :
    ∃ l t', TranslateLabel f l l' ∧ CTree.trans l t t' ∧ u' = translate f t' := by
  unfold CTree.trans at h
  generalize ht : (translate f t).unfold = ot at h
  induction h generalizing t with
  | br x _ ih =>
    cases t <;> simp only [translate_ret, translate_stuck, translate_step, translate_guard,
      translate_vis, translate_br, unfold_pure, unfold_stuck, unfold_step, unfold_guard,
      unfold_vis, unfold_br, reduceCtorEq] at ht
    case br c k =>
      cases ht
      obtain ⟨l, t', hl, ht', rfl⟩ := ih (t := k x) rfl
      exact ⟨l, t', hl, trans_br x ht', rfl⟩
  | guard _ ih =>
    cases t <;> simp only [translate_ret, translate_stuck, translate_step, translate_guard,
      translate_vis, translate_br, unfold_pure, unfold_stuck, unfold_step, unfold_guard,
      unfold_vis, unfold_br, reduceCtorEq] at ht
    case guard t =>
      cases ht
      obtain ⟨l, t', hl, ht', rfl⟩ := ih (t := t) rfl
      exact ⟨l, t', hl, trans_guard ht', rfl⟩
  | step =>
    cases t <;> simp only [translate_ret, translate_stuck, translate_step, translate_guard,
      translate_vis, translate_br, unfold_pure, unfold_stuck, unfold_step, unfold_guard,
      unfold_vis, unfold_br, reduceCtorEq] at ht
    case step t =>
      cases ht
      exact ⟨.tau, t, .tau, trans_step t, rfl⟩
  | obs y =>
    cases t <;> simp only [translate_ret, translate_stuck, translate_step, translate_guard,
      translate_vis, translate_br, unfold_pure, unfold_stuck, unfold_step, unfold_guard,
      unfold_vis, unfold_br, reduceCtorEq] at ht
    case vis e k =>
      cases ht
      exact ⟨.obs e ((f e).2 y), k ((f e).2 y), .obs e y, trans_vis _ k, rfl⟩
  | val =>
    cases t <;> simp only [translate_ret, translate_stuck, translate_step, translate_guard,
      translate_vis, translate_br, unfold_pure, unfold_stuck, unfold_step, unfold_guard,
      unfold_vis, unfold_br, reduceCtorEq] at ht
    case ret r =>
      cases ht
      exact ⟨.val _, .stuck, .val _, trans_ret _, (translate_stuck f).symm⟩

/-- `translate` preserves strong bisimulation (Rocq instance `translate_sbisim`). -/
theorem translate_sbisim {t u : CTree E B X} (h : t ~ u) : translate f t ~ translate f u := by
  let R : Rel (CTree F B X) (CTree F B X) := fun a b =>
    ∃ t u, t ~ u ∧ a = translate f t ∧ b = translate f u
  have key : R ≤ sb Eq R := by
    rintro _ _ ⟨t, u, htu, rfl, rfl⟩
    refine ⟨fun l' a' ha => ?_, fun l' b' hb => ?_⟩
    · obtain ⟨l, t', hl, ht', rfl⟩ := trans_translate_inv f ha
      obtain ⟨_, u', hu', htu', rfl⟩ := (sbisim_unfold.1 htu).1 l t' ht'
      exact ⟨l', translate f u', trans_translate f hl hu', ⟨t', u', htu', rfl, rfl⟩, rfl⟩
    · obtain ⟨l, u', hl, hu', rfl⟩ := trans_translate_inv f hb
      obtain ⟨_, t', ht', htu', rfl⟩ := (sbisim_unfold.1 htu).2 l u' hu'
      exact ⟨l', translate f t', trans_translate f hl ht', ⟨t', u', htu', rfl, rfl⟩, rfl⟩
  exact le_gfp key _ _ ⟨t, u, h, rfl, rfl⟩

end TranslateSBisim

/-! ## Structural equations of the instrumented runner -/

section FairInterpretation
variable {E : Effect.{0}} {W Sg : Type} (sch : Scheduler)
  (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e))

/-- Rocq `pool_equ ts ts'` hypothesis, stated pointwise. -/
theorem interp_schedule_fair_equ (n : Nat) (ts ts' : Pool E Bn n) (focus : Option (Fin n))
    (st : sch.sched_state) (σ : Sg) (hts : ∀ i : Fin n, ts[i] = ts'[i]) :
    interp_schedule_fair sch h n ts focus st σ = interp_schedule_fair sch h n ts' focus st σ := by
  rw [Vector.ext fun i hi => hts ⟨i, hi⟩]

theorem interp_schedule_fair_empty (ts : Pool E Bn 0) (st : sch.sched_state) (σ : Sg) :
    interp_schedule_fair sch h 0 ts none st σ ~
      (pure (⟨⟩, σ) : ctreeW (W ⊕ Nat) Bn (PUnit × Sg)) := by
  have : schedule_policy sch 0 ts none st = pure ⟨⟩ :=
    unfold_inj (by rw [schedule_policy_empty_none, unfold_pure])
  rw [interp_schedule_fair, this, interp_state_ret]; exact sbisim_refl _

/-! ### Exact (`=`) node equations -/

theorem interp_schedule_fair_ret_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (σ : Sg) (hobs : ts[i].unfold = .ret ⟨⟩) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      .guard (interp_schedule_fair sch h n (ts.eraseIdx i) none st σ) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .guard (schedule_policy sch n (ts.eraseIdx i) none st) :=
    unfold_inj (by rw [schedule_policy_focused_ret sch n ts i st hobs, unfold_guard])
  simp only [interp_schedule_fair, this, interp_state_guard]

theorem interp_schedule_fair_guard_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (st : sch.sched_state) (σ : Sg) (hobs : ts[i].unfold = .guard t) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      .guard (interp_schedule_fair sch h (n + 1) (ts.set i t) (some i) st σ) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .guard (schedule_policy sch (n + 1) (ts.set i t) (some i) st) :=
    unfold_inj (by rw [schedule_policy_focused_guard sch n ts i t st hobs, unfold_guard])
  simp only [interp_schedule_fair, this, interp_state_guard]

theorem interp_schedule_fair_step_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (st : sch.sched_state) (σ : Sg) (hobs : ts[i].unfold = .step t) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      .step (.guard (interp_schedule_fair sch h (n + 1) (ts.set i t) (some i) st σ)) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .step (schedule_policy sch (n + 1) (ts.set i t) (some i) st) :=
    unfold_inj (by rw [schedule_policy_focused_step sch n ts i t st hobs, unfold_step])
  simp only [interp_schedule_fair, this, interp_state_step]

/-- The event-only property: a thread-internal branch is kept as is. -/
theorem interp_schedule_fair_br (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    {c : Bn.I} (k : Bn.O c → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .br c k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      .br c fun j =>
        .guard (interp_schedule_fair sch h (n + 1) (ts.set i (k j)) (some i) st σ) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .br c fun j => schedule_policy sch (n + 1) (ts.set i (k j)) (some i) st :=
    unfold_inj (by rw [schedule_policy_focused_br sch n ts i k st hobs, unfold_br])
  simp only [interp_schedule_fair, this, interp_state_br, CTree.branch', CTree.br', br_bind,
    pure_bind]
  rfl

theorem interp_schedule_fair_yield_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inl ⟨⟩) k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      .guard (interp_schedule_fair sch h (n + 1) (ts.set i (k ⟨⟩)) none st σ) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .guard (schedule_policy sch (n + 1) (ts.set i (k ⟨⟩)) none st) :=
    unfold_inj (by rw [schedule_policy_focused_yield sch n ts i k st hobs, unfold_guard])
  simp only [interp_schedule_fair, this, interp_state_guard]

theorem interp_schedule_fair_fork_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      .guard (interp_schedule_fair sch h (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) st σ) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .guard (schedule_policy sch (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) st) :=
    unfold_inj (by rw [schedule_policy_focused_fork sch n ts i k st hobs, unfold_guard])
  simp only [interp_schedule_fair, this, interp_state_guard]

theorem interp_schedule_fair_user_exact (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inr (.inr e)) k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ =
      (translate relabel_log (h e σ) >>= fun p =>
        .guard (interp_schedule_fair sch h (n + 1) (ts.set i (k p.1)) (some i) st p.2)) := by
  have : schedule_policy sch (n + 1) ts (some i) st =
      .vis (.inl e) fun x => schedule_policy sch (n + 1) (ts.set i (k x)) (some i) st :=
    unfold_inj (by rw [schedule_policy_focused_user_event sch n ts i e k st hobs, unfold_vis])
  simp only [interp_schedule_fair, this, interp_state_vis]
  rfl

theorem interp_schedule_fair_stuck (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (σ : Sg) (hstuck : ts[i] = .stuck) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ = .stuck := by
  have : schedule_policy sch (n + 1) ts (some i) st = .stuck :=
    unfold_inj (by
      rw [schedule_policy_focused_stuck sch n ts i st (by rw [hstuck, unfold_stuck]), unfold_stuck])
  simp only [interp_schedule_fair, this, interp_state_stuck]

/-! ### Node equations up to strong bisimulation -/

theorem interp_schedule_fair_ret (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (st : sch.sched_state) (σ : Sg) (hobs : ts[i].unfold = .ret ⟨⟩) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ ~
      interp_schedule_fair sch h n (ts.eraseIdx i) none st σ := by
  rw [interp_schedule_fair_ret_exact sch h n ts i st σ hobs]; exact sb_guard _

theorem interp_schedule_fair_guard (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (st : sch.sched_state) (σ : Sg) (hobs : ts[i].unfold = .guard t) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ ~
      interp_schedule_fair sch h (n + 1) (ts.set i t) (some i) st σ := by
  rw [interp_schedule_fair_guard_exact sch h n ts i t st σ hobs]; exact sb_guard _

theorem interp_schedule_fair_step (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (st : sch.sched_state) (σ : Sg) (hobs : ts[i].unfold = .step t) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ ~
      .step (interp_schedule_fair sch h (n + 1) (ts.set i t) (some i) st σ) := by
  rw [interp_schedule_fair_step_exact sch h n ts i t st σ hobs]; exact sb_step (sb_guard _)

theorem interp_schedule_fair_yield (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inl ⟨⟩) k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ ~
      interp_schedule_fair sch h (n + 1) (ts.set i (k ⟨⟩)) none st σ := by
  rw [interp_schedule_fair_yield_exact sch h n ts i k st σ hobs]; exact sb_guard _

theorem interp_schedule_fair_fork (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ ~
      interp_schedule_fair sch h (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) st σ := by
  rw [interp_schedule_fair_fork_exact sch h n ts i k st σ hobs]; exact sb_guard _

theorem interp_schedule_fair_user (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E Bn) (st : sch.sched_state) (σ : Sg)
    (hobs : ts[i].unfold = .vis (.inr (.inr e)) k) :
    interp_schedule_fair sch h (n + 1) ts (some i) st σ ~
      (translate relabel_log (h e σ) >>= fun p =>
        interp_schedule_fair sch h (n + 1) (ts.set i (k p.1)) (some i) st p.2) := by
  rw [interp_schedule_fair_user_exact sch h n ts i e k st σ hobs]
  exact sbisim_bind_eq _ fun _ => sb_guard _

/-- The scheduling point: the policy's alternatives, each logging its slot and continuing in the
focused pool. -/
theorem interp_schedule_fair_select (n : Nat) (ts : Pool E Bn (n + 1)) (st : sch.sched_state)
    (σ : Sg) :
    interp_schedule_fair sch h (n + 1) ts none st σ ~
      br_alts (sch.sched_arity n st) fun a =>
        .vis (E := writerE (W ⊕ Nat)) (.inr (slot_index (sch.sched_pick n st a).1)) fun _ =>
          interp_schedule_fair sch h (n + 1) ts (some (sch.sched_pick n st a).1)
            (sch.sched_pick n st a).2 σ := by
  rw [interp_schedule_fair, schedule_policy_no_focus_nonempty]
  refine sbisim_trans (interp_state_br_alts_sb _ _ _ _) (br_alts_sbisim _ fun a => ?_)
  simp only [interp_state_vis, policy_handler, sched_handler, vis_bind, pure_bind]
  exact sb_vis _ fun _ => sb_guard _

/-- Keep one scheduler continuation fixed while interpreting a raw user event. -/
@[grind =>] theorem interp_schedule_fair_user_bind (n : Nat) (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) (t : Thread E Bn) (e : E.I) (k : E.O e → Thread E Bn)
    (st : sch.sched_state) (σ : Sg)
    (hnode : t = .vis (.inr (.inr e)) k) :
    interp_schedule_fair sch h (n + 1) (ts.set i t) (some i) st σ ~
      (translate relabel_log (h e σ) >>= fun p =>
        interp_schedule_fair sch h (n + 1) (ts.set i (k p.1)) (some i) st p.2) := by
  subst hnode
  have := interp_schedule_fair_user sch h n (ts.set i (.vis (.inr (.inr e)) k)) i e k st σ
    (by simp)
  simpa only [Vector.set_set] using this

/-! The focused-slot laws with the slot written by `set`, as the runner equations meet them. -/

@[grind .] theorem interp_schedule_fair_yield_set (n : Nat) (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) (k : PUnit → Thread E Bn) (st : sch.sched_state) (σ : Sg) :
    interp_schedule_fair sch h (n + 1) (ts.set i (.vis (.inl ⟨⟩) k)) (some i) st σ ~
      interp_schedule_fair sch h (n + 1) (ts.set i (k ⟨⟩)) none st σ := by
  have hy := interp_schedule_fair_yield sch h n (ts.set i (.vis (.inl ⟨⟩) k)) i k st σ
    (by rw [Fin.getElem_fin, Vector.getElem_set_self, unfold_vis])
  rwa [Vector.set_set] at hy

@[grind .] theorem interp_schedule_fair_fork_set (n : Nat) (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) (k : Bool → Thread E Bn) (st : sch.sched_state) (σ : Sg) :
    interp_schedule_fair sch h (n + 1) (ts.set i (.vis (.inr (.inl ⟨⟩)) k)) (some i) st σ ~
      interp_schedule_fair sch h (n + 2) (Vector.cons (k true) (ts.set i (k false)))
        (some i.succ) st σ := by
  have hf := interp_schedule_fair_fork sch h n (ts.set i (.vis (.inr (.inl ⟨⟩)) k)) i k st σ
    (by rw [Fin.getElem_fin, Vector.getElem_set_self, unfold_vis])
  rwa [Vector.set_set] at hf

@[grind =] theorem interp_schedule_fair_stuck_set (n : Nat) (ts : Pool E Bn (n + 1))
    (i : Fin (n + 1)) (st : sch.sched_state) (σ : Sg) :
    interp_schedule_fair sch h (n + 1) (ts.set i .stuck) (some i) st σ = .stuck :=
  interp_schedule_fair_stuck sch h n _ i st σ (by rw [Fin.getElem_fin, Vector.getElem_set_self])

/-! ### Focused-slot congruence -/

theorem segment_fair_replace_equ (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t u : Thread E Bn) (focus : Option (Fin (n + 1))) (st : sch.sched_state) (σ : Sg)
    (heq : t = u) :
    interp_schedule_fair sch h (n + 1) (ts.set i t) focus st σ ~
      interp_schedule_fair sch h (n + 1) (ts.set i u) focus st σ := by
  subst heq; exact sbisim_refl _

theorem segment_fair_focused_guard (n : Nat) (ts : Pool E Bn (n + 1)) (i : Fin (n + 1))
    (t : Thread E Bn) (st : sch.sched_state) (σ : Sg) :
    interp_schedule_fair sch h (n + 1) (ts.set i (.guard t)) (some i) st σ ~
      interp_schedule_fair sch h (n + 1) (ts.set i t) (some i) st σ := by
  have := interp_schedule_fair_guard sch h n (ts.set i (.guard t)) i t st σ (by simp)
  simpa only [Vector.set_set] using this

end FairInterpretation

/-- A standalone thread interpreted through the policy handler is the relabelled plain
interpretation: the policy handler only relabels user-event responses. -/
theorem interp_state_policy_translate {E : Effect.{0}} {W Sg X : Type}
    (h : (e : E.I) → StateT Sg (ctreeW W Bn) (E.O e)) (u : CTree E Bn X) (σ : Sg) :
    interp_state (policy_handler h)
        (translate (fun e => (⟨.inl e, id⟩ : (f : (E ⊕ₑ schedE).I) × ((E ⊕ₑ schedE).O f → E.O e)))
          u) σ =
      translate relabel_log (interp_state h u σ) := by
  let ι : (e : E.I) → (f : (E ⊕ₑ schedE).I) × ((E ⊕ₑ schedE).O f → E.O e) := fun e => ⟨.inl e, id⟩
  let I : CTree E Bn X → Sg → ctreeW (W ⊕ Nat) Bn (X × Sg) := fun u σ =>
    interp_state (policy_handler h) (translate ι u) σ
  let T : CTree E Bn X → Sg → ctreeW (W ⊕ Nat) Bn (X × Sg) := fun u σ =>
    translate relabel_log (interp_state h u σ)
  -- Up to `bind`: both sides share the relabelled handler response `s`.
  let R : CTree (writerE (W ⊕ Nat)) Bn (X × Sg) → CTree (writerE (W ⊕ Nat)) Bn (X × Sg) → Prop :=
    fun a b => (∃ u σ, a = I u σ ∧ b = T u σ) ∨
      ∃ (Y : Type) (s : CTree (writerE (W ⊕ Nat)) Bn Y) (g : Y → CTree E Bn X × Sg),
        a = (s >>= fun y => .guard (I (g y).1 (g y).2)) ∧
        b = (s >>= fun y => .guard (T (g y).1 (g y).2))
  have hbind : ∀ (Y : Type) (s : CTree (writerE (W ⊕ Nat)) Bn Y) (g : Y → CTree E Bn X × Sg),
      EqF (fun a b => R a b ∨ a = b) (s >>= fun y => .guard (I (g y).1 (g y).2)).unfold
        (s >>= fun y => .guard (T (g y).1 (g y).2)).unfold := by
    intro Y s g
    cases s with
    | ret y => simp only [pure_bind, unfold_guard]; exact .guard (.inl (.inl ⟨_, _, rfl, rfl⟩))
    | stuck => simp only [stuck_bind, unfold_stuck]; exact .stuck
    | step s => simp only [step_bind, unfold_step]; exact .step (.inl (.inr ⟨Y, s, g, rfl, rfl⟩))
    | guard s =>
      simp only [guard_bind, unfold_guard]; exact .guard (.inl (.inr ⟨Y, s, g, rfl, rfl⟩))
    | vis e k =>
      simp only [vis_bind, unfold_vis]; exact .vis e fun x => .inl (.inr ⟨Y, k x, g, rfl, rfl⟩)
    | br c k =>
      simp only [br_bind, unfold_br]; exact .br c fun x => .inl (.inr ⟨Y, k x, g, rfl, rfl⟩)
  refine eq_coind_upto R ?_ _ _ (.inl ⟨u, σ, rfl, rfl⟩)
  rintro _ _ (⟨u, σ, rfl, rfl⟩ | ⟨Y, s, g, rfl, rfl⟩)
  · cases u with
    | ret x => simp only [I, T, translate_ret, interp_state_ret]; exact .ret _
    | stuck => simp only [I, T, translate_stuck, interp_state_stuck, unfold_stuck]; exact .stuck
    | step t =>
      simp only [I, T, translate_step, interp_state_step, translate_guard, unfold_step]
      exact .step (.inl (.inr ⟨PUnit, pure ⟨⟩, fun _ => (t, σ), by simp [I], by simp [T]⟩))
    | guard t =>
      simp only [I, T, translate_guard, interp_state_guard, unfold_guard]
      exact .guard (.inl (.inl ⟨t, σ, rfl, rfl⟩))
    | vis e k =>
      have e1 : I (.vis e k) σ =
          (translate relabel_log (h e σ) >>= fun y => .guard (I (k y.1) y.2)) := by
        simp only [I, translate_vis, interp_state_vis]; rfl
      have e2 : T (.vis e k) σ =
          (translate relabel_log (h e σ) >>= fun y => .guard (T (k y.1) y.2)) := by
        simp only [T, interp_state_vis, translate_bind, translate_guard]
      rw [e1, e2]; exact hbind _ _ fun (y : E.O e × Sg) => (k y.1, y.2)
    | br c k =>
      simp only [I, T, translate_br, interp_state_br, CTree.branch', CTree.br', br_bind,
        pure_bind, translate_guard, unfold_br]
      exact .br _ fun x => .inl (.inr ⟨PUnit, pure ⟨⟩,
        fun _ => (k ((ITree.Subeffect.map c).2 x), σ), by simp [I], by simp [T]⟩)
  · exact hbind Y s g

-- Not ported: `interp_schedule_fair_guard_equ` (moved to `Logic/Yield/SBisimAlign.lean`: needs
-- the galigned scheduler theorems of `Logic/Yield/SBisim*`); `trans_translate_`,
-- `trans_translate_inv_` (`trans_` helpers of the `observe`-level induction, folded into
-- `trans_translate`/`trans_translate_inv`). `translate_label` is the relation `TranslateLabel`.

end Tisl.Yield
