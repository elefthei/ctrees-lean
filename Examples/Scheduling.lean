/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Fair
public import Logic.Yield.Observed
public import Logic.Yield.RoundRobin
public import Logic.Yield.Nondeterministic
public import Logic.Yield.Segments
public import Logic.Yield.SBisimAlign
public import Logic.CTree.Trans

/-!
# Direct scheduling regressions

Program choices are not scheduling turns: concrete runs of the ND, RR, generic-policy, fair and
offer-instrumented schedulers on small pools of pulsing workers, sampled by fuel-bounded prefix
evaluators (← `examples/Scheduling.v`). Rocq's `vm_compute` checks are proved by `sched_eval`,
which unfolds the scheduler one tree node at a time.
-/

@[expose] public section
namespace Examples.Scheduling
open CTree Tisl Tisl.Yield
open ITree (Effect Subeffect)

/-- Pulse events (Rocq `Pulse n : pulseE unit`). -/
@[implicit_reducible] def pulseE : Effect.{0} := ⟨Nat, fun _ => PUnit⟩
unif_hint (x : pulseE.I) where |- pulseE.O x ≟ PUnit

/-- Emit a pulse, optionally take a hidden singleton branch, yield, repeat. -/
def worker (id : Nat) (internal : Bool) : Thread pulseE Bn :=
  .vis (.inr (.inr id)) fun _ =>
    if internal then
      .br (⟨1⟩ : Bn.I) fun _ => .vis (.inl ⟨⟩) fun _ => worker id internal
    else .vis (.inl ⟨⟩) fun _ => worker id internal
partial_fixpoint

@[simp] theorem worker_unfold (id : Nat) (internal : Bool) :
    (worker id internal).unfold = .vis (.inr (.inr id)) fun _ =>
      if internal then
        .br (⟨1⟩ : Bn.I) fun _ => .vis (.inl ⟨⟩) fun _ => worker id internal
      else .vis (.inl ⟨⟩) fun _ => worker id internal := by
  conv => lhs; rw [worker]
  simp

def worker0 := worker 0 true
def worker1 := worker 1 false
def two_workers : Pool pulseE Bn 2 := #v[worker0, worker1]

/-- Decode a scheduled event: `(false, i)` for `Pulse i`, `(true, i)` for `Scheduled i`. -/
def pulse_or_pick : (e : (pulseE ⊕ₑ schedE).I) → (pulseE ⊕ₑ schedE).O e × (Bool × Nat)
  | .inl i => (⟨⟩, (false, i))
  | .inr i => (⟨⟩, (true, i))

/-- One node of `bounded_prefix`; `rec` is the evaluator at the remaining fuel. Split off so
that unfolding the evaluator never runs ahead of the tree being observed. -/
def bounded_prefix_node {E : Effect.{0}} {A Z X : Type} (decode : (e : E.I) → E.O e × A)
    (keep : A → Option Z) (allow_step : Bool)
    (rec : Nat → List Nat → CTree E Bn X → Option (List Z)) (needed : Nat) (script : List Nat) :
    CTreeF E Bn X (CTree E Bn X) → Option (List Z)
  | .step u => if allow_step then rec (needed + 1) script u else none
  | .guard u => rec (needed + 1) script u
  | .vis e k =>
    let (answer, event) := decode e
    match keep event with
    | none => rec (needed + 1) script (k answer)
    | some z =>
      match rec needed script (k answer) with
      | some zs => some (z :: zs)
      | none => none
  | .br ⟨0⟩ _ => none
  | .br ⟨1⟩ k => rec (needed + 1) script (k ⟨0⟩)
  | .br ⟨m + 2⟩ k =>
    match script with
    | [] => none
    | i :: rest => if hi : i < m + 2 then rec (needed + 1) rest (k ⟨⟨i, hi⟩⟩) else none
  | _ => none

/-- The evaluator is deliberately partial. A prefix is successful only when all requested
observations have been collected. Hidden singleton choices do not consume the script; every
genuinely branching choice does. -/
def bounded_prefix {E : Effect.{0}} {A Z X : Type} (decode : (e : E.I) → E.O e × A)
    (keep : A → Option Z) (allow_step : Bool) :
    (fuel needed : Nat) → List Nat → CTree E Bn X → Option (List Z)
  | _, 0, _, _ => some []
  | 0, _ + 1, _, _ => none
  | fuel + 1, needed + 1, script, t =>
    bounded_prefix_node decode keep allow_step (bounded_prefix decode keep allow_step fuel)
      needed script t.unfold

section Unfold
variable {E : Effect.{0}} {A Z X : Type} (decode : (e : E.I) → E.O e × A)
  (keep : A → Option Z) (allow_step : Bool) (script : List Nat) (t : CTree E Bn X)

theorem bounded_prefix_done (fuel : Nat) :
    bounded_prefix decode keep allow_step fuel 0 script t = some [] := by
  cases fuel <;> rfl

theorem bounded_prefix_no_fuel (needed : Nat) :
    bounded_prefix decode keep allow_step 0 (needed + 1) script t = none := rfl

/-- One evaluation step; the evaluator itself is never unfolded at a partial application. -/
theorem bounded_prefix_succ (fuel needed : Nat) :
    bounded_prefix decode keep allow_step (fuel + 1) (needed + 1) script t =
      bounded_prefix_node decode keep allow_step (bounded_prefix decode keep allow_step fuel)
        needed script t.unfold := rfl

end Unfold

def sample (fuel needed : Nat) (picks : Bool) (script : List Nat) (t : Completed pulseE Bn) :
    Option (List Nat) :=
  bounded_prefix pulse_or_pick
    (fun (is_pick, i) => if picks == is_pick then some i else none)
    true fuel needed script t

def events_sample (fuel needed : Nat) (script : List Nat) (t : Completed pulseE Bn) :
    Option (List (Bool × Nat)) :=
  bounded_prefix pulse_or_pick some true fuel needed script t

/-- A terminated sample: the number of `Step`s, the visible events, and the final value. -/
structure FiniteResult (A X : Type) where
  silent_steps : Nat
  visible_events : List A
  final_value : X

/-- One node of `finish_sample`; `rec` is the evaluator at the remaining fuel. -/
def finish_sample_node {E : Effect.{0}} {A X : Type} (decode : (e : E.I) → E.O e × A)
    (rec : List Nat → CTree E Bn X → Option (FiniteResult A X)) (script : List Nat) :
    CTreeF E Bn X (CTree E Bn X) → Option (FiniteResult A X)
  | .ret x => some ⟨0, [], x⟩
  | .stuck => none
  | .guard u => rec script u
  | .step u =>
    match rec script u with
    | some r => some ⟨r.silent_steps + 1, r.visible_events, r.final_value⟩
    | none => none
  | .vis e k =>
    let (answer, event) := decode e
    match rec script (k answer) with
    | some r => some ⟨r.silent_steps, event :: r.visible_events, r.final_value⟩
    | none => none
  | .br ⟨0⟩ _ => none
  | .br ⟨1⟩ k => rec script (k ⟨0⟩)
  | .br ⟨m + 2⟩ k =>
    match script with
    | [] => none
    | i :: rest => if hi : i < m + 2 then rec rest (k ⟨⟨i, hi⟩⟩) else none

/-- Unlike `bounded_prefix`, this evaluator explicitly demands termination. It counts all
`Step`s and records the final handler state. -/
def finish_sample {E : Effect.{0}} {A X : Type} (decode : (e : E.I) → E.O e × A) :
    (fuel : Nat) → List Nat → CTree E Bn X → Option (FiniteResult A X)
  | 0, _, _ => none
  | fuel + 1, script, t => finish_sample_node decode (finish_sample decode fuel) script t.unfold

theorem finish_sample_no_fuel {E : Effect.{0}} {A X : Type} (decode : (e : E.I) → E.O e × A)
    (script : List Nat) (t : CTree E Bn X) : finish_sample decode 0 script t = none := rfl

/-- One evaluation step; the evaluator itself is never unfolded at a partial application. -/
theorem finish_sample_succ {E : Effect.{0}} {A X : Type} (decode : (e : E.I) → E.O e × A)
    (fuel : Nat) (script : List Nat) (t : CTree E Bn X) :
    finish_sample decode (fuel + 1) script t =
      finish_sample_node decode (finish_sample decode fuel) script t.unfold := rfl

/-! ## Evaluation tactic

`sched_eval` evaluates the samplers above on concrete runs: it unfolds only the `.unfold` of
scheduler, interpreter and `bind` applications, so it never unfolds under continuations. -/

/-- The identity subeffect embedding (used by `CTree.brn` over `Bn`). -/
theorem subeffect_map_refl {E : Effect.{0}} (i : E.I) :
    Subeffect.map (E₁ := E) (E₂ := E) i = ⟨i, fun x => x⟩ := rfl

/-- Evaluate a prefix sampler on a concrete scheduler run (Rocq `vm_compute`). -/
syntax "sched_eval" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| sched_eval) => `(tactic| sched_eval [])
  | `(tactic| sched_eval [$xs,*]) => `(tactic|
    set_option linter.unusedSimpArgs false in
    simp [bounded_prefix_done, bounded_prefix_no_fuel, bounded_prefix_succ, bounded_prefix_node,
      finish_sample_no_fuel, finish_sample_succ, finish_sample_node, subeffect_map_refl, $xs,*,
      congrArg CTree.unfold (schedule_policy.eq_2 _ _ _ _),
      congrArg CTree.unfold (schedule_policy.eq_4 _ _ _ _ _),
      congrArg CTree.unfold (schedule_with_offers.eq_2 _ _),
      congrArg CTree.unfold (schedule_with_offers.eq_4 _ _ _),
      congrArg CTree.unfold (schedule_with_offers_offer_prefix.eq_2 _ _),
      congrArg CTree.unfold (schedule_with_offers_offer_prefix.eq_3 _ _ _),
      congrArg CTree.unfold (schedule_with_offers_offer_prefix.eq_4 _ _ _ _),
      congrArg CTree.unfold (unfold_interp _ _),
      congrArg CTree.unfold (unfold_interp_state _ _ _),
      congrArg CTree.unfold (unfold_translate _ _), unfold_bind,
      schedule, schedule_rr, interp_schedule_fair, interp_schedule_rr, interp_schedule_nd,
      project_scheduled,
      forget_scheduler_offers, handle_scheduled_step, handle_scheduler_offers, policy_handler,
      sched_handler, relabel_log, rr_scheduler, nd_scheduler, br_alts, CTree.brn, CTree.br',
      rr_pick, CTree.branch', CTree.trigger, MonadBr.mbr, live_slot_ref])

/-! ## 1. RR advances only at pool selections, never at source branches -/

def rr_internal_branch_picks : Option (List Nat) :=
  sample 1000 8 true [] (schedule_rr 2 two_workers none 0)
def rr_internal_branch_pulses : Option (List Nat) :=
  sample 1000 8 false [] (schedule_rr 2 two_workers none 0)
def rr_three_thread_picks : Option (List Nat) :=
  sample 1000 6 true [] (schedule_rr 3 #v[worker 0 false, worker 1 false, worker 2 false] none 1)

theorem rr_internal_branch_picks_correct :
    rr_internal_branch_picks = some [0, 1, 0, 1, 0, 1, 0, 1] := by
  sched_eval [rr_internal_branch_picks, sample, two_workers, worker0, worker1, pulse_or_pick]
theorem rr_internal_branch_pulses_correct :
    rr_internal_branch_pulses = some [0, 1, 0, 1, 0, 1, 0, 1] := by
  sched_eval [rr_internal_branch_pulses, sample, two_workers, worker0, worker1, pulse_or_pick]
theorem rr_three_thread_picks_correct :
    rr_three_thread_picks = some [1, 2, 0, 1, 2, 0] := by
  sched_eval [rr_three_thread_picks, sample, pulse_or_pick]

theorem yielding_worker_branchfree (id : Nat) : BranchFree (worker id false) := by
  refine branchfree_invariant (fun t => ∃ (id : Nat) (phase : Bool),
    t = if phase then worker id false else .vis (.inl ⟨⟩) fun _ => worker id false) ?_ _
    ⟨id, true, rfl⟩
  rintro t ⟨who, phase, rfl⟩
  cases phase
  · simp only [Bool.false_eq_true, ite_false, unfold_vis]
    exact .vis _ _ fun _ => ⟨who, true, rfl⟩
  · simp only [ite_true, worker_unfold, Bool.false_eq_true, ite_false]
    exact .vis _ _ fun _ => ⟨who, false, rfl⟩

theorem rr_yielding_pool_branchfree (focus : Option (Fin 2)) (cursor : Nat) :
    BranchFree (schedule_rr 2 #v[worker 0 false, worker 1 false] focus cursor) := by
  refine branchfree_schedule_rr 2 _ focus cursor fun ⟨i, hi⟩ => ?_
  match i, hi with
  | 0, _ => exact yielding_worker_branchfree 0
  | 1, _ => exact yielding_worker_branchfree 1

/-! ## 2. Source nondeterminism remains visible before any selection -/

def choice_body (i : Fin 2) : Thread pulseE Bn :=
  .vis (.inr (.inr (if slot_index i = 0 then 10 else 20 : Nat))) fun _ => .stuck
def program_choice : Thread pulseE Bn := .br (⟨2⟩ : Bn.I) fun i => choice_body i.down
def choice_pool : Pool pulseE Bn 2 := #v[program_choice, worker1]

theorem focused_program_branch_state {E B : Effect.{0}} [Bn -< B] (sch : Scheduler) (n : Nat)
    (ts : Pool E B n) {c : B.I} (k : B.O c → Thread E B) (st : sch.sched_state) :
    schedule_policy sch (n + 1) (Vector.cons (.br c k) ts) (some 0) st =
      .br c fun a => schedule_policy sch (n + 1)
        ((Vector.cons (.br c k) ts).set (0 : Fin (n + 1)) (k a)) (some 0) st :=
  unfold_inj ((schedule_policy_focused_br sch n _ 0 k st (by simp)).trans (unfold_br _ _).symm)

theorem focused_pulse_transition (sch : Scheduler) (n : Nat) (ts : Pool pulseE Bn (n + 1))
    (i : Fin (n + 1)) (id : Nat) (k : PUnit → Thread pulseE Bn) (st : sch.sched_state)
    (hobs : ts[i].unfold = .vis (.inr (.inr id)) k) :
    ∃ u, trans (.obs (E := pulseE ⊕ₑ schedE) (.inl id) ⟨⟩)
      (schedule_policy sch (n + 1) ts (some i) st) u := by
  rw [← fold_unfold (schedule_policy sch (n + 1) ts (some i) st),
    schedule_policy_focused_user_event sch n ts i id k st hobs]
  exact ⟨_, trans_vis _ _⟩

theorem policy_program_choice_first (sch : Scheduler) (st : sch.sched_state) (a : Fin 2) :
    ∃ u, trans (.obs (E := pulseE ⊕ₑ schedE)
      (.inl (if slot_index a = 0 then 10 else 20 : Nat)) ⟨⟩)
      (schedule_policy sch 2 choice_pool (some 0) st) u := by
  rw [← fold_unfold (schedule_policy sch 2 choice_pool (some 0) st),
    schedule_policy_focused_br sch 1 choice_pool 0 (fun i => choice_body i.down) st rfl]
  obtain ⟨u, hu⟩ := focused_pulse_transition sch 1 (choice_pool.set (0 : Fin 2) (choice_body a))
    0 (if slot_index a = 0 then 10 else 20) (fun _ => .stuck) st (by simp [choice_body])
  exact ⟨u, trans_br ⟨a⟩ hu⟩

theorem nd_program_choice_both :
    (∃ u, trans (.obs (E := pulseE ⊕ₑ schedE) (.inl (10 : Nat)) ⟨⟩)
      (schedule 2 choice_pool (some 0)) u) ∧
    (∃ u, trans (.obs (E := pulseE ⊕ₑ schedE) (.inl (20 : Nat)) ⟨⟩)
      (schedule 2 choice_pool (some 0)) u) :=
  ⟨policy_program_choice_first nd_scheduler ⟨⟩ 0, policy_program_choice_first nd_scheduler ⟨⟩ 1⟩

theorem rr_program_choice_both (cursor : Nat) :
    (∃ u, trans (.obs (E := pulseE ⊕ₑ schedE) (.inl (10 : Nat)) ⟨⟩)
      (schedule_rr 2 choice_pool (some 0) cursor) u) ∧
    (∃ u, trans (.obs (E := pulseE ⊕ₑ schedE) (.inl (20 : Nat)) ⟨⟩)
      (schedule_rr 2 choice_pool (some 0) cursor) u) :=
  ⟨policy_program_choice_first rr_scheduler cursor 0,
    policy_program_choice_first rr_scheduler cursor 1⟩

theorem nd_program_choice_prefixes :
    events_sample 1000 1 [0] (schedule 2 choice_pool (some 0)) = some [(false, 10)] ∧
    events_sample 1000 1 [1] (schedule 2 choice_pool (some 0)) = some [(false, 20)] := by
  sched_eval [events_sample, choice_pool, program_choice, choice_body, pulse_or_pick]

theorem rr_program_choice_prefixes :
    events_sample 1000 1 [0] (schedule_rr 2 choice_pool (some 0) 5) = some [(false, 10)] ∧
    events_sample 1000 1 [1] (schedule_rr 2 choice_pool (some 0) 5) = some [(false, 20)] := by
  sched_eval [events_sample, choice_pool, program_choice, choice_body, pulse_or_pick]

def empty_program_branch : Thread pulseE Bn := .br (⟨0⟩ : Bn.I) fun i => i.down.elim0

theorem policy_empty_program_branch (sch : Scheduler) (st : sch.sched_state) :
    (schedule_policy sch 1 #v[empty_program_branch] (some 0) st).unfold =
      .br (⟨0⟩ : Bn.I) fun a => schedule_policy sch 1
        (#v[empty_program_branch].set (0 : Fin 1) a.down.elim0) (some 0) st :=
  schedule_policy_focused_br sch 0 _ 0 _ st rfl

theorem nd_empty_program_branch :
    events_sample 1000 1 [] (schedule 1 #v[empty_program_branch] (some 0)) = none := by
  sched_eval [events_sample, empty_program_branch]
theorem rr_empty_program_branch :
    events_sample 1000 1 [] (schedule_rr 1 #v[empty_program_branch] (some 0) 7) = none := by
  sched_eval [events_sample, empty_program_branch]

/-! ## 3. ND's hidden choice reports the actual selected vector slot -/

theorem nd_two_boundary :
    schedule 2 two_workers none =
      .br (⟨2⟩ : Bn.I) fun i => .vis (.inr (slot_index i.down)) fun _ =>
        schedule 2 two_workers (some i.down) :=
  (schedule_no_focus_nonempty 1 two_workers).trans rfl

theorem nd_pick0_then_pulse0 :
    ∃ u v, trans (.obs (E := pulseE ⊕ₑ schedE) (.inr (0 : Nat)) ⟨⟩)
      (schedule 2 two_workers none) u ∧
      trans (.obs (E := pulseE ⊕ₑ schedE) (.inl (0 : Nat)) ⟨⟩) u v := by
  obtain ⟨v, hv⟩ := focused_pulse_transition nd_scheduler 1 two_workers 0 0 _ ⟨⟩
    (worker_unfold 0 true)
  exact ⟨_, v, by rw [nd_two_boundary]; exact trans_br ⟨0⟩ (trans_vis _ _), hv⟩

theorem nd_pick1_then_pulse1 :
    ∃ u v, trans (.obs (E := pulseE ⊕ₑ schedE) (.inr (1 : Nat)) ⟨⟩)
      (schedule 2 two_workers none) u ∧
      trans (.obs (E := pulseE ⊕ₑ schedE) (.inl (1 : Nat)) ⟨⟩) u v := by
  obtain ⟨v, hv⟩ := focused_pulse_transition nd_scheduler 1 two_workers 1 1 _ ⟨⟩
    (worker_unfold 1 false)
  exact ⟨_, v, by rw [nd_two_boundary]; exact trans_br ⟨1⟩ (trans_vis _ _), hv⟩

theorem nd_first_label_is_scheduled (l : Label (pulseE ⊕ₑ schedE)) (u : Completed pulseE Bn)
    (h : trans l (schedule 2 two_workers none) u) :
    ∃ i : Fin 2, l = .obs (E := pulseE ⊕ₑ schedE) (.inr (slot_index i)) ⟨⟩ := by
  rw [nd_two_boundary] at h
  obtain ⟨⟨i⟩, h⟩ := trans_br_inv h
  obtain ⟨⟨⟩, -, hl⟩ := trans_vis_inv h
  exact ⟨i, hl⟩

theorem nd_boundary_not_tau (u : Completed pulseE Bn) :
    ¬ trans .tau (schedule 2 two_workers none) u := fun h => by
  obtain ⟨_, h⟩ := nd_first_label_is_scheduled _ _ h
  cases h

theorem nd_selected_prefixes :
    events_sample 1000 2 [0] (schedule 2 two_workers none) = some [(true, 0), (false, 0)] ∧
    events_sample 1000 2 [1] (schedule 2 two_workers none) = some [(true, 1), (false, 1)] := by
  sched_eval [events_sample, two_workers, worker0, worker1, pulse_or_pick]

theorem nd_singleton_direct :
    (schedule 1 #v[worker0] none).unfold =
      .vis (.inr (0 : Nat)) fun _ => schedule 1 #v[worker0] (some 0) := by
  rw [schedule_no_focus_nonempty]; simp

/-! ## 4. A genuinely branching fair policy may repeat a cursor once -/

/-- Pick the round-robin slot; while no duplicate is due, a choice may keep the cursor once. -/
def optional_duplicate_pick (n : Nat) :
    (st : Nat × Bool) → Fin ((if st.2 then 0 else 1) + 1) → Fin (n + 1) × (Nat × Bool)
  | (cursor, true), _ => (rr_pick n cursor, (cursor + 1, false))
  | (cursor, false), ⟨0, _⟩ => (rr_pick n cursor, (cursor, true))
  | (cursor, false), ⟨_ + 1, _⟩ => (rr_pick n cursor, (cursor + 1, false))

def optional_duplicate_rr : Scheduler where
  sched_state := Nat × Bool
  sched_arity _ st := if st.2 then 0 else 1
  sched_pick := optional_duplicate_pick

theorem optional_duplicate_eventually_picks (n : Nat) (i : Fin (n + 1))
    (st : optional_duplicate_rr.sched_state) : EventuallyPicks optional_duplicate_rr n i st := by
  obtain ⟨cursor, due⟩ := st
  refine eventually_picks_simulation rr_scheduler optional_duplicate_rr n i
    (fun (dst : Nat × Bool) (src : Nat) => dst.1 = src)
    (fun (dst : Nat × Bool) => if dst.2 then 0 else 1) (· < ·) Nat.lt_wfRel.wf ?_ cursor
    (cursor, due) (rr_eventually_picks n i cursor) rfl
  rintro ⟨c, due⟩ src offer rfl
  cases due with
  | true => exact ⟨0, rfl, .inl rfl⟩
  | false =>
    match offer with
    | ⟨0, _⟩ => exact ⟨0, rfl, .inr ⟨rfl, by simp [optional_duplicate_rr, optional_duplicate_pick]⟩⟩
    | ⟨_ + 1, _⟩ => exact ⟨0, rfl, .inl rfl⟩

instance optional_duplicate_fair : FairScheduler optional_duplicate_rr :=
  eventually_picks_fair optional_duplicate_rr optional_duplicate_eventually_picks

def fair_repeat_picks : Option (List Nat) :=
  sample 1000 8 true (List.replicate 8 0)
    (schedule_policy optional_duplicate_rr 2 two_workers none ((0, false) : Nat × Bool))
def fair_advance_picks : Option (List Nat) :=
  sample 1000 8 true (List.replicate 8 1)
    (schedule_policy optional_duplicate_rr 2 two_workers none ((0, false) : Nat × Bool))

theorem fair_repeat_picks_correct : fair_repeat_picks = some [0, 0, 1, 1, 0, 0, 1, 1] := by
  sched_eval [fair_repeat_picks, sample, two_workers, worker0, worker1, pulse_or_pick,
    optional_duplicate_rr, optional_duplicate_pick]
theorem fair_advance_picks_correct : fair_advance_picks = some [0, 1, 0, 1, 0, 1, 0, 1] := by
  sched_eval [fair_advance_picks, sample, two_workers, worker0, worker1, pulse_or_pick,
    optional_duplicate_rr, optional_duplicate_pick]

theorem policy_program_choice_prefixes :
    events_sample 1000 1 [0]
      (schedule_policy optional_duplicate_rr 2 choice_pool (some 0) ((5, false) : Nat × Bool)) =
        some [(false, 10)] ∧
    events_sample 1000 1 [1]
      (schedule_policy optional_duplicate_rr 2 choice_pool (some 0) ((5, false) : Nat × Bool)) =
        some [(false, 20)] := by
  sched_eval [events_sample, choice_pool, program_choice, choice_body, pulse_or_pick,
    optional_duplicate_rr]

/-- Pulses log their identifier and keep the state. -/
def hpulse : (e : pulseE.I) → StateT Nat (ctreeW Nat Bn) (pulseE.O e) :=
  fun i σ => .vis (E := writerE Nat) i fun _ => pure (⟨⟩, σ)

def log_payload {A : Type} : (e : (writerE A).I) → (writerE A).O e × A := fun x => (⟨⟩, x)

def fair_sample (fuel needed : Nat) (script : List Nat) (t : ctreeW (Nat ⊕ Nat) Bn (PUnit × Nat)) :
    Option (List (Nat ⊕ Nat)) :=
  bounded_prefix log_payload some false fuel needed script t

theorem fair_pick_directly_precedes_worker :
    fair_sample 1000 2 [0]
      (interp_schedule_fair optional_duplicate_rr hpulse 2 two_workers none
        ((0, false) : Nat × Bool) 42) = some [.inr 0, .inl 0] := by
  sched_eval [fair_sample, log_payload, hpulse, two_workers, worker0, worker1,
    optional_duplicate_rr, optional_duplicate_pick]

theorem fair_pick_not_program (P : Nat → Prop) (i : Nat) : ¬ fair_obs P (.inr i) := fun h => h

/-! ## 5. Boundaries, faults, focus, fork, and removal use current positions -/

theorem empty_pool_no_pick (sch : Scheduler) (st : sch.sched_state) :
    (schedule_policy sch 0 (#v[] : Pool pulseE Bn 0) none st).unfold = .ret ⟨⟩ :=
  schedule_policy_empty_none sch _ st

theorem rr_stuck_slot_selected :
    schedule_rr 2 #v[.stuck, worker1] none 0 = .vis (.inr (0 : Nat)) fun _ => .stuck := by
  apply unfold_inj
  rw [schedule_rr_no_focus_nonempty, unfold_vis]
  congr; funext
  exact unfold_inj ((schedule_rr_focused_stuck 1 _ _ 1 (by simp [rr_pick])).trans
    unfold_stuck.symm)

theorem rr_stuck_slot_not_skipped :
    events_sample 1000 1 [] (schedule_rr 2 #v[.stuck, worker1] none 0) = some [(true, 0)] ∧
    events_sample 1000 2 [] (schedule_rr 2 #v[.stuck, worker1] none 0) = none := by
  sched_eval [events_sample, worker1, pulse_or_pick]

theorem initially_focused_no_pick :
    events_sample 1000 1 [] (schedule_rr 2 two_workers (some 0) 13) = some [(false, 0)] := by
  sched_eval [events_sample, two_workers, worker0, worker1, pulse_or_pick]

def fork_workers : Thread pulseE Bn :=
  .vis (.inr (.inl ⟨⟩)) fun child => if child then worker 1 false else worker 0 false

theorem focused_fork_parent_keeps_turn :
    events_sample 1000 5 [] (schedule_rr 1 #v[fork_workers] (some 0) 0) =
      some [(false, 0), (true, 0), (false, 1), (true, 1), (false, 0)] := by
  sched_eval [events_sample, fork_workers, pulse_or_pick]

theorem return_reindexes_slots :
    events_sample 1000 3 [] (schedule_rr 2 #v[pure ⟨⟩, worker1] none 0) =
      some [(true, 0), (true, 0), (false, 1)] := by
  sched_eval [events_sample, worker1, pulse_or_pick]

theorem yield_does_not_spend_cursor :
    events_sample 1000 3 [] (schedule_rr 2 two_workers (some 0) 1) =
      some [(false, 0), (true, 1), (false, 1)] := by
  sched_eval [events_sample, two_workers, worker0, worker1, pulse_or_pick]

theorem focused_return_does_not_spend_cursor :
    events_sample 1000 2 []
      (schedule_rr 3 #v[pure ⟨⟩, worker 7 false, worker 8 false] (some 0) 1) =
        some [(true, 1), (false, 8)] := by
  sched_eval [events_sample, pulse_or_pick]

/-! ## 6. Nondeterministic projection, logged RR, handler choices, and truthful offers -/

def one_pulse (id : Nat) : Thread pulseE Bn := .vis (.inr (.inr id)) fun _ => pure ⟨⟩

theorem nd_selection_one_tau_state (sigma : Nat) :
    finish_sample log_payload 1000 []
      (interp_schedule_nd hpulse 1 #v[one_pulse 7] none sigma) =
    some ⟨1, [7], (⟨⟩, sigma)⟩ := by
  sched_eval [log_payload, hpulse, one_pulse]

theorem rr_selection_one_log_state (sigma : Nat) :
    finish_sample log_payload 1000 []
      (interp_schedule_rr hpulse 1 #v[one_pulse 7] none 0 sigma) =
    some ⟨0, [.inr 0, .inl 7], (⟨⟩, sigma)⟩ := by
  sched_eval [log_payload, hpulse, one_pulse]

theorem nd_singleton_selection_exact (sigma : Nat) :
    interp_schedule_nd hpulse 1 #v[one_pulse 7] none sigma =
      .step (guards 2 (interp_schedule_nd hpulse 1 #v[one_pulse 7] (some 0) sigma)) := by
  conv => lhs; rw [interp_schedule_nd, schedule_no_focus_nonempty]
  simp [interp_schedule_nd, guards]

theorem nd_selection_world_unchanged (sigma : Nat) (w : World (writerE Nat))
    (u : ctreeW Nat Bn (PUnit × Nat)) (w' : World (writerE Nat)) :
    ktrans (interp_schedule_nd hpulse 1 #v[one_pulse 7] none sigma) w u w' ↔
      u = guards 2 (interp_schedule_nd hpulse 1 #v[one_pulse 7] (some 0) sigma) ∧
      w = w' ∧ NotDone w := by
  rw [nd_singleton_selection_exact]; exact ktrans_step

theorem rr_selection_world_logged (sigma : Nat) (w : World (writerE (Nat ⊕ Nat)))
    (u : ctreeW (Nat ⊕ Nat) Bn (PUnit × Nat)) (w' : World (writerE (Nat ⊕ Nat))) :
    ktrans (interp_schedule_rr hpulse 1 #v[one_pulse 7] none 0 sigma) w u w' ↔
      u = .guard (interp_schedule_rr hpulse 1 #v[one_pulse 7] (some 0) 1 sigma) ∧
      w' = .obs (E := writerE (Nat ⊕ Nat)) (.inr 0) ⟨⟩ ∧ NotDone w := by
  rw [segment_rr_select_exact, ktrans_vis]
  constructor
  · rintro ⟨⟨⟩, rfl, rfl, hw⟩; exact ⟨rfl, rfl, hw⟩
  · rintro ⟨rfl, rfl, hw⟩; exact ⟨⟨⟩, rfl, rfl, hw⟩

theorem fair_selection_one_log_state (sigma : Nat) :
    finish_sample log_payload 1000 [0]
      (interp_schedule_fair optional_duplicate_rr hpulse 1 #v[one_pulse 7] none
        ((0, false) : Nat × Bool) sigma) =
    some ⟨0, [.inr 0, .inl 7], (⟨⟩, sigma)⟩ := by
  sched_eval [log_payload, hpulse, one_pulse, optional_duplicate_rr, optional_duplicate_pick]

/-- Each pulse is logged as `10` or `20`, chosen by a genuine branch of the handler. -/
def branching_hpulse : (e : pulseE.I) → StateT Nat (ctreeW Nat Bn) (pulseE.O e) :=
  fun _ σ => .br (⟨2⟩ : Bn.I) fun i =>
    .vis (E := writerE Nat) (if slot_index i.down = 0 then 10 else 20 : Nat) fun _ =>
      pure (⟨⟩, σ)

def program_log_sample (fuel needed : Nat) (script : List Nat)
    (t : ctreeW Nat Bn (PUnit × Nat)) : Option (List Nat) :=
  bounded_prefix log_payload some true fuel needed script t

theorem nd_handler_choices_preserved :
    program_log_sample 1000 1 [0]
      (interp_schedule_nd branching_hpulse 1 #v[one_pulse 7] none 42) = some [10] ∧
    program_log_sample 1000 1 [1]
      (interp_schedule_nd branching_hpulse 1 #v[one_pulse 7] none 42) = some [20] := by
  sched_eval [program_log_sample, log_payload, branching_hpulse, one_pulse]

theorem rr_handler_choices_preserved :
    fair_sample 1000 2 [0]
      (interp_schedule_rr branching_hpulse 1 #v[one_pulse 7] none 0 42) = some [.inr 0, .inl 10] ∧
    fair_sample 1000 2 [1]
      (interp_schedule_rr branching_hpulse 1 #v[one_pulse 7] none 0 42) =
        some [.inr 0, .inl 20] := by
  sched_eval [fair_sample, log_payload, branching_hpulse, one_pulse]

theorem fair_handler_choices_preserved :
    fair_sample 1000 2 [0, 0]
      (interp_schedule_fair optional_duplicate_rr branching_hpulse 1 #v[one_pulse 7]
        none ((0, false) : Nat × Bool) 42) = some [.inr 0, .inl 10] ∧
    fair_sample 1000 2 [0, 1]
      (interp_schedule_fair optional_duplicate_rr branching_hpulse 1 #v[one_pulse 7]
        none ((0, false) : Nat × Bool) 42) = some [.inr 0, .inl 20] := by
  sched_eval [fair_sample, log_payload, branching_hpulse, one_pulse, optional_duplicate_rr,
    optional_duplicate_pick]

/-- Decoded observations of the offer-instrumented scheduler (Rocq `sampled_event`). -/
inductive SampledEvent
  | point (n : Nat)
  | offered (size slot : Nat)
  | pick (i : Nat)
  | user (i : Nat)

def observed_payload :
    (e : (scheduler_observedE pulseE).I) → (scheduler_observedE pulseE).O e × SampledEvent
  | .inl (.point n) => (⟨⟩, .point n)
  | .inl (.offered slot) => (⟨⟩, .offered slot.slot_pool_size (slot_index slot.slot_live_slot))
  | .inr (.inl i) => (⟨⟩, .user i)
  | .inr (.inr i) => (⟨⟩, .pick i)

def offer_sample (fuel needed : Nat) (script : List Nat) (t : observed_completed pulseE Bn) :
    Option (List SampledEvent) :=
  bounded_prefix observed_payload some true fuel needed script t

theorem offers_precede_selection0 :
    offer_sample 1000 5 [0] (schedule_with_offers 2 two_workers none) =
      some [.point 2, .offered 2 0, .offered 2 1, .pick 0, .user 0] := by
  sched_eval [offer_sample, observed_payload, two_workers, worker0, worker1]
theorem offers_precede_selection1 :
    offer_sample 1000 5 [1] (schedule_with_offers 2 two_workers none) =
      some [.point 2, .offered 2 0, .offered 2 1, .pick 1, .user 1] := by
  sched_eval [offer_sample, observed_payload, two_workers, worker0, worker1]

theorem forgetting_offers_agrees_with_nd :
    forget_scheduler_offers (schedule_with_offers 2 two_workers none) ~
      schedule 2 two_workers none :=
  forget_scheduler_offers_preserves_schedule 2 two_workers none

theorem forgetting_offers_preserves_selected_observations :
    events_sample 1000 2 [1]
      (forget_scheduler_offers (schedule_with_offers 2 two_workers none)) =
      some [(true, 1), (false, 1)] ∧
    events_sample 1000 2 [1] (schedule 2 two_workers none) = some [(true, 1), (false, 1)] := by
  sched_eval [events_sample, pulse_or_pick, two_workers, worker0, worker1]

/-- Failure behavior is part of the prefix evaluator's contract, not a default interpretation
of unfinished executions. -/
theorem prefix_failures_are_not_successes :
    events_sample 0 1 [] (schedule_rr 2 two_workers none 0) = none ∧
    events_sample 1000 1 [] (pure ⟨⟩) = none ∧
    events_sample 1000 1 [] .stuck = none ∧
    events_sample 1000 1 [] (schedule 2 two_workers none) = none ∧
    events_sample 1000 1 [2] (schedule 2 two_workers none) = none ∧
    sample 1000 2 false [] (schedule_rr 1 #v[one_pulse 7] none 0) = none := by
  sched_eval [events_sample, sample, pulse_or_pick, two_workers, worker0, worker1, one_pulse]

-- Not ported: nothing. Renamed: `finite_result` ↦ `FiniteResult`, `sampled_event` ↦
-- `SampledEvent` (constructors `point`/`offered`/`pick`/`user`); the Rocq `Arguments` directives
-- are the implicit binders. Added for evaluation (Rocq `vm_compute`): `bounded_prefix_node`,
-- `finish_sample_node` (one evaluator node), `bounded_prefix_{done,no_fuel,succ}`,
-- `finish_sample_{no_fuel,succ}`, `subeffect_map_refl`, `worker_unfold`, tactic `sched_eval`.

end Examples.Scheduling
