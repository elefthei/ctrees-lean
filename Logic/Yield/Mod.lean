/- SPDX-License-Identifier: MIT -/
module

public import Logic.Yield.Scheduler
public import Logic.Events.Yield
public import Logic.Events.Writer
public import Logic.Interp.State
public import Logic.Utils.Vectors

/-!
# The raw cooperative scheduler

The policy-generic scheduler `schedule_policy` of a pool of cooperative threads (selection only
at unfocused boundaries), its nondeterministic and round-robin instances, its exact one-node
equations, and the erasure/instrumentation interpreters for scheduling observations, yields and
forks (← `CTree/Interp/Yield/Mod.v`, after `br_alts`).
-/

@[expose] public section
namespace Tisl.Yield
open CTree Lean.Order Coinduction
open ITree (Effect)

section Scheduler
variable {E B : Effect.{0}}

@[partial_fixpoint_monotone]
theorem br_alts_mono [Bn -< B] {X : Type} α [PartialOrder α] (m : Nat)
    (f : α → Fin (m + 1) → CTree E B X) :
    monotone f → monotone (fun x => br_alts m (f x)) := by
  intro hf
  cases m with
  | zero => exact fun a b h => hf a b h 0
  | succ m => exact br'_mono α (B₁ := Bn) ⟨m + 2⟩ (fun a x => f a x.down) fun a b h x => hf a b h _

/-- The policy-generic cooperative scheduler. Selection happens only at an unfocused boundary
(`sched_arity n st + 1` alternatives, each logging the selected slot); focused source branches
are preserved, and all focused clauses leave the policy state unchanged. `Fork` prepends the
`true` child and keeps focusing the shifted `false` parent, a return removes the slot, a yield
clears the focus. -/
def schedule_policy [Bn -< B] (sch : Scheduler) :
    (n : Nat) → Pool E B n → Option (Fin n) → sch.sched_state → Completed E B
  | 0, _, none, _ => pure ⟨⟩
  | n + 1, v, none, st =>
    br_alts (sch.sched_arity n st) fun a =>
      .vis (.inr (slot_index (sch.sched_pick n st a).1))
        fun _ => schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
          (sch.sched_pick n st a).2
  | 0, _, some i, _ => i.elim0
  | n + 1, v, some i, st =>
    match v[i].unfold with
    | .ret _ => .guard (schedule_policy sch n (v.eraseIdx i) none st)
    | .stuck => .stuck
    | .br c k => .br c fun j => schedule_policy sch (n + 1) (v.set i (k j)) (some i) st
    | .step t => .step (schedule_policy sch (n + 1) (v.set i t) (some i) st)
    | .guard t => .guard (schedule_policy sch (n + 1) (v.set i t) (some i) st)
    | .vis (.inl _) k => .guard (schedule_policy sch (n + 1) (v.set i (k ⟨⟩)) none st)
    | .vis (.inr (.inl _)) k =>
      .guard (schedule_policy sch (n + 2) (Vector.cons (k true) (v.set i (k false)))
        (some i.succ) st)
    | .vis (.inr (.inr e)) k =>
      .vis (.inl e) fun x => schedule_policy sch (n + 1) (v.set i (k x)) (some i) st
partial_fixpoint

theorem unfold_schedule_policy [Bn -< B] (sch : Scheduler) (n : Nat) (v : Pool E B n)
    (focus : Option (Fin n)) (st : sch.sched_state) :
    schedule_policy sch n v focus st = match n, v, focus, st with
      | 0, _, none, _ => pure ⟨⟩
      | n + 1, v, none, st =>
        br_alts (sch.sched_arity n st) fun a =>
          .vis (.inr (slot_index (sch.sched_pick n st a).1))
            fun _ => schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
              (sch.sched_pick n st a).2
      | 0, _, some i, _ => i.elim0
      | n + 1, v, some i, st =>
        match v[i].unfold with
        | .ret _ => .guard (schedule_policy sch n (v.eraseIdx i) none st)
        | .stuck => .stuck
        | .br c k => .br c fun j => schedule_policy sch (n + 1) (v.set i (k j)) (some i) st
        | .step t => .step (schedule_policy sch (n + 1) (v.set i t) (some i) st)
        | .guard t => .guard (schedule_policy sch (n + 1) (v.set i t) (some i) st)
        | .vis (.inl _) k => .guard (schedule_policy sch (n + 1) (v.set i (k ⟨⟩)) none st)
        | .vis (.inr (.inl _)) k =>
          .guard (schedule_policy sch (n + 2) (Vector.cons (k true) (v.set i (k false)))
            (some i.succ) st)
        | .vis (.inr (.inr e)) k =>
          .vis (.inl e) fun x => schedule_policy sch (n + 1) (v.set i (k x)) (some i) st := by
  rw [schedule_policy.eq_def]

/-- Nondeterministic scheduling. -/
def schedule [Bn -< B] (n : Nat) (v : Pool E B n) (focus : Option (Fin n)) : Completed E B :=
  schedule_policy nd_scheduler n v focus ⟨⟩

/-- Round-robin scheduling from `cursor`. -/
def schedule_rr [Bn -< B] (n : Nat) (v : Pool E B n) (focus : Option (Fin n)) (cursor : Nat) :
    Completed E B :=
  schedule_policy rr_scheduler n v focus cursor

theorem schedule_policy_no_focus_nonempty [Bn -< B] (sch : Scheduler) (n : Nat)
    (v : Pool E B (n + 1)) (st : sch.sched_state) :
    schedule_policy sch (n + 1) v none st =
      br_alts (E := E ⊕ₑ schedE) (sch.sched_arity n st) fun a =>
        .vis (.inr (slot_index (sch.sched_pick n st a).1))
          fun _ => schedule_policy sch (n + 1) v (some (sch.sched_pick n st a).1)
            (sch.sched_pick n st a).2 := by
  conv => lhs; rw [schedule_policy]

end Scheduler

/-! ## Event erasure handlers -/

section Handlers
variable {E B : Effect.{0}}

/-- Preserve user effects and project each native selection to one silent step. -/
def handle_scheduled_step : (e : (E ⊕ₑ schedE).I) → CTree E B ((E ⊕ₑ schedE).O e)
  | .inl e => CTree.trigger e
  | .inr _ => .step (pure ⟨⟩)

/-- Project scheduling selections to silent steps. -/
def project_scheduled {X : Type} (t : CTree (E ⊕ₑ schedE) B X) : CTree E B X :=
  interp handle_scheduled_step t

/-- Erase cooperative yield observations, leaving only user events. -/
def handle_yield : (e : (yieldE ⊕ₑ E).I) → CTree E B ((yieldE ⊕ₑ E).O e)
  | .inl _ => pure ⟨⟩
  | .inr m => CTree.trigger m

def interp_yield {X : Type} (t : CTree (yieldE ⊕ₑ E) B X) : CTree E B X :=
  interp handle_yield t

/-- Interpret a raw thread without scheduling by resolving `Fork` to `false`: a standalone thread
behaves as the parent path and never starts the fork body. -/
def handle_thread : (e : (yieldE ⊕ₑ forkE ⊕ₑ E).I) →
    CTree (yieldE ⊕ₑ E) B ((yieldE ⊕ₑ forkE ⊕ₑ E).O e)
  | .inl y => CTree.trigger (E := yieldE ⊕ₑ E) (.inl y)
  | .inr (.inl _) => pure false
  | .inr (.inr m) => CTree.trigger (E := yieldE ⊕ₑ E) (.inr m)

def interp_thread {X : Type} (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) : CTree E B X :=
  interp_yield (interp handle_thread t)

end Handlers

/-! ## Exact scheduler node observations -/

section SchedulerFacts
variable {E B : Effect.{0}} [Bn -< B]

@[simp] theorem schedule_policy_empty_none (sch : Scheduler) (v : Pool E B 0)
    (st : sch.sched_state) : (schedule_policy sch 0 v none st).unfold = .ret ⟨⟩ := by
  rw [schedule_policy]; rfl

theorem schedule_policy_focused_ret (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (st : sch.sched_state) (h : v[i].unfold = .ret ⟨⟩) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .guard (schedule_policy sch n (v.eraseIdx i) none st) := by
  rw [schedule_policy, h]; rfl

theorem schedule_policy_focused_stuck (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (st : sch.sched_state) (h : v[i].unfold = .stuck) :
    (schedule_policy sch (n + 1) v (some i) st).unfold = .stuck := by
  rw [schedule_policy, h]; rfl

theorem schedule_policy_focused_br (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) {c : B.I} (k : B.O c → Thread E B) (st : sch.sched_state)
    (h : v[i].unfold = .br c k) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .br c fun j => schedule_policy sch (n + 1) (v.set i (k j)) (some i) st := by
  rw [schedule_policy, h]; rfl

theorem schedule_policy_focused_step (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (t : Thread E B) (st : sch.sched_state) (h : v[i].unfold = .step t) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .step (schedule_policy sch (n + 1) (v.set i t) (some i) st) := by
  rw [schedule_policy, h]; rfl

theorem schedule_policy_focused_guard (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (t : Thread E B) (st : sch.sched_state) (h : v[i].unfold = .guard t) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .guard (schedule_policy sch (n + 1) (v.set i t) (some i) st) := by
  rw [schedule_policy, h]; rfl

theorem schedule_policy_focused_yield (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (k : PUnit → Thread E B) (st : sch.sched_state)
    (h : v[i].unfold = .vis (.inl ⟨⟩) k) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .guard (schedule_policy sch (n + 1) (v.set i (k ⟨⟩)) none st) := by
  conv => lhs; rw [schedule_policy]
  rw [h]; rfl

theorem schedule_policy_focused_fork (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (k : Bool → Thread E B) (st : sch.sched_state)
    (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .guard (schedule_policy sch (n + 2) (Vector.cons (k true) (v.set i (k false)))
        (some i.succ) st) := by
  rw [schedule_policy, h]; rfl

theorem schedule_policy_focused_user_event (sch : Scheduler) (n : Nat) (v : Pool E B (n + 1))
    (i : Fin (n + 1)) (e : E.I) (k : E.O e → Thread E B) (st : sch.sched_state)
    (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    (schedule_policy sch (n + 1) v (some i) st).unfold =
      .vis (.inl e) fun x => schedule_policy sch (n + 1) (v.set i (k x)) (some i) st := by
  rw [schedule_policy, h]; rfl

@[simp] theorem schedule_empty_none (v : Pool E B 0) : (schedule 0 v none).unfold = .ret ⟨⟩ :=
  schedule_policy_empty_none _ v _

theorem schedule_focused_ret (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .ret ⟨⟩) :
    (schedule (n + 1) v (some i)).unfold = .guard (schedule n (v.eraseIdx i) none) :=
  schedule_policy_focused_ret _ n v i _ h

theorem schedule_focused_stuck (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (h : v[i].unfold = .stuck) : (schedule (n + 1) v (some i)).unfold = .stuck :=
  schedule_policy_focused_stuck _ n v i _ h

theorem schedule_focused_br (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) {c : B.I}
    (k : B.O c → Thread E B) (h : v[i].unfold = .br c k) :
    (schedule (n + 1) v (some i)).unfold =
      .br c fun j => schedule (n + 1) (v.set i (k j)) (some i) :=
  schedule_policy_focused_br _ n v i k _ h

theorem schedule_focused_step (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .step t) :
    (schedule (n + 1) v (some i)).unfold = .step (schedule (n + 1) (v.set i t) (some i)) :=
  schedule_policy_focused_step _ n v i t _ h

theorem schedule_focused_guard (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (h : v[i].unfold = .guard t) :
    (schedule (n + 1) v (some i)).unfold = .guard (schedule (n + 1) (v.set i t) (some i)) :=
  schedule_policy_focused_guard _ n v i t _ h

theorem schedule_focused_yield (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (h : v[i].unfold = .vis (.inl ⟨⟩) k) :
    (schedule (n + 1) v (some i)).unfold = .guard (schedule (n + 1) (v.set i (k ⟨⟩)) none) :=
  schedule_policy_focused_yield _ n v i k _ h

theorem schedule_focused_fork (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    (schedule (n + 1) v (some i)).unfold =
      .guard (schedule (n + 2) (Vector.cons (k true) (v.set i (k false))) (some i.succ)) :=
  schedule_policy_focused_fork _ n v i k _ h

theorem schedule_focused_user_event (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E B) (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    (schedule (n + 1) v (some i)).unfold =
      .vis (.inl e) fun x => schedule (n + 1) (v.set i (k x)) (some i) :=
  schedule_policy_focused_user_event _ n v i e k _ h

@[simp] theorem schedule_rr_empty_none (v : Pool E B 0) (cursor : Nat) :
    (schedule_rr 0 v none cursor).unfold = .ret ⟨⟩ :=
  schedule_policy_empty_none _ v _

theorem schedule_rr_focused_ret (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (cursor : Nat) (h : v[i].unfold = .ret ⟨⟩) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .guard (schedule_rr n (v.eraseIdx i) none cursor) :=
  schedule_policy_focused_ret _ n v i _ h

theorem schedule_rr_focused_stuck (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (cursor : Nat) (h : v[i].unfold = .stuck) :
    (schedule_rr (n + 1) v (some i) cursor).unfold = .stuck :=
  schedule_policy_focused_stuck _ n v i _ h

theorem schedule_rr_focused_br (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1)) {c : B.I}
    (k : B.O c → Thread E B) (cursor : Nat) (h : v[i].unfold = .br c k) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .br c fun j => schedule_rr (n + 1) (v.set i (k j)) (some i) cursor :=
  schedule_policy_focused_br _ n v i k _ h

theorem schedule_rr_focused_step (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (cursor : Nat) (h : v[i].unfold = .step t) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .step (schedule_rr (n + 1) (v.set i t) (some i) cursor) :=
  schedule_policy_focused_step _ n v i t _ h

theorem schedule_rr_focused_guard (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (t : Thread E B) (cursor : Nat) (h : v[i].unfold = .guard t) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .guard (schedule_rr (n + 1) (v.set i t) (some i) cursor) :=
  schedule_policy_focused_guard _ n v i t _ h

theorem schedule_rr_focused_yield (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : PUnit → Thread E B) (cursor : Nat) (h : v[i].unfold = .vis (.inl ⟨⟩) k) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .guard (schedule_rr (n + 1) (v.set i (k ⟨⟩)) none cursor) :=
  schedule_policy_focused_yield _ n v i k _ h

theorem schedule_rr_focused_fork (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (k : Bool → Thread E B) (cursor : Nat) (h : v[i].unfold = .vis (.inr (.inl ⟨⟩)) k) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .guard (schedule_rr (n + 2) (Vector.cons (k true) (v.set i (k false))) (some i.succ)
        cursor) :=
  schedule_policy_focused_fork _ n v i k _ h

theorem schedule_rr_focused_user_event (n : Nat) (v : Pool E B (n + 1)) (i : Fin (n + 1))
    (e : E.I) (k : E.O e → Thread E B) (cursor : Nat)
    (h : v[i].unfold = .vis (.inr (.inr e)) k) :
    (schedule_rr (n + 1) v (some i) cursor).unfold =
      .vis (.inl e) fun x => schedule_rr (n + 1) (v.set i (k x)) (some i) cursor :=
  schedule_policy_focused_user_event _ n v i e k _ h

/-- An unfocused nondeterministic boundary: one selection event for a singleton pool, otherwise a
hidden branch over all slots. Stated on trees (Rocq: on `observe`, with `BrF (branchn _)`). -/
theorem schedule_no_focus_nonempty (n : Nat) (v : Pool E B (n + 1)) :
    schedule (n + 1) v none = match n, v with
      | 0, v => .vis (.inr (0 : Nat)) fun _ => schedule 1 v (some 0)
      | m + 1, v => CTree.brn (m + 2) fun i =>
          .vis (.inr (slot_index i)) fun _ => schedule (m + 2) v (some i) := by
  cases n <;> exact (schedule_policy_no_focus_nonempty nd_scheduler _ v ⟨⟩).trans rfl

theorem schedule_rr_no_focus_nonempty (n : Nat) (v : Pool E B (n + 1)) (cursor : Nat) :
    (schedule_rr (n + 1) v none cursor).unfold =
      .vis (.inr (slot_index (rr_pick n cursor)))
        fun _ => schedule_rr (n + 1) v (some (rr_pick n cursor)) (cursor + 1) := by
  exact (congrArg CTree.unfold
    (schedule_policy_no_focus_nonempty rr_scheduler n v cursor)).trans rfl

end SchedulerFacts

/-! ## Raw instrumentation entry points -/

/-- Instrument a standalone raw thread: erase `Fork` to the parent branch and erase cooperative
`Yield`, then instrument the residual state effects. -/
def instr_thread {Sg : Type} {B : Effect.{0}} {X : Type}
    (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B X) (σ : Sg) : ctreeW Sg B (X × Sg) :=
  instr_stateE (interp_thread t) σ

/-- Project scheduling selections to silent steps, then instrument user effects. -/
def instr_schedule {Sg : Type} {B : Effect.{0}} [Bn -< B] (n : Nat) (v : Pool (stateE Sg) B n)
    (focus : Option (Fin n)) (σ : Sg) : ctreeW Sg B (PUnit × Sg) :=
  instr_stateE (project_scheduled (schedule n v focus)) σ

/-! ### Composed erasure equations for a single raw thread node -/

section ThreadNodes
variable {E B : Effect.{0}} {X : Type}

theorem interp_thread_yield_node (k : PUnit → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) :
    interp_thread (.vis (.inl ⟨⟩) k) = .guard (.guard (interp_thread (k ⟨⟩))) := by
  simp [interp_thread, interp_yield, handle_thread, handle_yield, CTree.trigger]

theorem interp_thread_user_node {e : E.I} (k : E.O e → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) :
    interp_thread (.vis (.inr (.inr e)) k) =
      .vis e fun x => .guard (.guard (interp_thread (k x))) := by
  simp [interp_thread, interp_yield, handle_thread, handle_yield, CTree.trigger]

end ThreadNodes

/-! ### Thread erasure under an arbitrary state handler -/

section ThreadStateInterp
variable {E F B : Effect.{0}} {S : Type} (h : (e : E.I) → StateT S (CTree F B) (E.O e))

@[grind =] theorem interp_state_thread_ret {X : Type} (x : X) (s : S) :
    interp_state h (interp_thread (pure x : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X)) s = pure (x, s) := by
  simp [interp_thread, interp_yield]

theorem interp_state_thread_bind {A C : Type} (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B A)
    (k : A → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B C) (s : S) :
    interp_state h (interp_thread (t >>= k)) s =
      (interp_state h (interp_thread t) s >>= fun p =>
        interp_state h (interp_thread (k p.1)) p.2) := by
  simp only [interp_thread, interp_yield, interp_bind, interp_state_bind]

@[grind .] theorem interp_state_thread_yield {X : Type}
    (k : PUnit → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) (s : S) :
    interp_state h (interp_thread (.vis (.inl ⟨⟩) k)) s ~
      interp_state h (interp_thread (k ⟨⟩)) s := by
  rw [interp_thread_yield_node, interp_state_guard, interp_state_guard]
  exact sb_guard_l (sb_guard _)

@[grind .] theorem interp_state_thread_user {X : Type} (e : E.I)
    (k : E.O e → CTree (yieldE ⊕ₑ forkE ⊕ₑ E) B X) (s : S) :
    interp_state h (interp_thread (.vis (.inr (.inr e)) k)) s ~
      (h e s >>= fun p => interp_state h (interp_thread (k p.1)) p.2) := by
  rw [interp_thread_user_node, interp_state_vis]
  refine sbisim_bind_eq _ fun p => ?_
  simp only [interp_state_guard]
  exact sb_guard_l (sb_guard_l (sb_guard _))

end ThreadStateInterp

/-! ### Instrumentation algebra for raw threads -/

section InstrThread
variable {Sg : Type} {B : Effect.{0}}

theorem instr_thread_ret {X : Type} (x : X) (σ : Sg) :
    instr_thread (B := B) (pure x) σ = pure (x, σ) :=
  interp_state_thread_ret h_stateW x σ

theorem instr_thread_bind {A C : Type} (t : CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B A)
    (k : A → CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B C) (σ : Sg) :
    instr_thread (t >>= k) σ = (instr_thread t σ >>= fun p => instr_thread (k p.1) p.2) :=
  interp_state_thread_bind h_stateW t k σ

theorem instr_thread_yield {X : Type} (k : PUnit → CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B X)
    (σ : Sg) : instr_thread (.vis (.inl ⟨⟩) k) σ ~ instr_thread (k ⟨⟩) σ :=
  interp_state_thread_yield h_stateW k σ

theorem instr_thread_get {X : Type} (k : Sg → CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B X)
    (σ : Sg) : instr_thread (.vis (.inr (.inr StateOp.get)) k) σ ~ instr_thread (k σ) σ := by
  refine sbisim_trans (interp_state_thread_user h_stateW StateOp.get k σ) ?_
  simp only [h_stateW, pure_bind']
  exact sbisim_refl _

theorem instr_thread_put {X : Type} (σ' : Sg)
    (k : PUnit → CTree (yieldE ⊕ₑ forkE ⊕ₑ stateE Sg) B X) (σ : Sg) :
    instr_thread (.vis (.inr (.inr (StateOp.put σ'))) k) σ ~
      (log σ' >>= fun _ => instr_thread (k ⟨⟩) σ') := by
  refine sbisim_trans (interp_state_thread_user h_stateW (StateOp.put σ') k σ) ?_
  simp only [h_stateW, bind_assoc, pure_bind']
  exact sbisim_refl _

end InstrThread

/-! ## Exact equations of the scheduling observation projection -/

section Project
variable {E B : Effect.{0}} {X : Type}

@[simp] theorem project_scheduled_ret (x : X) :
    project_scheduled (pure x : CTree (E ⊕ₑ schedE) B X) = pure x :=
  interp_ret _ x

@[simp] theorem project_scheduled_stuck :
    project_scheduled (.stuck : CTree (E ⊕ₑ schedE) B X) = .stuck :=
  interp_stuck _

@[simp] theorem project_scheduled_guard (t : CTree (E ⊕ₑ schedE) B X) :
    project_scheduled (.guard t) = .guard (project_scheduled t) :=
  interp_guard _ t

@[simp] theorem project_scheduled_step (t : CTree (E ⊕ₑ schedE) B X) :
    project_scheduled (.step t) = .step (.guard (project_scheduled t)) :=
  interp_step _ t

@[simp] theorem project_scheduled_br (c : B.I) (k : B.O c → CTree (E ⊕ₑ schedE) B X) :
    project_scheduled (.br c k) = .br c fun x => .guard (project_scheduled (k x)) :=
  interp_br' _ c k

@[simp] theorem project_scheduled_user (e : E.I) (k : E.O e → CTree (E ⊕ₑ schedE) B X) :
    project_scheduled (.vis (.inl e) k) = .vis e fun x => .guard (project_scheduled (k x)) := by
  simp [project_scheduled, handle_scheduled_step, CTree.trigger]

@[simp] theorem project_scheduled_scheduled (i : Nat) (k : PUnit → CTree (E ⊕ₑ schedE) B X) :
    project_scheduled (.vis (.inr i) k) = .step (.guard (project_scheduled (k ⟨⟩))) := by
  simp [project_scheduled, handle_scheduled_step]

end Project

-- Not ported: `project_scheduled_equ`, `interp_yield_equ`, `interp_thread_equ_proper`,
-- `instr_thread_equ` (`Proper` instances for `equ`, i.e. `congrArg`); `solve_focused_schedule`
-- (Ltac). The head of `Yield/Mod.v` (`rr_pick` … `interp_state_br_alts_sb`) is in
-- `Logic/Yield/Scheduler.lean`.

end Tisl.Yield
