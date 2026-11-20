/- SPDX-License-Identifier: MIT -/
module

public import Logic.Utils.Relations
public import Logic.Utils.Lists

/-!
# Infinite executions and finite replay

A language-independent execution record with a finite script runner `run_turns` over a partial
transition, a constructive builder of an infinite execution from a choice sequence and a total,
invariant-preserving transition, counter/index bookkeeping, and reachability through `Star`
(← `Utils/Execution.v`).
-/

@[expose] public section
namespace Tisl
open CTree (Star)

/-! ## The record -/

/-- An infinite execution: states, selected actions and emitted outputs indexed by turn. -/
structure Execution (St Act Out : Type _) where
  states : Nat → St
  selected : Nat → Act
  emitted : Nat → Out

/-- `e` starts in an initial state and every turn is a `step`. -/
def execution_valid {St Act Out} (step : Act → St → Out → St → Prop) (initial : St → Prop)
    (e : Execution St Act Out) : Prop :=
  initial (e.states 0) ∧ ∀ k, step (e.selected k) (e.states k) (e.emitted k) (e.states (k + 1))

/-- Establish validity and preservation together for generated executions. -/
theorem execution_invariant_steps {St Act Out} (step : Act → St → Out → St → Prop)
    (Inv : St → Prop) (e : Execution St Act Out) :
    Inv (e.states 0) →
    (∀ n, Inv (e.states n) →
      step (e.selected n) (e.states n) (e.emitted n) (e.states (n + 1)) ∧ Inv (e.states (n + 1))) →
    (∀ n, Inv (e.states n)) ∧
      (∀ n, step (e.selected n) (e.states n) (e.emitted n) (e.states (n + 1))) := by
  intro h0 hstep
  have hI : ∀ n, Inv (e.states n) := fun n => by
    induction n with
    | zero => exact h0
    | succ n ih => exact (hstep n ih).2
  exact ⟨hI, fun n => (hstep n (hI n)).1⟩

/-- Every action is chosen infinitely often. -/
def fair_choices {Act} (pick : Nat → Act) : Prop := ∀ a, infinitely (fun k => pick k = a)

/-! ## Finite replay of a script -/

/-- Replay `script` from `s`, concatenating the logs of every output; `none` on a failed step. -/
def run_turns {St Act Out W} (step : Act → St → Option (St × Out)) (logs : Out → List W) :
    List Act → St → Option (St × List W)
  | [], s => some (s, [])
  | who :: rest, s =>
    match step who s with
    | none => none
    | some (next, output) =>
      match run_turns step logs rest next with
      | none => none
      | some (last, tail) => some (last, logs output ++ tail)

section RunTurns
variable {St Act Out W : Type _} (step : Act → St → Option (St × Out)) (logs : Out → List W)

theorem run_turns_append (left right : List Act) (s : St) :
    run_turns step logs (left ++ right) s =
      match run_turns step logs left s with
      | none => none
      | some (middle, first) =>
        match run_turns step logs right middle with
        | none => none
        | some (last, second) => some (last, first ++ second) := by
  induction left generalizing s with
  | nil =>
    simp only [List.nil_append, run_turns]
    rcases run_turns step logs right s with _ | ⟨last, ws⟩ <;> rfl
  | cons who left ih =>
    simp only [List.cons_append, run_turns]
    rcases step who s with _ | ⟨next, output⟩
    · rfl
    · simp only [ih]
      rcases run_turns step logs left next with _ | ⟨middle, first⟩
      · rfl
      · cases h : run_turns step logs right middle <;> simp [h]

theorem run_turns_compose (left right : List Act) (s middle last : St) (first second : List W) :
    run_turns step logs left s = some (middle, first) →
    run_turns step logs right middle = some (last, second) →
    run_turns step logs (left ++ right) s = some (last, first ++ second) := by
  intro hl hr
  rw [run_turns_append, hl]
  simp only [hr]

/-- A script certified turn by turn against a state table `S` and an output table `E` replays
along the table (Lean-only). -/
theorem run_turns_table (script : List Act) (fallback : Act) (S : Nat → St) (E : Nat → Out)
    (cert : ∀ i, i < script.length →
      step (script.getD i fallback) (S i) = some (S (i + 1), E i)) :
    ∀ i, i ≤ script.length →
      run_turns step logs (script.take i) (S 0) =
        some (S i, ((List.range' 0 i).map fun j => logs (E j)).flatten) := by
  intro i
  induction i with
  | zero => intro; rfl
  | succ i ih =>
    intro hi
    have hlt : i < script.length := hi
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      List.range'_concat, List.map_append, List.flatten_append]
    refine run_turns_compose step logs _ _ _ _ _ _ _ (ih (Nat.le_of_lt hlt)) ?_
    have hc := cert i hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at hc
    simp [run_turns, hc]

/-- An invariant preserved by one transition is preserved by a whole run. -/
theorem run_turns_preserves_inv (Inv : St → Prop)
    (preserves : ∀ a s s' o, Inv s → step a s = some (s', o) → Inv s') :
    ∀ script s last ws, Inv s → run_turns step logs script s = some (last, ws) → Inv last := by
  intro script
  induction script with
  | nil => intro s last ws hinv hrun; simp only [run_turns, Option.some.injEq,
      Prod.mk.injEq] at hrun; exact hrun.1 ▸ hinv
  | cons who rest ih =>
    intro s last ws hinv hrun
    simp only [run_turns] at hrun
    split at hrun
    · exact absurd hrun (by simp)
    · rename_i next output hstep
      split at hrun
      · exact absurd hrun (by simp)
      · rename_i last' tail hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        exact hrun.1 ▸ ih next last' tail (preserves who s next output hinv hstep) hrest

end RunTurns

/-! ## Congruence in the state, through an arbitrary state relation

Rocq's `Proper (eq ==> R ==> Roption (RelProd R eq)) step` is the explicit hypothesis `hstep`. -/

section RunTurnsProper
variable {St Act Out W : Type _} (step : Act → St → Option (St × Out)) (logs : Out → List W)
  (R : St → St → Prop)
  (hstep : ∀ a s t, R s t → Option.Rel (fun p q => R p.1 q.1 ∧ p.2 = q.2) (step a s) (step a t))
include hstep

theorem step_some_compatible (a : Act) (s t s' : St) (o : Out) :
    R s t → step a s = some (s', o) → ∃ t', step a t = some (t', o) ∧ R s' t' := by
  intro hst hrun
  have h := hstep a s t hst
  rw [hrun] at h
  revert h
  match step a t with
  | some (t', o') => intro h; cases h with | some h => obtain ⟨hr, rfl⟩ := h; exact ⟨t', rfl, hr⟩
  | none => intro h; cases h

theorem run_turns_proper (script : List Act) :
    ∀ s t, R s t → Option.Rel (fun p q => R p.1 q.1 ∧ p.2 = q.2)
      (run_turns step logs script s) (run_turns step logs script t) := by
  induction script with
  | nil => intro s t hst; exact .some ⟨hst, rfl⟩
  | cons who rest ih =>
    intro s t hst
    simp only [run_turns]
    match step who s, step who t, hstep who s t hst with
    | none, none, .none => exact .none
    | some (next, output), some (next', _), .some ⟨hnext, rfl⟩ =>
      simp only
      match run_turns step logs rest next, run_turns step logs rest next', ih next next' hnext with
      | none, none, .none => exact .none
      | some (last, ws), some (last', _), .some ⟨hlast, rfl⟩ => exact .some ⟨hlast, rfl⟩

theorem run_turns_some_compatible (script : List Act) (s t last : St) (observations : List W) :
    R s t → run_turns step logs script s = some (last, observations) →
    ∃ last', run_turns step logs script t = some (last', observations) ∧ R last last' := by
  intro hst hrun
  have h := run_turns_proper step logs R hstep script s t hst
  rw [hrun] at h
  revert h
  match run_turns step logs script t with
  | some (l', o') => intro h; cases h with | some h => obtain ⟨hr, rfl⟩ := h; exact ⟨l', rfl, hr⟩
  | none => intro h; cases h

end RunTurnsProper

/-! ## Constructing an infinite execution from a choice sequence

The impossible branch is eliminated in `Prop` using totality; no default state is manufactured. -/

section OfChoices
variable {St Act Out : Type _} (step : Act → St → Option (St × Out)) (Inv : St → Prop)
  (total : ∀ a s, Inv s → ∃ r, step a s = some r)
  (preserves : ∀ a s s' o, Inv s → step a s = some (s', o) → Inv s')

/-- The successful, invariant-preserving result of one step from an invariant state. -/
def next_valid (a : Act) (s : St) (hinv : Inv s) :
    {result : St × Out // step a s = some result ∧ Inv result.1} :=
  match hs : step a s with
  | some (next, output) => ⟨(next, output), rfl, preserves a s next output hinv hs⟩
  | none => False.elim (by obtain ⟨r, h⟩ := total a s hinv; simp [hs] at h)

/-- The state after the first `k` choices. -/
def chosen_state (s0 : St) (h0 : Inv s0) (picks : Nat → Act) : Nat → {s : St // Inv s}
  | 0 => ⟨s0, h0⟩
  | j + 1 =>
    let prior := chosen_state s0 h0 picks j
    let next := next_valid step Inv total preserves (picks j) prior.1 prior.2
    ⟨next.1.1, next.2.2⟩

/-- The execution driven by `picks` from `s0`. -/
def execution_of_choices (s0 : St) (h0 : Inv s0) (picks : Nat → Act) : Execution St Act Out where
  states k := (chosen_state step Inv total preserves s0 h0 picks k).1
  selected := picks
  emitted k :=
    let prior := chosen_state step Inv total preserves s0 h0 picks k
    (next_valid step Inv total preserves (picks k) prior.1 prior.2).1.2

theorem execution_of_choices_valid (s0 : St) (h0 : Inv s0) (picks : Nat → Act) :
    execution_valid (fun a s o s' => step a s = some (s', o)) (fun s => s = s0)
      (execution_of_choices step Inv total preserves s0 h0 picks) :=
  ⟨rfl, fun k => (next_valid step Inv total preserves (picks k) _
    (chosen_state step Inv total preserves s0 h0 picks k).2).2.1⟩

@[simp] theorem execution_of_choices_selected (s0 : St) (h0 : Inv s0) (picks : Nat → Act)
    (k : Nat) : (execution_of_choices step Inv total preserves s0 h0 picks).selected k = picks k :=
  rfl

end OfChoices

/-! ## Reading an execution -/

section ExecutionFacts
variable {St Act Out : Type _} (step : Act → St → Option (St × Out)) (Inv : St → Prop)
  (initial : St → Prop)

theorem execution_step (e : Execution St Act Out) (k : Nat) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e →
    step (e.selected k) (e.states k) = some (e.states (k + 1), e.emitted k) :=
  fun h => h.2 k

theorem execution_inv (e : Execution St Act Out) (hinit : ∀ s, initial s → Inv s)
    (preserves : ∀ a s s' o, Inv s → step a s = some (s', o) → Inv s') (k : Nat) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → Inv (e.states k) := by
  intro ⟨hi, hstep⟩
  induction k with
  | zero => exact hinit _ hi
  | succ k ih => exact preserves _ _ _ _ ih (hstep k)

end ExecutionFacts

section ExecutionRun
variable {St Act Out W : Type _} (step : Act → St → Option (St × Out)) (logs : Out → List W)
  (initial : St → Prop)

theorem execution_run_turns (e : Execution St Act Out) (lo len : Nat) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e →
    run_turns step logs ((List.range' lo len).map e.selected) (e.states lo) =
      some (e.states (lo + len), (List.range' lo len).flatMap fun k => logs (e.emitted k)) := by
  intro hvalid
  induction len generalizing lo with
  | zero => rfl
  | succ len ih =>
    simp only [List.range'_succ, List.map_cons, List.flatMap_cons, run_turns,
      execution_step step initial e lo hvalid, ih, Nat.add_assoc, Nat.add_comm 1 len]

end ExecutionRun

/-! ## Windows of an execution

Endpoint relatedness and exact output equality of one window, under a state relation. -/

section ExecutionWindow
variable {St Act Out W : Type _} (step : Act → St → Option (St × Out)) (logs : Out → List W)
  (initial : St → Prop) (R : St → St → Prop)
  (hstep : ∀ a s t, R s t → Option.Rel (fun p q => R p.1 q.1 ∧ p.2 = q.2) (step a s) (step a t))
include hstep

theorem execution_window_state (e : Execution St Act Out) (lo len : Nat) (s : St) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → R (e.states lo) s →
    ∃ last, run_turns step logs ((List.range' lo len).map e.selected) s =
        some (last, (List.range' lo len).flatMap fun k => logs (e.emitted k)) ∧
      R (e.states (lo + len)) last :=
  fun hvalid hs => run_turns_some_compatible step logs R hstep _ _ _ _ _ hs
    (execution_run_turns step logs initial e lo len hvalid)

theorem execution_turn_observation (e : Execution St Act Out) (k : Nat) (s : St) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → R (e.states k) s →
    ∃ next, step (e.selected k) s = some (next, e.emitted k) ∧ R (e.states (k + 1)) next :=
  fun hvalid hs => step_some_compatible step R hstep _ _ _ _ _ hs
    (execution_step step initial e k hvalid)

/-- A window whose script is fixed pointwise: the endpoint state after replaying it. -/
theorem execution_script_state (e : Execution St Act Out) (lo : Nat) (script : List Act)
    (s last : St) (ws : List W) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → R (e.states lo) s →
    (List.range' lo script.length).map e.selected = script →
    run_turns step logs script s = some (last, ws) → R (e.states (lo + script.length)) last := by
  intro hvalid hs hscript hrun
  obtain ⟨actual, hactual, hstate⟩ :=
    execution_window_state step logs initial R hstep e lo script.length s hvalid hs
  rw [hscript, hrun] at hactual
  simp only [Option.some.injEq, Prod.mk.injEq] at hactual
  exact hactual.1 ▸ hstate

/-- A window whose script is fixed pointwise: the state and output at any position inside it. -/
theorem execution_script_emitted (e : Execution St Act Out) (lo : Nat) (script : List Act)
    (i : Nat) (d : Act) (s middle : St) (ws : List W) (next : St) (out : Out) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → R (e.states lo) s →
    (List.range' lo script.length).map e.selected = script →
    i < script.length →
    run_turns step logs (script.take i) s = some (middle, ws) →
    step (script.getD i d) middle = some (next, out) →
    R (e.states (lo + i)) middle ∧ e.emitted (lo + i) = out := by
  intro hvalid hs hscript hi hrun hturn
  have hpre : (List.range' lo i).map e.selected = script.take i := by
    rw [← map_seq_firstn e.selected lo script.length i (Nat.le_of_lt hi), hscript]
  have hsel : e.selected (lo + i) = script.getD i d := by
    conv => rhs; rw [← hscript]
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨actual, hactual, hstate⟩ :=
    execution_window_state step logs initial R hstep e lo i s hvalid hs
  rw [hpre, hrun] at hactual
  simp only [Option.some.injEq, Prod.mk.injEq] at hactual
  obtain ⟨rfl, -⟩ := hactual
  refine ⟨hstate, ?_⟩
  obtain ⟨next', hturn', -⟩ :=
    execution_turn_observation step initial R hstep e (lo + i) middle hvalid hstate
  rw [hsel, hturn] at hturn'
  simp only [Option.some.injEq, Prod.mk.injEq] at hturn'
  exact hturn'.2.symm

/-- Repeated selected windows follow their successful boundary replays. Related replay endpoints
may differ as states, but no failed replay supplies an endpoint. Empty prefixes and cycles are
permitted. -/
theorem execution_script_cycles {C : Type _} (e : Execution St Act Out) (pre cycle : List Act)
    (boundary : C → St) (c0 : C) (advance : C → C) (s : St) :
    Equivalence R →
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → R (e.states 0) s →
    (List.range' 0 pre.length).map e.selected = pre →
    (∃ last ws, run_turns step logs pre s = some (last, ws) ∧ R last (boundary c0)) →
    (∀ k, (List.range' (pre.length + k * cycle.length) cycle.length).map e.selected = cycle) →
    (∀ c, ∃ last ws, run_turns step logs cycle (boundary c) = some (last, ws) ∧
      R last (boundary (advance c))) →
    ∀ k, R (e.states (pre.length + k * cycle.length)) (boundary (Nat.repeat advance k c0)) := by
  intro heqv hvalid hstart hpre ⟨last, ws, hrun, hboundary⟩ hwindows hcycle k
  induction k with
  | zero =>
    have := execution_script_state step logs initial R hstep e 0 pre s last ws hvalid hstart hpre
      hrun
    show R (e.states (pre.length + 0 * cycle.length)) (boundary c0)
    rw [Nat.zero_mul, Nat.add_zero]
    exact heqv.trans (by simpa using this) hboundary
  | succ k ih =>
    obtain ⟨next, obs, hreplay, hnext⟩ := hcycle (Nat.repeat advance k c0)
    have hstate := execution_script_state step logs initial R hstep e
      (pre.length + k * cycle.length) cycle _ next obs hvalid ih (hwindows k) hreplay
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact heqv.trans hstate hnext

/-- A boundary self-transition for each future selected action preserves state relatedness. Its
output is existential and may vary each turn; success is required. -/
theorem execution_stutters_from (e : Execution St Act Out) (start : Nat) (boundary : St) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e →
    R (e.states start) boundary →
    (∀ n, ∃ out, step (e.selected (start + n)) boundary = some (boundary, out)) →
    ∀ n, R (e.states (start + n)) boundary := by
  intro hvalid hstart hstutter n
  induction n with
  | zero => exact hstart
  | succ n ih =>
    obtain ⟨out, hout⟩ := hstutter n
    obtain ⟨next, hturn, hnext⟩ :=
      execution_turn_observation step initial R hstep e (start + n) boundary hvalid ih
    rw [hout] at hturn
    simp only [Option.some.injEq, Prod.mk.injEq] at hturn
    exact hturn.1 ▸ hnext

end ExecutionWindow

/-! ## Counters and observation indices

Generic over an output projection, a state counter and an event index. Each turn contributes at
most one indexed event. -/

section ExecutionCounter
variable {St Act Out W : Type _} (step : Act → St → Option (St × Out)) (initial : St → Prop)
  (events : Out → List W) (counter : St → Nat) (index : W → Nat)
  (hcounter : ∀ a s s' out, step a s = some (s', out) →
    (events out).length ≤ 1 ∧ counter s' = counter s + (events out).length ∧
    ∀ w, w ∈ events out → index w = counter s)
include hcounter

theorem execution_event_index (e : Execution St Act Out) (k : Nat) (w : W) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e →
    w ∈ events (e.emitted k) →
    counter (e.states (k + 1)) = counter (e.states k) + 1 ∧ index w = counter (e.states k) := by
  intro hvalid hobs
  obtain ⟨hlength, hcount, hindex⟩ :=
    hcounter _ _ _ _ (execution_step step initial e k hvalid)
  have hpos : 0 < (events (e.emitted k)).length := List.length_pos_of_mem hobs
  exact ⟨by omega, hindex w hobs⟩

theorem execution_counter_mono (e : Execution St Act Out) (lo hi : Nat) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → lo ≤ hi →
    counter (e.states lo) ≤ counter (e.states hi) := by
  intro hvalid hle
  have hstep : ∀ k, counter (e.states k) ≤ counter (e.states (k + 1)) := fun k => by
    have := (hcounter _ _ _ _ (execution_step step initial e k hvalid)).2.1
    omega
  induction hle with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (hstep _)

theorem execution_event_order (e : Execution St Act Out) (k j : Nat) (w p : W) :
    execution_valid (fun a s o s' => step a s = some (s', o)) initial e → k < j →
    w ∈ events (e.emitted k) → p ∈ events (e.emitted j) → index w < index p := by
  intro hvalid hkj hw hp
  obtain ⟨hk, hi⟩ :=
    execution_event_index step initial events counter index hcounter e k w hvalid hw
  obtain ⟨-, hj⟩ := execution_event_index step initial events counter index hcounter e j p hvalid hp
  have := execution_counter_mono step initial events counter index hcounter e (k + 1) j hvalid hkj
  omega

end ExecutionCounter

/-! ## Reachability -/

/-- `s` is reachable from an initial state by finitely many steps. -/
def reachable {St Act Out} (step : Act → St → Out → St → Prop) (initial : St → Prop) (s : St) :
    Prop :=
  ∃ s0, initial s0 ∧ Star (fun x y => ∃ a o, step a x o y) s0 s

theorem reachable_inv {St Act Out} (step : Act → St → Out → St → Prop) (initial : St → Prop)
    (Inv : St → Prop) (hinit : ∀ s, initial s → Inv s)
    (preserves : ∀ a s o s', Inv s → step a s o s' → Inv s') (s : St) :
    reachable step initial s → Inv s := by
  intro ⟨s0, h0, hclos⟩
  induction hclos with
  | refl => exact hinit _ h0
  | tail _ hyz ih => obtain ⟨a, o, h⟩ := hyz; exact preserves _ _ _ _ ih h

end Tisl

-- Not ported: the section-local `valid` abbreviations (inlined as `execution_valid …`).
