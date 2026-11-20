/- SPDX-License-Identifier: MIT -/
module

public import Examples.CSL.Allocator.Execution

/-!
# Allocator liveness: contention and ownership ranks

Model-level budgets (contention ranks, `remote_free_lockfree`), raw-source realization and the
pending-remote alignment (`source_remote_free_lockfree`), and the ownership/round ranks with the
reclaim credit (`retired_eventually_reclaimed`, `source_retired_eventually_reclaimed`)
(<- `examples/CSL/Allocator/Liveness.v`, lines 1-1179; the rest is in `Liveness.lean`).
-/

@[expose] public section
namespace Examples.CSL.Allocator.Liveness
open CTree Tisl Tisl.Heap Tisl.Ctx Tisl.CSL Tisl.Yield CoCSL
open Examples.CSL.Allocator.Layout Examples.CSL.Allocator.Program Examples.CSL.Allocator.Model
open Examples.CSL.Allocator.Execution
open Actor owner_pc remote_pc

/-! ## Model-level budgets -/

def event_is (tag : Nat) (logs : List (CSLObs (Nat × Nat))) : Bool :=
  (csl_emissions logs).any fun emission => emission.value.1 == tag

def remote_pending (who : Actor) (s : AState) : Bool :=
  match who with
  | Owner => false
  | Remote0 => match s.remote0_state with | RPoll => false | _ => true
  | Remote1 => match s.remote1_state with | RPoll => false | _ => true

def owner_selected (who : Actor) : Bool :=
  match who with | Owner => true | _ => false

theorem owner_selected_spec (who : Actor) : owner_selected who = true ↔ who = Owner := by
  cases who <;> simp [owner_selected]

theorem event_is_spec (tag : Nat) (logs : List (CSLObs (Nat × Nat))) :
    event_is tag logs = true ↔ ∃ block idx, stamp (tag, block) idx ∈ csl_emissions logs := by
  simp only [event_is, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨kind, block⟩, idx⟩, hin, rfl⟩; exact ⟨block, idx, hin⟩
  · rintro ⟨block, idx, hin⟩; exact ⟨_, hin, rfl⟩

/-- Ghost potentials, not execution states; the default head is immaterial on an invariant
state, where the remote header is present. -/
def contention_head (s : AState) : Nat :=
  (s.aheap (remote_head 1)).getD 0

def contention_stale (current : Nat) : remote_pc → Nat
  | RLink _ old | RCAS _ old => if current = old then 0 else 1
  | RPoll | RRead _ => 0

def contention_phase : remote_pc → Nat
  | RPoll | RRead _ => 3 | RLink _ _ => 2 | RCAS _ _ => 1

def contention_cost (current : Nat) (pc : remote_pc) : Nat :=
  contention_phase pc + 3 * contention_stale current pc

def contention_pending_potential (current : Nat) (p0 p1 : remote_pc) : Nat :=
  contention_cost current p0 + contention_cost current p1 + (if current = 0 then 0 else 6)

def contention_failure_potential (current : Nat) (p0 p1 : remote_pc) : Nat :=
  contention_stale current p0 + contention_stale current p1 + (if current = 0 then 0 else 2)

def contention_pending_rank (s : AState) : Nat :=
  contention_pending_potential (contention_head s) s.remote0_state s.remote1_state

def contention_failure_rank (s : AState) : Nat :=
  contention_failure_potential (contention_head s) s.remote0_state s.remote1_state

theorem contention_stale_bound (current : Nat) (pc : remote_pc) :
    contention_stale current pc ≤ 1 := by
  cases pc <;> simp only [contention_stale] <;> (try split) <;> omega

theorem contention_cost_bound (current : Nat) (pc : remote_pc) :
    contention_cost current pc ≤ 5 := by
  unfold contention_cost
  cases pc <;> simp only [contention_phase, contention_stale] <;> (try split) <;> omega

theorem contention_pending_rank_bound (s : AState) : contention_pending_rank s ≤ 16 := by
  have := contention_cost_bound (contention_head s) s.remote0_state
  have := contention_cost_bound (contention_head s) s.remote1_state
  simp only [contention_pending_rank, contention_pending_potential]
  split <;> omega

theorem contention_failure_rank_bound (s : AState) : contention_failure_rank s ≤ 4 := by
  have := contention_stale_bound (contention_head s) s.remote0_state
  have := contention_stale_bound (contention_head s) s.remote1_state
  simp only [contention_failure_rank, contention_failure_potential]
  split <;> omega

theorem contention_stale_reset (current : Nat) (pc : remote_pc) :
    contention_stale 0 pc ≤ contention_stale current pc + 1 := by
  have := contention_stale_bound 0 pc; omega

theorem contention_cost_reset (current : Nat) (pc : remote_pc) :
    contention_cost 0 pc ≤ contention_cost current pc + 3 := by
  have := contention_stale_reset current pc
  simp only [contention_cost]; omega

theorem contention_reset_ranks (current : Nat) (p0 p1 : remote_pc) :
    contention_pending_potential 0 p0 p1 ≤ contention_pending_potential current p0 p1 ∧
    contention_failure_potential 0 p0 p1 ≤ contention_failure_potential current p0 p1 := by
  have := contention_cost_reset current p0
  have := contention_cost_reset current p1
  have := contention_stale_reset current p0
  have := contention_stale_reset current p1
  by_cases h : current = 0
  · subst h; omega
  · simp only [contention_pending_potential, contention_failure_potential, h, ↓reduceIte]; omega

/-- Every block of the ownership partition lies past the five metadata cells of page `1`. -/
theorem page_block_ge {capacity b : Nat} (h : b ∈ page_blocks 1 capacity) : 6 ≤ b :=
  (page_blocks_bounds 1 capacity b h).1

theorem turn_contention_ranks (capacity : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) :
    allocator_inv 1 capacity s → turn 1 who s = some (t, event) →
    event_is tag_retire event = false →
    (if remote_pending who s then 1 else 0) + contention_pending_rank t ≤
      contention_pending_rank s ∧
    (if event_is tag_retry event then 1 else 0) + contention_failure_rank t ≤
      contention_failure_rank s := by
  obtain ⟨h, allocs, count, op, p0, p1⟩ := s
  rintro ⟨L, R, D, -, -, m0, m1, -, -, hd, -, -, -, -, -, hp, -, -, -, -⟩ hturn hnoret
  have hge : ∀ x, x ∈ L ++ R ++ D ++ mailbox_nodes m0 ++ mailbox_nodes m1 ++ held p0 ++
      held p1 → 6 ≤ x := fun x hx => page_block_ge (hp.subset hx)
  dsimp only at hd hp
  have hheld : ∀ b, b ∈ held p0 ++ held p1 → ¬ 1 = b := fun b hb =>
    have := hge b (by simp only [List.mem_append] at hb ⊢; rcases hb with hb | hb <;> simp [hb])
    by omega
  have hdrain : ∀ v, h (drain_head 1) = some v → ¬(v == 0) = true → ¬ 1 = v := by
    intro v hv hz
    rw [hd, Option.some.injEq] at hv
    subst hv
    cases D with
    | nil => simp at hz
    | cons b D => have := hge b (by simp); simp; omega
  clear hge hp hd
  cases who <;>
    simp only [turn, Bool.false_eq_true, ↓reduceIte] at hturn <;>
    (repeat' split at hturn) <;>
    simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hturn <;>
    obtain ⟨rfl, rfl⟩ := hturn
  all_goals
    simp_all [contention_pending_rank, contention_failure_rank, contention_head,
      remote_pending, event_is, csl_emissions, upd, remote_head, drain_head,
      local_head, mailbox, tag_retry, tag_retire, tag_reclaim, tag_alloc, held]
  all_goals first
    | omega
    | exact contention_reset_ranks _ _ _
    | simp only [contention_pending_potential, contention_failure_potential, contention_cost,
        contention_phase.eq_1, contention_phase.eq_2, contention_phase.eq_3,
        contention_phase.eq_4, contention_stale.eq_1, contention_stale.eq_2,
        contention_stale.eq_3, contention_stale.eq_4, ↓reduceIte, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add]
      (repeat' split) <;> omega


theorem execution_contention_ranks (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k : Nat) :
    allocator_valid capacity c e → event_is tag_retire (e.emitted k) = false →
    (if remote_pending (e.selected k) (e.states k) then 1 else 0) +
        contention_pending_rank (e.states (k + 1)) ≤ contention_pending_rank (e.states k) ∧
    (if event_is tag_retry (e.emitted k) then 1 else 0) +
        contention_failure_rank (e.states (k + 1)) ≤ contention_failure_rank (e.states k) :=
  fun hv hnone => turn_contention_ranks capacity _ _ _ _
    (execution_inv (turn 1) (allocator_inv 1 capacity) (fun s => s = initial_state capacity c) e
      (allocator_initial_inv capacity c) (turn_preserves_inv 1 capacity) k hv)
    (execution_step (turn 1) (fun s => s = initial_state capacity c) e k hv) hnone

/-- Both budgets are `credit_interval` instances: the credit is the rank at the execution's
state, the charge the pending remote turn (resp. `tag_retry`), the goal publication of
`tag_retire`. -/
theorem no_publication_contention_potential (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) :
    allocator_valid capacity c e →
    (∀ k, lo ≤ k ∧ k < lo + len → event_is tag_retire (e.emitted k) = false) →
    count_if (fun k => remote_pending (e.selected k) (e.states k)) lo len +
        contention_pending_rank (e.states (lo + len)) ≤ contention_pending_rank (e.states lo) ∧
    count_if (fun k => event_is tag_retry (e.emitted k)) lo len +
        contention_failure_rank (e.states (lo + len)) ≤ contention_failure_rank (e.states lo) := by
  intro hv hnone
  have hgoal : ∀ k, lo ≤ k ∧ k < lo + len → ¬ event_is tag_retire (e.emitted k) = true :=
    fun k hk => by simp [hnone k hk]
  constructor
  · obtain ⟨r, rfl, hb⟩ := credit_interval
      (fun k r => r = contention_pending_rank (e.states k))
      (fun k => remote_pending (e.selected k) (e.states k))
      (fun k => event_is tag_retire (e.emitted k) = true)
      (fun k r hr hg => ⟨_, rfl,
        hr ▸ (execution_contention_ranks capacity c e k hv (by simpa using hg)).1⟩)
      lo len _ rfl hgoal
    exact hb
  · obtain ⟨r, rfl, hb⟩ := credit_interval
      (fun k r => r = contention_failure_rank (e.states k))
      (fun k => event_is tag_retry (e.emitted k))
      (fun k => event_is tag_retire (e.emitted k) = true)
      (fun k r hr hg => ⟨_, rfl,
        hr ▸ (execution_contention_ranks capacity c e k hv (by simpa using hg)).2⟩)
      lo len _ rfl hgoal
    exact hb

/-- Only a failed remote CAS emits `tag_retry`; its unit stale-bit charge bounds the failures
independently of the number of idle turns. -/
theorem no_publication_failed_cas_bound (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) :
    allocator_valid capacity c e →
    (∀ k, lo ≤ k ∧ k < lo + len → event_is tag_retire (e.emitted k) = false) →
    count_if (fun k => event_is tag_retry (e.emitted k)) lo len ≤ 4 := by
  intro hv hnone
  have := (no_publication_contention_potential capacity c e lo len hv hnone).2
  have := contention_failure_rank_bound (e.states lo)
  omega

theorem no_publication_pending_bound (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) :
    allocator_valid capacity c e →
    (∀ k, lo ≤ k ∧ k < lo + len → event_is tag_retire (e.emitted k) = false) →
    count_if (fun k => remote_pending (e.selected k) (e.states k)) lo len ≤ 16 := by
  intro hv hnone
  have := (no_publication_contention_potential capacity c e lo len hv hnone).1
  have := contention_pending_rank_bound (e.states lo)
  omega

theorem remote_free_lockfree (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) :
    allocator_valid capacity c e →
    infinitely (fun k => remote_pending (e.selected k) (e.states k) = true) →
    infinitely (fun k => event_is tag_retire (e.emitted k) = true) := by
  intro hv hpending lo
  obtain ⟨len, hmany⟩ := infinitely_count_if _ hpending 17 lo
  rcases finite_bool_search (fun k => event_is tag_retire (e.emitted k)) lo len with
    ⟨k, hk, hev⟩ | hnone
  · exact ⟨k, hk.1, hev⟩
  · have := no_publication_pending_bound capacity c e lo len hv hnone
    omega


/-! ## Raw source executions -/

theorem source_pool0_branchfree (i : Fin 3) : BranchFree (source_pool0 1)[i] := by
  obtain ⟨i, hi⟩ := i
  match i, hi with
  | 0, _ | 1, _ | 2, _ => exact denote_branchfree _

/-- Finite raw-source reachability needs no model premise: every physical slot stays
selectable. -/
theorem every_reachable_source_slot_yields (capacity : Nat) (ctx : Ctx) (c : Nat)
    (ts : Pool sE Bn 3) (sigma : SSig) (i : Fin 3) :
    reachable (pool_step 2 sh slot_of_actor)
      (fun p => pool_equ p.1 (source_pool0 1) ∧
        p.2 = ((page_heap 1 capacity hemp, upd hemp 1 (page_size capacity)), (ctx, c)))
      (ts, sigma) →
    BranchFree ts[i] ∧
    (∃ logs residual sigma', ThreadSegment sh csl_sb ts[i] sigma logs residual sigma') ∧
    ¬ guard_equ ts[i] (pure ⟨⟩) ∧
    (∀ k : Bool → Thread sE Bn, ¬ guard_equ ts[i] (.vis (.inr (.inl ⟨⟩)) k)) ∧
    (∀ (c : Bn.I) (k : Bn.O c → Thread sE Bn), ¬ guard_equ ts[i] (.br c k)) ∧
    (∀ u, ¬ guard_equ ts[i] (.step u)) ∧
    ¬ guard_equ ts[i] (.stuck : Thread sE Bn) ∧
    ¬ guard_equ ts[i] (CTree.spinS : Thread sE Bn) := by
  intro hreach
  have hbf : ∀ j : Fin 3, BranchFree ts[j] := by
    refine reachable_inv (pool_step 2 sh slot_of_actor) _
      (fun p => ∀ j : Fin 3, BranchFree p.1[j]) ?_ ?_ (ts, sigma) hreach
    · rintro ⟨ts0, sigma0⟩ ⟨hE, -⟩ j
      exact branchfree_equ_impl _ _ (hE j).symm (source_pool0_branchfree j)
    · rintro who ⟨ts1, sigma1⟩ logs ⟨ts2, sigma2⟩ h hstep
      exact pool_step_branchfree 2 sh slot_of_actor who ts1 sigma1 logs ts2 sigma2 hstep h
  refine ⟨hbf i, ?_⟩
  obtain ⟨s, hinv, hagree, hpool⟩ := pool_simulation_reachable (allocator_simulation 1 capacity)
    (source_pool0 1) _ (initial_state capacity c) (initial_state_inv capacity c)
    ⟨heq_refl _, heq_refl _, rfl⟩ (pool_equ_guard _ _ (source_pool0_initial capacity c))
    ts sigma hreach
  rw [← slot_of_actor_of_slot i]
  obtain ⟨event, residual, sigma', hseg⟩ := pool_simulation_worker_segment
    (allocator_simulation 1 capacity) ts s (actor_of_slot i) sigma hinv hagree hpool
  obtain ⟨hr, hf, hb, hs, hstuck⟩ := pool_simulation_no_terminal_prefix
    (allocator_simulation 1 capacity) ts s (actor_of_slot i) sigma hinv hagree hpool
  obtain ⟨-, hspin, -⟩ := pool_simulation_no_fault_or_divergence
    (allocator_simulation 1 capacity) ts s (actor_of_slot i) sigma hinv hagree hpool
  exact ⟨⟨event, residual, sigma', hseg⟩, hr, hf, hb, hs, hstuck, hspin⟩

theorem valid_execution_realizes_source (capacity : Nat) (ctx : Ctx) (c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) :
    allocator_valid capacity c e →
    realizes (prepend_chunk
      ((new_page_logs 1 capacity managed_empty).map fun o => .obs (E := writerE _) o ⟨⟩)
      (fun j => turn_labels (e.emitted j))) 0
      (run_nd (allocator_program capacity) (managed_empty, (ctx, c))) := by
  intro hv
  refine realizes_sbisim (sbisim_symm (run_nd_allocator_bisim capacity ctx c)) ?_
  refine realizes_emit_list_prefix _ _ _ ?_
  exact valid_execution_realizes_model 2 actor_of_slot (turn 1) slot_of_actor
    actor_of_slot_of_actor _ e hv 0 _ (by rw [hv.1]; exact sbisim_refl _)

/-- Initialization labels precede the turns; each turn keeps exactly one scheduling tau, then its
mutation snapshots in source order and its optional final user emission. -/
theorem run_turns_realizes_source (capacity : Nat) (ctx : Ctx) (c : Nat) (script : List Actor)
    (last : AState) (logs : List (CSLObs (Nat × Nat))) :
    run_turns (turn 1) (fun xs => xs) script (initial_state capacity c) = some (last, logs) →
    ∃ labels residual,
      Option.map (fun result =>
          (new_page_logs 1 capacity managed_empty).map (fun o => .obs (E := writerE _) o ⟨⟩) ++
            result.2)
        (run_turns (turn 1) turn_labels script (initial_state capacity c)) = some labels ∧
      label_logs labels = new_page_logs 1 capacity managed_empty ++ logs ∧
      label_taus labels = script.length ∧
      FiniteSteps (run_nd (allocator_program capacity) (managed_empty, (ctx, c))) labels residual ∧
      residual ~ (model_nd 2 actor_of_slot (turn 1) last
        : ctreeW (CSLObs (Nat × Nat)) Bn (PUnit × SSig)) := by
  intro hrun
  obtain ⟨labels, model, hlabels, hlogs, htaus, hsteps, emodel⟩ :=
    model_run_turns_labels (X := PUnit × SSig) (B := Bn) 2 actor_of_slot (turn 1) slot_of_actor
      actor_of_slot_of_actor script (initial_state capacity c) last logs hrun
  obtain ⟨residual, hsource, eres⟩ := finite_steps_sbisim
    (finite_steps_app (finite_steps_emit_list (new_page_logs 1 capacity managed_empty) _) hsteps)
    _ (sbisim_symm (run_nd_allocator_bisim capacity ctx c))
  refine ⟨_, residual, by rw [hlabels]; rfl, ?_, ?_, hsource,
    sbisim_trans (sbisim_symm eres) emodel⟩
  · rw [label_logs_app, hlogs]
    generalize new_page_logs 1 capacity managed_empty = init
    induction init with
    | nil => rfl
    | cons o init ih => simpa [label_logs] using ih
  · rw [label_taus_app, htaus]; simp [label_taus]


/-- A pending raw remote is one of the actual continuations after mailbox pickup and before
`remote_free` returns through the successful CAS path. -/
def raw_remote_pending (base : Nat) (client : Bool) (t : Thread sE Bn) : Prop :=
  ∃ pc, pc ≠ RPoll ∧ guard_equ t (remote_residual base client pc)

def selected_source_pending
    (se : Execution (Pool sE Bn 3 × SSig) Actor (List (CSLObs (Nat × Nat)))) (k : Nat) : Prop :=
  match se.selected k with
  | Owner => False
  | Remote0 => raw_remote_pending 1 false (se.states k).1[slot_of_actor Remote0]
  | Remote1 => raw_remote_pending 1 true (se.states k).1[slot_of_actor Remote1]

/-- The heap events answer in `Nat`, `Unit` and `Bool`: distinct types. -/
theorem nat_neq_unit : (Nat : Type) = Unit → False := by
  intro h
  have : ∀ x y : Nat, x = y := by rw [h]; intro x y; rfl
  exact absurd (this 0 1) (by decide)

theorem nat_neq_bool : (Nat : Type) = Bool → False := by
  intro h
  have : ∀ x y z : Nat, x = y ∨ y = z ∨ x = z := by
    rw [h]; intro x y z; cases x <;> cases y <;> cases z <;> simp
  rcases this 0 1 2 with h | h | h <;> exact absurd h (by decide)

def remote_first_type (pc : remote_pc) : Type :=
  match pc with | RPoll | RRead _ => Nat | RLink _ _ => Unit | RCAS _ _ => Bool

def remote_first_event (base : Nat) (client : Bool) (pc : remote_pc) : heapE.I :=
  match pc with
  | RPoll => .read (mailbox base client)
  | RRead _ => .read (remote_head base)
  | RLink block old => .write block old
  | RCAS block old => .cas (remote_head base) old block

/-- The answer type of `remote_first_event` is `remote_first_type` (Rocq indexes the event by
it). -/
theorem remote_first_event_type (base : Nat) (client : Bool) (pc : remote_pc) :
    heapE.O (remote_first_event base client pc) = remote_first_type pc := by
  cases pc <;> rfl

theorem remote_residual_first_event (base : Nat) (client : Bool) (pc : remote_pc) :
    ∃ k, remote_residual base client pc =
      .vis (.inr (.inr (.inl (remote_first_event base client pc)))) k := by
  cases pc <;> apply Exists.intro
  · simp only [remote_residual, denote, remote_client, source_raw_until, client_round,
      source_raw_bind, source_raw_read_head]
    rfl
  · simp only [remote_residual, remote_free, source_raw_until, remote_attempt,
      source_raw_bind, source_raw_read_head]
    rfl
  · simp only [remote_residual, remote_link_tail, source_raw_bind, source_raw_write_head]
    rfl
  · simp only [remote_residual, remote_cas_tail, source_raw_bind, source_raw_cas_head]
    rfl

theorem remote_poll_not_pending (base : Nat) (client : Bool) (pc : remote_pc) :
    pc ≠ RPoll →
    ¬ guard_equ (remote_residual base client RPoll) (remote_residual base client pc) := by
  intro hpc he
  have he := guard_equ_sbisim _ _ he
  obtain ⟨kp, ep⟩ := remote_residual_first_event base client RPoll
  obtain ⟨kq, eq⟩ := remote_residual_first_event base client pc
  rw [ep, eq] at he
  have hev := sbisim_vis_invT (0 : Nat) he
  cases pc with
  | RPoll => exact hpc rfl
  | RRead =>
    injection hev with hev; injection hev with hev; injection hev with hev
    injection hev with hev
    cases client <;> simp only [mailbox, remote_head] at hev <;> omega
  | _ =>
    injection hev with hev; injection hev with hev; injection hev with hev
    injection hev

theorem raw_remote_pending_alignment (base : Nat) (client : Bool) (t : Thread sE Bn)
    (pc : remote_pc) :
    guard_equ t (remote_residual base client pc) →
    (raw_remote_pending base client t ↔ (match pc with | RPoll => false | _ => true) = true) := by
  intro he
  cases pc with
  | RPoll =>
    refine ⟨fun ⟨pc, hpc, hraw⟩ => ?_, nofun⟩
    exact absurd (guard_equ_trans _ _ _ (guard_equ_sym _ _ he) hraw)
      (remote_poll_not_pending base client pc hpc)
  | RRead b => exact ⟨fun _ => rfl, fun _ => ⟨RRead b, nofun, he⟩⟩
  | RLink b old => exact ⟨fun _ => rfl, fun _ => ⟨RLink b old, nofun, he⟩⟩
  | RCAS b old => exact ⟨fun _ => rfl, fun _ => ⟨RCAS b old, nofun, he⟩⟩


theorem allocator_execution_valid (capacity c : Nat) (picks : Nat → Actor) :
    allocator_valid capacity c (allocator_execution capacity c picks) :=
  execution_of_choices_valid _ _ _ _ _ _ _

/-- On a valid raw execution the raw pending predicate is exactly the model's pending-remote
predicate at the model execution making the same selections. -/
theorem selected_source_pending_alignment (capacity : Nat) (ctx : Ctx) (c : Nat)
    (se : Execution (Pool sE Bn 3 × SSig) Actor (List (CSLObs (Nat × Nat)))) (k : Nat) :
    allocator_source_valid capacity ctx c se →
    (selected_source_pending se k ↔
      remote_pending (se.selected k)
        ((allocator_execution capacity c se.selected).states k) = true) := by
  intro hvalid
  obtain ⟨-, -, hpool, -⟩ := source_execution_complete (allocator_simulation 1 capacity)
    (source_pool0 1) _ (initial_state capacity c) se (allocator_execution capacity c se.selected)
    (initial_state_inv capacity c) ⟨heq_refl _, heq_refl _, rfl⟩
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) hvalid
    (allocator_execution_valid capacity c se.selected) (fun _ => rfl) k
  unfold selected_source_pending
  cases se.selected k with
  | Owner => exact ⟨False.elim, nofun⟩
  | Remote0 => exact raw_remote_pending_alignment _ _ _ _ (hpool (slot_of_actor Remote0))
  | Remote1 => exact raw_remote_pending_alignment _ _ _ _ (hpool (slot_of_actor Remote1))

theorem source_remote_free_lockfree (capacity : Nat) (ctx : Ctx) (c : Nat)
    (se : Execution (Pool sE Bn 3 × SSig) Actor (List (CSLObs (Nat × Nat)))) :
    allocator_source_valid capacity ctx c se →
    infinitely (selected_source_pending se) →
    infinitely (fun k =>
      ∃ block idx, CSLObs.emit (stamp (tag_retire, block) idx) ∈ se.emitted k) := by
  intro hvalid hpending
  have halign := source_execution_complete (allocator_simulation 1 capacity)
    (source_pool0 1) _ (initial_state capacity c) se (allocator_execution capacity c se.selected)
    (initial_state_inv capacity c) ⟨heq_refl _, heq_refl _, rfl⟩
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) hvalid
    (allocator_execution_valid capacity c se.selected) (fun _ => rfl)
  have hlive := remote_free_lockfree capacity c _ (allocator_execution_valid capacity c se.selected)
    fun n => by
      obtain ⟨k, hnk, hk⟩ := hpending n
      exact ⟨k, hnk, (selected_source_pending_alignment capacity ctx c se k hvalid).1 hk⟩
  intro n
  obtain ⟨k, hnk, hevent⟩ := hlive n
  obtain ⟨block, idx, hevent⟩ := (event_is_spec _ _).1 hevent
  refine ⟨k, hnk, block, idx, ?_⟩
  rw [(halign k).2.2.2]
  exact (csl_emissions_in _ _).1 hevent

/-! ## Ownership and round ranks -/

theorem owner_lists_lengths (capacity : Nat) (s : AState) (L R D : List Nat) :
    allocator_view 1 capacity s L R D → L.length + R.length + D.length ≤ capacity := by
  rintro ⟨-, -, m0, m1, -, -, -, -, -, -, -, -, hp, -⟩
  have := hp.length_eq
  simp only [List.length_append, page_blocks_length] at this
  omega

theorem owner_lists_disjoint (capacity : Nat) (s : AState) (L R D : List Nat) (b : Nat) :
    allocator_view 1 capacity s L R D → b ∈ R ++ D → b ∉ L := by
  rintro ⟨-, -, m0, m1, -, -, -, -, -, -, -, -, hp, -⟩ hrd hl
  have := List.nodup_iff_count.1 (hp.nodup_iff.2 (page_blocks_nodup 1 capacity)) b
  simp only [List.count_append] at this
  have := List.count_pos_iff.2 hl
  rcases List.mem_append.1 hrd with h | h <;> have := List.count_pos_iff.2 h <;> omega

def owner_boundary (who : Actor) (pc : owner_pc) : Bool :=
  match who, pc with | Owner, OOffer true => true | _, _ => false

def collection_phase (pc : owner_pc) : Bool :=
  match pc with | ORead | OCAS _ => true | _ => false

def owner_rank (capacity : Nat) (pc : owner_pc) (R D : List Nat) : Nat :=
  match pc with
  | ORead => 2 * (capacity - R.length) + capacity + 5
  | OCAS old => 2 * (capacity - R.length) + capacity + (if R.headD 0 = old then 4 else 6)
  | ODrain => D.length + 3
  | OOffer false => 2
  | OOffer true => 1

def owner_round_bound (capacity : Nat) : Nat := 3 * capacity + 5

def block_event (tag block : Nat) (logs : List (CSLObs (Nat × Nat))) : Prop :=
  ∃ idx, stamp (tag, block) idx ∈ csl_emissions logs

theorem ownership_rank_step (capacity : Nat) (who : Actor) (pc pc' : owner_pc)
    (event : List (CSLObs (Nat × Nat))) (L R D L' R' D' : List Nat) :
    ownership_transition who pc pc' event L R D L' R' D' →
    R.length ≤ capacity → D.length ≤ capacity → R'.length ≤ capacity → D'.length ≤ capacity →
    if owner_boundary who pc
    then owner_rank capacity pc' R' D' ≤ owner_round_bound capacity
    else (if owner_selected who then 1 else 0) + owner_rank capacity pc' R' D' ≤
      owner_rank capacity pc R D := by
  intro hstep hr hd hr' hd'
  cases hstep <;>
    simp_all [owner_boundary, owner_selected, owner_rank, owner_after_offer, owner_round_bound] <;>
    (repeat' split) <;> (try simp_all) <;> omega

theorem owner_rank_positive (capacity : Nat) (pc : owner_pc) (R D : List Nat) :
    0 < owner_rank capacity pc R D := by
  cases pc with
  | OOffer client => cases client <;> simp [owner_rank]
  | _ => simp only [owner_rank]; (try split) <;> omega

theorem owner_lists_step_bounded (capacity : Nat) (who : Actor) (s t : AState)
    (event : List (CSLObs (Nat × Nat))) (L R D : List Nat) :
    allocator_view 1 capacity s L R D →
    owner_rank capacity s.owner_state R D ≤ owner_round_bound capacity →
    turn 1 who s = some (t, event) →
    ∃ L' R' D', allocator_view 1 capacity t L' R' D' ∧
      owner_rank capacity t.owner_state R' D' ≤ owner_round_bound capacity ∧
      ownership_transition who s.owner_state t.owner_state event L R D L' R' D' := by
  intro hview hbound hturn
  obtain ⟨L', R', D', hview', hstep⟩ :=
    turn_view_step 1 capacity who s t event L R D hview hturn
  have := owner_lists_lengths capacity s L R D hview
  have := owner_lists_lengths capacity t L' R' D' hview'
  have hrank := ownership_rank_step capacity who _ _ event L R D L' R' D' hstep
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨L', R', D', hview', ?_, hstep⟩
  split at hrank <;> omega

theorem execution_owner_rank (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k : Nat) :
    allocator_valid capacity c e → ∃ L R D,
      allocator_view 1 capacity (e.states k) L R D ∧
      owner_rank capacity (e.states k).owner_state R D ≤ owner_round_bound capacity := by
  intro hv
  refine execution_inv (turn 1)
    (fun s => ∃ L R D, allocator_view 1 capacity s L R D ∧
      owner_rank capacity s.owner_state R D ≤ owner_round_bound capacity)
    (fun s => s = initial_state capacity c) e ?_ ?_ k hv
  · rintro s rfl
    obtain ⟨L, R, D, hview⟩ := initial_state_inv capacity c
    refine ⟨L, R, D, hview, ?_⟩
    simp only [initial_state, owner_rank, owner_round_bound]
    omega
  · rintro a s s' o ⟨L, R, D, hview, hrank⟩ hturn
    obtain ⟨L', R', D', hview', hrank', -⟩ :=
      owner_lists_step_bounded capacity a s s' o L R D hview hrank hturn
    exact ⟨L', R', D', hview', hrank'⟩

def round_completion (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k : Nat) : Prop :=
  owner_boundary (e.selected k) (e.states k).owner_state = true

/-- The owner round budget is `credit_interval` at the existentially bounded ownership view:
`Credit k r` says the view holds at `e.states k` with rank `r`. -/
theorem owner_round_interval_descent (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) (L R D : List Nat) :
    allocator_valid capacity c e → allocator_view 1 capacity (e.states lo) L R D →
    (∀ j, lo ≤ j ∧ j < lo + len → ¬ round_completion e j) →
    ∃ L' R' D', allocator_view 1 capacity (e.states (lo + len)) L' R' D' ∧
      count_if (fun k => owner_selected (e.selected k)) lo len +
        owner_rank capacity (e.states (lo + len)).owner_state R' D' ≤
        owner_rank capacity (e.states lo).owner_state R D := by
  intro hv hview hnone
  obtain ⟨r, ⟨L', R', D', hview', rfl⟩, hbound⟩ := credit_interval
    (fun k r => ∃ L1 R1 D1, allocator_view 1 capacity (e.states k) L1 R1 D1 ∧
      r = owner_rank capacity (e.states k).owner_state R1 D1)
    (fun k => owner_selected (e.selected k)) (round_completion e)
    (fun k r ⟨L1, R1, D1, hview1, hr⟩ hgoal => by
      obtain ⟨L2, R2, D2, hview2, hstep⟩ := turn_view_step 1 capacity (e.selected k) (e.states k)
        (e.states (k + 1)) (e.emitted k) L1 R1 D1 hview1
        (execution_step (turn 1) (fun s => s = initial_state capacity c) e k hv)
      have := owner_lists_lengths capacity _ _ _ _ hview1
      have := owner_lists_lengths capacity _ _ _ _ hview2
      have hrank := ownership_rank_step capacity _ _ _ _ _ _ _ _ _ _ hstep
        (by omega) (by omega) (by omega) (by omega)
      have hnb : owner_boundary (e.selected k) (e.states k).owner_state = false := by
        simpa [round_completion] using hgoal
      rw [hnb] at hrank
      exact ⟨_, ⟨L2, R2, D2, hview2, rfl⟩,
        by simp only [Bool.false_eq_true, ↓reduceIte] at hrank; omega⟩)
    lo len _ ⟨L, R, D, hview, rfl⟩ hnone
  exact ⟨L', R', D', hview', hbound⟩

theorem no_round_completion_owner_bound (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) :
    allocator_valid capacity c e →
    (∀ j, lo ≤ j ∧ j < lo + len → ¬ round_completion e j) →
    count_if (fun k => owner_selected (e.selected k)) lo len < 3 * capacity + 5 := by
  intro hv hnone
  obtain ⟨L, R, D, hview, hbound⟩ := execution_owner_rank capacity c e lo hv
  obtain ⟨L', R', D', -, hrank⟩ :=
    owner_round_interval_descent capacity c e lo len L R D hv hview hnone
  have := owner_rank_positive capacity (e.states (lo + len)).owner_state R' D'
  unfold owner_round_bound at hbound
  omega

instance round_completion_dec (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k : Nat) :
    Decidable (round_completion e k) :=
  inferInstanceAs (Decidable (_ = true))

theorem owner_round_selection_bound (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) :
    allocator_valid capacity c e →
    3 * capacity + 5 ≤ count_if (fun k => owner_selected (e.selected k)) lo len →
    ∃ j, (lo ≤ j ∧ j < lo + len) ∧ round_completion e j ∧
      count_if (fun k => owner_selected (e.selected k)) lo (j + 1 - lo) ≤ 3 * capacity + 5 :=
  fun hv hcount => count_if_first _ (round_completion e) (round_completion_dec e) lo len _
    (fun m hnone => no_round_completion_owner_bound capacity c e lo m hv hnone) hcount

/-- Credit for reclaiming `block`: a block still in the remote list pays the owner's current
round plus a full round unless the owner is already collecting; a detached block pays its
position in the drain list. -/
inductive ReclaimCredit (capacity block : Nat) (pc : owner_pc) (R D : List Nat) : Nat → Prop
  | reclaim_remote : block ∈ R →
    ReclaimCredit capacity block pc R D
      (owner_rank capacity pc R D + (if collection_phase pc then 0 else owner_round_bound capacity))
  | reclaim_detached : block ∈ D → ReclaimCredit capacity block pc R D D.length

theorem reclaim_credit_positive (capacity block : Nat) (pc : owner_pc) (R D : List Nat)
    (credit : Nat) : ReclaimCredit capacity block pc R D credit → 0 < credit := by
  intro h
  cases h with
  | reclaim_remote =>
    have := owner_rank_positive capacity pc R D
    split <;> omega
  | reclaim_detached hin => exact List.length_pos_of_mem hin

theorem reclaim_credit_member (capacity block : Nat) (pc : owner_pc) (R D : List Nat)
    (credit : Nat) : ReclaimCredit capacity block pc R D credit → block ∈ R ++ D := by
  intro h
  cases h with
  | reclaim_remote hin => exact List.mem_append_left _ hin
  | reclaim_detached hin => exact List.mem_append_right _ hin

theorem reclaim_credit_bound (capacity block : Nat) (pc : owner_pc) (R D : List Nat)
    (credit : Nat) : ReclaimCredit capacity block pc R D credit →
    owner_rank capacity pc R D ≤ owner_round_bound capacity →
    D.length ≤ capacity → credit ≤ 2 * owner_round_bound capacity := by
  intro h hrank hd
  cases h with
  | reclaim_remote => unfold owner_round_bound at *; split <;> omega
  | reclaim_detached => unfold owner_round_bound; omega

theorem ownership_retire_member (who : Actor) (pc pc' : owner_pc)
    (event : List (CSLObs (Nat × Nat))) (L R D L' R' D' : List Nat) (block : Nat) :
    ownership_transition who pc pc' event L R D L' R' D' →
    block_event tag_retire block event → block ∈ R' := by
  rintro hstep ⟨idx, hev⟩
  cases hstep <;> (try rename_i hem; rcases hem with hem | ⟨b, i, hem⟩ <;> rw [hem] at hev) <;>
    simp_all [csl_emissions_heap_prefix, csl_emissions_heaps, csl_emissions, stamp, tag_retire,
      tag_retry, tag_reclaim, tag_alloc]

theorem ownership_no_premature_alloc (who : Actor) (pc pc' : owner_pc)
    (event : List (CSLObs (Nat × Nat))) (L R D L' R' D' : List Nat) (block : Nat) :
    ownership_transition who pc pc' event L R D L' R' D' →
    block ∉ L → ¬ block_event tag_alloc block event := by
  rintro hstep hnot ⟨idx, hev⟩
  cases hstep <;> (try rename_i hem; rcases hem with hem | ⟨b, i, hem⟩ <;> rw [hem] at hev) <;>
    simp_all [csl_emissions_heap_prefix, csl_emissions_heaps, csl_emissions, stamp, tag_retire,
      tag_retry, tag_reclaim, tag_alloc]

theorem ownership_reclaim_credit_step (capacity : Nat) (who : Actor) (pc pc' : owner_pc)
    (event : List (CSLObs (Nat × Nat))) (L R D L' R' D' : List Nat) (block credit : Nat) :
    ownership_transition who pc pc' event L R D L' R' D' →
    R.length ≤ capacity → D.length ≤ capacity → R'.length ≤ capacity → D'.length ≤ capacity →
    ReclaimCredit capacity block pc R D credit →
    ¬ block_event tag_reclaim block event →
    ∃ credit', ReclaimCredit capacity block pc' R' D' credit' ∧
      (if owner_selected who then 1 else 0) + credit' ≤ credit := by
  intro hstep hr hd hr' hd' hcredit hno
  cases hstep with
  | ownership_drain =>
    cases hcredit with
    | reclaim_remote hin =>
      exact ⟨_, .reclaim_remote hin, by simp [owner_selected, owner_rank, collection_phase]; omega⟩
    | reclaim_detached hin =>
      rcases List.mem_cons.1 hin with rfl | hin
      · simp [block_event, csl_emissions_heap_prefix, csl_emissions] at hno
      · exact ⟨_, .reclaim_detached hin, by simp [owner_selected]; omega⟩
  | ownership_detach =>
    cases hcredit with
    | reclaim_remote hin =>
      exact ⟨_, .reclaim_detached hin,
        by simp [owner_selected, owner_rank, collection_phase]; omega⟩
    | reclaim_detached hin => simp at hin
  | ownership_remote hwho =>
    exact ⟨credit, hcredit, by cases who <;> simp_all [owner_selected]⟩
  | ownership_publish hwho =>
    cases hcredit with
    | reclaim_remote hin =>
      refine ⟨_, .reclaim_remote (List.mem_cons_of_mem _ hin), ?_⟩
      cases who <;> try contradiction
      all_goals cases pc <;> simp_all [owner_selected, owner_rank, collection_phase] <;>
        (repeat' split) <;> omega
    | reclaim_detached hin =>
      refine ⟨_, .reclaim_detached hin, ?_⟩
      cases who <;> simp_all [owner_selected]
  | _ =>
    cases hcredit with
    | reclaim_remote hin =>
      refine ⟨_, .reclaim_remote hin, ?_⟩
      (try cases ‹Bool›) <;>
        simp_all [owner_selected, owner_rank, collection_phase, owner_after_offer,
          owner_round_bound] <;> omega
    | reclaim_detached hin => simp at hin

theorem execution_retired_credit (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k block idx : Nat) :
    allocator_valid capacity c e → stamp (tag_retire, block) idx ∈ csl_emissions (e.emitted k) →
    ∃ L R D credit,
      allocator_view 1 capacity (e.states (k + 1)) L R D ∧
      ReclaimCredit capacity block (e.states (k + 1)).owner_state R D credit ∧
      credit ≤ 2 * owner_round_bound capacity := by
  intro hv hevent
  obtain ⟨L, R, D, hview, hrank⟩ := execution_owner_rank capacity c e k hv
  obtain ⟨L', R', D', hview', hrank', hstep⟩ := owner_lists_step_bounded capacity (e.selected k)
    (e.states k) (e.states (k + 1)) (e.emitted k) L R D hview hrank
    (execution_step (turn 1) (fun s => s = initial_state capacity c) e k hv)
  have hcredit := ReclaimCredit.reclaim_remote (capacity := capacity)
    (pc := (e.states (k + 1)).owner_state) (D := D')
    (ownership_retire_member _ _ _ _ _ _ _ _ _ _ block hstep ⟨idx, hevent⟩)
  refine ⟨L', R', D', _, hview', hcredit, reclaim_credit_bound _ _ _ _ _ _ hcredit hrank' ?_⟩
  have := owner_lists_lengths capacity _ _ _ _ hview'
  omega

/-- Reclamation is the same interval theorem at the reclaim credit; the one-step obligation is
`ownership_reclaim_credit_step`. -/
theorem reclaim_interval_descent (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (lo len : Nat) (L R D : List Nat)
    (block credit : Nat) :
    allocator_valid capacity c e → allocator_view 1 capacity (e.states lo) L R D →
    ReclaimCredit capacity block (e.states lo).owner_state R D credit →
    (∀ j, lo ≤ j ∧ j < lo + len → ¬ block_event tag_reclaim block (e.emitted j)) →
    ∃ L' R' D' credit',
      allocator_view 1 capacity (e.states (lo + len)) L' R' D' ∧
      ReclaimCredit capacity block (e.states (lo + len)).owner_state R' D' credit' ∧
      count_if (fun k => owner_selected (e.selected k)) lo len + credit' ≤ credit := by
  intro hv hview hcredit hnone
  obtain ⟨r, ⟨L', R', D', hview', hcredit'⟩, hbound⟩ := credit_interval
    (fun k r => ∃ L1 R1 D1, allocator_view 1 capacity (e.states k) L1 R1 D1 ∧
      ReclaimCredit capacity block (e.states k).owner_state R1 D1 r)
    (fun k => owner_selected (e.selected k)) (fun j => block_event tag_reclaim block (e.emitted j))
    (fun k r ⟨L1, R1, D1, hview1, hr⟩ hgoal => by
      obtain ⟨L2, R2, D2, hview2, hstep⟩ := turn_view_step 1 capacity (e.selected k) (e.states k)
        (e.states (k + 1)) (e.emitted k) L1 R1 D1 hview1
        (execution_step (turn 1) (fun s => s = initial_state capacity c) e k hv)
      have := owner_lists_lengths capacity _ _ _ _ hview1
      have := owner_lists_lengths capacity _ _ _ _ hview2
      obtain ⟨r1, hcredit1, hrank⟩ := ownership_reclaim_credit_step capacity _ _ _ _ _ _ _ _ _ _
        block r hstep (by omega) (by omega) (by omega) (by omega) hr hgoal
      exact ⟨r1, ⟨L2, R2, D2, hview2, hcredit1⟩, hrank⟩)
    lo len credit ⟨L, R, D, hview, hcredit⟩ hnone
  exact ⟨L', R', D', r, hview', hcredit', hbound⟩

instance block_event_dec (tag block : Nat) (event : List (CSLObs (Nat × Nat))) :
    Decidable (block_event tag block event) :=
  decidable_of_iff (∃ emission ∈ csl_emissions event, emission.value = (tag, block)) <| by
    constructor
    · rintro ⟨⟨v, idx⟩, hin, rfl⟩; exact ⟨idx, hin⟩
    · rintro ⟨idx, hin⟩; exact ⟨_, hin, rfl⟩

theorem no_reclaim_owner_bound (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k block idx len : Nat) :
    allocator_valid capacity c e → stamp (tag_retire, block) idx ∈ csl_emissions (e.emitted k) →
    (∀ j, k + 1 ≤ j ∧ j < k + 1 + len → ¬ block_event tag_reclaim block (e.emitted j)) →
    count_if (fun k => owner_selected (e.selected k)) (k + 1) len < 6 * capacity + 10 := by
  intro hv hevent hnone
  obtain ⟨L, R, D, credit, hview, hcredit, hbound⟩ :=
    execution_retired_credit capacity c e k block idx hv hevent
  obtain ⟨L', R', D', credit', -, hcredit', hrank⟩ :=
    reclaim_interval_descent capacity c e (k + 1) len L R D block credit hv hview hcredit hnone
  have := reclaim_credit_positive _ _ _ _ _ _ hcredit'
  unfold owner_round_bound at hbound
  omega

theorem retired_reclaimed_owner_selection_bound (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k block idx len : Nat) :
    allocator_valid capacity c e → stamp (tag_retire, block) idx ∈ csl_emissions (e.emitted k) →
    6 * capacity + 10 ≤ count_if (fun k => owner_selected (e.selected k)) (k + 1) len →
    ∃ j idx', k < j ∧ j < k + 1 + len ∧ idx < idx' ∧
      stamp (tag_reclaim, block) idx' ∈ csl_emissions (e.emitted j) ∧
      count_if (fun k => owner_selected (e.selected k)) (k + 1) (j - k) ≤ 6 * capacity + 10 := by
  intro hv hret hcount
  obtain ⟨j, hj, ⟨idx', hreclaim⟩, hbound⟩ := count_if_first
    (fun k => owner_selected (e.selected k)) (fun j => block_event tag_reclaim block (e.emitted j))
    (fun j => block_event_dec tag_reclaim block (e.emitted j)) (k + 1) len (6 * capacity + 10)
    (fun m hnone => no_reclaim_owner_bound capacity c e k block idx m hv hret hnone) hcount
  refine ⟨j, idx', by omega, by omega, ?_, hreclaim, by rwa [show j - k = j + 1 - (k + 1) by omega]⟩
  exact execution_event_order (turn 1) (fun s => s = initial_state capacity c) csl_emissions
    AState.acount Indexed.index (turn_counter 1) e k j _ _ hv (by omega) hret hreclaim

theorem retired_eventually_reclaimed (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) :
    allocator_valid capacity c e →
    infinitely (fun k => e.selected k = Owner) →
    ∀ k block idx,
      stamp (tag_retire, block) idx ∈ csl_emissions (e.emitted k) →
      ∃ j idx', k < j ∧ idx < idx' ∧
        stamp (tag_reclaim, block) idx' ∈ csl_emissions (e.emitted j) := by
  intro hv howner k block idx hret
  have hcharged : infinitely (fun j => owner_selected (e.selected j) = true) := fun start => by
    obtain ⟨m, hm, hsel⟩ := howner start
    exact ⟨m, hm, (owner_selected_spec _).2 hsel⟩
  obtain ⟨len, hlen⟩ := infinitely_count_if _ hcharged (6 * capacity + 10) (k + 1)
  obtain ⟨j, idx', hkj, -, hidx, hevent, -⟩ :=
    retired_reclaimed_owner_selection_bound capacity c e k block idx len hv hret hlen
  exact ⟨j, idx', hkj, hidx, hevent⟩

theorem retired_not_reallocated_before_reclaim (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k block idx j : Nat) :
    allocator_valid capacity c e →
    stamp (tag_retire, block) idx ∈ csl_emissions (e.emitted k) → k < j →
    (∀ q idx', k < q ∧ q < j →
      stamp (tag_reclaim, block) idx' ∉ csl_emissions (e.emitted q)) →
    ∀ idx', stamp (tag_alloc, block) idx' ∉ csl_emissions (e.emitted j) := by
  intro hv hret hkj hnone idx' halloc
  obtain ⟨L, R, D, credit, hview, hcredit, -⟩ :=
    execution_retired_credit capacity c e k block idx hv hret
  obtain ⟨Lj, Rj, Dj, creditj, hviewj, hcreditj, -⟩ :=
    reclaim_interval_descent capacity c e (k + 1) (j - (k + 1)) L R D block credit hv hview
      hcredit fun q hq ⟨i, hi⟩ => hnone q i ⟨by omega, by omega⟩ hi
  rw [show k + 1 + (j - (k + 1)) = j by omega] at hviewj hcreditj
  have hnot := owner_lists_disjoint capacity (e.states j) Lj Rj Dj block hviewj
    (reclaim_credit_member _ _ _ _ _ _ hcreditj)
  obtain ⟨L', R', D', -, hstep⟩ := turn_view_step 1 capacity (e.selected j) (e.states j)
    (e.states (j + 1)) (e.emitted j) Lj Rj Dj hviewj
    (execution_step (turn 1) (fun s => s = initial_state capacity c) e j hv)
  exact ownership_no_premature_alloc _ _ _ _ _ _ _ _ _ _ block hstep hnot ⟨idx', halloc⟩

theorem retired_reallocation_requires_reclaim (capacity c : Nat)
    (e : Execution AState Actor (List (CSLObs (Nat × Nat)))) (k j block idx alloc_idx : Nat) :
    allocator_valid capacity c e → k < j →
    stamp (tag_retire, block) idx ∈ csl_emissions (e.emitted k) →
    stamp (tag_alloc, block) alloc_idx ∈ csl_emissions (e.emitted j) →
    ∃ q reclaim_idx, k < q ∧ q < j ∧ idx < reclaim_idx ∧ reclaim_idx < alloc_idx ∧
      stamp (tag_reclaim, block) reclaim_idx ∈ csl_emissions (e.emitted q) := by
  intro hv hkj hret halloc
  have order := execution_event_order (turn 1) (fun s => s = initial_state capacity c)
    csl_emissions AState.acount Indexed.index (turn_counter 1) e
  rcases finite_first (fun q => block_event tag_reclaim block (e.emitted q))
      (fun q => block_event_dec tag_reclaim block (e.emitted q)) (k + 1) (j - (k + 1)) with
    hnone | ⟨q, hq, ⟨qi, hreclaim⟩, -⟩
  · exact absurd halloc <| retired_not_reallocated_before_reclaim capacity c e k block idx j hv
      hret hkj (fun q qi hq hin => hnone q ⟨by omega, by omega⟩ ⟨qi, hin⟩) alloc_idx
  · exact ⟨q, qi, by omega, by omega, order k q _ _ hv (by omega) hret hreclaim,
      order q j _ _ hv (by omega) hreclaim halloc, hreclaim⟩

theorem source_retired_eventually_reclaimed (capacity : Nat) (ctx : Ctx) (c : Nat)
    (se : Execution (Pool sE Bn 3 × SSig) Actor (List (CSLObs (Nat × Nat)))) :
    allocator_source_valid capacity ctx c se →
    infinitely (fun k => se.selected k = Owner) →
    ∀ k block idx,
      CSLObs.emit (stamp (tag_retire, block) idx) ∈ se.emitted k →
      ∃ j idx', k < j ∧ idx < idx' ∧
        CSLObs.emit (stamp (tag_reclaim, block) idx') ∈ se.emitted j := by
  intro hvalid howner k block idx hretire
  have halign := source_execution_complete (allocator_simulation 1 capacity)
    (source_pool0 1) _ (initial_state capacity c) se (allocator_execution capacity c se.selected)
    (initial_state_inv capacity c) ⟨heq_refl _, heq_refl _, rfl⟩
    (pool_equ_guard _ _ (source_pool0_initial capacity c)) hvalid
    (allocator_execution_valid capacity c se.selected) (fun _ => rfl)
  rw [(halign k).2.2.2] at hretire
  obtain ⟨j, idx', hkj, hidx, hreclaim⟩ := retired_eventually_reclaimed capacity c _
    (allocator_execution_valid capacity c se.selected) howner k block idx
    ((csl_emissions_in _ _).2 hretire)
  refine ⟨j, idx', hkj, hidx, ?_⟩
  rw [(halign j).2.2.2]
  exact (csl_emissions_in _ _).1 hreclaim

end Examples.CSL.Allocator.Liveness

-- Not ported: none; Rocq `reclaim_credit` (a Prop inductive) is `ReclaimCredit`, the Rocq
-- `block_event_dec`/`round_completion_dec` `sumbool` definitions are `Decidable` instances.
